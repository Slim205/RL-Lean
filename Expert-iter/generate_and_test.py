import re
import time
import os
import json
import argparse
import traceback
from typing import List, Dict, Any
import ray
from ray.util.actor_pool import ActorPool
import numpy as np
import pickle
import hashlib
from tqdm.auto import tqdm
from vllm import LLM, SamplingParams
from datasets import load_dataset
from client.client import Lean4Client, batch_verify_proof
from sentence_transformers import SentenceTransformer, util
import fire
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Any, Sequence, Tuple


def extrac_code(inputs):
    try:
        HEADER = "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n"
        return HEADER + 'theorem' + inputs.split(':= by')[0] + ':= by sorry'
    except:
        return "None"

def get_verification_results(old_result) : 
    custom_id= old_result['custom_id']
    system_messages = old_result['error']
    old_result = old_result['response']
    try:
        result = {
            "sorries" : old_result.get('sorries', []), 
            "tactics" : old_result.get('tactics', []),
            "errors" : [m for m in old_result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in old_result.get('messages', []) if m['severity'] == 'warning'],
            "infos" : [m for m in old_result.get('messages', []) if m['severity'] == 'info'],
            "system_messages" : system_messages,
            "system_errors" : None,
        }
        result['pass'] = not result['errors']
        result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
        result['verify_time']  = old_result['time']
    except:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages,
            "tactics" : []
        }
    result['custom_id'] = custom_id
    return result

def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def save_statements(statements, filename):
    with open(filename, 'w') as f:
        json.dump(statements, f, indent=1)

def add_new_statements(new_statements, filename):
    existing = load_statements(filename)
    combined = existing + new_statements
    save_statements(combined, filename)


def _split_round_robin(indexed: List[Tuple[int, Any]], n: int) -> List[List[Tuple[int, Any]]]:
    """Evenly split (index, sample) pairs into n round-robin shards."""
    return [indexed[i::n] for i in range(n)]

def _run_one_shard(shard: List[Tuple[int, Any]], url: str, timeout: int, num_proc: int, batch_size: int):
    """Run a single batch_verify_proof call for a shard and keep indices to merge later."""
    if not shard:
        return []  # nothing to do
    indices, shard_samples = zip(*shard)
    client = Lean4Client(base_url=url, disable_cache=False)
    shard_results = batch_verify_proof(
        samples=list(shard_samples),
        client=client,
        timeout=timeout,
        num_proc=num_proc,
        batch_size=batch_size,
    )
    # zip results back with their original indices so we can reconstruct order
    return list(zip(indices, shard_results))

def parallel_verify_over_urls(
    samples: Sequence[Any],
    urls: Sequence[str],
    timeout: int = 60,
    num_proc: int = 64,
    batch_size: int = 1,
) -> List[Any]:
    """
    Split samples across len(urls) shards and verify them in parallel (one call per URL).
    Returns a list aligned with the original samples order.
    """

    indexed = list(enumerate(samples))
    shards = _split_round_robin(indexed, len(urls))

    combined: List[Any] = [None] * len(samples)

    # Outer layer: threads. Inner layer: batch_verify_proof can keep using num_proc processes.
    with ThreadPoolExecutor(max_workers=len(urls)) as ex:
        futures = [
            ex.submit(_run_one_shard, shards[i], urls[i], timeout, num_proc, batch_size)
            for i in range(len(urls))
            if shards[i]  # skip empty shard
        ]
        for fut in as_completed(futures):
            shard_pairs = fut.result()  # may raise if the shard failed; handle as you prefer
            for idx, result in shard_pairs:
                combined[idx] = result

    return combined

START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = (
    "Complete the following Lean 4 code:\n\n```lean4\n"
    "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n"
    "open BigOperators Real Nat Topology Rat\n"
)

def get_prompt(sample):
    shared_lemma = ''
    easy_theorem = sample
    prompt = (
        f"{PROVER_PROMPT}"
        f"{INVOKED_LEMMA}\n{shared_lemma.strip()}\n"
        f"{START_LEMMA_STMT}\n{easy_theorem.strip()}\n"
        f"{START_THM}\n theorem"
    )
    return prompt

# -------------------------------
# Ray actor per-GPU for vLLM
# -------------------------------
@ray.remote(num_gpus=1)
class LLMPredictor:
    def __init__(self, model_name: str, worker_id: int, debug: bool = False, **llm_kwargs):
        self.model_name = model_name
        self.worker_id = worker_id
        self.debug = debug
        self.llm_kwargs = llm_kwargs
        self.llm = None  # lazy init

    def get_id(self) -> int:
        return self.worker_id

    def _maybe_init(self):
        if self.llm is None:
            # Each actor owns one GPU; avoid TP here (TP=1)
            self.llm = LLM(model=self.model_name, tensor_parallel_size=1, **self.llm_kwargs)

    def predict(self, batch: Dict[str, List[str]], sampling_params_dict: Dict[str, Any]) -> List[Dict]:
        """batch = {'text': [...], 'ids': [...]}; returns [{'id': i, 'texts': [cand1, cand2, ...]}]"""
        self._maybe_init()
        sp = SamplingParams(**sampling_params_dict)
        outputs = self.llm.generate(
            batch['text'],
            sp,
            use_tqdm=(self.worker_id == 0),  # show ETA on worker 0
        )
        results = []
        for req_id, req_out in zip(batch['ids'], outputs):
            texts = [o.text for o in req_out.outputs]  # support n>1
            item = {"id": req_id, "texts": texts}
            if sp.logprobs is not None:
                item["logprobs"] = [o.logprobs for o in req_out.outputs]
            results.append(item)
        return results


def _infer_num_workers(user_num_workers: int | None) -> int:
    if user_num_workers is not None and user_num_workers > 0:
        return user_num_workers
    try:
        # Prefer cluster-wide GPU count
        return int(round(ray.cluster_resources().get("GPU", 1)))
    except Exception:
        return 1

def _build_batches(prompts: List[str], num_workers: int) -> List[Dict[str, List]]:
    requests = [(prompts[i], i) for i in range(len(prompts))]
    rng = np.random.default_rng(0)
    rng.shuffle(requests)
    batches = []
    batch_size = (len(prompts) + num_workers - 1) // num_workers
    for i in range(num_workers):
        l, r = i * batch_size, min((i + 1) * batch_size, len(prompts))
        if r > l:
            batches.append({
                'text': [requests[j][0] for j in range(l, r)],
                'ids':  [requests[j][1] for j in range(l, r)],
            })
    return batches

def ray_completion(
    pool: ActorPool,
    prompts: list[str],
    num_workers: int,
    sampling_params: dict,
    show_progress: bool = True,
) -> list[dict]:
    """
    Returns ordered list: [{'id': i, 'texts': [..]}, ...] aligned to prompts.

    Fix: we must SUBMIT work to the pool (pool.submit) before calling get_next_unordered().
    """
    batches = _build_batches(prompts, num_workers)

    # --- SUBMIT ALL TASKS ---
    for b in batches:
        pool.submit(lambda a, bb: a.predict.remote(bb, sampling_params), b)

    # --- DRAIN RESULTS ---
    results: list[dict] = []
    if show_progress:
        pbar = tqdm(total=len(batches), desc="Generating (Ray)", unit="batch")

    remaining = len(batches)
    while remaining > 0:
        try:
            res = pool.get_next_unordered()  # one batch's result (list[dict])
        except StopIteration:
            # Shouldn't happen if we've submitted 'remaining' tasks,
            # but guard just in case to avoid hard crash.
            break
        results.extend(res)
        remaining -= 1
        if show_progress:
            pbar.update(1)

    if show_progress:
        pbar.close()

    # Reorder to match original prompt order and sanity-check
    results = sorted(results, key=lambda x: x["id"])
    assert len(results) == len(prompts), f"mismatch: {len(results)} vs {len(prompts)}"
    assert all(results[i]["id"] == i for i in range(len(results))), "non-consecutive ids"
    return results

def make_actor_pool(model_name: str, num_workers: int, **llm_kwargs) -> ActorPool:
    workers = [LLMPredictor.remote(model_name, i, **llm_kwargs) for i in range(num_workers)]
    # ensure actors are alive and finished init
    _ = ray.get([w.get_id.remote() for w in workers])
    return ActorPool(workers)

def get_complexity_scores_ray(data_list: List[Dict], n: int, urls: list[str], pool: ActorPool, num_workers: int) -> Dict[str, List[str]]:
    """Ray-parallel generation for the second phase; verification stays as in your code."""
    model_inputs = []
    for data in data_list:
        text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
            formal_statement=data['proof'][:-6],
        )
        model_inputs.append(text)

    print(model_inputs[0])

    sampling_params = dict(
        temperature=1,
        max_tokens=2048,
        top_p=0.95,
        n=n,
    )

    # === Generation Phase 2 (progress + timing) ===
    print("\n[Phase 2] Starting vLLM generation for complexity scoring …")
    t0 = time.perf_counter()
    gen_results = ray_completion(pool, model_inputs, num_workers, sampling_params, show_progress=True)
    t1 = time.perf_counter()
    print(f"[Phase 2] Finished in {t1 - t0:.1f}s\n")

    def extrac_code_block(full_text: str) -> str:
        try:
            # keep your original heuristic
            assert len(full_text.split('```lean4\n')[1]) > 0
            return full_text.split('```lean4\n')[1]
        except:
            return "None"

    # Map back to codes per original data item
    is_correct: Dict[str, List[str]] = {}
    to_inference_codes = []
    for i, data in enumerate(data_list):
        cand_texts = gen_results[i]["texts"]  
        full_codes = [extrac_code_block(model_inputs[i] + ct) for ct in cand_texts]
        data["full_code"] = full_codes
        to_inference_codes += [{"name": data["custom_id"], "code": code} for code in full_codes]
        is_correct[data["custom_id"]] = []

    samples = []
    for i in range(len(to_inference_codes)):
        to_inference_codes[i]["custom_id"] = f"{to_inference_codes[i]['name']}_{i}"
        samples.append({"custom_id": to_inference_codes[i]["custom_id"] , "proof": to_inference_codes[i]["code"] })

    results = parallel_verify_over_urls(
        samples=samples,
        urls=urls,
        timeout=60,
        num_proc=64,   
        batch_size=1,
    )

    compilation_results = [get_verification_results(res) for res in results]
    compilation_dict = {r['custom_id']: r for r in compilation_results}
    for code in to_inference_codes:
        cid = code['custom_id']
        if cid in compilation_dict:
            code['compilation_result'] = compilation_dict[cid]
            if code['compilation_result']['complete']:
                is_correct[code['name']].append(code['code'])
    return is_correct


def generate_and_test(
    model_name: str,
    iteration: int,
    path: str,
    n_sample: int = -1,
    num_workers: int | None = None,
    dtype: str = "bfloat16",
    max_model_len: int = 4096,
    gpu_memory_utilization: float = 0.85,
):
    if len(load_statements(path)) > 0:
        return
    else:
        save_statements([], path)

    ray.init(address="auto", ignore_reinit_error=True)

    dataset = load_dataset("Slim205/LeanWorkbook", split='train')
    print(model_name)
    print(iteration)
    print(path)
    if n_sample and n_sample > 0:
        dataset = dataset.select(range(n_sample))
    
    data_list_full = []
    for sample in dataset:
        data_list_full.append({'formal_statement': sample['formal_statement']})

    model_inputs = [get_prompt(d['formal_statement']) for d in data_list_full]
    print(model_inputs[0])

    # Build Ray pool
    nw = _infer_num_workers(num_workers)
    print(f"[Ray] Using {nw} worker(s).")
    pool = make_actor_pool(
        model_name,
        nw,
        dtype=dtype,
        max_model_len=max_model_len,
        gpu_memory_utilization=gpu_memory_utilization,
        trust_remote_code=True,
        swap_space=8,
    )

    # === Generation Phase 1 (Ray) ===
    sampling_params_phase1 = dict(
        temperature=1,
        max_tokens=2048,
        top_p=0.95,
        n=1,
        seed=1,
    )
    print("\n[Phase 1] Starting vLLM generation for new statements …")
    t0 = time.perf_counter()
    gen_results = ray_completion(pool, model_inputs, nw, sampling_params_phase1, show_progress=True)
    t1 = time.perf_counter()
    print(f"[Phase 1] Finished in {t1 - t0:.1f}s\n")

    # Build data for verification prefilter
    data = []
    for i in range(len(data_list_full)):
        for text in gen_results[i]["texts"]:  # n=1, but keeps structure
            code = extrac_code(text)
            if code != 'None':
                data.append({'custom_id': i, 'proof': code, 'theorem': data_list_full[i]['formal_statement']})
    print(data[0] if data else "No valid generations found in Phase 1.")

    # Filter with semantic similarity
    encoder_model = SentenceTransformer('all-MiniLM-L6-v2')  
    samples = []
    statement_dict = {}
    new_theorems=[]
    old_theorems = []
    for sample in data:
        new_theorem = extract_theorem(sample['proof'])
        old_theorems.append(extract_theorem(sample['theorem']))
        new_theorems.append(new_theorem)
    emb_old = encoder_model.encode(old_theorems, convert_to_tensor=True)
    emb_new = encoder_model.encode(new_theorems, convert_to_tensor=True)
    i = 0
    for sample in data:
        cosine_old_new = util.cos_sim(emb_old[i], emb_new[i]).item()
        if cosine_old_new < 0.9 and cosine_old_new > 0.4:
            statement_dict[sample['custom_id']] = (extract_theorem(sample['proof']), extract_theorem(sample['theorem']))
            samples.append({'proof': sample['proof'], 'custom_id': sample['custom_id']})
        i+=1

    urls = [
    "http://holy8a14401:12332" ,"http://holy8a14104:12332", "http://holy8a14101:12332",
    "http://holy8a14301:12332",  "http://holy8a14103:12332",  "http://holy8a14107:12332",
     "http://holy8a14108:12332", "http://holy8a14302:12332", "http://holy8a14202:12332",
     "http://holy8a14105:12332", "http://holy8a14106:12332", "http://holy8a14201:12332",
     "http://holy8a14102:12332",

    ]  
    results = parallel_verify_over_urls(
        samples=samples,
        urls=urls,
        timeout=60,
        num_proc=64,   
        batch_size=1,
    )

    list_eval_complexity = []
    for x in results:
        res = get_verification_results(x)
        if res['pass']:
            list_eval_complexity.append(res['custom_id'])

    new_samples = [s for s in samples if s['custom_id'] in list_eval_complexity]

    # === Phase 2 (Ray) ===
    n = 8
    statements_to_save = []
    if len(new_samples) > 0:
        complexity_scores = get_complexity_scores_ray(new_samples, n, urls, pool, nw)
        for x, y in complexity_scores.items():
            if len(y) <= 0.5 * n and len(y) > 0:
                statements_to_save.append({
                    'old': statement_dict[x][1],
                    'new': statement_dict[x][0],
                    'step': iteration,
                    'proof': list(set(y))[:16]
                })

    print(len(statements_to_save))
    if len(statements_to_save) > 0:
        add_new_statements(statements_to_save, path)

if __name__ == "__main__":
    fire.Fire(generate_and_test)
