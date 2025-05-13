import os
import ray
import time
import shutil
import pickle
import hashlib
import logging
import subprocess
import numpy as np
from tqdm.auto import tqdm
from ray.util import ActorPool
from vllm import LLM, SamplingParams
from transformers import AutoTokenizer
from typing import Any, Dict, List, Tuple, Callable
#from utils.gcloud_utils import execute_on_all_workers, cleanup_dir, TPU_NAME, ZONE, HOME,
from utils.gcloud_utils import  read_file, write_data, execute_on_all_workers

START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = 'Complete the following Lean 4 code:\n\n```lean4\nimport Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'

# CHECKPOINT_TMP_DIR = f'{HOME}/ckpt_tmp'
__DEBUG__ = os.getenv("DEBUG", 'False').lower() in ('true', '1', 't')

def get_prompt(
        test_info: Dict, 
        tokenizer: Any, 
        max_length: int, 
        invoke_type, 
) -> str:
    if invoke_type == 'conjecture':
        shared_lemma = test_info['shared_lemma_statement']
        easy_theorem = test_info['statement'] + test_info['proof']
        prompt = f'Complete the following Lean 4 code:\n\n```lean4\n' \
            f'{INVOKED_LEMMA}\n{shared_lemma.strip()}\n{START_LEMMA_STMT}\n' \
            f'{easy_theorem.strip()}\n{START_THM}\n theorem'
    else:
        if ('header' in test_info) and (test_info['header'] is not None):
            prompt = 'Complete the following Lean 4 code:\n\n```lean4\n' + test_info["header"] + test_info["statement"].strip()
        else:
            prompt = f'{PROVER_PROMPT}\n{test_info["statement"].strip()}'

    return right_truncate(prompt, tokenizer, max_length)

def get_checkpoint_name(directory):
    checkpoint_files = []
    for file in os.listdir(directory):
        if file.startswith("checkpoint"):
            checkpoint_files.append(os.path.join(directory, file))
    assert(len(checkpoint_files) == 1)
    return checkpoint_files[0]

def right_truncate(s, tokenizer, max_tokens):
    tokens = tokenizer.encode(
            s,
            return_tensors="pt",
            padding="longest",
            max_length=max_tokens,
            truncation=True,
        )[0]
    return tokenizer.decode(tokens, skip_special_tokens = True)

# Create a class to do batch inference.
@ray.remote(num_gpus=1)
class LLMPredictor:
    def __init__(self, model, tokenizer, id, debug = False, **kwargs):
        # Create an LLM.
        self.kwargs = kwargs
        self.model = model
        self.llm = None
        self.tokenizer = AutoTokenizer.from_pretrained(tokenizer)
        self.tokenizer.truncation_side = 'left'
        self.tokenizer.pad_token = self.tokenizer.eos_token
        self.id = id

    def predict(self, batch: Dict[str, List], sampling_params: Any) -> List[Dict]:
        if self.llm is None:
            self.llm = LLM(model=self.model, dtype='bfloat16', max_model_len = 1024, gpu_memory_utilization=0.85, **self.kwargs)
        outputs = self.llm.generate(batch['text'], sampling_params, use_tqdm=(self.id == 0))
        results = []
        for id, output in zip(batch['ids'], outputs):
            result = {"id": id, "text": output.outputs[0].text}
            if sampling_params.logprobs is not None:
                result["logprobs"] = output.outputs[0].logprobs
            results.append(result)
        return results
    
    def tokenize(self, batch: List[Dict], **kwargs) -> List[Dict]:
        results = []
        for id, test_info in zip(batch['ids'], batch['queries']):
            result = {"id": id, "text": get_prompt(test_info, self.tokenizer, **kwargs)}
            results.append(result)
        return results

    def get_id(self):
        # we use this function to check if the actors finished initialization
        return self.id

def ray_completion(
        pool: ActorPool,
        prompts: List[str],
        num_workers: int, 
        temperature: float = 0.7,
        max_tokens: int = 1024,
        seed: int = 0,
        logprobs: int = None,
        cache_dir: str = None,
) -> List[Dict]:
    # Create a unique cache key based on the function's inputs
    cache_key = hashlib.md5(pickle.dumps((prompts, temperature, max_tokens, seed, logprobs))).hexdigest()
    cache_file_path = os.path.join(cache_dir, f"{cache_key}.pkl") if cache_dir else None
    cache_file_path_inputs = os.path.join(cache_dir, f"{cache_key}_inputs.pkl") if cache_dir else None

    # Check if the result is already cached
    cache_ret = read_file(cache_file_path)
    if cache_ret is not None:
        assert len(cache_ret) == len(prompts), f"len(cache_ret)={len(cache_ret)}, len(prompts)={len(prompts)}"
        return cache_ret

    if (cache_file_path_inputs is not None) and (__DEBUG__):
        write_data(pickle.dumps(prompts), cache_file_path_inputs, 'pickle')
    # Create a sampling params object.
    sampling_params = SamplingParams(temperature=temperature, top_p=1.0, seed=seed, max_tokens = max_tokens, logprobs = logprobs)

    rng = np.random.default_rng(seed)
    requests = [(prompts[i], i) for i in range(len(prompts))]
    rng.shuffle(requests)

    batches = []
    batch_size = (len(prompts) + num_workers - 1) // num_workers
    for i in range(num_workers):
        l, r = i * batch_size, min((i + 1) * batch_size, len(prompts))
        if r > l:
            batch = {'text': [requests[j][0] for j in range(l,r)], 'ids': [requests[j][1] for j in range(l,r)]}
            batches.append(batch)

    pool.map_unordered(lambda actor, b: actor.predict.remote(b, sampling_params), batches)

    results = []
    for _ in range(len(batches)):
        results.extend(pool.get_next_unordered())
    # sort results by id
    results = sorted(results, key=lambda x: x["id"])
    assert len(results) == len(prompts), f"len(results)={len(results)}, len(prompts)={len(prompts)}"
    assert all(result["id"] == i for i, result in enumerate(results)), "found non-consecutive ids"

    if cache_file_path is not None:
        write_data(pickle.dumps(results), cache_file_path, 'pickle')
    return results

def ray_get_embeddings(
    pool: ActorPool,
    inputs: List[Dict],
    cache_dir: str = None,
) -> np.ndarray:
    """
    Distributes input texts across a pool of ModelWorker actors to compute embeddings in batches.

    Args:
        pool (ActorPool): A Ray ActorPool containing ModelWorker actors.
        inputs (List[Dict]): A list of test_info dictionaries containing the input texts.

    Returns:
        List[np.ndarray]: A list of embedding arrays corresponding to the input texts, maintaining the original order.
    """
    cache_key = hashlib.md5(pickle.dumps(inputs)).hexdigest()
    cache_file_path = os.path.join(cache_dir, f"{cache_key}.pkl") if cache_dir else None
    cache_file_path_inputs = os.path.join(cache_dir, f"{cache_key}_inputs.pkl") if cache_dir else None

    # Check if the result is already cached
    cache_ret = read_file(cache_file_path)
    if cache_ret is not None:
        assert len(cache_ret) == len(inputs), f"len(cache_ret)={len(cache_ret)}, len(prompts)={len(inputs)}"
        return np.array(cache_ret)

    if cache_file_path_inputs is not None:
        write_data(pickle.dumps(inputs), cache_file_path_inputs, 'pickle')

    batch_size = 12
    total = len(inputs)
    
    # Enumerate inputs to keep track of their original indices
    indexed_inputs = list(enumerate([test_info['statement'] for test_info in inputs]))
    batches = [indexed_inputs[i:i + batch_size] for i in range(0, total, batch_size)]
    
    # Submit all batches to the pool and collect futures
    pool.map_unordered(lambda actor, batch: actor.submit_batch.remote(tuple(batch)), batches)
    
    results = []
    for _ in tqdm(range(len(batches)), desc="Collecting embeddings"):
        results += list(pool.get_next_unordered())

    # sort results by id
    assert len(results) == total, f"len(results)={len(results)}, total={total}"
    results = sorted(results, key=lambda x: x[0])
    ordered_embeddings = [embedding for _, embedding in results]
    
    if cache_file_path is not None:
        write_data(pickle.dumps(ordered_embeddings), cache_file_path, 'pickle')
    return np.array(ordered_embeddings)

def ray_get_prompt(
        pool: ActorPool,
        num_workers: int, 
        queries: List[Dict],
        **kwargs,
) -> List[Dict]:
    logging.debug(f"Start tokenizing {len(queries)} prompts...")
    rng = np.random.default_rng(0)
    requests = [(queries[i], i) for i in range(len(queries))]
    rng.shuffle(requests)

    batches = []
    batch_size = (len(queries) + num_workers - 1) // num_workers
    for i in range(num_workers):
        l, r = i * batch_size, min((i + 1) * batch_size, len(queries))
        if r > l:
            batch = {'queries': [requests[j][0] for j in range(l,r)], 'ids': [requests[j][1] for j in range(l,r)]}
            batches.append(batch)

    pool.map_unordered(lambda actor, b: actor.tokenize.remote(b, **kwargs), batches)

    results = []
    for _ in range(len(batches)):
        results.extend(pool.get_next_unordered())
    # sort results by id
    results = sorted(results, key=lambda x: x["id"])
    assert len(results) == len(queries), f"len(results)={len(results)}, len(prompts)={len(queries)}"
    assert all(result["id"] == i for i, result in enumerate(results)), "found non-consecutive ids"
    logging.debug(f"Tokenization complete.")
    return [result["text"] for result in results]

# def copy_checkpoints_all(src_dir, dest_dir):
#     if src_dir is None:
#         execute_on_all_workers(f'rm -r {dest_dir}; mkdir -p {dest_dir};')
#         return None
#     else:
#         checkpoint_name = src_dir.rsplit('/', 1)[-1]
#         execute_on_all_workers(f'rm -r {dest_dir}; mkdir -p {dest_dir}; gcloud storage cp -r {src_dir} {dest_dir}')
#         return os.path.join(dest_dir, checkpoint_name)

def create_inference_actors(
        model_dir: str, 
        tokenizer_path: str,
        num_workers: int = None, 
        **kwargs
) -> List:
#    execute_on_all_workers(f'rm -r {CHECKPOINT_TMP_DIR}; mkdir -p {CHECKPOINT_TMP_DIR}')

    # if 'gs://' in model_dir:
    #     model_dir = copy_checkpoints_all(model_dir, CHECKPOINT_TMP_DIR)

    logging.debug('Creating ray actors...')
    if num_workers is None:
        num_workers = int(ray.cluster_resources()['GPU'])
    ray_workers = [LLMPredictor.remote(model_dir, tokenizer_path, id, **kwargs) for id in range(num_workers)]
   # if not __DEBUG__:
       # assert len(ray_workers) > 4, f"Number of workers is {len(ray_workers)}, expected at least 4"
    # ray.get([actor.get_id.remote() for actor in ray_workers])
    logging.debug(f'Ray inference actors created. Number of workers: {len(ray_workers)}')
    return ray_workers, model_dir

def create_embedding_actors(
        model_dir: str, 
        tokenizer_path: str,
        num_workers: int = None, 
        **kwargs
) -> List:
    from utils.embedding_utils import EmbeddingWorker
    if num_workers is None:
        num_workers = int(ray.cluster_resources()['GPU'])
    ray_workers = [EmbeddingWorker.remote(model_dir, None, tokenizer_path) for id in range(num_workers)]
    # ray.get([actor.get_id.remote() for actor in ray_workers])
    logging.debug(f'Ray embedding actors created. Number of workers: {len(ray_workers)}')
    return ray_workers

def init_ray_cluster(numcpus,numgpus):
    # if __DEBUG__:
    #     ray.init(namespace="prover")
    #     return
    
    #compute_command = f'bash ../run_inference.sh'
    #os.system(compute_command)

    os.system("ray stop")
    os.system(f"ray start --head --port=6379 --num-cpus={numcpus} --num-gpus={numgpus}")

    print('Ray cluster initialized.')
    ray.init(namespace="prover")
    print(ray.cluster_resources())
   # assert int(ray.cluster_resources()['GPU']) > 1, f"CPU count is {ray.cluster_resources()['GPU']}, expected at least 4"

def get_lemma_key(test_info):
    return test_info['statement']

def update_lemma_mapping(lemma_mapping, test_info):
    lemma_mapping[get_lemma_key(test_info)] = test_info['lemma_id']

def insert_lemma(lemma_mapping, test_info):
    key = get_lemma_key(test_info)
    if key not in lemma_mapping:
        lemma_mapping[key] = len(lemma_mapping)
    test_info['lemma_id'] = lemma_mapping[key]