from client.client import Lean4Client, batch_verify_proof
import traceback
import re
import requests
import json
import os
from sentence_transformers import SentenceTransformer, util
from typing import List, Any, Sequence, Tuple, Dict
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Any, Sequence, Tuple


def _split_round_robin_eval(indexed: List[Tuple[int, Any]], n: int) -> List[List[Tuple[int, Any]]]:
    """Evenly split (index, sample) pairs into n round-robin shards."""
    return [indexed[i::n] for i in range(n)]

def _run_one_shard_eval(shard: List[Tuple[int, Any]], url: str, timeout: int, num_proc: int, batch_size: int):
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
    shards = _split_round_robin_eval(indexed, len(urls))

    combined: List[Any] = [None] * len(samples)

    # Outer layer: threads. Inner layer: batch_verify_proof can keep using num_proc processes.
    with ThreadPoolExecutor(max_workers=len(urls)) as ex:
        futures = [
            ex.submit(_run_one_shard_eval, shards[i], urls[i], timeout, num_proc, batch_size)
            for i in range(len(urls))
            if shards[i]  # skip empty shard
        ]
        for fut in as_completed(futures):
            shard_pairs = fut.result()  # may raise if the shard failed; handle as you prefer
            for idx, result in shard_pairs:
                combined[idx] = result

    return combined

  
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


def split_round_robin(indexed: List[Tuple[int, Any]], n: int) -> List[List[Tuple[int, Any]]]:
    """Evenly split (index, sample) pairs into n round-robin shards."""
    return [indexed[i::n] for i in range(n)]

def run_one_shard(shard: List[Tuple[int, str]], url: str, n: int):
    """Run a single model inference call for a shard and keep indices to merge later."""
    if not shard:
        return []  # nothing to do
    
    indices, shard_inputs = zip(*shard)
    
    payload = {
        "inputs": list(shard_inputs),
        "pass_n": n
    }
    
    try:
        response = requests.post(url, json=payload)
        response.raise_for_status()
        model_outputs = response.json()
        
        # zip results back with their original indices so we can reconstruct order
        return list(zip(indices, model_outputs))
        
    except requests.exceptions.RequestException as e:
        print(f"Error calling server at {url}: {e}")
        # Return empty results for failed indices to maintain order
        return [(idx, None) for idx in indices]

def parallel_inference_over_urls(
    model_inputs: List[str],
    urls: List[str],
    n: int
) -> List[Any]:
    """
    Split model inputs across len(urls) shards and process them in parallel.
    Returns a list aligned with the original inputs order.
    """
    indexed = list(enumerate(model_inputs))
    shards = split_round_robin(indexed, len(urls))
    combined: List[Any] = [None] * len(model_inputs)
    
    # Process shards in parallel across different URLs
    with ThreadPoolExecutor(max_workers=len(urls)) as executor:
        futures = [
            executor.submit(run_one_shard, shards[i], urls[i], n)
            for i in range(len(urls))
            if shards[i]  # skip empty shards
        ]
        
        for future in as_completed(futures):
            try:
                shard_pairs = future.result()
                for idx, result in shard_pairs:
                    combined[idx] = result
            except Exception as e:
                print(f"Shard processing failed: {e}")
                # Handle failed shard as needed
    
    return combined
def get_complexity_scores(data_list,n,urls_cpu) : 

    model_inputs = []
    for data in data_list:    
        text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=data['proof'][:-6],
            )
        model_inputs.append(text)
    print(model_inputs[0])

    url_gpus =['http://holygpu8a22406:8000/generate', 'http://holygpu8a22603:8000/generate',
    'http://holygpu8a22505:8000/generate', 'http://holygpu8a22301:8000/generate']

    model_outputs = parallel_inference_over_urls(model_inputs, url_gpus, n)
    
    assert len(model_outputs) == len(model_inputs)

    def extrac_code(inputs):
        try:
            return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)
        except:
            return "None"

    is_correct = {}
    to_inference_codes = []
    for i in range(len(data_list)):
        data_list[i]["model_input"] = model_inputs[i]
        data_list[i]["model_outputs"] = [output for output in model_outputs[i]]
        data_list[i]["full_code"] = [extrac_code(model_inputs[i] + output) for output in model_outputs[i]] 

        to_inference_codes += [{"name": data_list[i]["custom_id"], "code": code} for code in data_list[i]["full_code"]]
        is_correct[data_list[i]["custom_id"]] = []

    samples= []
    for i in range(len(to_inference_codes)):
        to_inference_codes[i]["custom_id"] = f"{to_inference_codes[i]['name']}_{i}"
        samples.append({"custom_id": to_inference_codes[i]["custom_id"] , "proof": to_inference_codes[i]["code"] })

    results = parallel_verify_over_urls(
        samples=samples,
        urls=urls_cpu,
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

def get_step(statements_dict) :
    if len(statements_dict) == 0 : 
        return 0
    return statements_dict[-1]['step']

def get_goal(thm) : 
   
    if thm.startswith(':') :
        return thm[2:]
    elif  ') :' in thm : 
        ch = ') :'
        return thm.split(ch)[1].strip()
    elif  '):' in thm : 
        ch = '):'
        return thm.split(ch)[1].strip()
    elif  '} :' in thm : 
        ch = '} :'
        return thm.split(ch)[1].strip()
    elif  '}:' in thm : 
        ch = '}:'
        return thm.split(ch)[1].strip()
    elif  '] :' in thm : 
        ch = '] :'
        return thm.split(ch)[1].strip()
    elif  ']:' in thm : 
        ch = ']:'
        return thm.split(ch)[1].strip()

    return thm
def pat(text: str) -> str:
    """Coarse syntactic pattern of a Lean statement."""
    s = get_goal(text)
    s = re.sub(r'\s+', ' ', s)
    if s.startswith("¬") :
        return "negation"

    if s.startswith("∃") :
        return "exists"
    if s.startswith("∀") :
        return "forall"
    if "↔" in s :
        return "iff"
    if "∨" in s :
        return "or"
    if "∧" in s :
        return "and"
    if " → " in s:
        return "imp"
    return "atom"

def get_results(data) :
    split = data[0]['split']
    path = f'/n/netscratch/amin_lab/Lab/slim/RL/storage/conjecturer_V1/data/{split}.json'
    statements_dict = load_statements(path)
    
    global_step = get_step(statements_dict)

    encoder_model = SentenceTransformer('all-MiniLM-L6-v2')  
    samples = []
    statement_dict = {}
    new_theorems=[]
    old_theorems = []
    scores=[]
    for sample in data:
        new_theorem = extract_theorem(sample['proof'])
        old_theorems.append(extract_theorem(sample['theorem']))
        new_theorems.append(new_theorem)
    emb_old = encoder_model.encode(old_theorems, convert_to_tensor=True)
    emb_new = encoder_model.encode(new_theorems, convert_to_tensor=True)
    i = 0

    new_embs = []
    batch_statements=[]
    for sample in data:
        cosine_old_new = util.cos_sim(emb_old[i], emb_new[i]).item()
        if len(new_embs) == 0 :
            sim_batch = 0
        else : 
            sim_batch = max([util.cos_sim(emb_new[i], x).item() for x in new_embs])
        if cosine_old_new < 0.9 and cosine_old_new > 0.6 and sim_batch < 0.9:
            statement_dict[sample['custom_id']] = (extract_theorem(sample['proof']), extract_theorem(sample['theorem']))
            samples.append({'proof': sample['proof'], 'custom_id': sample['custom_id']})
            new_embs.append(emb_new[i])
        else : 
            scores.append({'custom_id' :  sample['custom_id'] , 'score':  0  }) 
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

 
    list_eval_complexity=[]
    for x in results :
        res = get_verification_results(x)
        if res['pass'] :
            list_eval_complexity.append(res['custom_id']) 
        else : 
            scores.append({'custom_id' :  res['custom_id'] , 'score':  0  }) 

    new_samples = [s for s in samples if s['custom_id'] in list_eval_complexity]

    target_dist = {'negation': 1., 'iff': 5., 'or': 1., 'and': 6., 'forall': 9., 'exists': 4., 'imp': 2., 'atom': 100}

    patterns = ["negation", "iff", "or", "and", "forall", "exists", "imp", "atom"]

    pattern_dict={ x : 0 for x in patterns }

    n = 16
    statements_to_save =[]
    total = 0
    if len(new_samples) > 0:
        complexity_scores = get_complexity_scores(new_samples, n, urls)
        for x, y in complexity_scores.items():
            if len(y) <= 0.5 * n and len(y) > 0:
                theorem_pattern = pat(statement_dict[x][0]) 
                pattern_dict[theorem_pattern]+=1
                total+=1

        pattern_dict_2 = { x : 0 for x in patterns }

        for x, y in complexity_scores.items():
            if len(y) <= 0.5 * n and len(y) > 0:

                theorem_pattern = pat(statement_dict[x][0]) 
                pattern_dict[theorem_pattern]+=1
                target_proportion = int(total * target_dist[theorem_pattern] / 100)
                if pattern_dict_2[theorem_pattern] <= target_proportion : 
                    statements_to_save.append({
                        'old': statement_dict[x][1],
                        'new': statement_dict[x][0],
                        'step': global_step + 1,
                        'proof': list(set(y))
                    })
                    score = 1
                else : 
                    score = max(0.1, target_proportion / pattern_dict[theorem_pattern])
            else : 
                score  = 0
            scores.append({'custom_id' :  x , 'score':   score})


    if len(statements_to_save) > 0:
        add_new_statements(statements_to_save, path)

    return scores

header = "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n"
old_code =  'theorem lean_workbook_39743 :   Int.floor (Real.sqrt 2021) = 44  := by'
code = "theorem norm_num_tactic_form (n : ℕ) (hn : 1 < n) :    Int.floor (Real.sqrt 2021) = 44 ↔    44 * 44 ≤ 2021 ∧ 2021 < (44 + 1) * (44 + 1) := by sorry"
print(get_results([{'custom_id' : '0', 'proof':header + code , 'theorem' : old_code, 'split' : 'train' }]))

