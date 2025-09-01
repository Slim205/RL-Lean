import json
import sys
import argparse
import os
from loguru import logger
from client.client import Lean4Client, batch_verify_proof
import time
import traceback
import re
from typing import List, Any, Sequence, Tuple, Dict
from concurrent.futures import ThreadPoolExecutor, as_completed


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

parser = argparse.ArgumentParser()
parser.add_argument('--input_path', default="", type=str)
parser.add_argument('--output_path', default="", type=str)
parser.add_argument('--cpu', default=64, type=int)
args = parser.parse_args()

input_file_path = args.input_path

# if os.path.exists(args.output_path):
#     exit(0)
    
with open(input_file_path, 'r') as json_file:
    codes = json.load(json_file)


samples= []
for i in range(len(codes)):
    codes[i]["custom_id"] = f"{codes[i]['name']}_{i}"
    samples.append({"custom_id": codes[i]["custom_id"] , "proof": codes[i]["code"] })

urls = [
    "http://holy8a14401:12332" ,"http://holy8a14104:12332", "http://holy8a14101:12332",
    "http://holy8a14301:12332",  "http://holy8a14103:12332",  "http://holy8a14107:12332",
     "http://holy8a14108:12332", "http://holy8a14302:12332", "http://holy8a14202:12332",
     "http://holy8a14105:12332", "http://holy8a14106:12332", "http://holy8a14201:12332",
     "http://holy8a14102:12332",

    ]  
    
print(len(codes))
result = parallel_verify_over_urls(
        samples=samples,
        urls=urls,
        timeout=60,
        num_proc=64,   
        batch_size=1,
    )

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


compilation_results =[]
for res in result : 
    compilation_results.append(get_verification_results(res))

assert len(compilation_results) == len(codes)

compilation_dict = {result['custom_id']: result for result in compilation_results}

for code in codes:
    custom_id = code['custom_id']  
    if custom_id in compilation_dict:
        code['compilation_result'] = compilation_dict[custom_id]
    else :
        print(custom_id)
with open(args.output_path, 'w') as json_file:
    json.dump(codes, json_file, indent=4)