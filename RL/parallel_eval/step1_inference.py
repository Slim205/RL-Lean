import re
from transformers import AutoTokenizer
import json
import argparse
import os
import traceback
import requests
from typing import List, Any, Sequence, Tuple, Dict
from concurrent.futures import ThreadPoolExecutor, as_completed

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



parser = argparse.ArgumentParser()
# datasets/minif2f.jsonl
parser.add_argument('--input_path',  type=str)
# Goedel-LM/Goedel-Prover-SFT
parser.add_argument('--model_path', type=str)
# results/test
parser.add_argument('--output_dir',  type=str)
parser.add_argument('--split', default="none", type=str)
parser.add_argument('--n', default=32, type=int)
parser.add_argument('--gpu', default=1, type=int)



args = parser.parse_args()

# toinfer_file_path = F'{args.output_dir}/to_inference_codes.json'
# if os.path.exists(toinfer_file_path):
#     exit(0)

data_path = args.input_path

# Initialize an empty list to hold the dictionaries
data_list = []

# Open the file and read each line
with open(data_path, 'r') as file:
    for line in file:
        # Parse the JSON object and append it to the list
        # if data_split is not None and prob['split'] not in data_split:
        #     continue
        data = json.loads(line)
        # if (data["split"] == args.split) or (args.split == "none"):
        #     data_list.append(data)
        if args.split == "none":
            data_list.append(data)
        else:
            try:
                int_split = int(args.split)
            except:
                int_split = None
                pass
            if isinstance(int_split, int):
                if (int(data["split"]) == int(args.split)):
                    data_list.append(data)
            else:
                if ((data["split"]) == (args.split)):
                    data_list.append(data)


LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
model_name = args.model_path
tokenizer = AutoTokenizer.from_pretrained(model_name)

model_inputs = []
for data in data_list:    
#        text = "Complete the following Lean 4 code with explanatory comments preceding each line of code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(

    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
            header= data.get('header', LEAN4_DEFAULT_HEADER),
            informal_prefix=data.get('informal_prefix', str()),
            formal_statement=data['formal_statement'],
        )
    model_inputs.append(text)
print(model_inputs[0])
url_gpus =['http://holygpu8a22305:8000/generate', 'http://holygpu8a22603:8000/generate',
'http://holygpu8a22505:8000/generate', 'http://holygpu8a22301:8000/generate',
'http://holygpu8a22406:8000/generate', 'http://holygpu8a22401:8000/generate',
'http://holygpu8a22205:8000/generate', 'http://holygpu8a22402:8000/generate',

]

model_outputs = parallel_inference_over_urls(model_inputs, url_gpus, args.n)
    
assert len(model_outputs) == len(model_inputs)

def extrac_code(inputs):
    try:
        return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)        
    except:
        return "None"

to_inference_codes = []
for i in range(len(data_list)):
    data_list[i]["model_input"] = model_inputs[i]
    data_list[i]["model_outputs"] = [output for output in model_outputs[i]]
    data_list[i]["full_code"] = [extrac_code(model_inputs[i] + output) for output in model_outputs[i]] 

    if "problem_id" in data_list[i]:
        to_inference_codes += [{"name": data_list[i]["problem_id"], "code": code} for code in data_list[i]["full_code"]]
    else:
        to_inference_codes += [{"name": data_list[i]["name"], "code": code} for code in data_list[i]["full_code"]]

import os
os.makedirs(args.output_dir, exist_ok=True)

output_file_path = F'{args.output_dir}/full_records.json'
print(F"Outputting to {output_file_path}")
# Dump the list to a JSON file with indents
with open(output_file_path, 'w') as json_file:
    json.dump(data_list, json_file, indent=4)

toinfer_file_path = F'{args.output_dir}/to_inference_codes.json'
print(F"Outputting to {toinfer_file_path}")
# Dump the list to a JSON file with indents
with open(toinfer_file_path, 'w') as json_file:
    json.dump(to_inference_codes, json_file, indent=4)
