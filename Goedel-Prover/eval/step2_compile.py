import json
import sys
import argparse
import os
from loguru import logger
from client.client import Lean4Client, batch_verify_proof
import time
import traceback

parser = argparse.ArgumentParser()
parser.add_argument('--input_path', default="", type=str)
parser.add_argument('--output_path', default="", type=str)
parser.add_argument('--cpu', default=64, type=int)
args = parser.parse_args()

input_file_path = args.input_path

with open(input_file_path, 'r') as json_file:
    codes = json.load(json_file)
#codes = codes[7000:7128]

batch_size = 1
num_proc = args.cpu
print(num_proc)
timeout = 60 
url = "http://holy8a14106:12332"
logger.info("Testing cached mode")
client = Lean4Client(base_url=url, disable_cache=False)

samples= []
for i in range(len(codes)):
    codes[i]["custom_id"] = f"{codes[i]['name']}_{i}"
    # if codes[i]["code"] =='None' : 
    #     proof = 'None'
    # else : 
    #     proof = 'import miniF2F\nimport Aesop\n' + 'set_option maxRecDepth 100000'+  codes[i]["code"].split('Aesop')[1] 
    # if i==0 :
    #     print(proof)
    samples.append({"custom_id": codes[i]["custom_id"] , "proof": codes[i]["code"] })

print(len(codes))
result = batch_verify_proof(
    samples=samples,
    client=client,
    timeout=timeout,
    num_proc=num_proc,
    batch_size=batch_size,
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