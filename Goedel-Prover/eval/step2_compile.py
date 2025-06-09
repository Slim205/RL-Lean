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

timeout = 60
batch_size = 1
print(os.cpu_count())
num_proc = args.cpu
print(num_proc)
url = "http://0.0.0.0:12332"

logger.info("Testing cached mode")
client = Lean4Client(base_url=url, disable_cache=False)

samples= []
for i in range(len(codes)):
    codes[i]["custom_id"] = f"{codes[i]['name']}_{i}"
    samples.append({"custom_id": codes[i]["custom_id"] , "proof": codes[i]["code"]})


result = batch_verify_proof(
    samples=samples,
    client=client,
    timeout=timeout,
    num_proc=num_proc,
    batch_size=batch_size,
)

def change_result(results):
    transformed_results = []
    for item in results:

        start_time = time.time()
        system_messages = ''
        try:
            response = item["response"]
            messages = response["messages"]
            
            transformed = {
                "custom_id" : item['custom_id'],
                "errors": [m for m in messages if m["severity"] == "error"],
                "warnings": [m for m in messages if m["severity"] == "warning"],
                "infos": [m for m in messages if m["severity"] == "info"],
                "sorries": [m for m in messages if "sorry" in m.get("data", "")],
                "system_messages": '',
                "system_errors": None,
                "verify_time": response["time"],
                "pass": not any(m["severity"] == "error" for m in messages),
                "complete": (not any(m["severity"] == "error" for m in messages) and 
                           not any("sorry" in m.get("data", "") for m in messages) and
                           not any("failed" in m.get("data", "") for m in messages if m["severity"] == "warning"))
            }

        except:
            transformed = {
                "custom_id" : item['custom_id'],
                "pass": False,
                "complete": False,
                "system_errors": traceback.format_exc(),
                "system_messages": system_messages
            }
        transformed['verify_time'] = time.time() - start_time
        transformed_results.append(transformed)

    return transformed_results

compilation_results = change_result(result)

assert len(compilation_results) == len(codes)

compilation_dict = {result['custom_id']: result for result in compilation_results}

for code in codes:
    custom_id = code['custom_id']  
    if custom_id in compilation_dict:
        code['compilation_result'] = compilation_dict[custom_id]

with open(args.output_path, 'w') as json_file:
    json.dump(codes, json_file, indent=4)