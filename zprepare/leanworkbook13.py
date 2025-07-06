import numpy as np
from datasets import DatasetDict,load_dataset
import json

import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback

def get_verification_results(old_result1) : 
    custom_id= old_result1['custom_id']
    old_result = old_result1['response']
    system_messages = old_result1['error']
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

    except:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages
        }
    result['custom_id'] = custom_id
    return result

ds = load_dataset("Slim205/lean_workbook_RL_V8_goals_full",split='train')#.select(range(10))

csv_path0 = '../Goedel-Prover/results/leanworkbook_train/SFT-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

def hinter(sample) : 
    new_code =f"""import Mathlib
import Aesop

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem {sample['problem_id']}_V1 {sample['processed_goals'][1]} := by"""

    return new_code

inputs=[]
num_ds=0
for sample in ds:
    theorem_name = sample['problem_id']
    if theorem_name in data0.keys() : 
        sample['eval_complexity'] = data0[theorem_name] / 32

        if  sample['eval_complexity'] > 0 or len(sample['processed_goals']) < 2 : 
            sample['old_theorem'] = ''
            #inputs.append(sample)

        else : 
            sample['old_theorem'] = sample['theorem'] 
            for i,goal in  enumerate(sample['processed_goals']) : 
                sample['theorem'] = hinter(sample) 
                inputs.append(sample)
        num_ds+=1
print(num_ds)

from datasets import Dataset
ds_train = Dataset.from_list(inputs)

dataset_test = load_dataset("Slim205/lean_workbook_RL_V8_goals_full", split='test')

dataset_test = dataset_test.map(lambda x: {'eval_complexity': 0.0})

dataset_test = dataset_test.map(lambda x: {'old_theorem': ''})
dataset_test = dataset_test.map(lambda x: {'pass': True})

dataset =ds_train

#ds2.push_to_hub('Slim205/lean_workbook_RL_V8_hinter')
theorem_list=[]
proofs=[]
for example in dataset:
    if example['old_theorem'] != '': 
        proof_text =  example['theorem'] + ' sorry'
        proofs.append(proof_text)
        theorem_list.append(example['problem_id'])
    

proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]

score_dict = {thm: 0 for thm in theorem_list}

print('Start Verification')
client = Lean4Client(base_url="http://0.0.0.0:12332",disable_cache=False)
responses = batch_verify_proof(
    samples=proof_dict,
    client=client,
    timeout=60,
    num_proc=64,
    batch_size=1    )

compilation_results =[]
for response in responses : 
    compilation_results.append(get_verification_results(response))
p = 0
s=0
list_errors=[]
for res in compilation_results:
    theorem_name = res['custom_id']
    if res['pass']:
        score_dict[theorem_name] += 1 
        p+=1
    else : 
        print(s)
        list_errors.append(res)
    s+=1
print(f'Final score : {p} / {len(compilation_results)}')
inputs_data = []
for example in dataset : 
    theorem = example['problem_id']
    if example['old_theorem'] == '' : 
        example['pass'] = True
    else : 
        example['pass'] = score_dict[theorem] == 1 
    inputs_data.append(example)

hf_dataset = Dataset.from_list(inputs_data)

ds4 = DatasetDict({'train'  : hf_dataset , 'test' : dataset_test })

#ds4.push_to_hub('Slim205/lean_workbook_RL_V13')
print(ds4)
