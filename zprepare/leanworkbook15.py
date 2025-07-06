import numpy as np
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


csv_path0 = '../Goedel-Prover/results/leanworkbook_hinter/SFT-4/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

dataset = load_dataset("Slim205/lean_workbook_RL_V13", split='train')#.select(range(12000))

inputs = []
p = 0
thm=[]
for sample in dataset:
    if sample['pass']  : 
        theorem_name = sample['problem_id'] + str(p)
        p+=1

        if theorem_name in data0.keys() : 
            if data0[theorem_name] < 3 : 
                inputs.append(sample)

dataset = Dataset.from_list(inputs)
print(dataset)

#dataset.push_to_hub('Slim205/lean_workbook_RL_V13_V1')