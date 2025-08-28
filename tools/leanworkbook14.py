import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback
import re
def format_lines(text: str) -> str:
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    return " ".join(f"({ln})" for ln in lines) 

def post_process(text) : 
    text =  text.replace('✝', 'o')
    text =  text.replace('π', 'Real.pi')
    text =  text.replace('o¹', 'oo')
    text =  text.replace('o²', 'ooo')
    return text
def process_state(ch) : 
    try :
        goal = ch.split('⊢')[1]
        hypo = ch.split('⊢')[0]
        new_hypo = ''        
        if len(hypo) == 0 : 
            return post_process(":" + goal)
        if '\n' in hypo : 
            hypo = hypo.replace(':\n', ':')
            hypo = hypo.replace('∧\n', '∧')
            hypo = hypo.replace('→\n', '→')
            hypo = hypo.replace('=\n', '=')
            hypo = hypo.replace('≥\n', '≥')
            hypo = hypo.replace('≤\n', '≤')
            hypo = hypo.replace('>\n', '>')
            hypo = hypo.replace('<\n', '<')
            hypo = hypo.replace('*\n', '*')
            hypo = hypo.replace('+\n', '+')
            hypo = hypo.replace('/\n', '/')

            return post_process(format_lines(hypo) + ':' + goal)

        for i, x in enumerate(hypo.split(' : ')) :
            if i == 0 : 
                new_hypo = '(' + x + ' : '
                continue

            pos = re.split(r'[ \n]', x)[-1]
            for y in re.split(r'[ \n]', x)[:-1] : 
                new_hypo += y + ' '
            if pos == '' : 
                continue
            if pos[0] != '('  :
                new_hypo += ') ('
            new_hypo += pos + ' : '
        return post_process(new_hypo + ") :" + goal)
    except : 
        print(ch)
        print(traceback.format_exc())
        return ch

def process_state_final(ch) : 
    try : 
        if 'case' in ch : 
            pattern = re.compile(
                r'^case\s+(\S+)\s*(.*?)(?=^case\s|\Z)',       
                flags=re.MULTILINE | re.DOTALL
            )

            list_hints = []                                        
            for m in pattern.finditer(ch):
                name = m.group(1)                             
                body = m.group(2).strip()                   
                list_hints.append(process_state(body))
            return list_hints
        elif len(ch.split('⊢')) > 2 : 
            final_result=[]
            for i in range( len(ch.split('⊢'))-1) : 
                hypo = ch.split('⊢')[i]
                if '\n' in ch.split('⊢')[i] : 
                    hypo = ''
                    for x in ch.split('⊢')[i].split('\n')[1:] : 
                        hypo += '\n' + x 
                    hypo = hypo[1:]
                
                goal = ch.split('⊢')[i+1].split('\n')[0]
                final_result.append(process_state(hypo + ' ⊢ ' + goal))
            return final_result
        else : 
            return [process_state(ch)]
    except : 

        print(ch)
        print(traceback.format_exc())

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

ds = load_dataset("Slim205/lean_workbook_RL_hinter_V1",split='train').select(range(12000))

csv_path0 = '../Goedel-Prover/results/leanworkbook_train/SFT-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

def hinter(problem_id, theorem) : 
    new_code =f"""import Mathlib
import Aesop

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem {problem_id}_V1 {theorem} := by"""

    return new_code

inputs=[]

import copy

for sample in ds:
    theorem_name = sample['problem_id']
    if theorem_name not in data0:
        continue

    eval_complexity = data0[theorem_name] / 32
    if eval_complexity > 0.0 or len(sample['processed_goals']) < 2:
        continue

    for goal in sample['goals'][1:]:          # skip i == 0 implicitly
        new_sample = sample.copy()       # or copy.deepcopy(sample) if it has nested mutables
        new_sample['eval_complexity'] = eval_complexity
        new_sample['old_theorem'] = sample['theorem']
        for sub_goal in process_state_final(goal) : 
            new_sample['theorem'] = hinter(theorem_name, sub_goal)
            inputs.append(new_sample)
                    
print(len(inputs))

dataset = Dataset.from_list(inputs)
print(dataset)

theorem_list=[]
proofs=[]
p=0
for example in dataset:
    proof_text =  example['theorem'] + ' sorry'
    proofs.append(proof_text)
    theorem_list.append(example['problem_id'] + str(p))
    p+=1
    

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
s = 0
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
p = 0
thm_list = []
for example in dataset : 
    theorem = example['problem_id'] + str(p)
    example['pass'] = score_dict[theorem] == 1 
    if example['pass'] and example['problem_id'] not in thm_list : 
        thm_list.append(example['problem_id'])
    inputs_data.append(example)
    p+=1

hf_dataset = Dataset.from_list(inputs_data)

hf_dataset.push_to_hub('Slim205/lean_workbook_RL_V15')
print(hf_dataset)

print(len(thm_list))