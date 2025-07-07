import pandas as pd
import numpy as np
import json
from datasets import load_dataset
def get_theorem_name(theorem_str: str) -> str:
    """Extracts theorem name safely from a Lean theorem string."""
    try:
        parts = theorem_str.split("theorem", 1)
        theorem_part = parts[1].strip()
        name = theorem_part.split()[0] if theorem_part else "unknown"
        return name
    except Exception as e:
        print(f"Error parsing theorem: {e}")
        return "error"
input_file= '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/minif2f/deepseek-SFT-2/code_compilation.json'

with open(input_file, 'r') as json_file:
    codes = json.load(json_file)


def get_goals(res) : 
    goals = []
    if 'tactics' not in res : 
        print(res)
        return []
    for x in res['tactics'] : 
        goal = x['goals'].split('⊢')[-1]
        if goal not in goals : 
            goals.append(goal)
    return goals

dataset = load_dataset("Slim205/mathlib_RL_v3_traced", split='train')
inputs = []
p = 0
thm=[]
theoreom_to_goals= {}
for sample in dataset:
    p+=1
    theorem_name = get_theorem_name(sample['theorem']) + str(p)
    theoreom_to_goals[theorem_name] = sample['goals']
score_dict={}

for code in codes : 
    res = code['compilation_result']
    goals = get_goals(res)
    if res['complete'] : 
        score = 1 
    elif code['name'] in theoreom_to_goals.keys() : 
        ground_truth = theoreom_to_goals[code['name']]
        if len(ground_truth) > 0 : 
            goals = get_goals(res)
            ss = 0
            for goal in goals : 
                if goal in ground_truth :
                    ss +=1
            score = ss/len(ground_truth)
    else :
        score = 0

    score_dict[code['name']] = score
file_name_txt =f"scores_goal.txt"
with open(file_name_txt, 'w', encoding='utf-8') as f:
    f.write("Theorem Scores:\n")
    
    score_final = 0
    for k, v in score_dict.items():
        line = f'{k} : {v}\n'
        f.write(line)
        score_final += v

    f.write(f"\nTotal theorems with at least one successful proof: {score_final}\n")
    f.write(f"Out of total theorems: {len(codes)} \n")

print(score_final)

