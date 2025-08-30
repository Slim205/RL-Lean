import os
import json
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  
import os
import json
import random
import fire 
import re

def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"


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
    
# ----------------- helper -----------------
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



def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

patterns = [
    "negation", "iff", "or", "and",
    "forall", "exists", "imp", "atom"
]

from datasets import load_dataset 

# ds = load_dataset('Slim205/LeanWorkbook')['train']

# def get_pattern(s) :
#     s['pattern'] =  pat(extract_theorem(s['formal_statement']))
#     return s

# ds = ds.map(get_pattern)
# pattern_dict={ x : 0 for x in patterns }
# for x in ds : 
#     pattern_dict[x['pattern']] += 1
# for x,y in pattern_dict.items() : 
#     pattern_dict[x] = round(y / len(ds) * 100,3)

# print(pattern_dict)
# for i in range(8) : 
#     conjs_pattern = []
#     path = f'/n/netscratch/amin_lab/Lab/slim/Lean/storage/Expert_V2/round{i}/data/train.json'
#     old_statements=load_statements(path)
#     pattern_dict={ x : 0 for x in patterns }

#     new_conjecturers = []
#     for st in old_statements : 
#         if st['new'] not in new_conjecturers : 
          
#             class_thm = pat(st['new'])
#             pattern_dict[class_thm] += 1
#             new_conjecturers.append(st['new'])
#     print(i)
#     for x,y in pattern_dict.items() : 
#         pattern_dict[x] = round(y / len(new_conjecturers) * 100,3)
#     print(pattern_dict)


for i in range(9) : 
    conjs_pattern = []
    path = f'/n/netscratch/amin_lab/Lab/slim/Lean/storage/Expert_V2/round{i}/data/train.json'
    old_statements=load_statements(path)
    pattern_dict={ x : 0 for x in patterns }
    total = 0
    for st in old_statements : 
        if 'by\n</hard theorem>' in st['target'] : 
            pattern = pat(extract_theorem(st['target']))
            pattern_dict[pattern] +=1
            total+=1
    print(i)
    for x,y in pattern_dict.items() : 
        pattern_dict[x] = round(y / total * 100,3)

    print(pattern_dict)