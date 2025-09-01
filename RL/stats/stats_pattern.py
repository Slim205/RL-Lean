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


conjs_pattern = []
path = f'/n/netscratch/amin_lab/Lab/slim/RL/storage/conjecturer_V1/data/train.json'
old_statements=load_statements(path)
sts = [st['new'] for st in old_statements  ]
print(f'Number of conjecutres : {len(sts)}')
print(f'Number of conjecutres after deduplication : {len(list(set(sts)))}')

sts_dict = {}
for x in old_statements : 
    if x['new'] not in sts_dict : 
        sts_dict[x['new']] = []
    sts_dict[x['new']].extend(x['proof'])

s = 0
for x,y in sts_dict.items() : 
    sts_dict[x] = list(set(y))
    s+= len(sts_dict[x])
print(f'Number of proofs : {s}')

pattern_dict={ x : 0 for x in patterns }
total = 0
for st in list(set(sts)) : 
    pattern = pat(st)
    pattern_dict[pattern] +=1
    total+=1
for x,y in pattern_dict.items() : 
    pattern_dict[x] = round(y / total * 100,3)

print(pattern_dict)