from datasets import load_dataset
from sentence_transformers import SentenceTransformer
import torch, numpy as np, faiss, pandas as pd
import re

def extract_theorem(inputs):
    try:
        return  'theorem ' + ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split())
    except:
        return "None"

ds = load_dataset('kfdong/STP_Lean_0320')['train']#.select(range(1000))

def filter1(s) : 
    return s['tag'] == "['conjecture']"

ds1 = ds.filter(filter1)

def extract_fn(example):
    return {"conjecture": extract_theorem(example["prompt"])}

# apply to the whole dataset in parallel
ds1 = ds1.map(extract_fn, num_proc=64)  # adjust num_proc for CPU cores

# now you can access them as a column directly
conjectures = ds1["conjecture"]

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

patterns = ["negation", "iff", "or", "and", "forall", "exists", "imp", "atom"]
def extract_code(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

print(conjectures[0])

pattern_dict={ x : 0 for x in patterns }
total = 0
for st in conjectures : 
    conj_pattern= pat(extract_code(st))
    pattern_dict[conj_pattern]+=1
    total += 1
for x,y in pattern_dict.items() : 
    pattern_dict[x] = round(100/total * y,3)
print(pattern_dict)

# {'negation': 0.298, 'iff': 7.514, 'or': 2.562, 'and': 5.594, 'forall': 8.921, 'exists': 3.096, 'imp': 1.277, 'atom': 70.737}