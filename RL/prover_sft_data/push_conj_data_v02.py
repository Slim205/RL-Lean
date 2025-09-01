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
import re 
from datasets import Dataset,DatasetDict

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

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


def get_data(path,split) :
    path_split = os.path.join(path, f"{split}.json")

    old_statements =load_statements(path_split)

    target_dist = {'negation': 1., 'iff': 5., 'or': 1., 'and': 6., 'forall': 9., 'exists': 4., 'imp': 2., 'atom': 100}

    patterns = ["negation", "iff", "or", "and", "forall", "exists", "imp", "atom"]

    pattern_dict={ x : 0 for x in patterns }

    statements = []
    new_conjecturers = []
    for st in old_statements : 
        conj_pattern= pat(st['new'])
        pattern_dict[conj_pattern]+=1
        if pattern_dict[conj_pattern] <= int(target_dist[conj_pattern] / 100 * len(old_statements)) : 
            if st['new'] not in new_conjecturers : 
                    new_conjecturers.append(st['new'])
                    statements.append(st)

    print(f'Number of new conjectures before deduplication : {len(old_statements)}')
    print(f'Number of new conjectures : {len(statements)}')

    pattern_dict={ x : 0 for x in patterns }
    total = 0
    for st in statements : 
        conj_pattern= pat(st['new'])
        pattern_dict[conj_pattern]+=1
        total += 1
    for x,y in pattern_dict.items() : 
        pattern_dict[x] = round(100/total * y,3)
    print(pattern_dict)

    theorem_dict = {}
    for statement in statements: 
        y = statement['proof']
        list_proofs = []
        for code in y :
            split_marker = ':= by'
            split_index = code.find(split_marker)
            if split_index == -1 :
                split_marker = ':=  by'
                split_index = code.find(split_marker)

            assert    split_index > -1 
            proof = code[split_index + len(split_marker):]
            list_proofs.append(proof)
        theorem_dict[statement['new']] = list(set(list_proofs))

    list_data = []
    for i, (x, y) in enumerate(theorem_dict.items()):
        theorem = f"theorem conjecture_{i} {x}"
        list_data.append({
            "problem_id": f"conjecture_{i}",
            "formal_statement": theorem,
            "proofs": y
        })
    random.seed(42) 
    random.shuffle(list_data)
    for i in range(1) : 
        print(list_data[i]['formal_statement'])
        print(list_data[i]['proofs'][0])
        print('-----------------------------')

    print(f"Full data size: {len(list_data)}")

    ds_train = Dataset.from_list(list_data)
    return ds_train

data_train_path ='/n/netscratch/amin_lab/Lab/slim/RL/storage/conjecturer_V1/data/'
ds_train = get_data(data_train_path,'train')
ds_test = get_data(data_train_path,'test')

dataset = DatasetDict({
    "train": ds_train,
    "test": ds_test,
})

dataset.push_to_hub("Slim205/Lean_conjecturer_data_v02")
