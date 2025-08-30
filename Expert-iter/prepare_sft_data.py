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
def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []
def write_data(string, filename, content_type='json', no_compression=False):

    if not no_compression:
        extension = '.gz'
        if isinstance(string, str):
            string = string.encode()
        string = pgzip.compress(string, thread=ZIP_THREAD)
    else:
        extension = ''
    full_filename = filename + extension
    # Ensure directory exists
    os.makedirs(os.path.dirname(full_filename), exist_ok=True)
    with open(full_filename, 'wb' if (content_type == 'pickle') or (len(extension) > 0) else 'w') as file:
        file.write(string)
    result = f'{full_filename} write complete'


def get_prompt_prover(theorem) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=theorem,
            )
    return text
START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = (
    "Complete the following Lean 4 code:\n\n```lean4\n"
    "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n"
    "open BigOperators Real Nat Topology Rat\n"
)

def get_prompt_conj(easy_theorem):
    shared_lemma = ''
    prompt = (
        f"{PROVER_PROMPT}"
        f"{INVOKED_LEMMA}\n{shared_lemma.strip()}\n"
        f"{START_LEMMA_STMT}\n{easy_theorem.strip()}\n"
        f"{START_THM}"
    )
    return prompt

def get_target_conj(hard_theorem):
    target = f'\n{hard_theorem}\n{END_THM}'

    return target

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


def get_data(path,STORAGE) :
    path_train = os.path.join(STORAGE, "train.json")

    if os.path.exists(path_train):
        exit(0)

    old_statements =load_statements(path)

    #target_dist = {'negation': 0.893, 'iff': 5.201, 'or': 0.847, 'and': 5.983, 'forall': 8.115, 'exists': 3.418, 'imp': 1.516, 'atom': 74.026}
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
    list_data = []
    i = 0
    for statement in statements: 
        i+=1
        y = statement['proof']
        for code in y :
            split_marker = ':= by'
            split_index = code.find(split_marker)
            if split_index == -1 :
                split_marker = ':=  by'
                split_index = code.find(split_marker)

            assert    split_index > -1 
            theorem = code[:split_index + len(split_marker)]
            target = code[split_index + len(split_marker):]  #+ '\n```' (For STP)
            prompt = get_prompt_prover(theorem) 
            assert theorem + code[split_index + len(split_marker):]  == code
            list_data.append({'prompt': prompt, 'target': target})
        prompt_conj = get_prompt_conj(f'theorem leanworkbook_{i} ' + statement['old'])
        target_conj = get_target_conj(f'theorem leanworkbook_{i}_plus ' + statement['new'])
        list_data.append({'prompt': prompt_conj, 'target': target_conj})
    # Step 1: Shuffle the dataset
    random.seed(42)  # for reproducibility
    random.shuffle(list_data)
    for i in range(1) : 
        print(list_data[i]['prompt'])
        print(list_data[i]['target'])
        print('-----------------------------')
    print(len(list_data))
    print(f"Full data size: {len(list_data)}")

    train_path = os.path.join(STORAGE, "train.json")
    test_path = os.path.join(STORAGE, "test.json")
    print(train_path)
    print(test_path)
    test_size = int(0.01*len(list_data))
    print(f"Train set size: {len(list_data)-test_size}")
    print(f"Test set size: {test_size}")
    print(f'Number of training steps : {(len(list_data)-test_size)// 1024 }')
    write_data(json.dumps(list_data[:-test_size]), train_path,'json', no_compression=True)
    write_data(json.dumps(list_data[-test_size:]), test_path,'json',no_compression=True)


if __name__ == "__main__":
    fire.Fire(get_data)
