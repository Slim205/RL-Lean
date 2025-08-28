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

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

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

def get_data() :
    final_statements = 0
    conjs = []
    for i in range(5) : 
        path = f'/n/netscratch/amin_lab/Lab/slim/Lean/storage/Expert_V2/round{i}/train.json'
        old_statements=load_statements(path)

        new_conjecturers = []
        for st in old_statements : 
            if st['new'] not in new_conjecturers : 
                new_conjecturers.append(st['new'])
                final_statements += len(st['proof'])
        conjs+= new_conjecturers
    print(f'Number of new conjectures before deduplication : {final_statements}')
   # print(f'Number of new conjectures : {len(list(set(final_statements)))}')

    print(f'Number of new conjectures before deduplication : {len(conjs)}')
    print(f'Number of new conjectures : {len(list(set(conjs)))}')

#     list_data = []
#     i = 0
#     for statement in statements: 
#         i+=1
#         y = statement['proof']
#         for code in y :
#             split_marker = ':= by'
#             split_index = code.find(split_marker)
#             if split_index == -1 :
#                 split_marker = ':=  by'
#                 split_index = code.find(split_marker)

#             assert    split_index > -1 
#             theorem = code[:split_index + len(split_marker)]
#             target = code[split_index + len(split_marker):]  #+ '\n```' (For STP)
#             prompt = get_prompt_prover(theorem) 
#             assert theorem + code[split_index + len(split_marker):]  == code
#             list_data.append({'prompt': prompt, 'target': target})
#         prompt_conj = get_prompt_conj(f'theorem leanworkbook_{i} ' + statement['old'])
#         target_conj = get_target_conj(f'theorem leanworkbook_{i}_plus ' + statement['new'])
#         list_data.append({'prompt': prompt_conj, 'target': target_conj})
#     # Step 1: Shuffle the dataset
#     random.seed(42)  # for reproducibility
#     random.shuffle(list_data)
#     for i in range(1) : 
#         print(list_data[i]['prompt'])
#         print(list_data[i]['target'])
#         print('-----------------------------')
#     print(len(list_data))
#     print(f"Full data size: {len(list_data)}")

get_data()

