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
from datasets import load_dataset 

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
    LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
            header= LEAN4_DEFAULT_HEADER,
            formal_statement=theorem,
        )
    return text

def get_data(STORAGE,split) :
    ds = load_dataset('Slim205/Lean_conjecturer_data_v02')[split]
    list_data = []
    
    for sample in ds: 
        for code in sample['proofs'] :
            theorem = sample['formal_statement']
            target =  code + '\n```' 
            prompt = get_prompt_prover(theorem) 
            list_data.append({'prompt': prompt, 'target': target})
        

    random.seed(42) 
    random.shuffle(list_data)
    for i in range(1) : 
        print(list_data[i]['prompt'])
        print(list_data[i]['target'])
        print('-----------------------------')
    print(len(list_data))
    print(f"Full data size: {len(list_data)}")

    sft_path = os.path.join(STORAGE, f"{split}.json")

    print(f"SFT dataset size: {len(list_data)}")
    print(f'Number of training steps : {(len(list_data))// 1024 }')
    write_data(json.dumps(list_data), sft_path,'json', no_compression=True)

storage = '/n/netscratch/amin_lab/Lab/slim/RL/storage/conjecturer_V1/data/prover'

get_data(storage,'train')
get_data(storage,'test')