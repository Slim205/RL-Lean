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
from utils.gcloud_utils import write_data
from utils.RL_utils import STORAGE

def get_prompt(theorem) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=theorem,
            )
    return text

def get_data(path2) :
    file_path = f"/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/{path2}/code_compilation.json"

    with open(file_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    list_proved_theorems ={}
    for entry in data:
        compilation_result = entry.get("compilation_result", {})
        code = entry.get('code','')
        thm = entry.get('name','')
        if compilation_result['complete'] : 
            if thm not in list_proved_theorems.keys() : 
                list_proved_theorems[thm] = [code]
            else : 
                list_proved_theorems[thm].append(code)
    print(len(list_proved_theorems))

    list_proved_theorems_filtered = {}
    for x,y in list_proved_theorems.items() :
        new_list = list(set(y))
        list_proved_theorems_filtered[x] = new_list[:16]
        assert len(list_proved_theorems_filtered[x]) <= 16
    print(len(list_proved_theorems_filtered))

    list_data = []
    for x,y in list_proved_theorems_filtered.items() :
        for code in y :
            #print(code) 
            split_marker = ':= by'
            split_index = code.find(split_marker)
            if split_index == -1 :
                split_marker = ':=  by'
                split_index = code.find(split_marker)

            assert    split_index > -1 
            theorem = code[:split_index + len(split_marker)]
            target = code[split_index + len(split_marker):]  + '\n```'
            prompt = get_prompt(theorem) 
            assert theorem + code[split_index + len(split_marker):]  == code
            list_data.append({'prompt': prompt.replace('set_option maxRecDepth 100000',''), 'target': target})
    # Step 1: Shuffle the dataset
    random.seed(42)  # for reproducibility
    random.shuffle(list_data)
    for i in range(1) : 
        print(list_data[i]['prompt'])
        print(list_data[i]['target'])
        print('-----------------------------')
    print(len(list_data))
    return list_data

train_ds = get_data("sft_V1/SFT-64")
test_ds = get_data("sft_V1/SFT-test-64")

print(f"Train set size: {len(train_ds)}")
print(f"Test set size: {len(test_ds)}")

# Step 3: Save the splits
train_path = os.path.join(STORAGE, "data/SFT/SFT_prover_V1/train.json")
test_path = os.path.join(STORAGE, "data/SFT/SFT_prover_V1/test.json")
print(train_path)
print(test_path)

write_data(json.dumps(train_ds), train_path,'json', no_compression=True)
write_data(json.dumps(test_ds), test_path,'json',no_compression=True)
