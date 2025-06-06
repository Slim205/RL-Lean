import os
import json
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  

import os
from pathlib import Path

MATHLIB_DIR = Path("~/lean/mathlib4/Mathlib").expanduser()  
LeanDojo_DIR = Path("~/leandojo_benchmark_4/").expanduser()
Save_DIR = Path("./STP/SFT/").expanduser()  # Use Path for consistency

os.makedirs(Save_DIR, exist_ok=True)  # Now works with the full path

def read_lean_files(directory: Path) -> Dict[str, str]:
    """
    Recursively reads all `.lean` files in the specified directory and returns
    a dictionary mapping file paths to their contents, displaying a progress bar.

    Args:
        directory (Path): The root directory to start searching for `.lean` files.

    Returns:
        Dict[str, str]: A dictionary where keys are file paths (as strings) and
                        values are the contents of the files.
    """
    if not directory.exists():
        raise FileNotFoundError(f"The directory {directory} does not exist.")
    if not directory.is_dir():
        raise NotADirectoryError(f"The path {directory} is not a directory.")

    # Collect all .lean files first to determine the total number for the progress bar
    lean_files = list(directory.rglob('*.lean'))
    total_files = len(lean_files)
    print(f"Found {total_files} `.lean` files to process.") # Number of lean files

    file_contents = {}

    # Initialize tqdm progress bar
    with tqdm(total=total_files, desc="Reading .lean files", unit="file") as pbar:
        for file_path in lean_files:
            try:
                # Read the file content with UTF-8 encoding
                with file_path.open() as f:
                    content = f.readlines()
                # Use the absolute path as the key
                file_contents[str(file_path.resolve())] = content
            except Exception as e:
                print(f"Error reading {file_path}: {e}")
            finally:
                pbar.update(1)  # Update the progress bar

    return file_contents


try:
    lean_file_dict = read_lean_files(MATHLIB_DIR)
    lean_file_dict = {k.split('mathlib4/')[-1]: v for k, v in lean_file_dict.items()} # File name : [list of lines in the file]
    print(f"Total .lean files read: {len(lean_file_dict)}")
    # Example: Print the first file's path and its first 100 characters
    if lean_file_dict:
        first_path = next(iter(lean_file_dict))
        print(f"First file: {first_path}")
        print(f"Content snippet: {lean_file_dict[first_path][:10]}")
except Exception as error:
    print(f"An error occurred: {error}")


train_path = LeanDojo_DIR / "random/train.json"
val_path = LeanDojo_DIR / "random/val.json"
test_path = LeanDojo_DIR / "random/test.json"
proofs_train = json.load(train_path.open())
proofs_val = json.load(val_path.open())
proofs_test = json.load(test_path.open())

from collections import defaultdict
# What is leandojo dataset : extracted form of Mathlib, contain the tactics extracted / 
# load the leandojo dataseet
# use the train/eval and test splits
#  filter statemenets that they don't have tactics
entry_dict = defaultdict(list)
s=0
p=0
for entry in proofs_train + proofs_val + proofs_test:
    p+=1
    if len(entry['traced_tactics']) > 0: # we take only thoerems that have tactics list not empty
        s+=1 
        entry_dict[entry['file_path']].append(entry)

print(len(entry_dict))
print(sum(len(v) for v in entry_dict.values()))
print(s/p)
######### Example of proofs__train elements : 
#{'url': 'https://github.com/leanprover-community/mathlib4', 'commit': '29dcec074de168ac2bf835a77ef68bbe069194c5', 
#'file_path': 'Mathlib/RingTheory/IntegralRestrict.lean', 'full_name': 'Algebra.intTrace_eq_trace','start': [216, 1], 'end': [223, 81], 
#'traced_tactics': [{'tactic': 'ext x', 'annotated_tactic': ['ext x', []], 'state_before': 'A : Type u_1\nK : Type u_2\nL : Type ...
###### KEYS  : dict_keys(['url', 'commit', 'file_path', 'full_name', 'start', 'end', 'traced_tactics'])


for x,y in entry_dict.items() :
    print(x)
    for z in y :
        print(z['file_path'])
        print(z['full_name'])
        print(z['start'])
        print(z['end'])
        
        for tact in z['traced_tactics'] :   # z : dict_keys(['url', 'commit', 'file_path', 'full_name', 'start', 'end', 'traced_tactics'])
            print(tact['annotated_tactic']) # dict_keys(['tactic', 'annotated_tactic', 'state_before', 'state_after'])
        break #means that we have 16 statement in this file  
    break


def get_statement(theorem_str):
    return theorem_str.split(':=')[0].strip()

mathlib_theorems = []
theorem_dict = {}

empty_file = 0
for file_name in tqdm(lean_file_dict.keys()):
    if (len(entry_dict[file_name]) == 0): # if file name does not exist in Leandojo
        empty_file += 1
        continue
    lines = lean_file_dict[file_name]
    entries = entry_dict[file_name]
    entries = sorted(entries, key = lambda x: x['start'][0])
#    print(entries[0]['start'][0])
 #   break
    for entry in entries:
        theorem_str = ''.join(lines[entry['start'][0] - 1: entry['end'][0]])    
        theorem_item = (file_name, theorem_str)
        mathlib_theorems.append(theorem_item)
        theorem_dict[entry['full_name']] = theorem_item 
    
print('[warning] # Files without theorem:', empty_file)
print('# Mathlib theorems:', len(mathlib_theorems))


sum_premises = 0
conjecture_examples = []

try:
    for file_name in tqdm(lean_file_dict.keys()):
        if (len(entry_dict[file_name]) == 0):
            empty_file += 1
            continue
    
        theorems_in_file = []
        lines = lean_file_dict[file_name]
        entries = entry_dict[file_name]
        entries = sorted(entries, key = lambda x: x['start'][0])
        
        for entry in entries:
            theorem_str = ''.join(lines[entry['start'][0] - 1: entry['end'][0]])
            contexts = ''.join(lines[:entry['start'][0] - 1]).strip()
            
            premises = set()
            for tactics in entry['traced_tactics']:
                for p in tactics['annotated_tactic'][1]:
                    if p['full_name'] in theorem_dict:
                        premises.add(p['full_name'])
    
            for p_name in premises:
                for p_context, p_theorem, p_premises in reversed(theorems_in_file):
                    if p_name in p_premises:
                        conjecture_examples.append((file_name, p_context, p_theorem, theorem_dict[p_name][1], theorem_str))
            
            theorems_in_file.append((contexts, theorem_str, premises))
            sum_premises += len(premises)
except:
    pass
print(sum_premises)
print('# Conjecture examples:', len(conjecture_examples))

START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'

def format_conjecture_example(context, easy_theorem, shared_lemma, hard_theorem):
    prompt = f'Complete the following Lean 4 code:\n\n```lean4\n{context.strip()}\n' \
          f'{INVOKED_LEMMA}\n{shared_lemma.strip()}\n{START_LEMMA_STMT}\n' \
          f'{easy_theorem.strip()}\n{START_THM}'
    target = f'\n{get_statement(hard_theorem).strip()}\n{END_THM}'
    return {'prompt': prompt, 'target': target}

conjecture_ds = []
for file_name, context, theorem, shared_lemma, theorem_str in conjecture_examples:
    conjecture_ds.append(format_conjecture_example(context, theorem, shared_lemma, theorem_str))

print(len(conjecture_ds))
#with open(os.path.join(Save_DIR, 'conjecture.json'), 'w') as f:
 #   json.dump(conjecture_ds, f)

#with open(os.path.join(Save_DIR, 'theorem_dict.pkl'), 'wb') as f:
 #   pickle.dump(theorem_dict, f)


PROVER_PROMPT = 'Complete the following Lean 4 code:\n\n```lean4\n'
eval_theorems = []

empty_file = 0
for file_name in tqdm(lean_file_dict.keys()):
    if (len(entry_dict[file_name]) == 0):
        empty_file += 1
        continue
    lines = lean_file_dict[file_name]
    entries = entry_dict[file_name]
    entries = sorted(entries, key = lambda x: x['start'][0])
    
    for entry in entries:
        context_str = PROVER_PROMPT + ''.join(lines[:entry['start'][0] - 1]) # prompt + all the contexte
        theorem_str = ''.join(lines[entry['start'][0] - 1: entry['end'][0]])
        theorem_item = (file_name, context_str, theorem_str)
        eval_theorems.append(theorem_item)
print('# Mathlib theorems:', len(eval_theorems))


rng = np.random.default_rng(0)
rng.shuffle(eval_theorems)
cutoff = 4096
train_theorems = [{'prompt': entry[1], 'target': entry[2]} for entry in eval_theorems[cutoff:]]
eval_theorems = [{'prompt': entry[1], 'target': entry[2]} for entry in eval_theorems[:cutoff]]

with open(os.path.join(Save_DIR, 'eval.json'), 'w') as f:
    json.dump(eval_theorems, f)


train_ds = conjecture_ds + train_theorems
rng = np.random.default_rng(0)
rng.shuffle(train_ds)
print('train_ds length')
print(len(train_ds))

#with open(os.path.join(Save_DIR, 'mathlib_conjecture.json'), 'w') as f:
 #   json.dump(train_ds, f)

from datasets import Dataset

#dataset = Dataset.from_list(conjecture_ds)
#dataset.push_to_hub("Slim205/conjecture")  # Replace with your repo name

dataset = Dataset.from_list(eval_theorems)
dataset.push_to_hub("Slim205/mathlib_eval")  # Replace with your repo name

