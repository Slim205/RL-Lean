import os
import json
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  
import argparse
import re
import datasets
from verl.utils.hdfs_io import copy, makedirs

MATHLIB_DIR = Path("~/lean/mathlib4/Mathlib").expanduser()  
LeanDojo_DIR = Path("/n/netscratch/amin_lab/Lab/slim/leandojo_benchmark_4/").expanduser()
Save_DIR = Path("~/data/sft/").expanduser()  # Use Path for consistency

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

START_THM   = '<theorem>'
END_THM     = '</theorem>'
START_CONJ  = '<conjecture>'
END_CONJ    = '</conjecture>'

# ── unchanged header & leading prompt text ─────────────────────────
def format_conjecture_example(context, theorem, conjecture):
    prompt = f'Complete the following Lean 4 code:\n\n```lean4\n{context.strip()}\n' \
             f'{START_THM}\n' \
             f'{theorem.strip().strip()}\n' \
             f'{END_THM}\n' \
             f'{START_CONJ}\n'

    target = f'{conjecture.strip()}\n{END_CONJ}\n```'

    return {'prompt': prompt, 'target': target}

def get_statement(theorem) :
    return theorem.split(':= by')[0] + ':= by'
conjecture_ds = []
for file_name, context, theorem, shared_lemma, theorem_str in conjecture_examples:
    try : 
        conjecture_ds.append(format_conjecture_example(context, get_statement(theorem), get_statement(theorem_str)))
    except :
        continue
print(conjecture_ds[0])
for x in conjecture_ds : 
    print(x['prompt'])
    print(x['target'])
    break
print(len(conjecture_ds))

from datasets import Dataset
dataset = Dataset.from_list(conjecture_ds).shuffle(seed=42)

parser = argparse.ArgumentParser()
parser.add_argument("--local_dir", default="~/data/SFT_V1")
parser.add_argument("--hdfs_dir", default=None)

args = parser.parse_args()

data_source = "SFT" 

train_dataset = dataset.select(range(50000))
print(train_dataset)
test_dataset = dataset.select(range(50000,51273))
print(test_dataset)

# add a row to each data item that represents a unique id
def make_map_fn(split):
    def process_fn(example, idx):
        question = example['prompt']
        data = {
            "data_source": data_source,
            "prompt": question,
            "ability": "lean",
            "extra_info": {
                "split": split,
                "index": idx,
                "answer": example['target'],

            },
        }
        return data
    return process_fn
train_dataset = train_dataset.map(function=make_map_fn("train"), with_indices=True)
test_dataset = test_dataset.map(function=make_map_fn("test"), with_indices=True)
p = 0
for x in train_dataset : 
    print(x['prompt'])
    break

local_dir = args.local_dir
hdfs_dir = args.hdfs_dir

train_dataset.to_parquet(os.path.join(local_dir, "train.parquet"))
test_dataset.to_parquet(os.path.join(local_dir, "test.parquet"))

if hdfs_dir is not None:
    makedirs(hdfs_dir)

    copy(src=local_dir, dst=hdfs_dir)

