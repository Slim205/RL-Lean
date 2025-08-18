import os
import json
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  

MATHLIB_DIR = Path("~/lean/mathlib4/Mathlib").expanduser()  
LeanDojo_DIR = Path("/n/netscratch/amin_lab/Lab/slim/leandojo_benchmark_4/").expanduser()


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


conjecture_examples = []

for file_name in tqdm(lean_file_dict.keys()):
    if (len(entry_dict[file_name]) == 0):
        empty_file += 1
        continue
    lines = lean_file_dict[file_name]
    entries = entry_dict[file_name]
    entries = sorted(entries, key = lambda x: x['start'][0])
    
    for entry in entries:
        theorem_str = ''.join(lines[entry['start'][0] - 1: entry['end'][0]])
        contexts = ''.join(lines[:entry['start'][0] - 1]).strip()            
        conjecture_examples.append(( theorem_dict[p_name][1], theorem_str))
        

print('# Conjecture examples:', len(conjecture_examples))

START_THM   = '<theorem>'
END_THM     = '</theorem>'
START_COMP  = '<complexity>'
END_COMP   = '</complexity>'

# ── unchanged header & leading prompt text ─────────────────────────
def format_conjecture_example(context, theorem, complexity):
    prompt = f'Complete the following Lean 4 code:\n\n```lean4\n{context.strip()}\n' \
             f'{START_THM}\n' \
             f'{theorem.strip()}\n' \
             f'{END_THM}\n' \
             f'{START_COMP}\n'

    target = f'{complexity}\n{END_COMP}\n```'

    return {'prompt': prompt, 'target': target}

def get_statement(theorem) :
    return theorem.split(':= by')[0] + ':= by'
conjecture_ds = []
for file_name, context, theorem, shared_lemma, theorem_str in conjecture_examples:
    try : 
        conjecture_ds.append(format_conjecture_example(context, get_statement(theorem), complexity))
    except :
        continue
print(conjecture_ds[0])
for x in conjecture_ds : 
    print(x['prompt'])
    print(x['target'])
    break
print(len(conjecture_ds))


# import os
# import json
# import random
# from utils.gcloud_utils import write_data
# from utils.RL_utils import STORAGE

# # Step 1: Shuffle the dataset
# random.seed(42)  # for reproducibility
# random.shuffle(conjecture_ds)

# # Step 2: Split into train and test
# train_size = 50_000
# train_ds = conjecture_ds[:train_size]
# test_ds = conjecture_ds[train_size:]

# print(f"Train set size: {len(train_ds)}")
# print(f"Test set size: {len(test_ds)}")

# # Step 3: Save the splits
# train_path = os.path.join(STORAGE, "data/SFT/comp_V1/train.json")
# test_path = os.path.join(STORAGE, "data/SFT/comp_V1/test.json")
# print(train_path)
# print(test_path)

# write_data(json.dumps(train_ds), train_path,'json', no_compression=True)
# write_data(json.dumps(test_ds), test_path,'json',no_compression=True)
