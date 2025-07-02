import json
from datasets import load_dataset
import os
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  


# Construct data theorem | proof | file name | Context | start | end

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


HOME_DIR = os.path.expanduser('~')
path_to_mathlib = f'{HOME_DIR}/lean/mathlib4/'


MATHLIB_DIR = Path(path_to_mathlib).expanduser()  
lean_file_dict = read_lean_files(MATHLIB_DIR)
lean_file_dict = {k.split('mathlib4/')[-1]: v for k, v in lean_file_dict.items()} # File name : [list of lines in the file]
print(f"Total .lean files read: {len(lean_file_dict)}")

# Leandojo
LeanDojo_DIR = Path("../leandojo_benchmark_4/").expanduser()
train_path = LeanDojo_DIR / "random/train.json"
val_path = LeanDojo_DIR / "random/val.json"
test_path = LeanDojo_DIR / "random/test.json"
proofs_train = json.load(train_path.open())
proofs_val = json.load(val_path.open())
proofs_test = json.load(test_path.open())

from collections import defaultdict
entry_dict = defaultdict(list)
for entry in proofs_train + proofs_val + proofs_test:
    if len(entry['traced_tactics']) > 0: 
        entry_dict[entry['file_path']].append(entry)

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
        context_str =  ''.join(lines[:entry['start'][0] - 1]) 
        theorem_str = ''.join(lines[entry['start'][0] - 1: entry['end'][0]])        
        theorem_item = (file_name, context_str, theorem_str,entry['start'][0],entry['end'][0])
        eval_theorems.append(theorem_item)
    
print('# Mathlib theorems:', len(eval_theorems))

rng = np.random.default_rng(0)
rng.shuffle(eval_theorems)
train_theorems = [{'Context': entry[1], 'target': entry[2], 'file_name': entry[0], 'start' : entry[3], 'end' : entry[4]} for entry in eval_theorems ]

from datasets import Dataset
dataset = Dataset.from_list(train_theorems)
dataset.push_to_hub("Slim205/mathlib_v09")  

#dataset = load_dataset("Slim205/mathlib_v09")
def filter1(sample):
    """Filter samples that are theorems with proofs."""
    return sample['target'].startswith('theorem') and ':= by' in sample['target']

dataset = dataset.filter(filter1)

def map1(sample):
    """Split theorem statements from proofs."""
    target = sample['target']
    theorem_part, proof_part = target.split(':= by', 1)  
    return {
        'theorem': theorem_part + ':= by',
        'proof': proof_part
    }

dataset = dataset.map(map1)
dataset = dataset.remove_columns(['target'])  

dataset.push_to_hub('Slim205/mathlib_benchmark_v09')