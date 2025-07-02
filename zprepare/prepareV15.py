import numpy as np
from datasets import DatasetDict,load_dataset

ds = load_dataset("Slim205/mathlib_RL_v3",split='train')

csv_path = './Goedel-Prover/results/mathlib_train/SFT-32/compilation_summarize.csv'

import csv

def get_theorem_name(theorem_str: str) -> str:
    """Extracts theorem name safely from a Lean theorem string."""
    try:
        parts = theorem_str.split("theorem", 1)
        theorem_part = parts[1].strip()
        name = theorem_part.split()[0] if theorem_part else "unknown"
        return name
    except Exception as e:
        print(f"Error parsing theorem: {e}")
        return "error"

data = {}
with open(csv_path, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data[row["name"]] = int(row["correct"])
p=0
inputs=[]
num_ds=0
for sample in ds:
    p+=1
    theorem_name = get_theorem_name(sample['theorem']) +  str(p)
    if theorem_name in data.keys() : 
        sample['eval_complexity'] = data[theorem_name] / 32
        num_ds+=1
    inputs.append(sample)
print(num_ds)

from datasets import Dataset
ds_train = Dataset.from_list(inputs)

ds_train = ds_train.sort('eval_complexity',reverse=True)
dataset_test = load_dataset("Slim205/mathlib_RL_v3", split='test')

dataset_test = dataset_test.map(lambda x: {'eval_complexity': 0.0})

ds2 = DatasetDict({'train'  : ds_train , 'test' : dataset_test })
print(ds2)

ds2.push_to_hub('Slim205/mathlib_RL_eval_complexity')
