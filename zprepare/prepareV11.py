import json
from datasets import DatasetDict,load_dataset

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
def get_original_theorem(theorem_name) : 
    p = 0
    for x in range(len(theorem_name)) : 
        if theorem_name[x] == '_' : 
            p = x
    return theorem_name[:p]

# Path to the JSON file
file_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/mathlib_train/baseline/code_compilation.json"

# Load the list of dicts from the file
with open(file_path, "r", encoding="utf-8") as f:
    data = json.load(f)

list_proved_theorems =[]
for entry in data:
    compilation_result = entry.get("compilation_result", {})
    if compilation_result['complete'] : 
        list_proved_theorems.append(get_original_theorem(compilation_result['custom_id']))

print(len(list_proved_theorems))
print('===================')

dataset = load_dataset("Slim205/mathlib_RL_v3", split='train')

inputs = []
p = 0
num_ds=0
for sample in dataset:
    p+=1
    sample['iteration'] = 0
    theorem_name = get_theorem_name(sample['theorem']) +  str(p)
    if theorem_name in list_proved_theorems : 
        sample['iteration'] = 1
        num_ds+=1
    inputs.append(sample)
print(num_ds)

from datasets import Dataset
ds_train = Dataset.from_list(inputs)
dataset_test = load_dataset("Slim205/mathlib_RL_v3", split='test')

dataset_test = dataset_test.map(lambda x: {'iteration': 0})

ds = DatasetDict({'train'  : ds_train , 'test' : dataset_test })
print(ds)

ds.push_to_hub('Slim205/mathlib_RL_v3_iter11')
