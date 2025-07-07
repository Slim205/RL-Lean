from datasets import load_dataset, Dataset

# Load dataset with multiple processes and caching

# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return 'lean_workbook_' + prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None

#ds0 = load_dataset("Slim205/lean_workbook_goedel", split="train")
ds1 = load_dataset("Slim205/lean_workbook_RL_goedel_v4", split="train")
ds2 = load_dataset("Slim205/lean_workbook_RL_v3", split="train")

list_th = []
for x in ds2 : 
    thm = get_raw_theorem(x['input'])
    list_th.append(thm)

def update(x) : 
    x['is_proved']  = get_raw_theorem(x['theorem']) in  list_th 
    return x
ds3 = ds1.map(update)

from datasets import Dataset, DatasetDict
import numpy as np

ds3 = ds3.shuffle(seed=0)  # seed for reproducibility

# ── 1. percentage of proved theorems ───────────────────────────────
pct_proved = np.sum(ds3["is_proved"])        # True→1, False→0
print(f"{pct_proved:.2f}% of theorems are proved")
print(ds3)
print(ds2)
def filter2(s) : 
    return not s['is_proved']
ds4 = ds3.filter(filter2)
print(ds4)
new_dataset = []
for example in ds4 : 
    theorem = 'import Mathlib\nimport Aesop\n' + 'set_option maxRecDepth 100000'+  example['theorem'].split('Aesop')[1] 
    new_dataset.append({'problem_id' : example['problem_id'], 'theorem' : theorem , 'proof' : example['proof'] , 'is_proved' : example['is_proved']})

for example in ds2 : 
    theorem = 'import Mathlib\nimport Aesop\n' + 'set_option maxRecDepth 100000'+  example['input'].split('Aesop')[1] 
    new_dataset.append({'problem_id' : get_raw_theorem(example['input']), 'theorem' : theorem , 'proof' : example['proof'] , 'is_proved' : True })

ds6 = Dataset.from_list(new_dataset).shuffle(seed=0) 

print(ds6)
print(np.unique(ds6['problem_id']).shape[0])

print(np.mean(ds6["is_proved"]) * 100)
test_dataset = load_dataset('Slim205/minif2f',split='valid')

ds_test_list = []
for example in test_dataset :
    header= 'import Mathlib\nimport Aesop\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'

    theorem = header +   example['formal_statement']
    ds_test_list.append({'problem_id' : example['name'], 'theorem' : theorem , 'proof' : '' , 'is_proved' : False })
ds_test = Dataset.from_list(ds_test_list)


final_data = DatasetDict()
final_data['train'] = ds6
final_data['test'] = ds_test
print(final_data)


final_data.push_to_hub('Slim205/lean_workbook_RL_V5')
