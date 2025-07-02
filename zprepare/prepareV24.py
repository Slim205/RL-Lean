from datasets import load_dataset, Dataset

# Load dataset with multiple processes and caching

# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None
import numpy as np
ds = load_dataset("Slim205/lean_workbook_RL_full_v1", split="train")
print(np.mean(ds.select(range(20000))["is_proved"]) * 100)

# ds1 = load_dataset("Slim205/lean_workbook_RL_full", split="train")
# ds2 = load_dataset("Slim205/lean_workbook_RL_v3", split="train")

# list_th = []
# for x in ds2 : 
#     thm = get_raw_theorem(x['input'])
#     list_th.append(thm)

# def update(x) : 
#     x['is_proved']  = get_raw_theorem(x['input']) in  list_th 
#     return x
# ds3 = ds1.map(update)
# print(ds3)

# from datasets import Dataset, DatasetDict
# import numpy as np

# ds3 = ds3.shuffle(seed=0)  # seed for reproducibility

# # ── 1. percentage of proved theorems ───────────────────────────────
# pct_proved = np.mean(ds3["is_proved"]) * 100       # True→1, False→0
# print(f"{pct_proved:.2f}% of theorems are proved")

# test_val = int(np.mean(ds3["is_proved"]) * 1000 )      # True→1, False→0

# test_ds = ds3.select(range(84480,85961))
# train_ds = ds3.select(range(84480))
# print(np.mean(test_ds["is_proved"]) * 100)
# print(np.mean(train_ds["is_proved"]) * 100)

# final_data = DatasetDict()
# final_data['train'] = train_ds
# final_data['test'] = test_ds
# print(final_data)


# final_data.push_to_hub('Slim205/lean_workbook_RL_full_v1')
# header= 'import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'

# new_db = []
# for example in ds2: 
#     new_db.append({'input' : header +  example['formal_statement'].split('sorry')[0].strip()})

# hf_dataset = Dataset.from_list(new_db)

#hf_dataset.push_to_hub('Slim205/lean_workbook_RL_full')

# print(hf_dataset)

