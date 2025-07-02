from datasets import load_dataset
from collections import defaultdict

# Load dataset with multiple processes and caching
dataset = load_dataset("Slim205/LeanWorkbook", split="train")

# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None

# Using defaultdict for cleaner counting
theorem_counts = defaultdict(int)

for example in dataset:  # Direct iteration is faster than iterrows()
    theorem = get_raw_theorem(example['formal_statement'])
    if theorem:  # Skip None values
        theorem_counts[theorem] += 1
       
print(f"Unique theorems: {len(theorem_counts)}") 
print(f"Total examples: {len(dataset)}")
print(f"Most common theorems: {sorted(theorem_counts.items(), key=lambda x: x[1], reverse=True)[:5]}")

# def filter2(x) : 
#     return 'plus' not in x['formal_statement']

# print(dataset.filter(filter2)) # 51K leanworkbook / 38K Plus

path2 = 'Slim205/STP_Lean_SFT_workbook_only'

ds2 = load_dataset("Slim205/STP_Lean_SFT_workbook_only", split="train")

theorem_counts = defaultdict(int)

for example in ds2:  # Direct iteration is faster than iterrows()
    theorem = get_raw_theorem(example['prompt'])
    if theorem:  # Skip None values
        theorem_counts[theorem] += 1

print(f"Unique theorems: {len(theorem_counts)}") 
print(f"Total examples: {len(ds2)}")
print(f"Most common theorems: {sorted(theorem_counts.items(), key=lambda x: x[1], reverse=True)[:5]}")
# Unique theorems: 11780
# Total examples: 128509