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

