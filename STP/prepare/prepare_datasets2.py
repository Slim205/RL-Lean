from datasets import load_dataset
from collections import defaultdict

# Load dataset with multiple processes and caching
dataset = load_dataset("kfdong/STP_Lean_SFT", split="train")

# Optimized filtering
filtered_dataset = dataset.filter(
    lambda example: 'lean_workbook' in example['prompt'],
    num_proc=64  # Adjusted to more reasonable number based on typical CPU cores
)

# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return prompt.split('lean_workbook')[1].split(' ')[0][1:]
    except (IndexError, AttributeError):
        return None

# Using defaultdict for cleaner counting
theorem_counts = defaultdict(int)

# Vectorized operation would be better, but since we need to process strings:
for example in filtered_dataset:  # Direct iteration is faster than iterrows()
    theorem = get_raw_theorem(example['prompt'])
    if theorem:  # Skip None values
        theorem_counts[theorem] += 1

print(f"Unique theorems: {len(theorem_counts)}") # 128509 / 11780
print(f"Total examples: {len(filtered_dataset)}")
print(f"Most common theorems: {sorted(theorem_counts.items(), key=lambda x: x[1], reverse=True)[:5]}")

print(min(theorem_counts.values()))
print(max(theorem_counts.values()))
d={}
for x in theorem_counts.values() : 
    if x not in d.keys() : 
        d[x] = 1
    else : 
        d[x] +=1
print(sorted(d.items(), key=lambda x: x[1], reverse=True)) # 4892 == 16
#[(16, 4892), (1, 972), (2, 620), (3, 502), (14, 476), (4, 470), (15, 466), (13, 426), (12, 409), (11, 407),
# (5, 370), (10, 369), (8, 355), (9, 353), (7, 347), (6, 346)]
