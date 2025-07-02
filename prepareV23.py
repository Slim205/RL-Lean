from datasets import load_dataset, Dataset

# Load dataset with multiple processes and caching

# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None


ds2 = load_dataset("Slim205/STP_Lean_SFT_workbook_only", split="train")

theorem_counts = []
new_db = []
for example in ds2:  # Direct iteration is faster than iterrows()
    theorem = get_raw_theorem(example['prompt'])
    if theorem : 
        if theorem not in  theorem_counts : 
            theorem_counts.append(theorem)
            new_db.append({'input' : example['prompt'].split('lean4')[1].strip() , 'proof' : example['target']})
hf_dataset = Dataset.from_list(new_db)

hf_dataset.push_to_hub('Slim205/lean_workbook_RL_V2')

print(hf_dataset)

print(f"Unique theorems: {len(theorem_counts)}") 
print(f"Total examples: {len(ds2)}")
# Unique theorems: 11780
# Total examples: 128509