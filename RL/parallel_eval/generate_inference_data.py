from datasets import load_dataset
import json
# Optimized theorem counting
def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None

def save_inputs_to_jsonl(data: list, filename: str) -> None:
    """Saves a list of dicts to a JSONL file."""
    with open(filename, 'w') as f:
        for item in data:
            f.write(json.dumps(item) + '\n')

dataset = load_dataset("Slim205/Lean_conjecturer_data_v02", split='train')#.select(range(100))

inputs = []
thm=[]
for sample in dataset:
    theorem_name = sample['problem_id']
    thm.append(theorem_name )
    inputs.append({
        "name": theorem_name ,
        "split": "test"  ,
        "formal_statement" :  sample['formal_statement'],
    })
path_output = 'lean_conjecture_v2.jsonl'
assert len(thm) == len(inputs)
save_inputs_to_jsonl(inputs, path_output)
print(f"Saved {len(inputs)} entries to {path_output}")