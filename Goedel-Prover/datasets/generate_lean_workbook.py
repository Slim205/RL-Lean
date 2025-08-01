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

#dataset = load_dataset("Slim205/lean_workbook_RL_v3", split='train').select(range(10240,11745))
dataset = load_dataset("Slim205/lean_workbook_RL_V20", split='train').select(range(6000))

inputs = []
p = 0
thm=[]
for sample in dataset:
    theorem_name = sample['problem_id']# + str(p)
    thm.append(theorem_name )
    inputs.append({
        "name": theorem_name ,
        "split": "test"  ,
        "formal_statement" :  'theorem' + sample['theorem'].split('theorem')[1],
    })
    p+=1
path_output = 'leanworkbook_train_6K.jsonl'
assert len(thm) == len(inputs)
save_inputs_to_jsonl(inputs, path_output)
print(f"Saved {len(inputs)} entries to {path_output}")