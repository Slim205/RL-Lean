from datasets import load_dataset
import json

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

def save_inputs_to_jsonl(data: list, filename: str) -> None:
    """Saves a list of dicts to a JSONL file."""
    with open(filename, 'w') as f:
        for item in data:
            f.write(json.dumps(item) + '\n')

dataset = load_dataset("Slim205/mathlib_RL_v3", split='train')#.select(range(300,607))
inputs = []
p = 0
thm=[]
for sample in dataset:
    p+=1
    theorem_name = get_theorem_name(sample['theorem'])
    thm.append(theorem_name + str(p))

    inputs.append({
        "name": theorem_name + str(p),
        "split": "test"  ,
        "formal_statement" : sample['theorem'],
        'header' : sample['Context'],
    })

assert len(thm) == len(inputs)
save_inputs_to_jsonl(inputs, 'mathlib_train.jsonl')
print(f"Saved {len(inputs)} entries to mathlib.jsonl")