import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def get_dataset() : 
    path = '/n/netscratch/amin_lab/Lab/slim/statements_old/train_V28.json'
    initial_statements0 =load_statements(path)

    total_list  = [x['new'] for x in initial_statements0   ]
    total_list  = list(set(total_list))
    thm_list = []
    for i in range(len(total_list)) : 
        LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
        thm = LEAN4_DEFAULT_HEADER + f'theorem lean_conjecture_{i} ' + total_list[i]
        thm_list.append({ 'Formal statement' :thm})

    print(thm_list[0])

    from datasets import Dataset
    ds = Dataset.from_list(thm_list).shuffle(42)
    print(ds)
    return ds


from datasets import load_dataset

def save_inputs_to_jsonl(data: list, filename: str) -> None:
    """Saves a list of dicts to a JSONL file."""
    with open(filename, 'w') as f:
        for item in data:
            f.write(json.dumps(item) + '\n')

dataset = get_dataset()
dataset.push_to_hub('Slim205/Lean_conjecturer_data_v01')
