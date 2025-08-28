import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V33.json'
initial_statements0 =load_statements(path)#[12000:]#[26315+4730: ]
print(len(initial_statements0))

total_list  = [x['new'] for x in initial_statements0  ]
total_list  = list(set(total_list))
print(len(total_list))

thm_list = []
for i in range(len(total_list) ) : 
    LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
    thm = LEAN4_DEFAULT_HEADER + f'theorem lean_conjecture_{i} ' + total_list[i]
    thm_list.append({ 'theorem' :thm})

print(thm_list[0])

from datasets import Dataset
ds = Dataset.from_list(thm_list).shuffle(42)
print(ds)
