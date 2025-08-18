import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def get_dataset() : 

    path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V142.json'
    initial_statements0 =load_statements(path)[26315+4730:]

    total_list  = [x['new'] for x in initial_statements0  ]
    total_list  = list(set(total_list))
    thm_list = []
    for i in range(len(total_list)) : 
        LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
        thm = LEAN4_DEFAULT_HEADER + f'theorem lean_conjecture_{i+49295} ' + total_list[i]
        thm_list.append({ 'theorem' :thm})

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
# import csv 
# correct_proofs ={}
# s= 0 
# with open("/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/sft_V5/SFT-64-Part2-V1/compilation_summarize.csv", "r", encoding="utf-8") as f:
#     reader = csv.DictReader(f, delimiter="\t")
#     for row in reader:
#         name = row["name"].strip('"')
#         correct = row["correct"].strip('"')
#         correct_proofs[name] = int(correct) 
#         if int(correct) < 5:
#             s+=1
# print(s)
inputs = []
p = 49295
thm=[]
for sample in dataset:
    theorem_name = sample['theorem'].split('theorem')[1][1:].split(' ')[0]#f'lean_conjecture_{p}'
    #if  correct_proofs[theorem_name] < 5 : 
    thm.append(theorem_name)
    inputs.append({
        "name": theorem_name ,
        "split": "test"  ,
        "formal_statement" :  'theorem' + sample['theorem'].split('theorem')[1],
    })
    p+=1

    if p < 49295 + 10 : 
        print(theorem_name)
path_output = 'sft_V5_Part3.jsonl'
assert len(thm) == len(inputs)
save_inputs_to_jsonl(inputs, path_output)
print(f"Saved {len(inputs)} entries to {path_output}")