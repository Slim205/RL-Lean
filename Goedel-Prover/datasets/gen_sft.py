import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def get_dataset() : 
    path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V28.json'
    initial_statements0 =load_statements(path)[12000:]

    total_list  = [x['new'] for x in initial_statements0   ]
    total_list  = list(set(total_list))
    thm_list = []
    for i in range(len(total_list)) : 
        LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
        thm = LEAN4_DEFAULT_HEADER + f'theorem lean_conjecture_{i} ' + total_list[i]
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
# with open("/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/sft_V5/SFT-64-Part1-V2/compilation_summarize.csv", "r", encoding="utf-8") as f:
#     reader = csv.DictReader(f, delimiter="\t")
#     for row in reader:
#         name = row["name"].strip('"')
#         correct = row["correct"].strip('"')
#         correct_proofs[name] = int(correct) 
#         if int(correct) < 5 :
#             s+=1
inputs = []
p = 0
thm=[]
for sample in dataset:
    theorem_name = sample['theorem'].split('theorem')[1][1:].split(' ')[0]# f'lean_conjecture_{p}'
    # if theorem_name in correct_proofs.keys() and correct_proofs[theorem_name] < 4 : 
    thm.append(theorem_name)
    inputs.append({
        "name": theorem_name ,
        "split": "test"  ,
        "formal_statement" :  'theorem' + sample['theorem'].split('theorem')[1],
    })
    p+=1

    # if p < 20 : 
    #     print(sample['theorem'].split('theorem')[1])
assert len(thm) == len(inputs)
path_output1 = 'sft_V6_1.jsonl'
path_output2 = 'sft_V6_2.jsonl'
path_output3 = 'sft_V6_3.jsonl'

save_inputs_to_jsonl(inputs[:9000], path_output1)
save_inputs_to_jsonl(inputs[9000:18000], path_output2)
save_inputs_to_jsonl(inputs[18000:], path_output3)

print(f"Saved {len(inputs)} entries to {path_output1}")