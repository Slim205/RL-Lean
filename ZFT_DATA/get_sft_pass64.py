import json
from datasets import DatasetDict,load_dataset

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
def get_original_theorem(theorem_name) : 
    p = 0
    for x in range(len(theorem_name)) : 
        if theorem_name[x] == '_' : 
            p = x
    return theorem_name[:p]

# Path to the JSON file
file_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/sft_V1/SFT-64/code_compilation.json"

# Load the list of dicts from the file
with open(file_path, "r", encoding="utf-8") as f:
    data = json.load(f)

list_proved_theorems ={}
for entry in data:
    compilation_result = entry.get("compilation_result", {})
    if compilation_result['complete'] : 
        thm = get_original_theorem(compilation_result['custom_id'])
        if thm not in list_proved_theorems.keys() : 
            list_proved_theorems[thm] = [compilation_result['code']]
        else : 
            list_proved_theorems[thm].append(compilation_result['code'])
list_proved_theorems_filtered = {}
for x,y in list_proved_theorems.items() :
    new_list = list(set(y))
    list_proved_theorems_filtered[x] = new_list[:16]

list_data = []
for x,y in list_proved_theorems_filtered.items() :
    for code in y : 
    list_data.append({'theorem' :  })