new_lines = []
path = './results/conjecture/STP-6K-train'
with open(f'{path}/output_readable.txt', 'r', encoding='utf-8') as file:
    for line in file:
        if line.startswith("New:"):
            new_lines.append(line.strip())  # remove trailing newline characters
def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

import re
from collections import Counter, defaultdict
from tqdm import tqdm
import matplotlib.pyplot as plt
import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []
def get_goal(thm) : 
   
    if thm.startswith(':') :
        return thm[2:]
    elif  ') :' in thm : 
        ch = ') :'
        return thm.split(ch)[1].strip()
    elif  '):' in thm : 
        ch = '):'
        return thm.split(ch)[1].strip()
    elif  '} :' in thm : 
        ch = '} :'
        return thm.split(ch)[1].strip()
    elif  '}:' in thm : 
        ch = '}:'
        return thm.split(ch)[1].strip()
    elif  '] :' in thm : 
        ch = '] :'
        return thm.split(ch)[1].strip()
    elif  ']:' in thm : 
        ch = ']:'
        return thm.split(ch)[1].strip()

    return thm
    
# ----------------- helper -----------------
def pat(text: str) -> str:
    """Coarse syntactic pattern of a Lean statement."""
    s = get_goal(text)
    s = re.sub(r'\s+', ' ', s)
    if s.startswith("¬") :
        return "negation"
    if s.startswith("∃") :
        return "exists"
    if s.startswith("∀") :
        return "forall"
    if "↔" in s :
        return "iff"
    if "∨" in s :
        return "or"
    if "∧" in s :
        return "and"
    if "→" in s:
        return "imp"
    return "atom"

patterns = [
    "negation", "iff", "or", "and",
    "forall", "exists", "imp", "atom"
]

pattern_dict={ x : 0 for x in patterns }
for line in new_lines:
    theorem = extract_theorem(line)
    class_thm = pat(theorem)
    # if class_thm == 'atom' : 
    #     for i in range(1,10) : 
    #         if f'≤ {i})' in theorem :
    #             class_thm = 'part'
    #             break

    pattern_dict[class_thm] += 1


# Plotting the data
plt.figure(figsize=(10, 6))
plt.bar(pattern_dict.keys(), pattern_dict.values())
plt.xlabel('Pattern Class')
plt.ylabel('Count')
plt.title('Count of Theorems by Pattern Class')
plt.tight_layout()
plt.grid(axis='y')
plot_path = f"{path}/theorem_type3.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
