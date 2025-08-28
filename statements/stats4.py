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
    if " → " in s:
        return "imp"
    return "atom"


# # ----------------- load your data -----------------
n = 35
path = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{n}.json'
statements = load_statements(path)#[12000:] 

new_statements = []
p = 0
for x in statements : 
    # if 'tactic' not in x.keys() : 
    #     p= x['step']
    # else :
    #     x['step'] = x['step'] - 34
    new_statements.append(x)
print(p)
rank = [x['step'] for x in new_statements ]

tactics = [x['tactic'] for x in new_statements]
percentage = [x['percentage'] for x in new_statements]

from collections import Counter

tactics = [x['tactic'] for x in new_statements]
tactic_counts = Counter(tactics)

# Get the top 10 tactics
top_10 = tactic_counts.most_common(10)

# Print them nicely
for tactic, count in top_10:
    print(f"{tactic}: {count}")

tac_dict ={}
for x in new_statements :
    if x['tactic'] not in tac_dict : 
        tac_dict[x['tactic']] = []
    if x['step']  not in tac_dict[x['tactic']] : 
        tac_dict[x['tactic']].append(x['step'] )


# Invert mapping: rank → tactic
rank_to_tactic = {}
for tactic, ranks in tac_dict.items():
    for r in ranks:
        rank_to_tactic[r] = tactic

# Print in rank order
for r in sorted(rank_to_tactic.keys()):
    print(r, ":", rank_to_tactic[r])
plt.figure(figsize=(12, 7))


plt.scatter(rank, percentage)

plt.xlabel("Training Steps")
plt.ylabel("Max Tactic Occurrence")
plt.title("Peak Tactic Frequency per Batch During Training")
plt.grid(True)
plt.tight_layout()

plot_path = f"scatter_percentageV{n}special.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
