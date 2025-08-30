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
path = f'/n/netscratch/amin_lab/Lab/slim/RL/storage/conjecturer_V1/data/train.json'
statements = load_statements(path)#[12000:]          # your helper from above
rank = [x['step'] for x in statements ]

statements = [x['new'] for x in statements]

# ----------------- incremental statistics -----------------
patterns = [
    "negation", "iff", "or", "and",
    "forall", "exists", "imp", "atom"#, 'part'
]
running_counts   = Counter()                # how many of each seen so far
running_shares   = defaultdict(list)        # pattern -> list[float]
total_seen       = 0

for stmt in tqdm(statements, desc="Processing"):
    total_seen += 1
    ch =pat(stmt)

    running_counts[ch] += 1

    # append the current share of every pattern
    for p in patterns:
        running_shares[p].append(running_counts[p] / total_seen)

# ----------------- plot -----------------
plt.figure(figsize=(12, 7))
x = range(1, total_seen + 1)

for p in patterns:
    plt.scatter(rank, running_shares[p], label=p)

plt.xlabel("Training Steps")
plt.ylabel("Cumulative proportion")
plt.title("Pattern distribution as generation progresses")
plt.legend(title="Pattern")
plt.grid(True)
plt.tight_layout()

plot_path = f"./patterns_over_time_V1.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
