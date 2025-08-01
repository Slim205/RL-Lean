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
thm =   ": \u00ac(\u2200 (a b c : \u211d) , 1 < a ^ 2 / (a + 1) ^ 2 + b ^ 2 / (b + 1) ^ 2 + c ^ 2 / (c + 1) ^ 2 \u2194 5 < a * b * c \u2228 a * b * c < 2) := by"
print(get_goal(thm))
print(pat(thm))

thm=   "(x : ℕ → ℝ) (h₁ : ∀ n ≤ 1996, x n = 0) (h₂ : x 1997 = 1) (h₃ : ∀ n ≥ 1, ∀ m ≤ 1996, x (n + m) = (∑ i in Finset.range m, x (n + i)) / 1997) : ∃ l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε := by"
print(get_goal(thm))
print(pat(thm))




# # ----------------- load your data -----------------
path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V142.json'
statements = load_statements(path)[12000:]          # your helper from above

statements = [x['new'] for x in statements]
# ----------------- incremental statistics -----------------
patterns = [
    "negation", "iff", "or", "and",
    "forall", "exists", "imp", "atom", 'part'
]
running_counts   = Counter()                # how many of each seen so far
running_shares   = defaultdict(list)        # pattern -> list[float]
total_seen       = 0

for stmt in tqdm(statements, desc="Processing"):
    total_seen += 1
    ch =pat(stmt)
    if ch == 'atom' : 
        for i in range(1,10) : 
            if f'≤ {i})' in stmt :
                ch = 'part'
                break

    running_counts[ch] += 1

    # append the current share of every pattern
    for p in patterns:
        running_shares[p].append(running_counts[p] / total_seen)

# ----------------- plot -----------------
plt.figure(figsize=(12, 7))
x = range(1, total_seen + 1)

for p in patterns:
    plt.plot(x, running_shares[p], label=p)

plt.xlabel("Generated Statements")
plt.ylabel("Cumulative proportion")
plt.title("Pattern distribution as generation progresses")
plt.legend(title="Pattern")
plt.grid(True)
plt.tight_layout()

plot_path = "patterns_over_timeV14.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
