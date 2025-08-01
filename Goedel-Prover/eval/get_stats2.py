# load the josn file
import json
import re

path = './results/conjecture/STP-6K-train'
def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"


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

patterns = [
    "negation", "iff", "or", "and",
    "forall", "exists", "imp", "atom"
]

pattern_dict_before={ x : 0 for x in patterns }
pattern_dict_after={ x : 0 for x in patterns }


# read the accuracy (from the .txt file)
new_lines = []
with open(f'{path}/output_readable.txt', 'r', encoding='utf-8') as file:
    raw_data = file.read().strip()

# Split entries using the separator line

entries = raw_data.split("------------------------------------------------------------")
results = []

for entry in entries:
    lines = [line.strip() for line in entry.strip().splitlines() if line.strip()]
    if len(lines) < 6:
        continue  # skip incomplete entries

    try:
        record = {
            "Name": lines[0].split(":", 1)[1].strip(),
            "Pass": lines[1].split(":", 1)[1].strip() == "True",
            "Old": lines[2].split(":", 1)[1].strip(),
            "New": lines[3].split(":", 1)[1].strip(),
            "Cosine_similarity": float(lines[4].split(":", 1)[1].strip()),
            "Complexity": float(lines[5].split(":", 1)[1].strip()),
        }
        results.append(record)

        pattern_dict_before[pat(extract_theorem(record['New']))] += 1
        if record['Complexity'] > 0 and record['Complexity'] <= 0.5 :
            if record["Cosine_similarity"] > 0.4 and record["Cosine_similarity"] < 0.9 : 
                pattern_dict_after[pat(extract_theorem(record['New']))] += 1

    except Exception as e:
        print(f"Skipping problematic entry:\n{entry}\nError: {e}")

        break




# # plot the plot accuracy of each cluster. 

for pattern in patterns : 
    if pattern_dict_before[pattern] > 0 : 
        print(f'{pattern} {pattern_dict_after[pattern] / pattern_dict_before[pattern]}')

print(pattern_dict_before)
print(pattern_dict_after)

# SFT 1 
# negation 0.25
# iff 0.125
# or 0.0
# and 0.13333333333333333
# forall 0.06451612903225806
# exists 0.10714285714285714
# imp 0.0
# atom 0.0694980694980695
# {'negation': 8, 'iff': 40, 'or': 12, 'and': 15, 'forall': 62, 'exists': 28, 'imp': 10, 'atom': 259}
# {'negation': 2, 'iff': 5, 'or': 0, 'and': 2, 'forall': 4, 'exists': 3, 'imp': 0, 'atom': 18}


# SFT2
# negation 0.16666666666666666
# iff 0.02564102564102564
# or 0.06666666666666667
# and 0.125
# forall 0.0
# exists 0.0
# imp 0.0
# atom 0.06927710843373494
# {'negation': 6, 'iff': 39, 'or': 15, 'and': 8, 'forall': 11, 'exists': 17, 'imp': 6, 'atom': 332}
# {'negation': 1, 'iff': 1, 'or': 1, 'and': 1, 'forall': 0, 'exists': 0, 'imp': 0, 'atom': 23}