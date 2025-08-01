import json
import matplotlib.pyplot as plt
import csv
import argparse
import re
parser = argparse.ArgumentParser()
#path = 'results/conjecture/deepseek-SFT'
parser.add_argument('--input_path',  type=str)
args = parser.parse_args()
path = args.input_path

# Load cosine similarities from TSV into a dictionary
correct_proofs ={}
with open(f"{path}/complexity_scores/compilation_summarize.csv", "r", encoding="utf-8") as f:
    reader = csv.DictReader(f, delimiter="\t")
    for row in reader:
        name = row["name"].strip('"')
        correct = row["correct"].strip('"')
        correct_proofs[name] = int(correct) / 32

plt.figure(figsize=(10, 6))
plt.hist(list(correct_proofs.values()), bins=20, color="steelblue", alpha=0.8)
plt.xlabel("Pass@32")
plt.ylabel("Frequency")
plt.title("Complexity of conjectures")
plt.grid(True)
plt.tight_layout()
plot_path = f"{path}/complexity_plot.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")

#path = 'results/conjecture/deepseek-SFT/'
# Load cosine similarities from TSV into a dictionary
cosine_similarities = {}
with open(f"{path}/compilation_summarize2.csv", "r", encoding="utf-8") as f:
    reader = csv.DictReader(f, delimiter="\t")
    for row in reader:
        name = row["name"].strip('"')
        similarity = row["cosine_similarity"].strip('"')
        cosine_similarities[name] = round(float(similarity),3)
        if name not in correct_proofs.keys() : 
            correct_proofs[name] = -0.1
keys = list(cosine_similarities.keys())
x = [cosine_similarities[k] for k in keys]
y = [correct_proofs[k] for k in keys]


plt.figure(figsize=(10, 6))
plt.scatter(y,x)
plt.xlabel("Pass@32")
plt.ylabel("Cosine_similarity")
plt.title("Complexity of conjectures Vs Cosine_similarity")
plt.grid(True)
plt.tight_layout()
plot_path = f"{path}/scatter_plot.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")

with open(f"{path}/code_compilation.json", "r", encoding="utf-8") as f:
    data_list = json.load(f)

output_lines = []
new_lines=[]
for item in data_list:
    name = item.get("name", "")
    code_raw = item.get("code", "").replace("\n", " ").replace("\t", " ")
    theorem = item.get("theorem", "").replace("\n", " ").replace("\t", " ")
    passed = item.get("compilation_result", {}).get("pass", None)
    similarity = cosine_similarities[name]
    complexity = correct_proofs[name]
    # Try to isolate the `theorem` from `code`
    code = ""
    if "theorem" in code_raw:
        code = "theorem" + code_raw.split("theorem", 1)[1].split(' sorry')[0]
    else:
        code = code_raw  # fallback
    new_lines.append(code)
    output_lines.append(
        f"Name: {name}\nPass: {passed}\nOld: {theorem}\nNew: {code}\nCosine_similarity: {similarity}\nComplexity: {complexity}\n{'-'*60}"
    )

# Write all results to the output file once
with open(f"{path}/output_readable.txt", "w", encoding="utf-8") as f:
    f.write("\n".join(output_lines))


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

pattern_dict={ x : 0 for x in patterns }
for code in new_lines:
    theorem = extract_theorem(code)
    class_thm = pat(theorem)
    pattern_dict[class_thm] += 1


# Plotting the data
plt.figure(figsize=(10, 6))
plt.bar(pattern_dict.keys(), pattern_dict.values())
plt.xlabel('Pattern Class')
plt.ylabel('Count')
plt.title('Count of Theorems by Pattern Class')
plt.tight_layout()
plt.grid(axis='y')
plot_path = f"{path}/theorem_type.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
