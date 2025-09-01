import json
import csv
import argparse

parser = argparse.ArgumentParser()
#path = 'results/conjecture/deepseek-SFT/'
parser.add_argument('--input_path',  type=str)
args = parser.parse_args()
path = args.input_path

def save_inputs_to_jsonl(data: list, filename: str) -> None:
    """Saves a list of dicts to a JSONL file."""
    with open(filename, 'w') as f:
        for item in data:
            f.write(json.dumps(item) + '\n')

# Load the list of dictionaries from the JSON file
with open(f"{path}code_compilation.json", "r", encoding="utf-8") as f:
    data_list = json.load(f)

# Load cosine similarities from TSV into a dictionary
cosine_similarities = {}
with open(f"{path}compilation_summarize2.csv", "r", encoding="utf-8") as f:
    reader = csv.DictReader(f, delimiter="\t")
    for row in reader:
        name = row["name"].strip('"')
        similarity = row["cosine_similarity"].strip('"')
        cosine_similarities[name] = similarity

# Build the output lines directly
output_lines = []
for item in data_list:
    name = item.get("name", "")
    code_raw = item.get("code", "").replace("\n", " ").replace("\t", " ")
    theorem = item.get("theorem", "").replace("\n", " ").replace("\t", " ")
    passed = item.get("compilation_result", {}).get("pass", None)
    similarity = cosine_similarities.get(name, "N/A")

    # Try to isolate the `theorem` from `code`
    code = ""
    if "theorem" in code_raw:
        code = "theorem" + code_raw.split("theorem", 1)[1].split(' sorry')[0]
    else:
        code = code_raw  # fallback

    if passed  : 
        output_lines.append({'name' :name,  'split' : 'test' ,'formal_statement' : code })

path_output = f'{path}new_theorems.jsonl'
save_inputs_to_jsonl(output_lines, path_output)
print(f"Saved {len(output_lines)} entries to {path_output}")