import pandas as pd
import numpy as np
import argparse
from utils.proof_utils import analyze

parser = argparse.ArgumentParser()
# 'results/test/code_compilation.json'
parser.add_argument('--input_path',  type=str)
# 'results/test/compilation_summarize.json
parser.add_argument('--output_path',  type=str)
# 'results/test/to_inference_codes.json'
parser.add_argument('--code_path',  type=str)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)

#parser.add_argument('--field', default="is_valid_no_sorry",choices=["is_valid_no_sorry" , "is_valid_with_sorry" , "has_error" , "has_connection_error"], type=str)
args = parser.parse_args()

import json

input_file_path = args.code_path
with open(input_file_path, 'r') as json_file:
    codes = json.load(json_file)

input_file= args.input_path
with open(input_file, 'r') as f:
    result = json.load(f) 

df = analyze(result)

id_to_name = {f"{sample['name']}_{i}": sample['name'] 
              for i, sample in enumerate(codes)}

# Step 2: Add the original name to the DataFrame
df['original_name'] = df.index.map(lambda x: id_to_name[f"{codes[x]['name']}_{x}"])
df['complete'] = df['is_valid_no_sorry'].copy() # & ~df['has_error'] & ~df['has_connection_error']

print(df.head(10))
# Step 3: Group by name and count valid proofs
result_stats = df.groupby('original_name')[args.field].sum().reset_index()
result_stats.columns = ['name', 'correct']

# If you need to save as JSON
result_stats.reset_index()[["name", "correct"]].to_csv(args.output_path.replace(".json", ".csv"), index=False, header=True, sep='\t', quoting=1, na_rep='Missing')

result = {
  "total": len(result_stats['correct']),
  "correct": sum(result_stats['correct'] > 0),
  "accuracy": F"{sum(result_stats['correct'] > 0) / len(result_stats['correct'])  * 100:.2f}",
  "field": args.field
}

import json
with open(args.output_path, "w") as f:
    json.dump(result, f)
print(result)
