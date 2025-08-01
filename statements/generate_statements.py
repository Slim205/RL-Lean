import pandas as pd
import os
import json
# File paths

def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def save_statements(statements, filename):
    with open(filename, 'w') as f:
        json.dump(statements, f, indent=2)

def add_new_statements(new_statements, filename):
    existing = load_statements(filename)
    combined = existing + new_statements
    save_statements(combined, filename)


base_path = '/n/home07/sbarkallah/data/conjecture_V2'
train_path = f'{base_path}/train.parquet'
test_path = f'{base_path}/test.parquet'

train_df = pd.read_parquet(train_path, engine='pyarrow')  # or engine='fastparquet'
test_df = pd.read_parquet(test_path, engine='pyarrow')
path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V9.json'
initial_statements = []

for sample in train_df['extra_info'] :
    theorem = extract_theorem(sample['theorem'])
    initial_statements.append(theorem)

save_statements(initial_statements,path)
print(len(load_statements(path)))
path = '/n/netscratch/amin_lab/Lab/slim/statements/test_V9.json'
initial_statements = []

for sample in test_df['extra_info'] :
    theorem = extract_theorem(sample['theorem'])
    initial_statements.append(theorem)
save_statements(initial_statements,path)
print(len(load_statements(path)))
print(path)