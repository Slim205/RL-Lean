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
        json.dump(statements, f, indent=1)

def add_new_statements(new_statements, filename):
    existing = load_statements(filename)
    combined = existing + new_statements
    save_statements(combined, filename)

def get_step(statements_dict) :
    return statements_dict[-1]['step']

base_path = '/n/home07/sbarkallah/data/conjecture_V2'
train_path = f'{base_path}/train.parquet'
test_path = f'{base_path}/test.parquet'

train_df = pd.read_parquet(train_path, engine='pyarrow')  # or engine='fastparquet'
test_df = pd.read_parquet(test_path, engine='pyarrow')
n = 16

path = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{n}.json'
if os.path.exists(path):
    print("Path exists.")
else : 
    initial_statements = []

    for sample in train_df['extra_info'] :
        theorem = extract_theorem(sample['theorem'])
        initial_statements.append({'old' : '' , 'new' : theorem , 'step' : 0 })

    save_statements(initial_statements,path)
    print(len(load_statements(path)))
    print(get_step(initial_statements))
    path = f'/n/netscratch/amin_lab/Lab/slim/statements/test_V{n}.json'
    initial_statements = []

    for sample in test_df['extra_info'] :
        theorem = extract_theorem(sample['theorem'])
        initial_statements.append({'old' : '' , 'new' : theorem , 'step' : 0 })
        
    save_statements(initial_statements,path)
    print(len(load_statements(path)))
    print(path)
    print(get_step(initial_statements))