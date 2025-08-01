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

old_n = 131
new_n = 132
step = 120
step_test = 10

train_df = pd.read_parquet(train_path, engine='pyarrow')  # or engine='fastparquet'
test_df = pd.read_parquet(test_path, engine='pyarrow')

path = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{old_n}.json'
path2 = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{new_n}.json'

initial_statements = load_statements(path)
print(len(initial_statements)) # 12001
print(get_step(initial_statements)) # 1

new_initial_statements = []
for statement in initial_statements : 
    if statement['step'] <= step : 
        new_initial_statements.append(statement)

save_statements(new_initial_statements,path2)
print(len(load_statements(path2)))
print(get_step(new_initial_statements))


path = f'/n/netscratch/amin_lab/Lab/slim/statements/test_V{old_n}.json'
path2 = f'/n/netscratch/amin_lab/Lab/slim/statements/test_V{new_n}.json'

initial_statements = load_statements(path)
print(len(initial_statements)) # 12001
print(get_step(initial_statements)) # 1

new_initial_statements = []
for statement in initial_statements : 
    if statement['step'] <= step_test : 
        new_initial_statements.append(statement)

save_statements(new_initial_statements,path2)
print(len(load_statements(path2)))
print(get_step(new_initial_statements))