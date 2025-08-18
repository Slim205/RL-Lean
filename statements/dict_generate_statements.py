import pandas as pd
import os
import json


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
    if len(statements_dict) == 0 : 
        return 0
    return statements_dict[-1]['step']

n = 28

path = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{n}.json'

initial_statements = []
save_statements(initial_statements,path)
print(len(load_statements(path)))
print(get_step(initial_statements))
path = f'/n/netscratch/amin_lab/Lab/slim/statements/test_V{n}.json'
initial_statements = []
save_statements(initial_statements,path)
print(len(load_statements(path)))
print(path)
print(get_step(initial_statements))