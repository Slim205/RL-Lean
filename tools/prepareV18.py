import numpy as np
from datasets import DatasetDict,load_dataset
from collections import Counter

# Load your dataset
ds = load_dataset("Slim205/mathlib_RL_v3_traced2")["train"]

def f(sample) : 
    new_goals = []
    for x in sample['goals'] : 
        if x not in sample['goals_before'] : 
            new_goals.append(x)
    sample['new_goals'] = new_goals
    return sample
ds1 = ds.map(f)

def filter1(x) : 
    return len(x['goals']) > 0 

def filter2(x) : 
    return len(x['goals_before']) > 0 
def filter3(x) : 
    return len(x['new_goals']) > 0 

# print(ds1.filter(filter1))

# print(ds1.filter(filter2))

# print(ds1.filter(filter3))

ds4 = ds1.filter(filter1)
print(ds4.filter(filter2))
print(ds4)

# dataset_test = load_dataset("Slim205/mathlib_RL_v3", split='test')

# def xx1(x) : 
#     x['goals'] = []
#     x['goals_before'] = []
#     x['new_goals'] = []
#     return x 

# dataset_test = dataset_test.map(xx1)

# feature_spec = ds4.features
# dataset_test = dataset_test.cast(feature_spec)        # <- the critical line!

# print(ds4)
# print(dataset_test)

# ds2 = DatasetDict({'train'  : ds4 , 'test' : dataset_test })
# print(ds2)

# ds2.push_to_hub('Slim205/mathlib_RL_v3_goals')
