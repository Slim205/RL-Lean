import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback

csv_path0 = '../Goedel-Prover/results/leanworkbook_hinter_v2/SFT-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

dataset = load_dataset("Slim205/lean_workbook_RL_V14_pass4", split='train')#.select(range(12000))
inputs = []
list_inputs=[]
p = 0
dict_complexity={}
thm_hinter = {}
for sample in dataset:
    theorem_name = sample['problem_id'] + str(p)
    p+=1

    if theorem_name in data0.keys() : 
        if data0[theorem_name] > 0 and data0[theorem_name] < 17 and sample['theorem'] not in list_inputs : 
            if sample['problem_id']  not in dict_complexity.keys() : 
                dict_complexity[sample['problem_id'] ] = []
            sample['new_complexity'] = data0[theorem_name] / 32
       #     if dict_complexity[sample['problem_id']].count(sample['new_complexity']) < 4:
            inputs.append(sample)
            list_inputs.append(sample['theorem'] )
            dict_complexity[sample['problem_id'] ].append(sample['new_complexity'])

def closest_to_point_one(numbers):
    return min(numbers, key=lambda x: abs(x - 0.1))

dataset1 = Dataset.from_list(inputs)

for sample in dataset1 : 
    if sample['new_complexity'] == closest_to_point_one(dict_complexity[sample['problem_id'] ]) :
        #sample['complexity_list'] =  dict_complexity[sample['problem_id'] ]
        thm_hinter[sample['problem_id']] = sample
print(len(thm_hinter))
#print(dataset1)
#dataset1.push_to_hub('Slim205/leanworkbook_hinter_v14_v5')
#ds2 = dataset1.shuffle(seed=42)#.select(range(3551))

ds = load_dataset("Slim205/lean_workbook_RL_V8_hinter",split='train').select(range(12000)).remove_columns('processed_goals')

new_data = []
x=0
for sample in ds:
    if sample['problem_id'] in thm_hinter.keys() : 
        new_data.append(thm_hinter[sample['problem_id'] ])
    else : 
        if sample['eval_complexity'] == 0 and len(sample['old_theorem']) > 0:
            sample['new_complexity'] = 0.0
            sample['theorem'] = sample['old_theorem']
            sample['old_theorem'] = ''
        
        else : 
            sample['new_complexity'] = 2.0
       # sample['complexity_list'] = [0.0][1:]
        new_data.append(sample)

print(len(ds))
print(len(new_data))
   
            
combined_ds = Dataset.from_list(new_data)

combined_ds.push_to_hub('Slim205/lean_workbook_RL_V14_hinter_v6')