import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback


ds = load_dataset("Slim205/lean_workbook_RL_hinter_V1",split='train').select(range(12000))

csv_path0 = '../Goedel-Prover/results/leanworkbook_train/SFT-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])

thm_list = []
for sample in ds:
    theorem_name = sample['problem_id']
    if theorem_name in data0.keys() : 

        sample['eval_complexity'] = data0[theorem_name] / 32
        if  sample['eval_complexity'] > 0 or len(sample['processed_goals']) < 2 : 
            continue
        else : 
            thm_list.append(sample['problem_id'])
print(len(thm_list)) # 2208

dict_thm = {}
for x in thm_list : 
    dict_thm[x] = []

csv_path0 = '../Goedel-Prover/results/leanworkbook_hinter/SFT-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

dataset = load_dataset("Slim205/lean_workbook_RL_V13_V1", split='train')#.select(range(12000))
inputs = []
inputs_2 = []
p = 0
for sample in dataset:
    theorem_name = sample['problem_id'] + str(p)
    p+=1

    if theorem_name in data0.keys() : 
        dict_thm[sample['problem_id']].append(data0[theorem_name])
        if data0[theorem_name] > 0 : 
            sample['new_complexity'] = data0[theorem_name] / 32
            inputs.append(sample)
            if data0[theorem_name] < 17 : 
                inputs_2.append(sample)

dataset1 = Dataset.from_list(inputs)
dataset2 = Dataset.from_list(inputs_2)

dataset1.push_to_hub('Slim205/leanworkbook_hinter_v2')
dataset2.push_to_hub('Slim205/leanworkbook_hinter_v3')

s=0
for x,y in dict_thm.items() : 
    if len(y) == 0 : 
        s+=1
print(s)

s=0
for x,y in dict_thm.items() : 
    if len(y) > 0 : 

        if min(y) > 0 : 
            s+=1
print(s)

s=0
for x,y in dict_thm.items() : 
    if len(y) > 0 : 

        if min(y) > 0 and  min(y) < 17 : 
            s+=1
print(s)
# 2208
# 381
# 1068
# 502