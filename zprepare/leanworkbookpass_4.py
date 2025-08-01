import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm

dataset = load_dataset("Slim205/lean_workbook_RL_V14", split='train')


csv_path0 = '../Goedel-Prover/results/leanworkbook_hinter_v2/SFT-4/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t") 
    for row in reader:
        data0[row["name"]] = int(row["correct"])


inputs = []
p = 0
for sample in dataset:
    if sample['pass']  : 
        theorem_name = sample['problem_id'] + str(p) 
        if theorem_name in data0.keys() : 
            if data0[theorem_name] < 3  : 
                inputs.append(sample)     
        p+=1

dataset1 = Dataset.from_list(inputs).remove_columns(["processed_goals",'pass'])

print(dataset1)
dataset1.push_to_hub('Slim205/lean_workbook_RL_V14_pass4')
