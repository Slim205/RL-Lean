import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback

csv_path0 = '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/leanworkbook_hard/V9_200-32/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])
  

dataset = load_dataset("Slim205/lean_workbook_RL_V20", split='train')#.select(range(12000))
new_data = []
for sample in dataset:
    # if sample['eval_complexity'] > 0 :
    #     sample['after_RL'] = 2
    #     new_data.append(sample)
   # else : 
    if sample['problem_id'] in data0.keys() : 
        sample['after_RL'] = data0[sample['problem_id']] / 32
        if sample['after_RL'] == 0 : 
            new_data.append(sample)
            
combined_ds = Dataset.from_list(new_data)

combined_ds.push_to_hub('Slim205/lean_workbook_hard')