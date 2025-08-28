import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback

csv_path0 = '../Goedel-Prover/results/minif2f/deepseek-SFT/compilation_summarize.csv'

import csv


data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])

csv_path0 = '../Goedel-Prover/results/minif2f/deepseek-SFT-2/compilation_summarize.csv'

import csv


data2 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data2[row["name"]] = int(row["correct"])


csv_path0 = '../Goedel-Prover/results/minif2f/leanworkbook_V9_200-32/compilation_summarize.csv'

import csv


data1 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data1[row["name"]] = int(row["correct"])

csv_path0 = '../Goedel-Prover/results/minif2f/leanworkbook_V9_200/compilation_summarize.csv'

import csv


data3 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data3[row["name"]] = int(row["correct"])


dataset = load_dataset("Slim205/minif2f", split='test')#.select(range(12000))
inputs = []
for sample in dataset:
    theorem_name = sample['name'] 
    sample['complexity_1'] = data0[theorem_name] / 32
    sample['complexity_2'] = data1[theorem_name] / 32
    sample['complexity_3'] = data2[theorem_name]
    sample['complexity_4'] = data3[theorem_name]

    inputs.append(sample)
dataset1 = Dataset.from_list(inputs)
print(dataset1)
dataset1.push_to_hub('Slim205/minif2f_complexity')
