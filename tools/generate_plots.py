import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback
import csv

csv_path0 = '../Goedel-Prover/results/minif2f/deepseek-SFT/compilation_summarize.csv'

data0 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data0[row["name"]] = int(row["correct"])


csv_path0 = '../Goedel-Prover/results/minif2f/leanworkbook_V9_200-32/compilation_summarize.csv'

data1 = {}
with open(csv_path0, newline="") as f:
    reader = csv.DictReader(f, delimiter="\t")  # your sample shows tab-separated values
    for row in reader:
        data1[row["name"]] = int(row["correct"])

import matplotlib.pyplot as plt

# Plot success rate before RL
plt.hist(data0.values())
plt.title('Success Rate Before RL')
plt.xlabel('Success Rate')
plt.ylabel('Frequency')
plt.savefig('success_rate_before_rl.png')  # Save to file
plt.close()  # Close the figure to avoid overlap

# Plot success rate after RL
plt.hist(data1.values())
plt.title('Success Rate After RL')
plt.xlabel('Success Rate')
plt.ylabel('Frequency')
plt.savefig('success_rate_after_rl.png')  # Save to file
plt.close()
