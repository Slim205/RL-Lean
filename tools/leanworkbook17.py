import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback

path = 'Slim205/lean_workbook_RL_V20_total'
ds = load_dataset(path,split='train')
def filter2(s) : 
    return  s['eval_complexity'] ==  0.0 

ds1 =ds.filter(filter2)
print(ds1)
# s=0
# new_dataset = []
# for sample in ds : 
#     if sample['eval_complexity'] == 0 and s < 2000 : 
#         s+=1
#         new_dataset.append(sample)
#     elif  sample['eval_complexity'] > 0: 
#         new_dataset.append(sample)
# ds1 = Dataset.from_list(new_dataset)
ds1.push_to_hub('Slim205/lean_workbook_RL_V20_hard')