import numpy as np
import json
from datasets import load_dataset, Dataset, DatasetDict
import os
from tqdm import tqdm
import traceback

path = 'Slim205/lean_workbook_RL_V20'
ds = load_dataset(path,split='train')
# def filter2(s) : 
#     s['num_goals'] = len(s['goals'])
#     return s
# ds1 =ds.map(filter2).remove_columns(['processed_goals'])
# ds1.push_to_hub('Slim205/lean_workbook_RL_V8_goals_V1')

def fo(x) : 
    return 'Int.floor (Real.sqrt 2021)' in x['theorem']
print(ds.filter(fo)[0])