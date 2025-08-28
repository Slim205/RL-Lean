import numpy as np
from datasets import DatasetDict,load_dataset

ds = load_dataset("Slim205/mathlib_RL_v3_length")


def exp_length(sample) : 
    sample['complexity_score'] = np.exp(sample['num_lines'])
    return sample

ds_new = ds.map(exp_length)

ds_train = ds_new['train']

values = ds_train['complexity_score']

percentile_33 = np.percentile(values, 33)
percentile_67 = np.percentile(values, 67)

def diff_level(sample) : 
    if sample['complexity_score'] < percentile_33 : 
        level = 0
    elif sample['complexity_score'] < percentile_67 : 
        level = 1
    else : 
        level = 2
    sample['diff_level'] = level
    return sample

ds_new2 = ds_new.map(diff_level)

list_files = list(set([ sample['file_name'] for sample in ds['train'] ]))
diff_file = { x : [] for x in list_files}
list_filestest = list(set([ sample['file_name'] for sample in ds['test'] ]))
for x in list_filestest : 
    diff_file[x] = []


for x in ds_new2['train'] :
    diff_file[x['file_name']].append(x['diff_level'])
for x in ds_new2['test'] :
    diff_file[x['file_name']].append(x['diff_level'])

scores_ds = {x : np.mean(y) for x,y in diff_file.items()}

sorted_keys = sorted(scores_ds, key=scores_ds.get)
rank_dict = { sorted_keys[i] : i for i in range(len(sorted_keys))}
def pedict_level(sample) : 

    sample['file_diff_level'] = np.mean(diff_file[sample['file_name']])
    sample['theorem_same_file'] = len(diff_file[sample['file_name']])
    sample['rank_file'] = rank_dict[sample['file_name']]

    return sample

ds_new3 = ds_new2.map(pedict_level)

ds_final = DatasetDict()

ds_final['train'] = ds_new3['train'].sort(['rank_file' ,'start'])
ds_final['test'] = ds_new3['test']

print(ds_final)

ds_final.push_to_hub('Slim205/mathlib_RL_exp_length')