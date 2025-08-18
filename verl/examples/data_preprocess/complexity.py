import argparse
import os
import re

import datasets

from verl.utils.hdfs_io import copy, makedirs


def get_prompt(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=data['theorem'],
            )
    return text
# def change_input(lean_code):
#     l = []
#     for p in range(len(lean_code)) : 
#         if lean_code[p] == ':' :
#             l.append(p)
#     i = l[-2]
#     return  lean_code[:i+1]

# def get_prompt_new(data) :

#     if data['eval_complexity'] > 0.5 : 
#         thoerem = change_input(data['theorem'])
#     else : 
#         thoerem = data['theorem']
#     text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
#                 formal_statement=thoerem,
#             )
#     return text

# def get_prompt_minif2f(example) :
#     theorem = 'import miniF2F\nimport Aesop\n' + 'set_option maxRecDepth 100000'+  example['theorem'].split('Aesop')[1] 

#     text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
#                 formal_statement=theorem,
#             )
#     return text 

def get_prompt_test(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
                header= data['header'],
                informal_prefix=data['informal_prefix'],
                formal_statement=data['formal_statement'],
            )
    return text

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--local_dir", default="~/data/leanworkbook_V43")
    parser.add_argument("--hdfs_dir", default=None)

    args = parser.parse_args()

    dataset = datasets.load_dataset("Slim205/lean_workbook_RL_V20")
    data_source = "lean_workbook" # minif2f

    train_dataset = dataset["train"]#.select(range(12000))
    print(train_dataset)
    test_dataset = datasets.load_dataset('Slim205/minif2f',split='test')

    print(test_dataset)

    # add a row to each data item that represents a unique id
    def make_map_fn(split):
        def process_fn(example, idx):
            question = get_prompt(example)
            data = {
                "data_source": data_source,
                "prompt": question,
                "ability": "lean",
                "extra_info": {
                    "split": split,
                    "index": idx,
                },
            }
            return data
        def process_fn_test(example, idx):
            question = get_prompt_test(example)
            data = {
                "data_source": data_source,
                "prompt": question,
                "ability": "lean",
                "extra_info": {
                    "split": split,
                    "index": idx,
                },
            }
            return data
        if split == 'train' : 
            return process_fn
        return process_fn_test
    train_dataset = train_dataset.map(function=make_map_fn("train"), with_indices=True)
    test_dataset = test_dataset.map(function=make_map_fn("test"), with_indices=True)
    p = 0
    for x in train_dataset : 
        print(x['prompt'])
        break

    local_dir = args.local_dir
    hdfs_dir = args.hdfs_dir

    train_dataset.to_parquet(os.path.join(local_dir, "train.parquet"))
    test_dataset.to_parquet(os.path.join(local_dir, "test.parquet"))

    if hdfs_dir is not None:
        makedirs(hdfs_dir)

        copy(src=local_dir, dst=hdfs_dir)
