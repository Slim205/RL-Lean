import argparse
import os
import re

import datasets

from verl.utils.hdfs_io import copy, makedirs

def get_prompt(example) : 
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
                header=example['Context'],
                formal_statement=example["theorem"],
            )
    return text
# def get_prompt_new(example) : 
#     if example['iteration'] == 0 : 
#         line1 = example['proof'].split('\n')[0]
#         if line1 == '' : 
#             line1 = '\n' + example['proof'].split('\n')[1]
#         if len(example['proof'].split('\n')) <= 3 : 
#             line1 = ''
#     else :
#         line1 = ''
#     text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
#                 header=example['Context'],
#                 formal_statement=example["theorem"] + line1,
#     )
#     return text


def get_prompt_test(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
                header= data['header'],
                informal_prefix=data['informal_prefix'],
                formal_statement=data['formal_statement'],
            )
    return text

def get_prompt_workbook(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
                header= 'import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n',
                formal_statement=data['formal_statement'].split('sorry')[0].strip(),
            )
    return text

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--local_dir", default="~/data/mathlib_V22")
    parser.add_argument("--hdfs_dir", default=None)

    args = parser.parse_args()

    data_source = "Slim205/lean_workbook_RL"

    dataset = datasets.load_dataset(data_source)
    train_dataset = dataset["train"].select(range(88320))
    print(train_dataset)
    test_dataset = dataset["train"].select(range(88320,89221))
   # test_dataset = datasets.load_dataset('Slim205/minif2f',split='valid')
    print(test_dataset)
    data_source = "lean_workbook"

    # add a row to each data item that represents a unique id
    def make_map_fn(split):
        def process_fn(example, idx):
            question = get_prompt_workbook(example)
            data = {
                "data_source": data_source,
                "prompt": question,
                "ability": "lean",
                "extra_info": {
                    "split": split,
                    "index": idx,
                    # 'goals_before' : example['goals_before'],
                    # 'new_goals' : example['new_goals'],
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
                    # 'goals_before' : example['goals_before'],
                    # 'new_goals' : example['new_goals'],
                },
            }
            return data
        if split == 'train' : 
            return process_fn
        if split == 'test' : 
            return  process_fn
    train_dataset = train_dataset.map(function=make_map_fn("train"), with_indices=True)
    test_dataset = test_dataset.map(function=make_map_fn("test"), with_indices=True)

    local_dir = args.local_dir
    hdfs_dir = args.hdfs_dir

    train_dataset.to_parquet(os.path.join(local_dir, "train.parquet"))
    test_dataset.to_parquet(os.path.join(local_dir, "test.parquet"))

    if hdfs_dir is not None:
        makedirs(hdfs_dir)

        copy(src=local_dir, dst=hdfs_dir)
