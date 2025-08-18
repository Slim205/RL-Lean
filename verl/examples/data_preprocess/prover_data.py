import os
import json

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []

def get_dataset() : 
    path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V16.json'
    initial_statements1 =load_statements(path)
    total_list = [x['new'] for x in initial_statements1]

    print(len(total_list))

    thm_list = []
    for i in range(len(total_list)) : 
        LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
        thm = LEAN4_DEFAULT_HEADER + f'theorem lean_conjecture_{i} ' + total_list[i]
        thm_list.append({ 'theorem' :thm})

    print(thm_list[0])

    from datasets import Dataset
    ds = Dataset.from_list(thm_list).shuffle(42)
    print(ds)
    return ds
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

def get_prompt_test(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
                header= data['header'],
                informal_prefix=data['informal_prefix'],
                formal_statement=data['formal_statement'],
            )
    return text

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--local_dir", default="~/data/leanworkbook_V42")
    parser.add_argument("--hdfs_dir", default=None)

    args = parser.parse_args()

    train_dataset = get_dataset()
    data_source = "lean_workbook" 

    test_dataset = datasets.load_dataset('Slim205/minif2f',split='valid')

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
