import argparse
import os
import re

import datasets

from verl.utils.hdfs_io import copy, makedirs


def get_prompt(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=data['input'],
            )
    return text

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--local_dir", default="~/data/leanworkbook_V3")
    parser.add_argument("--hdfs_dir", default=None)

    args = parser.parse_args()

    data_source = "Slim205/lean_workbook_RL_full_v1"

    dataset = datasets.load_dataset(data_source)
    train_dataset = dataset["train"].select(range(20000))
    print(train_dataset)
  #  test_dataset = dataset["train"].select(range(10240,11745))
    test_dataset = dataset["test"]

    print(test_dataset)
    data_source = "lean_workbook"

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
        return process_fn
        
    train_dataset = train_dataset.map(function=make_map_fn("train"), with_indices=True)
    test_dataset = test_dataset.map(function=make_map_fn("test"), with_indices=True)

    local_dir = args.local_dir
    hdfs_dir = args.hdfs_dir

    train_dataset.to_parquet(os.path.join(local_dir, "train.parquet"))
    test_dataset.to_parquet(os.path.join(local_dir, "test.parquet"))

    if hdfs_dir is not None:
        makedirs(hdfs_dir)

        copy(src=local_dir, dst=hdfs_dir)
