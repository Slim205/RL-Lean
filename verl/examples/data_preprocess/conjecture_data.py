import argparse
import os
import re

import datasets

from verl.utils.hdfs_io import copy, makedirs

START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = (
    "Complete the following Lean 4 code:\n\n```lean4\n"
    "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n"
    "open BigOperators Real Nat Topology Rat\n"
)

def get_prompt(sample):
    shared_lemma = ''
    easy_theorem = 'theorem' + sample['theorem'].split('theorem')[1].split(' sorry')[0]
    prompt = (
        f"{PROVER_PROMPT}"
        f"{INVOKED_LEMMA}\n{shared_lemma.strip()}\n"
        f"{START_LEMMA_STMT}\n{easy_theorem.strip()}\n"
        f"{START_THM}\n theorem"
    )
    return prompt

# START_THM   = '<theorem>'
# END_THM     = '</theorem>'
# START_CONJ  = '<conjecture>'
# END_CONJ    = '</conjecture>'


# def get_prompt(sample):
#     theorem = 'theorem' + sample['theorem'].split('theorem')[1].split(' sorry')[0]
#     prompt = f'Complete the following Lean 4 code:\n\n```lean4\n\n' \
#             f'{START_THM}\n' \
#             f'{theorem.strip()}\n' \
#             f'{END_THM}\n' \
#             f'{START_CONJ}\n theorem'

#     return prompt


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--local_dir", default="~/data/conjecture_V4")
    parser.add_argument("--hdfs_dir", default=None)

    args = parser.parse_args()

    dataset = datasets.load_dataset("Slim205/lean_workbook_RL_V20")
    data_source = "conjecture" 

    train_dataset = dataset["train"]
    print(train_dataset)
    test_dataset = dataset['test']
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
                   'theorem' : example['theorem'],
                   'complexity' : example['eval_complexity'] ,
                },
            }
            return data
        return process_fn
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
