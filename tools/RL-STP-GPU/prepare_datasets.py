import os
import json
from datasets import load_dataset
from utils.gcloud_utils import read_file, write_data, path_exists
from utils.RL_utils import STORAGE

if __name__ == '__main__':
    sft_train_dataset = load_dataset("kfdong/STP_Lean_SFT", split="train")

    # create SFT dataset
    dataset = [example for example in sft_train_dataset]
    print(f'Number of examples in the SFT dataset: {len(dataset)}')
    write_data(json.dumps(dataset), os.path.join(STORAGE, 'data/SFT/mathlib_leanworkbook.json'), 'json', no_compression=True)
    
    # create mathlib dataset
    dataset = [example for example in sft_train_dataset if 'lean_workbook' not in example['prompt']]
    print(f'Number of examples in the mathlib dataset: {len(dataset)}')
    write_data(json.dumps(dataset), os.path.join(STORAGE, 'data/SFT/mathlib.json'), 'json', no_compression=True)

    # create eval dataset
    sft_eval_dataset = load_dataset("kfdong/STP_Lean_SFT", split="eval")
    dataset = [example for example in sft_eval_dataset]
    print(f'Number of examples in the SFT eval dataset: {len(dataset)}')
    write_data(json.dumps(dataset), os.path.join(STORAGE, 'data/SFT/eval.json'), 'json', no_compression=True)
