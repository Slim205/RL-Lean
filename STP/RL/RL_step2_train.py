import os
import gc
import ray
import json
import pickle
import random
import string
import logging
import argparse
import wandb
import numpy as np
from collections import defaultdict
from tqdm.auto import tqdm
from datetime import datetime
from copy import deepcopy
from typing import Any, Dict, List, Tuple, Optional

from utils.model_utils import START_THM, START_LEMMA_STMT, END_THM, INVOKED_LEMMA, PROVER_PROMPT
from utils.RL_utils import update_succ_lemmas, REPO_DIR, train_model, BATCH_SIZE
from utils.gcloud_utils import read_file, write_data, execute_on_all_workers, path_exists

def compute_weight(proof, verify_time = 0):
    return np.exp(-0.001 * len(proof) - 0.01 * verify_time)
    # return np.exp(-0.001 * len(proof))

def format_data(header, statement, proof):
    if header is not None:
        prompt = 'Complete the following Lean 4 code:\n\n```lean4\n' + header + statement.strip()
    else:
        prompt = f'{PROVER_PROMPT}\n{statement.strip()}'
    target = proof
    return (prompt, target)

def format_and_deduplicate_dataset(valid_proofs, replay_buffer, generated_proofs):
    correct_proof_count = {}
    for test_info in generated_proofs:
        if test_info.get('complete', False):
            key = test_info['statement']
            correct_proof_count[key] = correct_proof_count.get(key, 0) + 1
    known_examples = set((test_info['prompt'], test_info['target']) for test_info in replay_buffer)
    dataset = []
    for test_info in valid_proofs:
        prompt, target = format_data(test_info.get('header', None), test_info['statement'], test_info['proof'])
        weight = compute_weight(test_info['proof'], test_info.get('verify_time', 0))
        weight = weight / np.sum(correct_proof_count[test_info['statement']])

        if (prompt, target) not in known_examples:
            known_examples.add((prompt, target))
            dataset.append({'prompt': prompt, 'target': target, 'weight': weight})
    return dataset

def format_and_deduplicate_conjecture(dataset, replay_buffer):
    avaliable_lemmas = read_file(os.path.join(REPO_DIR, 'assets/data/theorem_dict.pkl'))
    avaliable_lemmas = {k: v[1].split(':=')[0].strip() for k, v in avaliable_lemmas.items()}
    avaliable_lemmas[''] = 'theorem true: True'

    known_examples = set((test_info['prompt'], test_info['target']) for test_info in replay_buffer)
    ret = []
    if any('weight' not in test_info for test_info in dataset):
        logging.warning('Weights not found in conjecture dataset!!')
        
    for test_info in dataset:
        shared_lemma, easy_proof, easy_theorem, hard_theorem = \
            test_info['shared_lemma'], test_info['easy_proof'], test_info['easy_statement'], test_info['statement']
        shared_lemma_statement = avaliable_lemmas[shared_lemma]

        prompt = f'{PROVER_PROMPT}\n' \
            f'{INVOKED_LEMMA}\n{shared_lemma_statement.strip()}\n{START_LEMMA_STMT}\n' \
            f'{(easy_theorem + easy_proof).strip()}\n{START_THM}'
        target = f'\n{hard_theorem.strip()}\n{END_THM}'
        if (prompt, target) not in known_examples:
            known_examples.add((prompt, target))
            ret.append({'prompt': prompt, 'target': target, 'weight': test_info.get('weight', 1)})

    print(f'Conjecture dataset: ', len(ret))
    return ret

def get_average_unique_proofs(generated_proofs):
    proof_dict = defaultdict(list)
    for test_info in generated_proofs:
        proof_dict[test_info['lemma_id']].append(test_info['proof'])
    sum_unique_proofs = 0
    for lemma_id, proofs in proof_dict.items():
        unique_proofs = len(set(proofs))
        sum_unique_proofs += unique_proofs
    return sum_unique_proofs / len(proof_dict)

def get_unique_invokes_in_proofs(valid_proofs):
    invokes = set()
    for test_info in valid_proofs:
        invokes |= set(test_info['invokes'])
    return len(invokes)

if __name__ == "__main__": 
    logging.basicConfig(format='[%(asctime)s - %(name)s - %(levelname)s] %(message)s', level=logging.DEBUG, force=True)

    parser = argparse.ArgumentParser()
    parser.add_argument("--lr", type=float, default=1e-4)
    parser.add_argument("--seed", type=int, default=2333)
    parser.add_argument("--epoch", type=int, default=2)
    parser.add_argument("--exp_dir", type=str, default=None)
    parser.add_argument("--base_model", type=str, default=None)
    parser.add_argument("--tokenizer_path", type=str, default="deepseek-ai/DeepSeek-Prover-V1.5-SFT")
    parser.add_argument("--sft_dataset", type=str, default=None, help="SFT dataset in the training format")
    parser.add_argument("--save_dir", type=str, default=None)
    args = parser.parse_args()
    if args.save_dir is None:
        args.save_dir = args.exp_dir
    print(args)
    rng = np.random.default_rng(args.seed)
    round = int(args.exp_dir.rsplit('/', 1)[-1][len('round'):])

    if path_exists(os.path.join(args.exp_dir, 'RL_model')) and (args.save_dir == args.exp_dir):
        logging.warning(f"Model already trained. Exiting...")
        exit(0)

    train_ds = read_file(args.sft_dataset)
    if train_ds is None:
        logging.warning(f"Dataset {args.sft_dataset} contains no data...")
        train_ds = []
    
    if 'gs://' not in args.exp_dir:
        os.makedirs(args.exp_dir, exist_ok = True)

    generated_proofs = []
    conjecture_examples = []
    lemma_mapping = {}
    succ_lemmas = set()
    generated_proofs = read_file(os.path.join(args.exp_dir, 'generated_proofs.json'))
    conjecture_examples = read_file(os.path.join(args.exp_dir, 'conjecture_examples.json'))
    assert generated_proofs is not None, f"Failed to read {os.path.join(args.exp_dir, 'generated_proofs.json')}"
    assert conjecture_examples is not None, f"Failed to read {os.path.join(args.exp_dir, 'conjecture_examples.json')}"
    logging.info(f'Number of generated_proofs: {len(generated_proofs)}')
    logging.info(f'Number of conjecture_examples: {len(conjecture_examples)}')
    
    update_succ_lemmas(generated_proofs, succ_lemmas)

    all_test_results = defaultdict(list)
    for test_info in generated_proofs:
        key = test_info['statement']
        for _ in range(test_info.get('multiplicity', 1)):
            all_test_results[key].append(test_info.get('complete', False))
    logging.info(f'Number of unique theorems: {len(all_test_results)}')
    
    valid_proofs = [test_info for test_info in reversed(generated_proofs) if test_info.get('complete', False)]
    # filter out proofs with too high success rate
    valid_proofs = [test_info for test_info in valid_proofs if np.mean(all_test_results[test_info['statement']]) <= 0.5]
    new_ds = format_and_deduplicate_dataset(valid_proofs, train_ds, generated_proofs)
    if len(new_ds) == 0:
        logging.error(f'[Erorr] No new data generated. Exiting...')
        exit(1)
    logging.info(f'Number of new data: {len(new_ds)}')
    train_ds += new_ds

    new_ds_conjecture = format_and_deduplicate_conjecture(conjecture_examples, train_ds)
    logging.info(f'Number of new easy to hard examples: {len(new_ds_conjecture)}')
    train_ds += new_ds_conjecture

    execute_on_all_workers("echo 'connection succ'", expect_succ=True) # health check
    wandb_id = ''.join(random.choices(string.ascii_lowercase, k=10))
    wandb_project = "STP_deepseek"
    wandb_run_name = '-'.join(args.exp_dir.split('/')[-2:])
    wandb.init(project=wandb_project, name=wandb_run_name, id=wandb_id, resume="allow")
    logging.info(f'Training dataset size = {len(train_ds)}')

    def compute_metric(data, key):
        return {
            f"{key}/nr_examples_proof": sum(START_THM not in example['prompt'] for example in data),
            f"{key}/nr_examples_conjecture": sum(START_THM in example['prompt'] for example in data),
            f"{key}/average length": sum([len(data['target']) for data in data]) / len(data) if len(data) > 0 else 0,
        }

    metrics = {}
    metrics |= compute_metric(train_ds, 'combined')
    metrics |= compute_metric(new_ds + new_ds_conjecture, 'RL_new')
    
    nr_unique_statements = len(set(test_info['statement'].split(':', 1)[-1] for test_info in generated_proofs))
    nr_statements = len(set(test_info['statement'] for test_info in generated_proofs))

    metrics |= {
        'monitoring/unique_statement_ratio': nr_unique_statements / nr_statements,
        'monitoring/average_unique_proofs': get_average_unique_proofs([test_info for test_info in generated_proofs if test_info.get('round', 0) == round]),
        'monitoring/unique_invokes_in_Pprime': len(set(test_info['shared_lemma'] for test_info in conjecture_examples)),
        'monitoring/unique_invokes_in_proofs': get_unique_invokes_in_proofs(valid_proofs),
    }
    wandb.log(metrics)
    logging.info(str(metrics))
    wandb.finish(quiet=True)

    # save trajectories
    rng.shuffle(train_ds)
    write_data(json.dumps(train_ds), os.path.join(args.save_dir, 'train_ds.json'), 'json', no_compression=True)
    
    start_time = datetime.now()
    # train the actor
    max_iters = max(len(train_ds) * args.epoch // BATCH_SIZE, 5)
    logging.info('max_iters: '+ str(len(train_ds) * args.epoch // BATCH_SIZE))
    logging.info('len train_ds: '+ str(len(train_ds)))

    train_model(os.path.join(args.save_dir, 'RL_model'), args.base_model, max_iters, os.path.join(args.save_dir, 'train_ds.json'), 
                    args, wandb_project, wandb_id)
    duration = datetime.now() - start_time
    logging.info('Training time: ' + str(duration))