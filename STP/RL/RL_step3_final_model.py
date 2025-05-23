import os
import gc
import ray
import json
import pickle
import random
import string
import hashlib
import logging
import argparse
import wandb
import numpy as np
from collections import defaultdict
from tqdm.auto import tqdm
from datetime import datetime
from copy import deepcopy
from typing import Any, Dict, List, Tuple, Optional
from multiprocessing import Pool
from ray.util import ActorPool

from utils.model_utils import init_ray_cluster
from utils.model_utils import START_THM, PROVER_PROMPT
from utils.gcloud_utils import read_file, write_data, execute_on_all_workers, path_exists
from utils.RL_utils import train_model, BATCH_SIZE, load_ds_from_config

def compute_weight(proof):
    return np.exp(-0.001 * len(proof))

def format_data(header, statement, proof):
    if header is not None:
        prompt = 'Complete the following Lean 4 code:\n\n```lean4\n' + header + statement.strip()
    else:
        prompt = f'{PROVER_PROMPT}\n{statement.strip()}'
    target = proof
    return (prompt, target)

def format_and_deduplicate_dataset(valid_proofs, replay_buffer):
    known_examples = set((test_info['prompt'], test_info['target']) for test_info in replay_buffer)
    dataset = []
    for test_info in valid_proofs:
        prompt, target = format_data(test_info.get('header', None), test_info['statement'], test_info['proof'])
        weight = compute_weight(test_info['proof'])

        if (prompt, target) not in known_examples:
            known_examples.add((prompt, target))
            dataset.append({'prompt': prompt, 'target': target, 'weight': weight})
    return dataset

def cleanup_info(test_info):
    return {k: v for k, v in test_info.items() if k in ['statement', 'proof', 'complete', 'multiplicity']}

@ray.remote
class Merge_Worker:
    def __init__(self, dataset_config_path):
        formatted_ds = load_ds_from_config(dataset_config_path)
        self.training_examples = set(test_info['statement'] for test_info in formatted_ds)

    def process_round(self, exp, i, args):
        # Check if any of the possible files exist
        if path_exists(f'{exp}/round{i}/sampler_ckpt/generated_proofs.json.gz'):
            logging.info(f"Reading {exp}/round{i}")

            generated_proofs_this_round = read_file(f'{exp}/round{i}/sampler_ckpt/generated_proofs.json.gz')

            assert generated_proofs_this_round is not None, f'{exp}/round{i}/sampler_ckpt/generated_proofs.json.gz'

            if args.include_synthetic_examples:
                all_test_results = defaultdict(list)
                # Build a dictionary of (context, statement) -> list of True/False indicating success/failure
                for test_info in generated_proofs_this_round:
                    key = test_info['statement']
                    for _ in range(test_info.get('multiplicity', 1)):
                        all_test_results[key].append(test_info.get('complete', False))

                valid_proofs = [test_info for test_info in reversed(generated_proofs_this_round) if test_info.get('complete', False)]

                # Filter out proofs that have >0.25 success rate unless they are in training_examples
                filtered_lemmas = [
                    test_info for test_info in valid_proofs
                    if (np.mean(all_test_results[test_info['statement']]) <= 0.25) 
                    or (test_info['statement'] in self.training_examples)
                ]
                return [cleanup_info(test_info) for test_info in filtered_lemmas]
            else:
                # If not including synthetic examples, filter directly
                filtered_lemmas = [
                    test_info for test_info in generated_proofs_this_round
                    if test_info.get('complete', False) and (test_info['statement'] in self.training_examples)
                ]
                return [cleanup_info(test_info) for test_info in filtered_lemmas]

        # If no file existed or no lemmas found, return empty list
        return []

def execute_process_rounds(dataset_config_path, tasks) -> List:
    # Initialize Ray
    if not ray.is_initialized():
        ray.init()

    # Get the list of current nodes in the cluster
    nodes = ray.nodes()
    num_nodes = len(nodes)
    if num_nodes == 0:
        raise RuntimeError("No Ray nodes available in the cluster.")

    ray_workers = []
    for i, node in enumerate(ray.nodes()):
        ip = node['NodeManagerAddress']

        worker = Merge_Worker.options(
            resources={f"node:{ip}": 0.1},
            num_cpus=1,
        ).remote(dataset_config_path)
        ray_workers.append(worker)

    pool = ActorPool(ray_workers)
    results = pool.map_unordered(lambda actor, task: 
                            actor.process_round.remote(*task),
                       tasks)

    # Merge all lists into a single list
    merged_result = []
    for sublist in results:
        merged_result.extend(sublist)

    # Shutdown the ray workers
    ray.shutdown()
    return merged_result

if __name__ == "__main__":
    logging.basicConfig(format='[%(asctime)s - %(name)s - %(levelname)s] %(message)s', level=logging.DEBUG, force=True)

    parser = argparse.ArgumentParser()
    parser.add_argument("--lr", type=float, default=1.6e-4)
    parser.add_argument("--seed", type=int, default=2333)
    parser.add_argument("--epoch", type=int, default=2)
    parser.add_argument("--exp_dir", type=str, default=None)
    parser.add_argument("--base_model", type=str, default=None)
    parser.add_argument("--dataset_config", type=str, default=None)
    parser.add_argument("--tokenizer_path", type=str, default="deepseek-ai/DeepSeek-Prover-V1.5-SFT")
    parser.add_argument("--sft_dataset", type=str, default=None, help="SFT dataset in the training format")
    parser.add_argument("--save_dir", type=str, default=None)
    parser.add_argument("--include_synthetic_examples", action='store_true')
    parser.add_argument("--merge_from", default=[], nargs='+')
    parser.add_argument("--merge_from_rounds", default=[], nargs='+')
    args = parser.parse_args()
    if args.save_dir is None:
        args.save_dir = args.exp_dir
    print(args)
    rng = np.random.default_rng(args.seed)

    if path_exists(os.path.join(args.exp_dir, 'RL_model')) and (args.save_dir == args.exp_dir):
        logging.warning(f"Model already trained. Exiting...")
        exit(0)

    init_ray_cluster()
    train_ds = read_file(args.sft_dataset)
    if train_ds is None:
        logging.warning(f"Dataset {args.sft_dataset} contains no data...")
        train_ds = []
    
    if 'gs://' not in args.exp_dir:
        os.makedirs(args.exp_dir, exist_ok = True)

    tasks = []
    # Prepare tasks
    for exp, nr_rounds in zip(args.merge_from, args.merge_from_rounds):
        for i in range(int(nr_rounds)):
            tasks.append((exp, i, args))

    generated_proofs = execute_process_rounds(os.path.abspath(args.dataset_config), tasks)
    logging.info(f'Number of correct proofs: {len(generated_proofs)}')
    
    rng.shuffle(generated_proofs)

    # only keep at most 16 unique proofs, and dedup
    proof_dedup = set()
    proof_count = defaultdict(int)
    train_examples = []
    for test_info in generated_proofs:
        key = test_info['statement']
        dedup_key = (test_info['statement'], test_info['proof'])
        if dedup_key in proof_dedup:
            continue
        proof_dedup.add(dedup_key)
        
        if proof_count[key] < 16:
            proof_count[key] += 1
            train_examples.append(test_info)
    logging.info(f'Number of proofs after deduplication: {len(train_examples)}')

    new_ds = format_and_deduplicate_dataset(train_examples, train_ds)
    if len(new_ds) == 0:
        logging.error(f'[Erorr] No new data generated. Exiting...')
        exit(0)
    logging.info(f'Number of new data: {len(new_ds)}')
    train_ds += new_ds

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
    metrics |= compute_metric(new_ds, 'RL_new')
    wandb.log(metrics)
    logging.info(str(metrics))
    wandb.finish(quiet=True)

    # save trajectories
    rng.shuffle(train_ds)
    write_data(json.dumps(train_ds), os.path.join(args.save_dir, 'train_ds.json'), 'json', no_compression=True)
    
    start_time = datetime.now()
    # train the actor
    max_iters = max(len(train_ds) * args.epoch // BATCH_SIZE, 10)
    train_model(os.path.join(args.save_dir, 'RL_model'), args.base_model, max_iters, os.path.join(args.save_dir, 'train_ds.json'), 
                    args, wandb_project, wandb_id)
    duration = datetime.now() - start_time
    logging.info('Training time: ' + str(duration))