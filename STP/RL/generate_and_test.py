import os
import ray
import json
import argparse
import logging
import numpy as np
from ray.util import ActorPool
from transformers import AutoTokenizer
from utils.gcloud_utils import read_file, write_data
from utils.model_utils import insert_lemma, init_ray_cluster, create_inference_actors
from utils.gcloud_utils import read_file
from utils.RL_utils import generate_and_test, collect_trajectories
from copy import deepcopy

MAX_LENGTH = 1024

def main(args: argparse.Namespace):
    args.save_file_path = os.path.join(args.exp_dir, f'generated_proofs_{args.save_file_name}.jsonl')
    print(args)
    #os.system(f'rm -r /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results')
    
    tokenizer = AutoTokenizer.from_pretrained(args.tokenizer_path)
    tokenizer.truncation_side = 'left'
    tokenizer.pad_token = tokenizer.eos_token

    if 'gs://' not in args.exp_dir:
        os.makedirs(args.exp_dir, exist_ok = True)

    lemmas_to_generate = []
    lemma_mapping = {}

    idx = 0
    dataset_configs = read_file(args.raw_dataset_config) #split the data_path
    print(dataset_configs)

    for dataset_config in dataset_configs:
        logging.debug(f'Processing dataset: {dataset_config["dataset_path"]}')
        REPO_DIR = "/n/netscratch/amin_lab/Lab/slim/STP/"
        raw_dataset = read_file(os.path.join(REPO_DIR, dataset_config['dataset_path']))
        nr_samples = dataset_config['weight']
        assert (raw_dataset is not None), f"Failed to read {dataset_config['dataset_path']}"
        logging.debug(f'Size of the dataset: {len(raw_dataset)}')
        
        formatted_ds = []
        for raw in raw_dataset:
            test_info = {'lemma_id': idx,
                        'statement': raw['formal_statement'].rsplit('sorry', 1)[0].strip(),
                        'label': [raw['split']] + (raw.get('tags', None) or []),
                        'header': raw.get('header', None),}
            idx += 1
            formatted_ds.append(test_info)

        for it in range(nr_samples):
            lemmas_to_generate += [test_info | {'iter': it} for test_info in deepcopy(formatted_ds)]
        
        for test_info in formatted_ds:
            insert_lemma(lemma_mapping, test_info) ## lemma_mapping : from statement to indx
    cache_dir = os.path.join(args.exp_dir, 'sampler_ckpt')

    init_ray_cluster(default=False)
    ray_inference_actors, model_dir = create_inference_actors(args.model, args.tokenizer_path,enable_prefix_caching=False)
    
    rng = np.random.default_rng(0)
    rng.shuffle(lemmas_to_generate)
    collect_traj = lambda inference_pool, nr_actors, selected_lemmas, lemma_mapping, seed: \
        collect_trajectories(inference_pool, nr_actors, selected_lemmas, \
                                           MAX_LENGTH, seed, args.temperature, cache_dir=os.path.join(args.exp_dir, 'sampler_ckpt'))

    generated_proofs = generate_and_test(lemmas_to_generate, collect_traj, ray_inference_actors, lemma_mapping, args.seed, os.path.join(args.exp_dir, 'sampler_ckpt'), 
                                         cpus_per_task=4, cpus_per_task_stage2=6, group_by_header=True, collect_premises=False)
    
    write_data('\n'.join([json.dumps(t) for t in generated_proofs]), args.save_file_path, 'jsonl')

if __name__ == "__main__":
    logging.basicConfig(format='[%(asctime)s - %(name)s - %(levelname)s] %(message)s', level=logging.DEBUG)
    parser = argparse.ArgumentParser(
        description="Generate and test proofs."
    )
    parser.add_argument("--model", type=str, default=None)
    parser.add_argument("--tokenizer_path", type=str, default='deepseek-ai/DeepSeek-Prover-V1.5-SFT')
    parser.add_argument("--exp_dir", type=str, default=None)
    parser.add_argument("--nr_samples", type=int, default=16)
    parser.add_argument("--save_file_name", type=str, default=None)
    parser.add_argument("--raw_dataset_config", type=str, default=None)
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--seed", type=int, default=0)

    parsed_args = parser.parse_args()
    parsed_args.tokenizer_path = parsed_args.model
    main(parsed_args)
