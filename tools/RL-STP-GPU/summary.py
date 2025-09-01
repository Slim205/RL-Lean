import re
import os
import sys
import json
import time
import torch
import shutil
import pickle
import numpy as np
from tqdm.auto import tqdm
import random; random.seed(0)  # Set a random seed for reproducibility
import argparse
from collections import defaultdict
from transformers import AutoTokenizer
from utils.gcloud_utils import read_file, write_data
from utils.RL_utils import REPO_DIR

proofnet_inputs = read_file(os.path.join(REPO_DIR, "assets/data/test/proofnet.jsonl"))
miniF2F_inputs = read_file(os.path.join(REPO_DIR, "assets/data/test/miniF2F_lean.json"))
miniF2F_valid_statements = [test_info['formal_statement'].rsplit('sorry', 1)[0].strip() for test_info in miniF2F_inputs if 'valid' in test_info['split']]
miniF2F_test_statements = [test_info['formal_statement'].rsplit('sorry', 1)[0].strip()  for test_info in miniF2F_inputs if 'test' in test_info['split']]
proofnet_valid_statements = [test_info['formal_statement'].rsplit('sorry', 1)[0].strip()  for test_info in proofnet_inputs if 'valid' in test_info['split']]
proofnet_test_statements = [test_info['formal_statement'].rsplit('sorry', 1)[0].strip()  for test_info in proofnet_inputs if 'test' in test_info['split']]

def compute_succ_lemmas(generated_lemmas):
    return set(test_info['lemma_id'] for test_info in generated_lemmas if test_info.get('complete', False))

def compute_succ_rate(all_generated_lemmas, lemma_ids):
    succ_rate = []
    succ_lemmas = set()
    if all_generated_lemmas is None:
        return [-1]
    if sum('test failed' in (test_info.get('system_errors', '') or '') for test_info in all_generated_lemmas) > len(all_generated_lemmas) * 0.01:
        raise ValueError(f'too many failed tests')
    
    generated_lemmas_by_round = defaultdict(list)
    for test_info in all_generated_lemmas:
        generated_lemmas_by_round[test_info['iter']].append(test_info)
        
    for i in range(len(generated_lemmas_by_round)):
        _succ_lemmas = compute_succ_lemmas(generated_lemmas_by_round[i])
        succ_lemmas |= _succ_lemmas
        succ_rate.append(len(succ_lemmas.intersection(set(lemma_ids))) / len(lemma_ids) * 100)
        
    return succ_rate

def load_succ_rate(file_paths, include_proofnet = True, include_miniF2F = True):
    generated_proofs = []
    for file_path in file_paths:
        generated_proofs += read_file(file_path)

    theorem_mapping = {}
    for test_info in generated_proofs:
        key = test_info['statement']
        if key not in theorem_mapping:
            theorem_mapping[key] = len(theorem_mapping)
        test_info['lemma_id'] = theorem_mapping[key]

    splits = {}
    if include_miniF2F:
        splits['miniF2F valid'] = set(theorem_mapping[s] for s in miniF2F_valid_statements)
        splits['miniF2F test'] = set(theorem_mapping[s] for s in miniF2F_test_statements)
        assert len(splits['miniF2F valid']) == len(miniF2F_valid_statements)
        assert len(splits['miniF2F test']) == len(miniF2F_test_statements)

    if include_proofnet:
        splits['proofnet valid'] = set(theorem_mapping[s] for s in proofnet_valid_statements)
        splits['proofnet test'] = set(theorem_mapping[s] for s in proofnet_test_statements)
        assert len(splits['proofnet valid']) == len(proofnet_valid_statements)
        assert len(splits['proofnet test']) == len(proofnet_test_statements)

    ret = {}
    for key, ids in splits.items():
        ret[key] = compute_succ_rate([test_info for test_info in generated_proofs if test_info['lemma_id'] in ids], 
                                     lemma_ids = ids)
        
    return ret

def get_metric(file_path, budgets = [128], split = 'miniF2F', max_iter = 3200):
    generated_proofs = read_file(file_path)
    
    theorem_mapping = {}
    for test_info in generated_proofs:
        key = test_info['statement']
        if key not in theorem_mapping:
            theorem_mapping[key] = len(theorem_mapping)
        test_info['lemma_id'] = theorem_mapping[key]

    splits = {}

    if split == 'miniF2F':
        splits['miniF2F valid'] = set(theorem_mapping[s] for s in miniF2F_valid_statements)
        splits['miniF2F test'] = set(theorem_mapping[s] for s in miniF2F_test_statements)
        assert len(splits['miniF2F valid']) == len(miniF2F_valid_statements)
        assert len(splits['miniF2F test']) == len(miniF2F_test_statements)
    else:
        splits['proofnet valid'] = set(theorem_mapping[s] for s in proofnet_valid_statements)
        splits['proofnet test'] = set(theorem_mapping[s] for s in proofnet_test_statements)
        assert len(splits['proofnet valid']) == len(proofnet_valid_statements)
        assert len(splits['proofnet test']) == len(proofnet_test_statements)

    grouped_proofs = defaultdict(list)
    for test_info in generated_proofs:
        grouped_proofs[test_info['iter']].append(test_info)

    metrics = defaultdict(list)
    for K in budgets:
        if K > max_iter:
            break

        stats = []
        for rd in tqdm(range(0, max_iter, K)):
            generated_proofs_subset = []
            for i in range(rd, rd + K):
                generated_proofs_subset += [test_info | {'iter': test_info['iter'] - rd} for test_info in grouped_proofs[i]]
            
            ret = {}
            for key, ids in splits.items():
                ret[key] = compute_succ_rate([test_info for test_info in generated_proofs_subset if test_info['lemma_id'] in ids], 
                                             lemma_ids = ids)
        
            stats.append(ret)
    
        ret = {}
        for k in stats[0].keys():
            pass_rates = [r[k][-1] for r in stats]
            # print(k, ' : ', np.mean(pass_rates), ' ± ', np.std(pass_rates))
            ave = np.mean(pass_rates)
            std = np.std(pass_rates) if len(pass_rates) >= 4 else None
            ret[k] = (ave, std)

        # metrics.append((K, ret['miniF2F test'][0], ret['miniF2F test'][1]))
        for k, v in ret.items():
            metrics[k].append((K, v[0], v[1]))
    return metrics

if __name__ == '__main__':
    # argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--log_path', type=str)
    parser.add_argument('--split', type=str, default='miniF2F')
    parser.add_argument('--max_iter', type=int, default=3200)
    args = parser.parse_args()

    budgets = [1, 32, 128, 640, 3200, 6400, 4 * 6400]
    stats = get_metric(args.log_path, budgets = budgets, split = args.split, max_iter = args.max_iter)
    # print(stats)
    # dump to json string
    print(json.dumps(stats))