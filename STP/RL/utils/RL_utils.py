import re
import os
import json
import time
import pickle
import pandas as pd
import psutil
import logging
from datetime import datetime
import numpy as np
from copy import deepcopy
from tqdm.auto import tqdm
import ray
import gc
import hashlib
import threading
from ray.util import ActorPool
from collections import defaultdict
from utils.model_utils import right_truncate, insert_lemma, get_lemma_key, update_lemma_mapping
from utils.model_utils import ray_completion, ray_get_prompt, create_inference_actors, create_embedding_actors, ray_get_embeddings
from typing import Any, Dict, List, Tuple, Set, Callable, Optional
from utils.gcloud_utils import read_file, write_data, cleanup_dir, move_file, execute_on_all_workers, copy_dir
from utils.model_utils import END_THM, START_LEMMA_STMT
from utils.prover.lean.verifier import create_ray_lean4_actors, TEST_BATCH_SIZE, DEFAULT_TIMEOUT
from concurrent.futures import ProcessPoolExecutor
#from utils.model_utils import copy_checkpoints_all, CHECKPOINT_TMP_DIR, get_lemma_key

BATCH_SIZE = 1024
prompt_length = 1024
CONJECTURE_THRESHOLD = 0.25
NR_FOLD = 5
EARLY_STOP_THRESHOLD = 0.1
CPU_PER_TASK = 1.5

__DEBUG__ = os.getenv("DEBUG", 'False').lower() in ('true', '1', 't')
REPO_DIR = os.path.abspath(os.path.join(__file__, '../../..'))
STORAGE = "/n/netscratch/amin_lab/Lab/slim/STP/storage"
HUGGING_FACE_HUB_TOKEN = os.getenv('HF_TOKEN', None)
WANDB_API_KEY = os.getenv('WANDB_API_KEY', None)
assert STORAGE is not None, 'STORAGE is not set'

def merge_labels(labels: List[str], new_labels: List[str]) -> List[str]:
    return list(set(labels + new_labels))
#READ 
def collect_trajectories(pool, num_workers, lemmas_to_generate, max_length, seed, temperature, cache_dir = None):
    # Function that prepare the prover dataset to pass it to the LLM : prompt construction + pass it to the LLM
    generated_proofs = []
    prompts = ray_get_prompt(pool, num_workers, lemmas_to_generate, max_length=prompt_length, invoke_type=None)
    # prompts = [get_prompt(test_info, tokenizer, prompt_length, None) for test_info in lemmas_to_generate]
    completions = ray_completion(pool, prompts, num_workers, temperature=temperature, max_tokens=max_length, seed=seed, cache_dir=cache_dir)
    for output, test_info in zip(completions, lemmas_to_generate):
        generated_text = output['text'].split('\n```', 1)[0]
        generated_proofs.append(test_info | {'proof': generated_text})
    return generated_proofs
#READ :
def collect_conjecture(pool, num_workers, lemmas_to_generate, lemma_mapping, max_length, seed, temperature, cache_dir = None):
    # print all the args for debugging
    # Function that prepare the conjecture dataset to pass it to the LLM

    logging.debug(f'Start collecting conjecture theorems:')
    logging.debug(f'num_workers = {num_workers}, num_queries: {len(lemmas_to_generate)}, max_length = {max_length}, seed = {seed}, temperature = {temperature}, cache_dir = {cache_dir}') # here the prompt is added for the conjecture (using tokenize.remote)
    prompts = ray_get_prompt(pool, num_workers, lemmas_to_generate, max_length=prompt_length, invoke_type='conjecture')
    # prompts = [get_prompt(test_info, tokenizer, prompt_length, 'conjecture') for test_info in lemmas_to_generate]
    completions = ray_completion(pool, prompts, num_workers, temperature=temperature, max_tokens=max_length, seed=seed, cache_dir=cache_dir) # THERE IS THE PART WHEN data is generated (completed)
    generated_proofs = []
    for output, test_info in zip(completions, lemmas_to_generate):
        statement = 'theorem ' + output['text'].split(END_THM)[0].strip()
        if ':=' in statement:
            statement = statement.split(':=')[0]
        statement = statement + ':= by' # we prepare the new theorem into the form of the dataset of the prover (no proof was generated yet)
        new_test_info = {'statement': statement,
                         'label': merge_labels(test_info.get('label', []), ['conjecture']),
                         'easy_statement': test_info['statement'],
                         'easy_proof': test_info['proof'],
                         'header': test_info.get('header', None),
                         'shared_lemma': test_info['shared_lemma']} # this is special for conjectures
        insert_lemma(lemma_mapping, new_test_info)
        generated_proofs.append(new_test_info)
    return generated_proofs

def update_succ_lemmas(generated_proofs: List[Dict], succ_lemmas: Set[int]) -> None:
    succ_lemmas |= set(test_info['lemma_id'] for test_info in generated_proofs if test_info.get('complete', False))

def filter_by_ratio(generated_proofs, filter_inputs, denominator, threshold):
    # first we filter based on the length of the goal
    min_p2s_ratio = defaultdict(lambda: 1e5)
    for test_info in generated_proofs:
        if test_info.get('complete', False):
            key = get_lemma_key(test_info)
            min_p2s_ratio[key] = min(min_p2s_ratio[key], len(test_info['proof']) / denominator(test_info['statement']))
    
    filter_results = []
    groups = defaultdict(list)
    for test_info in filter_inputs:
        groups[test_info['shared_lemma']].append(test_info)
    
    for shared_lemma, group in groups.items():
        p2s_ratios = [min_p2s_ratio[get_lemma_key(test_info)] for test_info in group]
        # sort p2s_ratios
        p2s_ratios.sort()
        cutoff = p2s_ratios[int(len(p2s_ratios) * threshold)]
        for test_info in group:
            key_hard = get_lemma_key(test_info)
            if (min_p2s_ratio[key_hard] >= cutoff) or len(group) < 2:
                filter_results.append(test_info)
    return filter_results

def save_result(results: Dict, file_path: str):
    file_path_tmp = file_path + '_backup'
    write_data(pickle.dumps(results), file_path_tmp, 'pkl')
    move_file(file_path_tmp + '.gz', file_path + '.gz')

def get_deduplication_key(test_info):
    return (test_info['statement'], test_info['proof'], test_info.get('header', ''), test_info.get('iter', 0))

def get_result_items(test_info):
    return {k: v for k, v in test_info.items() if k in ['complete', 'sorries', 'errors', 'system_messages', 'pass', 'invokes', 'verified_code', 'verify_time']}

def split_test_blocks(test_infos, batch_size, group_by_header):
    # sort by header
    rng = np.random.default_rng(0)
    rng.shuffle(test_infos)
    if group_by_header:
        test_infos = sorted(test_infos, key=lambda x: x.get('header', None) or '')
    blocks = [test_infos[i: i + batch_size] for i in range(0, len(test_infos), batch_size)]
    # shuffle the blocks
    rng.shuffle(blocks)
    return blocks
#READ
def generate_and_test(
        selected_lemmas: List[Dict], 
        collect_traj: Callable, 
        ray_inference_actors: List, 
        lemma_mapping: Dict, 
        seed: int, 
        save_dir: Optional[str],
        cpus_per_task: float = CPU_PER_TASK,
        cpus_per_task_stage2: float = CPU_PER_TASK + 1.5,
        test_batch_size: int = TEST_BATCH_SIZE,
        group_by_header: bool = False,
        collect_premises: bool = True,
) -> List[Dict]:
    """
    Generate and test proofs for the selected lemmas; parallelize the generation and testing process.

    Return: a list of generated and tested lemmas
    """
    if ray_inference_actors is not None:
        inference_pool = ActorPool(ray_inference_actors)

    ray_test_actors = create_ray_lean4_actors(reserved_cpus=2, cpus_per_task=1, 
                                              collect_premises=collect_premises, timeout=DEFAULT_TIMEOUT * test_batch_size)
    
    tester_pool = ActorPool(ray_test_actors)

    save_file_generation = os.path.join(save_dir, f'generated_proofs.json') if save_dir is not None else None
    generated_proofs_dedup = read_file(save_file_generation) if save_file_generation is not None else None
    save_file_tests = os.path.join(save_dir, f'test_results.pkl') if save_dir is not None else None
    test_results = (read_file(save_file_tests) if save_file_tests is not None else None) or {}
    total_test_tasks = 0
    total_test_instances = 0

    pool_lock = threading.Lock()
    pbar = tqdm(total=len(selected_lemmas))
    finished_generation = False
    
    def aggregate_results(early_stop_threshold = 0):
        save_interval = 300  # Time interval in seconds (300 seconds = 5 minutes)
        last_save_time = time.time()
        nr_finished_jobs = 0
        nr_tests_correct = 0
        nr_tests_done = 0
        cached_pbar_n = 0
        while tester_pool.has_next() or (not finished_generation):
            if finished_generation and (total_test_tasks - nr_finished_jobs <= early_stop_threshold):
                break
            if not tester_pool.has_next():
                time.sleep(2)
                continue
            try:
                with pool_lock:
                    results = tester_pool.get_next_unordered(timeout=0)
                nr_finished_jobs += 1
            except TimeoutError as e:
                if finished_generation:
                    cpu_usage = psutil.cpu_percent(interval=0.5)
                    memory_usage = psutil.virtual_memory().percent
                    pbar.set_postfix(cpu=f'{cpu_usage}%', mem=f'{memory_usage}%', remaining=f'{total_test_tasks - nr_finished_jobs}', pass_rate=f'{nr_tests_correct/max(nr_tests_done,1) * 100:.2f}%')
                    pbar.set_description('Ray testing')
                    pbar.refresh()
                else:
                    time.sleep(2)
                    
                continue
            
            for result in results:
                test_results[get_deduplication_key(result)] = get_result_items(result)

            nr_tests_done += len(results)
            nr_tests_correct += sum(result.get('complete', False) for result in results)

            current_time = time.time()
            if (current_time - last_save_time >= save_interval) and (save_file_tests is not None):
                save_result(test_results, save_file_tests)
                last_save_time = current_time  # Reset the last save time

            cached_pbar_n += len(results)
            if finished_generation:
                pbar.update(cached_pbar_n)
                cached_pbar_n = 0
        save_result(test_results, save_file_tests)

    if generated_proofs_dedup is None:
        monitoring_thread = threading.Thread(target=aggregate_results, args=(int(len(ray_test_actors) * EARLY_STOP_THRESHOLD),))
        monitoring_thread.daemon = True
        monitoring_thread.start()

        start_time = datetime.now()
        generated_proofs_dedup = []
        deduplicate_index = {}
        batch_size = (len(selected_lemmas) + NR_FOLD - 1) // NR_FOLD
        for shard in range(NR_FOLD):
            logging.debug(f'Processing shard {shard}/{NR_FOLD}...')
            batch = selected_lemmas[batch_size * shard: batch_size * (shard + 1)]
            generated_proofs = collect_traj(inference_pool, len(ray_inference_actors), batch, lemma_mapping, seed * NR_FOLD + shard)

            start_idx = len(generated_proofs_dedup)
            # deduplicate proofs before testing
            for test_info in generated_proofs:
                key = get_deduplication_key(test_info)
                if key not in deduplicate_index:
                    deduplicate_index[key] = len(generated_proofs_dedup)
                    generated_proofs_dedup.append(test_info | {'multiplicity': 1})
                else:
                    generated_proofs_dedup[deduplicate_index[key]]['multiplicity'] += 1

            new_testing_tasks = [test_info for test_info in generated_proofs_dedup[start_idx:] if get_deduplication_key(test_info) not in test_results]
            total_test_instances += len(new_testing_tasks)
            pbar.total = total_test_instances
            new_testing_tasks = split_test_blocks(new_testing_tasks, test_batch_size, group_by_header)
            with pool_lock:
                for testing_block in new_testing_tasks:
                    tester_pool.submit(lambda actor, batch: 
                                actor.run.remote(batch, batched=True),
                        testing_block)
                total_test_tasks += len(new_testing_tasks)

        finished_generation = True
        logging.info(f'Finished generation. #generated lemmas = {len(generated_proofs_dedup)}.')
        duration = datetime.now() - start_time
        logging.info('Inference time: ' + str(duration))

        logging.info(f'Start testing {total_test_tasks} tasks...')
        start_time = datetime.now()
        monitoring_thread.join()
        pbar.close()

        # stage 2 testing
        print('Stage 2: rerunning timed-out jobs...')
        for actor in ray_test_actors:
            ray.kill(actor)
        execute_on_all_workers("""pkill -f "repl"; pkill -f "lake" """)

        # allow more memory for stage 2 because the failed jobs are likely to be more memory-consuming
        ray_test_actors = create_ray_lean4_actors(reserved_cpus = 2, cpus_per_task=10, timeout=DEFAULT_TIMEOUT)
        tester_pool = ActorPool(ray_test_actors)

        new_testing_tasks = []
        for test_info in generated_proofs_dedup:
            if (get_deduplication_key(test_info) not in test_results) or ('complete' not in test_results[get_deduplication_key(test_info)]):
                new_testing_tasks.append(test_info)
        logging.info(f'Number of lemmas to test in stage 2: {len(new_testing_tasks)}')
        pbar = tqdm(total=len(new_testing_tasks))
        new_testing_tasks = [[test_info] for test_info in new_testing_tasks]
        with pool_lock:
            for testing_block in new_testing_tasks:
                tester_pool.submit(lambda actor, batch: 
                            actor.run.remote(batch, batched=False),
                        testing_block)
            total_test_tasks = len(new_testing_tasks)
        
        monitoring_thread = threading.Thread(target=aggregate_results)
        monitoring_thread.daemon = True
        monitoring_thread.start()
        monitoring_thread.join()
        pbar.close()

        duration = datetime.now() - start_time
        logging.info('Testing time: ' + str(duration))
        
        for actor in ray_test_actors:
            ray.kill(actor)
        execute_on_all_workers("""pkill -f "repl"; pkill -f "lake" """)
        # update generated lemmas
        nr_failed = 0
        for test_info in generated_proofs_dedup:
            key = get_deduplication_key(test_info)
            if key in test_results:
                test_info |= test_results[key]
            else:
                nr_failed += 1
                test_info['complete'] = False
                test_info['system_errors'] = 'test failed'
        assert nr_failed < len(generated_proofs_dedup) * 0.005, f'Failed to test {nr_failed} lemmas'
        write_data(json.dumps(generated_proofs_dedup), save_file_generation, 'json')
    else:
        print(f'Loaded {len(generated_proofs_dedup)} lemmas from {save_file_generation}')
        for test_info in generated_proofs_dedup:
            update_lemma_mapping(lemma_mapping, test_info)
    
    if ray_inference_actors is not None:
        # clean up inference actors
        for actor in ray_inference_actors:
            ray.kill(actor)

    return generated_proofs_dedup

def get_conjecture_level(test_info):
    for label in test_info['label']:
        if label.startswith('conjecture '):
            return int(label.split()[-1])
    return 0

def update_succ_rates(generated_proofs, succ_rates):
    proof_results = defaultdict(list)
    for test_info in generated_proofs:
        for _ in range(test_info.get('multiplicity', 1)):
            proof_results[test_info['lemma_id']].append(int(test_info.get('complete', False)))
    for lemma_id, results in proof_results.items():
        succ_rates[lemma_id] = max(np.mean(results), succ_rates.get(lemma_id, 0))

class Sampler_base:
    def __init__(self) -> None:
        self.succ_lemmas = set()
        self.succ_rates = {} # lemma_id -> succ_rate
        self.lemma_mapping = {}
        self.valid_conjecture_examples = []
        self.generated_proofs = []

        self.avaliable_lemmas = read_file(os.path.join(REPO_DIR, 'assets/data/theorem_dict.pkl'))
        self.avaliable_lemmas = {k: v[1].split(':=')[0].strip() for k, v in self.avaliable_lemmas.items()} # theroem_name : theorem statement (mathlib statements)
        self.avaliable_lemmas[''] = 'theorem true: True'
        # avaliable_lemmas: name of the lemma -> lemma statement

    def init_lemma_mapping(self, init_lemmas):
        for test_info in init_lemmas:
            insert_lemma(self.lemma_mapping, test_info)
        self.relevant_lemmas = set(test_info['lemma_id'] for test_info in init_lemmas)

    def to_dict(self) -> dict:
        # Convert the object's attributes to a dictionary for serialization
        return {
            'succ_lemmas': self.succ_lemmas,
            'lemma_mapping': self.lemma_mapping,
            'valid_conjecture_examples': self.valid_conjecture_examples,
            'generated_proofs': self.generated_proofs,
            'succ_rates': self.succ_rates,
            'relevant_lemmas': self.relevant_lemmas,
        }

    @classmethod
    def from_dict(cls, data: dict):
        # Create an object from a dictionary of attributes
        obj = cls()
        obj.succ_lemmas = data['succ_lemmas']
        obj.lemma_mapping = data['lemma_mapping']
        obj.valid_conjecture_examples = data['valid_conjecture_examples']
        obj.generated_proofs = data['generated_proofs']
        obj.succ_rates = data['succ_rates']
        obj.relevant_lemmas = data['relevant_lemmas']
        return obj
    
    def refresh_succ_lemmas(self) -> None:
        self.succ_lemmas = set()
#READ
    def filtered_conjecture_examples(self, valid_conjecture_examples, **kwargs) -> List[Dict]:
        if len(valid_conjecture_examples) == 0:
            return []
        filter_results = filter_by_ratio(self.generated_proofs, valid_conjecture_examples, lambda x: len(x), 0.2) # elegancy filter : not in the lowest 20% min(p)/len(conjecture)
        logging.info(f'[Filtering Stage 1] Number of conjecture examples: {len(valid_conjecture_examples)}; after filtering: {len(filter_results)}')
        ret = wasserstein_matching(P = filter_results, 
                                    Q = kwargs['project_to'], 
                                    ray_embedding_actors=kwargs['ray_embedding_actors'],
                                    seed=kwargs['seed'],
                                    cache_dir=kwargs['save_dir'],
                                    k=4) # this is not the same thing as the paper
        return ret # return the conjectures with weight  
    #READ
    def select(self, lemmas_to_generate: List[Dict], ray_inference_actors: List[Any], seed: int, **kwargs) -> List[Dict]:
        # select seed dataset for Self play
        rng = np.random.default_rng(seed)

        conjecture_inputs = []
        possible_inputs = []
        for test_info in reversed(self.generated_proofs):
            if (test_info.get('complete', False)) and self.succ_rates[test_info['lemma_id']] > CONJECTURE_THRESHOLD + 0.1: # we select sucessfull statements/proofs from previous rounds
                if (get_conjecture_level(test_info) <= 0):
                    possible_inputs.append(test_info)
        rng.shuffle(possible_inputs)
        possible_inputs = sorted(possible_inputs, key=lambda test_info: get_conjecture_level(test_info))
        dedup_set = set()
        lemma_count = defaultdict(int)
        for test_info in possible_inputs: # we use lean (verify.py) to parse the tactics / lemma used 
            invoked_lemmas = test_info.get('invokes', []) # For the first time it is [] but  when we evaluate a proof using lean we will have it
            if rng.random() < 0.5: # add a trivial lemma with probability 50%
                # randomly generate a statement without invoking any lemma
                invoked_lemmas += ['']
            for invoked_lemma in invoked_lemmas:
                if invoked_lemma not in self.avaliable_lemmas:
                    continue

                if (lemma_count[invoked_lemma] >= len(lemmas_to_generate) * 0.1) and (len(invoked_lemma) > 0): # verify that the lemma is not included too much
                    continue
                if (lemma_count[invoked_lemma] >= 0.1 * len(lemmas_to_generate)) and (len(invoked_lemma) == 0):
                    continue
                if (test_info['statement'], invoked_lemma) not in dedup_set:
                    dedup_set.add((test_info['statement'], invoked_lemma))
                    lemma_count[invoked_lemma] += 1
                else:
                    continue
                for _ in range(test_info.get('matching_weight', 1)):
                    conjecture_inputs.append(test_info | {'shared_lemma': invoked_lemma, 'shared_lemma_statement': self.avaliable_lemmas[invoked_lemma]})
        conjecture_inputs = conjecture_inputs[:len(lemmas_to_generate)] # to have sample budget is distributed equally between the conjectures and the statement
        
        logging.info(f'#conjecture inputs = {len(conjecture_inputs)}')
        if len(conjecture_inputs) == 0:
            logging.info('No conjecture inputs, return all statements in the original dataset.')
            return lemmas_to_generate
        # next 3 lines generate conjectures using the LLM that we have (without proofs for now)
        pool = ActorPool(ray_inference_actors)
        conjecture_multiplier = max(kwargs['conjecture_multiplier'], min(len(lemmas_to_generate) * 3 // len(conjecture_inputs), 8))
        conjecture_lemmas = kwargs['collect_conjecture'](pool, len(ray_inference_actors), conjecture_inputs * conjecture_multiplier, self.lemma_mapping, seed=seed)
        # deduplicate conjectures
        rng.shuffle(conjecture_lemmas)

        def get_deduplicate_key(test_info):
            ret = (test_info.get('header', None), test_info['statement'].replace(' ', '').replace('\n', ''))
            return ret
        # de duplication 
        deduplicate_set = set(get_deduplicate_key(test_info) for test_info in lemmas_to_generate)
        conjecture_lemmas_dedup = []
        for test_info in conjecture_lemmas:
            key = get_deduplicate_key(test_info)
            if key not in deduplicate_set:
                deduplicate_set.add(key)
                # deal with the labels
                labels = test_info['label']
                test_info['label'] = [label for label in labels if not label.startswith('conjecture')]
                conjecture_count = 0
                for label in labels:
                    if label.startswith('conjecture '):
                        conjecture_count = int(label.split()[-1])
                test_info['label'] += [f'conjecture {conjecture_count + 1}']

                conjecture_lemmas_dedup.append(test_info)
                
        logging.info(f'#conjecture lemmas before deduplication = {len(conjecture_lemmas)}, after deduplication = {len(conjecture_lemmas_dedup)}')
        # We want the number of generated_conjecture <= unproved theorems
        if len(conjecture_lemmas_dedup) > len(lemmas_to_generate):
            rng.shuffle(conjecture_lemmas_dedup)
            conjecture_lemmas_dedup = conjecture_lemmas_dedup[:len(lemmas_to_generate)]
            logging.info(f'Randomly select {len(conjecture_lemmas_dedup)} conjecture lemmas')
        
        ret = [test_info for test_info in lemmas_to_generate + conjecture_lemmas_dedup if test_info['lemma_id'] not in self.succ_lemmas]
        rng = np.random.default_rng(seed)
        for test_info in lemmas_to_generate:
            if test_info['lemma_id'] in self.succ_lemmas:
                if (rng.random() < 0.05) or (self.succ_rates[test_info['lemma_id']] < CONJECTURE_THRESHOLD + 0.1):
                    ret.append(test_info)
        return ret
# READ
    def get_conjecture_examples(self, generated_proofs, **kwargs) -> None: # let's extract the conjectures
        conjecture_examples = []
        rng = np.random.default_rng(0)
        # update valid_conjecture_examples
        proof_results = defaultdict(list)
        for test_info in generated_proofs:
            for _ in range(test_info.get('multiplicity', 1)):
                proof_results[test_info['lemma_id']].append(int(test_info.get('complete', False))) # from results for each conjecture, we add the results of its proof

        def get_succ_rate(test_info):
            return np.mean(proof_results[test_info['lemma_id']])

        generated_proofs = [test_info for test_info in generated_proofs \
                                if (test_info.get('complete', False))] # we take the sucessefull proofs here

        dedup_set = set() 
        for test_info in generated_proofs:
            if ('shared_lemma' in test_info) and (get_succ_rate(test_info) < CONJECTURE_THRESHOLD): # The pass rate  # 'shared_lemma' in test_info means it is a conjecture
                if test_info['shared_lemma'] in test_info.get('invokes', []):  # we verify that the new conjecture has used the lemma 
                    if test_info['statement'] not in dedup_set: #   de duplication
                        conjecture_examples.append(test_info)
                        dedup_set.add(test_info['statement'])
# for invokes : when we evaluate the proof in lean there is a function in verify.py to add invokes : extract_invokes
        invoke_count = len(conjecture_examples)
        no_invoke_count = 0
        for test_info in generated_proofs:
            if ('shared_lemma' in test_info) and (get_succ_rate(test_info) < CONJECTURE_THRESHOLD):
                if (test_info['statement'] not in dedup_set) and (no_invoke_count < max(invoke_count * 20, 4096)):  # case trivial lemma
                    # we don't want to generate too many examples without invoking any lemma
                    no_invoke_count += 1
                    new_test_info = deepcopy(test_info)
                    new_test_info['shared_lemma'] = ''
                    conjecture_examples.append(new_test_info)
                    dedup_set.add(test_info['statement'])
                    
        logging.info(f'#conjecture examples = {len(conjecture_examples)}')
        return conjecture_examples # return conjectures after verifying the filters conditions (no re-weighting was applied yet)
# READ # RL generation
    def generate( 
            self,
            model_dir: str,
            tokenizer_path: str,
            lemmas_to_generate: List[Dict],
            seed: int,
            collect_traj: Callable,
            project_to: List[Dict],
            save_dir: str = None,
            round_id: int = 0,
            sps: int = 16,
            **kwargs,
    ) -> List[Dict]:
        ray_inference_actors, model_dir = create_inference_actors(model_dir, tokenizer_path, enable_prefix_caching=False)

        for test_info in lemmas_to_generate:
            insert_lemma(self.lemma_mapping, test_info)
        for test_info in project_to: # same thing as lemmas_to_generate only when you select statements from statements_ds
            insert_lemma(self.lemma_mapping, test_info)
        selected_lemmas = self.select(lemmas_to_generate,  
                                      ray_inference_actors=ray_inference_actors, # ray inference actors were used to generate conjectures
                                      seed=seed,
                                      **kwargs)
        logging.info(selected_lemmas[0])      # selected lemmas contain the generated conjectures
        logging.info(f'#selected statements = {len(selected_lemmas)}')
        selected_lemmas = deepcopy(selected_lemmas * sps)

        rng = np.random.default_rng(seed)
        rng.shuffle(selected_lemmas)
        # Here we generate proofs (next token prediction)
        generated_proofs_dedup = generate_and_test(selected_lemmas, collect_traj, ray_inference_actors, self.lemma_mapping, seed, save_dir)
        logging.info(f'#generated proofs before deduplication = {len(selected_lemmas)}, total proofs after deduplication = {len(generated_proofs_dedup)}')

        for actor in ray_inference_actors:
            ray.kill(actor)
        ray_embedding_actors = create_embedding_actors(model_dir, tokenizer_path)

        update_succ_lemmas(generated_proofs_dedup, self.succ_lemmas)
        update_succ_rates(generated_proofs_dedup, self.succ_rates)
        
        conjecture_examples = self.get_conjecture_examples(generated_proofs_dedup, **kwargs) # get conjecture from outputs
        self.generated_proofs += [test_info | {'round': round_id} for test_info in generated_proofs_dedup] # add round_id to the data
        self.generated_proofs = [test_info for test_info in self.generated_proofs if (test_info['round'] >= round_id - 2) or (test_info['lemma_id'] in self.relevant_lemmas)]
        # filter out unproved lemmas
        self.generated_proofs = [test_info for test_info in self.generated_proofs if self.succ_rates[test_info['lemma_id']] > 0] # keep only generated proofs that were successfull
         # filter conjectures using the weights : take most interesting ones
        self.valid_conjecture_examples = self.filtered_conjecture_examples(conjecture_examples, 
                                                                               project_to=[test_info for test_info in project_to if test_info['lemma_id'] not in self.succ_lemmas],
                                                                               ray_embedding_actors=ray_embedding_actors,
                                                                               seed=seed,
                                                                               save_dir=save_dir)
        logging.info(f'#generated proofs = {len(generated_proofs_dedup)}, succ rate = {len(self.succ_lemmas.intersection(self.relevant_lemmas)) / len(self.relevant_lemmas) * 100:.4f}')
        
        # clean up embedding actors
        for actor in ray_embedding_actors:
            ray.kill(actor)
        return generated_proofs_dedup, conjecture_examples
    
class Sampler_naive(Sampler_base): # expert iteration
    def __init__(self) -> None:
        super().__init__()

    def select(self, lemmas_to_generate: List[Dict], ray_inference_actors: List[Any], seed: int, **kwargs) -> List[Dict]:
        # return lemmas_to_generate
        return [test_info for test_info in lemmas_to_generate if test_info['lemma_id'] not in self.succ_lemmas]

    def filtered_conjecture_examples(self) -> List[Dict]:
        return []

    def generate(
            self,
            model_dir: str,
            tokenizer_path: str,
            lemmas_to_generate: List[Dict],
            seed: int,
            collect_traj: Callable,
            save_dir: str = None,
            round_id: int = 0,
            sps: int = 16,
            **kwargs,
    ) -> List[Dict]:
        ray_inference_actors, model_dir = create_inference_actors(model_dir, tokenizer_path, enable_prefix_caching=False)
# same thing
        for test_info in lemmas_to_generate:
            insert_lemma(self.lemma_mapping, test_info)
        # No conjecture is generated ! No reweightening
        selected_lemmas = self.select(lemmas_to_generate, 
                                      ray_inference_actors=ray_inference_actors, 
                                      seed=seed,
                                      **kwargs)
        logging.info(f'#selected lemmas = {len(selected_lemmas)}')
        selected_lemmas = deepcopy(selected_lemmas * sps)

        rng = np.random.default_rng(seed)
        rng.shuffle(selected_lemmas)
        generated_proofs_dedup = generate_and_test(selected_lemmas, collect_traj, ray_inference_actors, self.lemma_mapping, seed, save_dir)
        logging.info(f'#generated lemmas before deduplication = {len(selected_lemmas)}, total lemmas after deduplication = {len(generated_proofs_dedup)}')

        update_succ_lemmas(generated_proofs_dedup, self.succ_lemmas)
        update_succ_rates(generated_proofs_dedup, self.succ_rates)
        self.generated_proofs += [test_info | {'round': round_id} for test_info in generated_proofs_dedup]
        self.generated_proofs = [test_info for test_info in self.generated_proofs if (test_info['round'] >= round_id - 2) or (test_info['lemma_id'] in self.relevant_lemmas)]
        self.generated_proofs = [test_info for test_info in self.generated_proofs if self.succ_rates[test_info['lemma_id']] > 0]
        logging.info(f'#generated lemmas = {len(generated_proofs_dedup)}, succ rate = {len(self.succ_lemmas.intersection(self.relevant_lemmas)) / len(self.relevant_lemmas) * 100:.4f}')
        # there is no weights change. 
        return generated_proofs_dedup, []
    
#Read
def wasserstein_matching(P: List[Dict], Q: List[Dict], ray_embedding_actors: List[Any], seed: int, cache_dir: str = None, k = 3):
    logging.info(f'Wasserstein matching: #inputs = {len(P)}, #candidates = {len(Q)}, seed = {seed}')
    Q = deepcopy(Q)
    rng = np.random.default_rng(seed)
    rng.shuffle(Q)
    # normalise the matrix
    embedding_pool = ActorPool(ray_embedding_actors)
    embedding_P = ray_get_embeddings(embedding_pool, P, cache_dir=cache_dir)
    embedding_P /= np.linalg.norm(embedding_P, axis=1, keepdims=True)
    embedding_Q = ray_get_embeddings(embedding_pool, Q, cache_dir=cache_dir)
    embedding_Q /= np.linalg.norm(embedding_Q, axis=1, keepdims=True)

    weights = [0] * len(P)
    mask = np.ones_like(embedding_P[:,0])
    
    N = len(P)
    M = sum(test_info['matching_weight'] for test_info in Q)
    similarities = embedding_P @ embedding_Q.T
    for i, test_info in tqdm(enumerate(Q), desc='Wasserstein Matching'):
        similarity = similarities[:, i] # the unproved theorem N* i = y
        top_k = min(test_info['matching_weight'], N) 
        for matching_id in np.argpartition(similarity * mask, -top_k)[-top_k:]: # the k conjectures with the smallest similarity
            weights[matching_id] += N / M
            if weights[matching_id] >= k:
                mask[matching_id] = 0
    
    ret = []
    for test_info, w in zip(P, weights):
        if w > 0:
            ret.append(test_info | {'weight': w}) # we add the new weights  and select conjectures only have positive weights (Reweighting )
    logging.info(f'Wasserstein matching: #inputs = {N}, #matched = {len(ret)}')
    return ret

def train_model(
        model_dir: str, 
        train_from: str,
        max_iters: int, 
        train_data_path: str, 
        args: Any, 
        wandb_project: str, 
        wandb_id: str, 
        eval_data_path: Optional[str] = None, 
) -> None:
    if 'gs://' in train_from:
        local_path = copy_checkpoints_all(train_from, CHECKPOINT_TMP_DIR)
    else:
        local_path = train_from

    model_name = model_dir.split('/')[-1]
    logging.info(f'training {model_name}...')
    # training
    output_dir = os.path.join(args.exp_dir, 'RL_training', model_name)
    data_cache_dir = os.path.join(output_dir, 'data_cache')
    cleanup_dir(output_dir)

    training_config = {
            'trainer.wandb.project': wandb_project,
            'trainer.wandb.resume': 'must',
            'trainer.wandb.id': wandb_id,

            'trainer.num_train_steps': max_iters,
            'trainer.train_batch_size': BATCH_SIZE,
            'trainer.checkpointer.base_path': os.path.join(output_dir, 'checkpoints'),
            'train_data': train_data_path,
            'train_data_cache_dir': os.path.join(data_cache_dir, 'train'),
            'eval_data': os.path.join(STORAGE, 'data/SFT/eval.json'),
            'eval_data_cache_dir': os.path.join(STORAGE, 'data/SFT/eval_cache'),
            'model_name_or_path': local_path,
            'save_freq': max_iters - 1,
            'config_path': 'levanter/config/RL_base.yaml',
            'hf_save_path': os.path.join(output_dir, 'hf_checkpoints'),

            'optimizer.learning_rate': args.lr,
            'optimizer.warmup': min(max_iters - 1, 5),
        }
    if eval_data_path is not None:
        training_config |= {
            'eval_data': eval_data_path,
            'eval_data_cache_dir': os.path.join(data_cache_dir, 'eval')
        }
    print(REPO_DIR)
    LEV_ROOT = os.path.join(REPO_DIR, 'levanter')
    training_cmd = f'module load python/3.12.5-fasrc01; module load cuda/12.4.1-fasrc01 ; module load cudnn/9.1.1.17_cuda12-fasrc01 ; conda activate /n/netscratch/amin_lab/Lab/slim/env ;'\
                    'mkdir -p ~/.logs/; cd /n/netscratch/amin_lab/Lab/slim/STP; ray stop; ' \
                    '/n/netscratch/amin_lab/Lab/slim/env/bin/python levanter/examples/weighted_lm.py'
    for k, v in training_config.items():
        if v is None:
            training_cmd += f' --{k}'
        else:
            training_cmd += f' --{k} {v}'
    command_hash = hashlib.md5(training_cmd.encode('utf-8')).hexdigest()
 #   training_cmd += f' &> ~/.logs/{command_hash}.log'
    logging.debug(training_cmd)
    execute_on_all_workers(training_cmd, expect_succ=True)

    # move the trained model
    trained_model_path = os.path.join(output_dir, 'hf_checkpoints', wandb_id, f'step-{max_iters - 1}')
    cleanup_dir(model_dir)
    copy_dir(trained_model_path, model_dir)
    cleanup_dir(os.path.join(args.exp_dir, 'RL_training'))
    gc.collect()
#READ
def load_ds_from_config(config_path):
    ret = []
    dataset_configs = read_file(config_path)
    for dataset_config in dataset_configs:
        logging.debug(f'Processing dataset: {dataset_config["dataset_path"]}')
        raw_dataset = read_file(os.path.join(REPO_DIR, dataset_config['dataset_path']))
        assert (raw_dataset is not None), f"Failed to read {dataset_config['dataset_path']}"
        logging.debug(f'Size of the dataset: {len(raw_dataset)}')

        matching_weight = dataset_config.get('weight', 1)
        for i, raw in enumerate(raw_dataset):
            test_info = {'statement': raw['formal_statement'].rsplit('sorry', 1)[0].strip(),
                        'label': [raw['split']] + (raw.get('tags', None) or []),
                        'header': raw.get('header', None),
                        'matching_weight': matching_weight}
            ret.append(test_info)
    return ret
