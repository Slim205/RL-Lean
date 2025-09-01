import os
import sys
import time
import json
import pickle
import psutil
import ctypes
import resource
import tempfile
import traceback
import signal
import threading
import subprocess
import multiprocessing as mp
from multiprocessing import Process, Event
from pprint import pprint
import numpy as np
from typing import List
import ray
from ray.util import placement_group, remove_placement_group, ActorPool
from tqdm.auto import tqdm
from utils.prover.lean.ast_parser import lean4_parser
from utils.gcloud_utils import read_file, write_data, move_file, execute_on_all_workers
from func_timeout import FunctionTimedOut, func_set_timeout
from client.client import Lean4Client, batch_verify_proof

__DEBUG__ = os.getenv("DEBUG", 'False').lower() in ('true', '1', 't')
HOME_DIR = os.path.expanduser('~')
DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'
DEFAULT_LEAN_WORKSPACE = f'{HOME_DIR}/lean/mathlib4/'
MEMORY_USAGE_THRESHOLD = 15
DEFAULT_TIMEOUT = 200
LEAN_HEADER = 'import miniF2F\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'
TEST_BATCH_SIZE = 100 # every actor how much it will take ? 

MEMORY_THRESHOLD = 75.0  # Memory usage percentage to trigger waiting


def get_code(custom_id,samples) :
    for sample in samples :
        if sample['custom_id']  == custom_id : 
            return sample['proof']
    print('code Not found ! False custom ID')
    assert False

def get_result_from_repl(results,samples):
    transformed_results = []
    for item in results:
        system_messages = ''
        try:
            repl_result = item["response"]            
            transformed = {
                "custom_id" : item['custom_id'],
                "sorries" : repl_result.get('sorries', []), 
                "tactics" : repl_result.get('tactics', []),
                "errors" : [m for m in repl_result.get('messages', []) if m['severity'] == 'error'],
                "warnings" : [m for m in repl_result.get('messages', []) if m['severity'] == 'warning'],
                "infos" : [m for m in repl_result.get('messages', []) if m['severity'] == 'info'],
                "system_messages": '',
                "system_errors": None,
                "verified_code" : get_code(item['custom_id'],samples),
                "verify_time": repl_result["time"],
                "pass": not any(m["severity"] == "error" for m in repl_result.get('messages', [])),
                "complete": (not any(m["severity"] == "error" for m in repl_result.get('messages', [])) and 
                           not any("sorry" in m.get("data", "") for m in repl_result.get('messages', [])) and
                           not any("failed" in m.get("data", "") for m in repl_result.get('messages', []) if m["severity"] == "warning"))
            }
            # if transformed['complete']:
            #     ast_results = lean4_parser(code, repl_result['ast']) if 'ast' in repl_result and repl_result['ast'] else {}
            #     transformed['invokes'] = extract_invokes(ast_results)

        except:
            transformed = {
                "custom_id" : item['custom_id'],
                "pass": False,
                "complete": False,
                "system_errors": traceback.format_exc(),
            }
        transformed_results.append(transformed)

    return transformed_results


def verify_lean4_file(codes, headers, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      allTactics=False, ast=False, premises=False, tactics=False):
    
    batch_size = 1
    timeout = DEFAULT_TIMEOUT
    url = "http://holy8a14104:12332"# "http://0.0.0.0:12332"

    client = Lean4Client(base_url=url, disable_cache=False)

    samples= []
    for i in range(len(codes)):
        samples.append({"custom_id": f"{codes[i].split('theorem')[1].split(' ')[0]}_{i}" , "proof": codes[i]})

    results = batch_verify_proof(
        samples=samples,
        client=client,
        timeout=timeout,
        num_proc=10,
        batch_size=batch_size,
    )

    compilation_results = get_result_from_repl(results,samples)
    return compilation_results # then what happen ???

@ray.remote
class Lean4Worker():
    def __init__(self, node, idx, collect_premises = True, timeout=DEFAULT_TIMEOUT):
        super().__init__()
        self.node = node
        self.idx = idx

        self.timeout = timeout
        self.last_output_time = time.time()
        self.complete_count = 0
        self.collect_premises = collect_premises

        if idx == 0:
            _monitor_process = mp.Process(target=self._monitor)
            _monitor_process.start()
            self.monitor_pid = _monitor_process.pid

        time.sleep(idx * 0.1)
        print(f'Lean4Worker id={self.idx} node={self.node} started.')
    
    def run(self, inputs, batched = True):
        # If (memory > threshold), wait until we have enough memory
        while psutil.virtual_memory().percent > MEMORY_THRESHOLD:
            print(f'Lean4Worker id={self.idx} node={self.node} waiting for memory...')
            time.sleep(5)

        tasks = dict(codes=[LEAN_HEADER + '\n' + test_info['statement'] + '\n' + test_info['proof'] for test_info in inputs],
                    headers=[test_info.get('header', None) for test_info in inputs],
                    premises=False,
                    ast=False,
                    last_env=0)
        results = verify_lean4_file(**tasks)
        outputs = []
        for test_info, result in zip(inputs, results):
            outputs.append(test_info | result)
            self.last_output_time = time.time()
            self.complete_count += 1

        return outputs
    
    def _monitor(self):
        while True:
            time.sleep(1.0)

            if psutil.virtual_memory().percent > 90.0:
                print(f'Node {self.node} memory usage too high...')
                subprocess.run(['killall', 'python'], capture_output=True)
                subprocess.run(['killall', 'repl'], capture_output=True)
                subprocess.run(['killall', 'lake'], capture_output=True)
            
            # Fetch all processes
            for process in psutil.process_iter(['pid', 'name', 'memory_info']):
                try:
                    if 'repl' in process.info['name']:
                        # Convert memory usage to GB
                        memory_usage_gb = process.info['memory_info'].rss / (1024 ** 3)
                        if memory_usage_gb > MEMORY_USAGE_THRESHOLD:  # Memory usage threshold
                            process.terminate()
                except (Exception, psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess) as e:
                    # print if there is an exception
                    print(f'Error in monitoring process: {e}')
                    continue
            subprocess.run(['killall', 'repl', f'--older-than={int(self.timeout) + 10}s'], capture_output=True)

def create_ray_lean4_actors(
        reserved_cpus: int = 0, 
        cpus_per_task: float = 4,
        **kwargs,
) -> List:
    import socket
    from ray._raylet import PlacementGroupID
    from ray._private.utils import hex_to_binary
    from ray.util.placement_group import PlacementGroup
    for pg_id_str in ray.util.placement_group_table():
        pg_id_bin = PlacementGroupID(hex_to_binary(pg_id_str))
        pg = PlacementGroup(pg_id_bin)
        remove_placement_group(pg)

    head_ip = socket.gethostbyname(socket.gethostname())
    print('Creating ray actors...')
    ray_workers = []
    
    for i, node in enumerate(ray.nodes()):
        ip = node['NodeManagerAddress']
        print(node)
        nr_cpus = int(node['Resources']['CPU']) - reserved_cpus
        nr_local_workers = int(nr_cpus / cpus_per_task)

        if (ip == head_ip) and len(ray.nodes()) > 4 :
            continue

        print(f'Creating {nr_local_workers} workers on node {ip}, host name {node["NodeManagerHostname"]}')
        pg = placement_group([{"CPU": nr_local_workers * cpus_per_task,
                               "node:" + ip: 0.1}], strategy="STRICT_PACK")
        ray.get(pg.ready())

        for j in range(nr_local_workers):
            worker = Lean4Worker.options(
                placement_group=pg,
            ).remote(i, j, **kwargs)
            ray_workers.append(worker)

    print(f'Ray actors created. Number of workers: {len(ray_workers)}')
    print('Lean4 environment initialized.')
    return ray_workers

