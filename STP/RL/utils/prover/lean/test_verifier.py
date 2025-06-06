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

__DEBUG__ = os.getenv("DEBUG", 'False').lower() in ('true', '1', 't')
HOME_DIR = os.path.expanduser('~')
DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'
DEFAULT_LEAN_WORKSPACE = f'{HOME_DIR}/lean/mathlib4/'
MEMORY_USAGE_THRESHOLD = 15
DEFAULT_TIMEOUT = 200
LEAN_HEADER = 'import miniF2F\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'
TEST_BATCH_SIZE = 64

MEMORY_THRESHOLD = 75.0  # Memory usage percentage to trigger waiting

def extract_invokes(ast_results):
    premises = ast_results.get('premises', [])
    invokes = set()
    for premise in premises:
        invokes.add(premise['fullName'])
    return list(invokes)

def get_result_from_repl(repl_result, code, start_time):
    result = {
        "sorries" : repl_result.get('sorries', []), 
        "tactics" : repl_result.get('tactics', []),
        "errors" : [m for m in repl_result.get('messages', []) if m['severity'] == 'error'],
        "warnings" : [m for m in repl_result.get('messages', []) if m['severity'] == 'warning'],
        "infos" : [m for m in repl_result.get('messages', []) if m['severity'] == 'info'],
        "verified_code" : code,
    }
    result['pass'] = not result['errors']
    result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
    if result['complete']:
        ast_results = lean4_parser(code, repl_result['ast']) if 'ast' in repl_result and repl_result['ast'] else {}
        result['invokes'] = extract_invokes(ast_results)
        if __DEBUG__:
            result['ast'] = ast_results
    result['verify_time'] = time.time() - start_time
    return result

def read_from_repl(proc):
    ret = ''
    while True:
        line = proc.stdout.readline()
        if len(line.strip()) == 0:
            break
        ret += line
    return ret

@func_set_timeout(DEFAULT_TIMEOUT, allowOverride=True)
def query_repl(proc, message_str):
    proc.stdin.write(message_str)
    proc.stdin.flush()
    return read_from_repl(proc)

@func_set_timeout(DEFAULT_TIMEOUT + 10, allowOverride=True)
def _start_repl_process(lake_path, lean_workspace, header = None):
    proc = subprocess.Popen([lake_path, "exe", 'repl'], 
                                    stdin=subprocess.PIPE,
                                    stdout=subprocess.PIPE, 
                                    stderr=subprocess.PIPE,  # Capture stderr
                                    text=True, 
                                    cwd=lean_workspace,)
    cmd = json.dumps({"cmd": header or LEAN_HEADER, "allTactics": False, "ast": False, "tactics": False, "premises": False}, ensure_ascii=False) + '\r\n\r\n'
    query_repl(proc, cmd)
    return proc

def start_repl_process(lake_path, lean_workspace, header = None):
    # Retry if the process is not started
    for i in range(5):
        try:
            return _start_repl_process(lake_path, lean_workspace, header)
        except Exception as e:
            if __DEBUG__:
                print(f"Error in starting Lean4 process: {e}")
            time.sleep(i + 1)
            continue
    raise Exception("Failed to start Lean4 process")

@func_set_timeout(DEFAULT_TIMEOUT, allowOverride=True)
def terminate_repl(proc):
    if proc is None:
        return
    
    try:
        # Create a psutil Process instance for the main process
        parent = psutil.Process(proc.pid)
        
        # Retrieve all child processes recursively
        children = parent.children(recursive=True)
        
        # Terminate all child processes
        for child in children:
            child.terminate()
        
        # Terminate the main process
        parent.terminate()
        
        # Wait for all processes to terminate gracefully
        gone, alive = psutil.wait_procs([parent] + children, timeout=5)
        
        # Force kill any processes that are still alive after the timeout
        for p in alive:
            p.kill()
            
    except psutil.NoSuchProcess:
        # The process may have already terminated
        pass
    except Exception as e:
        # Optionally log the exception if needed
        # print(f"Error in terminating processes: {e}")
        pass

def verify_lean4_file(codes, headers, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    
    results = []
    try:
        proc = None
        last_header = None
        for code, header in zip(codes, headers):
            if proc is None or header != last_header:
                terminate_repl(proc)
                proc = start_repl_process(lake_path, lean_workspace, header)
                last_header = header
            
            message_str = json.dumps(command | {'cmd': code, 'env': 0}, ensure_ascii=False) + '\r\n\r\n'
            try:
                start_time = time.time()
                output = query_repl(proc, message_str)
                repl_result = json.loads(output)
                result = get_result_from_repl(repl_result, code, start_time)
                results.append(result)
            except (Exception, FunctionTimedOut) as e:
                if __DEBUG__:
                    print(e)
                results.append({"system_messages": str(e), 'complete': False})
                terminate_repl(proc)
                proc = None

        terminate_repl(proc)
    except (Exception, FunctionTimedOut) as e:
        if __DEBUG__:
            print(e)
        results += [{"system_messages": str(e)}] * (len(codes) - len(results))

    assert len(results) == len(codes), f"Results length mismatch: {len(results)} != {len(codes)}"
    return results

def verify_lean4_file_premises(code, header, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      timeout=DEFAULT_TIMEOUT, allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    if last_env is not None:
        command.update(env=last_env)

    message_str = json.dumps(command | {'cmd': (header or LEAN_HEADER) + code}, ensure_ascii=False) + '\r\n\r\n'
    if verbose:
        print(message_str)
    start_time = time.time()
    
    results = []
    try:
        with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as temp_file:
            temp_file.write(message_str + "\r\n\r\n")
            temp_file.seek(0)
            outputs = subprocess.run([lake_path, "exe", 'repl'], 
                                     stdin=temp_file, 
                                     capture_output=True, 
                                     text=True, 
                                     cwd=lean_workspace, 
                                     timeout=timeout,)

        repl_result = json.loads(outputs.stdout)
        result = get_result_from_repl(repl_result, code, start_time)
        results.append(result)
        return results
    except Exception as e:
        if __DEBUG__:
            print(e)
        return [{"system_messages": str(e), 'complete': False}]

@ray.remote(num_cpus=1)
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
        print('hello')
        while psutil.virtual_memory().percent > MEMORY_THRESHOLD:
            print(f'Lean4Worker id={self.idx} node={self.node} waiting for memory...')
            time.sleep(5)

        if batched:
            tasks = dict(codes=[test_info['statement'] + '\n' + test_info['proof'] for test_info in inputs],
                        headers=[test_info.get('header', None) for test_info in inputs],
                        premises=False,
                        ast=False,
                        last_env=0)
            results = verify_lean4_file(**tasks)

            # get premises
            if self.collect_premises:
                for i, (test_info, result) in enumerate(zip(inputs, results)):
                    if result.get('complete', False):
                        task = dict(code=test_info['statement'] + '\n' + test_info['proof'],
                                    header=test_info.get('header', None),
                                    premises=True,
                                    ast=True,
                                    timeout=DEFAULT_TIMEOUT)
                        result = verify_lean4_file_premises(**task)
                        results[i] = result[0]
        else:
            assert len(inputs) == 1, "Single input only for premises mode"
            test_info = inputs[0]
            tasks = dict(code=test_info['statement'] + '\n' + test_info['proof'],
                        header=test_info.get('header', None),
                        premises=True,
                        ast=True,
                        timeout=DEFAULT_TIMEOUT)
            results = verify_lean4_file_premises(**tasks)

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



if __name__ == '__main__':
    ray.init(log_to_driver=True)

    test_inputs = json.loads('[{"lemma_id": 214, "statement": "theorem lean_workbook_214 (x y : \\u211d) : (x - y) ^ 2 \\u2265 0  :=  by", "label": ["lean_workbook", "inequality", "algebra", "number_theory"], "iter": 0, "proof": "\\n  rw [sq]\\n  apply mul_self_nonneg"}, {"lemma_id": 314, "statement": "theorem lean_workbook_314 (n : \\u2115) : \\u2211 i in Finset.range (n+1), choose n i = 2 ^ n  :=  by", "label": ["lean_workbook", "number_theory", "algebra", "combinatorics"], "iter": 0, "proof": "\\n  have := Nat.sum_range_choose n\\n  simpa only [Finset.sum_range_id] using this\\n  <;> rfl"}, {"lemma_id": 542, "statement": "theorem lean_workbook_543 : \\u2200 p : \\u2115, p.Prime \\u2192 \\u2200 n : \\u2115, p - 1 \\u2223 p ^ n - 1  :=  by", "label": ["lean_workbook", "number_theory", "divisibility", "proof"], "iter": 0, "proof": "\\n  intro p hp n\\n  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n"}]')
    worker = Lean4Worker.remote(0, 0)
    results=ray.get(worker.run.remote(test_inputs, batched=True))
    print(results)
