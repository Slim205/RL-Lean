import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback
def get_verification_results(old_result) : 
    custom_id= old_result['custom_id']
    old_result = old_result['response']
    system_messages = ''
    try:
        result = {
            "sorries" : old_result.get('sorries', []), 
            "tactics" : old_result.get('tactics', []),
            "errors" : [m for m in old_result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in old_result.get('messages', []) if m['severity'] == 'warning'],
        }
        result['pass'] = not result['errors']
        result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
        result['verify_time']  = old_result['time']
    except:

        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages
        }
    result['custom_id']  =custom_id
    return result



def get_theorem_name(ch) : 
  return ch.split('theorem')[1].split(' ')[1]

def get_goals(res) : 
    goals = []
    for x in res['tactics'] : 
        goal = x['goals'].split('⊢')[-1]
        if goal not in goals : 
            goals.append(goal)
    return goals

def main3(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/mathlib_RL_v3_traced1", split='train')
    print(dataset['goals'][0])
def main2(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/mathlib_RL_v3", split='train')

    with open('compilation_results.json', 'r') as json_file:
        compilation_results = json.load(json_file)
    dict_res = {}
    for res in compilation_results:
      dict_res[res['custom_id']] = res

    new_inputs=[]
    p=0
    for example in dataset:
      theorem =  get_theorem_name(example['theorem']) + str(p) 
      p+=1
      example['goals'] = get_goals(dict_res[theorem])
      new_inputs.append(example)

    hf_dataset = Dataset.from_list(new_inputs)
    hf_dataset.push_to_hub('Slim205/mathlib_RL_v3_traced1')

def main4(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/mathlib_RL_v3_traced1", split='train')

    with open('compilation_results_sorry.json', 'r') as json_file:
        compilation_results = json.load(json_file)
    dict_res = {}
    for res in compilation_results:
      dict_res[res['custom_id']] = res

    new_inputs=[]
    p=0
    for example in dataset:
      theorem =  get_theorem_name(example['theorem']) + str(p) 
      p+=1
      example['goals_before'] = get_goals(dict_res[theorem])
      new_inputs.append(example)

    hf_dataset = Dataset.from_list(new_inputs)
    hf_dataset.push_to_hub('Slim205/mathlib_RL_v3_traced2')

def main(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/mathlib_RL_v3", split='test').select(range(300,607))
    theorem_list=[]
    proofs=[]
    p=0
    for example in dataset:
      proof_text =  example['Context'] +  '\n'  + example['theorem'] + example['proof']
      proofs.append(proof_text)
      if debug : 
        print(proof_text)
      theorem_list.append( get_theorem_name(example['theorem']) + str(p) )
      p+=1
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]
    
    client = Lean4Client(base_url="http://holy8a14102:12332",disable_cache=True)

    responses = batch_verify_proof(
        samples=proof_dict,
        client=client,
        timeout=60,
        num_proc=100,
        batch_size=1    )
    if debug : 
        print(responses)
    compilation_results =[]
    for response in responses : 
      compilation_results.append(get_verification_results(response))

    with open('compilation_res_tests.json', 'w') as json_file:
        json.dump(compilation_results, json_file, indent=4)

    for res in compilation_results:
      if not res['complete']:
        print('============================================')
        print(res['custom_id'])


if __name__ == '__main__':
    fire.Fire(main)
