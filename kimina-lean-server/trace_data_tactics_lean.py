import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback
def get_verification_results(old_result) : 
    custom_id= old_result['custom_id']
    system_messages= old_result['error']
    old_result = old_result['response']
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
    if 'tactics' not in res.keys() :
      return []
    for x in res['tactics'] : 
        goal = x['goals'].split('⊢')[-1]
        if goal not in goals : 
            goals.append(goal)
    return goals

def main3(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/lean_workbook_RL_V8_goals", split='train')
    def filter1(z) : 
      return len(z['goals']) > 1
    print(dataset.filter(filter1))
def main2(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/lean_workbook_hard", split='train')

    with open('compilation_v20_hard.json', 'r') as json_file:
        compilation_results = json.load(json_file)
    dict_res = {}
    for res in compilation_results:
      dict_res[res['custom_id']] = res

    new_inputs=[]
    for example in dataset:
      theorem =  example['problem_id'] 
      example['goals'] = get_goals(dict_res[theorem])
      new_inputs.append(example)

    train_ds = Dataset.from_list(new_inputs)
    def map1(s) :
      s['goals'] = ['']
      return s
    #test_ds = load_dataset("Slim205/lean_workbook_RL_V8", split='test').map(map1)
    #print(test_ds)
    #print(train_ds)
    #hf_dataset = DatasetDict({'train' : train_ds , 'test' : test_ds})
    train_ds.push_to_hub('Slim205/lean_workbook_hard_goals')


def main(debug=False) : 
    dataset = load_dataset("Slim205/lean_workbook_hard", split='train')#.select(range(100))
    theorem_list=[]
    proofs=[]
    p=0
    for example in dataset:
      proof_text =   example['theorem'] + '\n' +  example['proof']
      proofs.append(proof_text)
      if debug : 
        print(proof_text)
      theorem_list.append( example['problem_id'] )
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]
    
    client = Lean4Client(base_url="http://0.0.0.0:12332",disable_cache=False)

    responses = batch_verify_proof(
        samples=proof_dict,
        client=client,
        timeout=200,
        num_proc=64,
        batch_size=1    )
    if debug : 
        print(responses)
    compilation_results =[]
    for response in responses : 
      compilation_results.append(get_verification_results(response))

    with open('compilation_v20_hard.json', 'w') as json_file:
        json.dump(compilation_results, json_file, indent=4)

    for res in compilation_results:
      if not res['complete']:
        print('============================================')
        print(res['custom_id'])


if __name__ == '__main__':
    fire.Fire(main2)
