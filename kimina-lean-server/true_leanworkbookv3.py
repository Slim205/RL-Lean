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
            "infos" : [m for m in old_result.get('messages', []) if m['severity'] == 'info'],
            "system_messages" : system_messages,
            "system_errors" : None,
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

def get_raw_theorem(prompt: str) -> str:
    """More robust theorem extraction with error handling"""
    try:
        return 'lean_workbook_' + prompt.split('lean_workbook')[1].split(' ')[0][1:] # Plus 38K
    except (IndexError, AttributeError):
        return None

# lean_workbook_27138 max recurrsion
# lean_workbook_plus_13461 ok 
# lean_workbook_plus_71132 import Mathlib.Data.Nat.Dist
# lean_workbook_9310 ok
# lean_workbook_29849 ok
# lean_workbook_plus_9265 ok
# lean_workbook_plus_33784
# lean_workbook_18212 ok
def main(debug=False) : 
    dataset = load_dataset("Slim205/lean_workbook_goedel", split='train')#.select(range(10))
    theorem_list=[]
    proofs=[]
    p=0
    for example in dataset:
        # if get_raw_theorem(example['input']) != 'lean_workbook_plus_33784' :
        #     continue
        proof_text = 'import Mathlib\nimport Aesop\n' + 'set_option maxRecDepth 100000'+  example['theorem'].split('Aesop')[1] + '\n' + example['proof']
     #   proof_text =  example['input'] + '\n' + example['proof']

        if debug : 
            print(proof_text)
        proofs.append(proof_text)
        theorem_list.append(get_raw_theorem(example['theorem']))
        p+=1
    if p == 1 :
        print(proof_text)
        debug = True
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]

    score_dict = {thm: 0 for thm in theorem_list}
    
    print('Start Verification')
    client = Lean4Client(base_url="http://holy8a14201:12332",disable_cache=False)
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
    p = 0
    for res in compilation_results:
        theorem_name = res['custom_id']
        if res['complete']:
            score_dict[theorem_name] += 1 
            p+=1
    print(f'Final score : {p} / {len(compilation_results)}')
    file_name_txt =f"leanworkbook_godel_scores.txt"
    with open(file_name_txt, 'w', encoding='utf-8') as f:
        f.write("Theorem Scores:\n")
        f.write("=========================\n")
        
        score_final = 0
        for k, v in score_dict.items():
            line = f'{k} : {v}\n'
            f.write(line)
            if v > 0:
                score_final += 1
        
        f.write(f"\nTotal theorems with at least one successful proof: {score_final}\n")
        f.write(f"Out of total theorems: {len(theorem_list)} \n")
        print(score_final)
    inputs_data = []
    for example in dataset : 
        theorem = get_raw_theorem(example['theorem'])
        if score_dict[theorem] == 1 : 
            inputs_data.append(example)
        else : 
            print(theorem)
    print(len(inputs_data))
    hf_dataset = Dataset.from_list(inputs_data)
    hf_dataset.push_to_hub('Slim205/lean_workbook_RL_goedel_v4')
    print(hf_dataset)
if __name__ == '__main__':
    fire.Fire(main)

