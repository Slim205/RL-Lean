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

    
def main(debug=False) : 
    dataset = load_dataset("Slim205/LeanWorkbook", split='train').select(range(1500))
    theorem_list=[]
    proofs=[]
    p=0
    for example in dataset:
        # if example['problem_id'] != 'lean_workbook_10065' : 
        #     continue
        PROVER_PROMPT = 'import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'
        proof_text =  PROVER_PROMPT + example['formal_statement']
        if debug : 
            print(proof_text)
        proofs.append(proof_text)
        theorem_list.append(get_raw_theorem(example['formal_statement']))
        p+=1
    
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]

    score_dict = {thm: 0 for thm in theorem_list}
    
    print('Start Verification')
    client = Lean4Client(base_url="http://holy8a14201:12332")

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
        
    # for res in compilation_results:
    #   theorem_name = res['custom_id']
    #   if res['pass']:
    #       score_dict[theorem_name] += 1 
    #   else : 
    #     print('============================================')
    #     print(res['custom_id'])
    # file_name_txt =f"leanworkbook_scores.txt"
    # with open(file_name_txt, 'w', encoding='utf-8') as f:
    #     f.write("Theorem Scores:\n")
    #     f.write("=========================\n")
        
    #     score_final = 0
    #     for k, v in score_dict.items():
    #         line = f'{k} : {v}\n'
    #         f.write(line)
    #         if v > 0:
    #             score_final += 1
        
    #     f.write(f"\nTotal theorems with at least one successful proof: {score_final}\n")
    #     f.write(f"Out of total theorems: {len(theorem_list)} \n")
    #     print(score_final)
    # inputs_data = []
    # for example in dataset : 
    #     theorem = get_raw_theorem(example['formal_statement'])
    #     if score_dict[theorem] == 1 : 
    #         inputs_data.append(example)
    # hf_dataset = Dataset.from_list(inputs_data)
    # hf_dataset.push_to_hub('Slim205/lean_workbook_RL')
    #print(dataset)
   # print(hf_dataset)
if __name__ == '__main__':
    fire.Fire(main)

