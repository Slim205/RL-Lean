import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback

def get_verification_results(old_result1) : 
    custom_id= old_result1['custom_id']
    old_result = old_result1['response']
    system_messages = old_result1['error']
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

    except:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages
        }
    result['custom_id'] = custom_id
    return result


def main(debug=False) : 
    dataset = load_dataset("Slim205/lean_workbook_RL_V8_hinter", split='train')#.select(range(100))
    theorem_list=[]
    proofs=[]
    for example in dataset:
        if example['old_theorem'] != '': 
            proof_text =  example['theorem'] + ' sorry'
            proofs.append(proof_text)
            theorem_list.append(example['problem_id'])
    

    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]

    score_dict = {thm: 0 for thm in theorem_list}
    
    print('Start Verification')
    client = Lean4Client(base_url="http://0.0.0.0:12332",disable_cache=False)
    responses = batch_verify_proof(
        samples=proof_dict,
        client=client,
        timeout=60,
        num_proc=64,
        batch_size=1    )
    if debug : 
        print(responses)
    compilation_results =[]
    for response in responses : 
      compilation_results.append(get_verification_results(response))
    p = 0
    s=0
    list_errors=[]
    for res in compilation_results:
        theorem_name = res['custom_id']
        if res['pass']:
            score_dict[theorem_name] += 1 
            p+=1
        else : 
            print(s)
            list_errors.append(res)
        s+=1
    print(f'Final score : {p} / {len(compilation_results)}')
    import json

    with open("list_errors.jsonl", "w") as f:
        json.dump(list_errors, f, indent=4)
    file_name_txt =f"leanwork_hint_scores.txt"
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
        theorem = example['problem_id']
        if example['old_theorem'] == '' : 
            example['pass'] = True
        else : 
            example['pass'] = score_dict[theorem] == 1 
        inputs_data.append(example)

    hf_dataset = Dataset.from_list(inputs_data)
    hf_dataset.push_to_hub('Slim205/lean_workbook_RL_V8_hinter_pass')
    print(hf_dataset)
if __name__ == '__main__':
    fire.Fire(main)

