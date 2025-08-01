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

def main(model_name='test/ground_true', n=4, pass_rate=1,debug=False) : 
    dataset = load_dataset("Slim205/mathlib_benchmark_v09_new", split='train').select(range(100))
    theorem_list=[]
    proofs=[]
    p=0
    for example in dataset:
      proof_text =  example['Context'] +  '\n' + example['theorem']   + example['proof']
      proofs.append(proof_text)
      theorem_list.append( get_theorem_name(example['theorem']) + str(p) )
      p+=1
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] } for i,proof in enumerate(proofs) ]

    score_dict = {thm: 0 for thm in theorem_list}
    
    print('Start Verification')
    client = Lean4Client(base_url="http://0.0.0.0:12332")

    responses = batch_verify_proof(
        samples=proof_dict,
        client=client,
        timeout=60,
        num_proc=64,
        batch_size=1    )
    compilation_results =[]
    for response in responses : 
      compilation_results.append(get_verification_results(response))
        
    for res in compilation_results:
      theorem_name = res['custom_id']
      if res['complete']:
          score_dict[theorem_name] += 1 
      else : 
        print('============================================')
        print(res['custom_id'])

    file_name_txt =f"scores_verif.txt"
    with open(file_name_txt, 'w', encoding='utf-8') as f:
        f.write("Theorem Scores:\n")
        f.write("=========================\n")
        
        score_final = 0
        for k, v in score_dict.items():
            line = f'{k} : {v}\n'
            
            f.write(line)
            if v > 0:
                score_final += v
        
        f.write(f"\nTotal theorems with at least one successful proof: {score_final}\n")
        f.write(f"Out of total theorems: {len(theorem_list)} \n")
        f.write(f"Pass rate : {pass_rate} \n")
        print(score_final)

if __name__ == '__main__':
    fire.Fire(main)

    # python mathlib_bench.py --model_name "AI-MO/Kimina-Prover-Preview-Distill-1.5B" --n 10 --pass_rate 32 --is_vllm False --push_to_hf False
    # python mathlib_bench.py --model_name  "deepseek-ai/DeepSeek-Prover-V1.5-SFT" --n 10 --pass_rate 32 --is_vllm False