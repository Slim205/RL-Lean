import json
from vllm import LLM, SamplingParams
from datasets import load_dataset, Dataset, DatasetDict
import nest_asyncio
from client import Lean4Client
from transformers import AutoModelForCausalLM, AutoTokenizer
import fire
import os
from tqdm import tqdm

def save_proofs(proofs, storage_file):
    """Save the proofs list to a file."""
    with open(storage_file, 'w') as f:
        json.dump(proofs, f)

def load_proofs(storage_file):
    """Load the proofs list from a file if it exists."""
    if os.path.exists(storage_file):
        with open(storage_file, 'r') as f:
            return json.load(f)
    return None

def change_result(results):
    transformed_results = []
    for item in results:
        response = item["response"]
        messages = response["messages"]
        transformed = {
            "custom_id": item['custom_id'],
            "complete": (not any(m["severity"] == "error" for m in messages) and 
                        not any("sorry" in m.get("data", "").lower() for m in messages) and
                        not any("failed" in m.get("data", "").lower() for m in messages if m["severity"] == "warning"))
        }
        transformed_results.append(transformed)
    return transformed_results

def generate(model_name, input_list, use_vllm=True):
    if use_vllm:
        llm = LLM(model=model_name, seed=1, trust_remote_code=True, max_model_len=4096, dtype="bfloat16")
        sampling_params = SamplingParams(
        temperature=1, #1
        max_tokens=8096, #2048
        top_p=0.95,
        )
        outputs = llm.generate(input_list, sampling_params)
        proofs = []
        for i,output in enumerate(outputs) : 
          out = output.outputs[0].text
          proof = input_list[i].split('lean4')[1] + output.outputs[0].text.split('`')[0] 
          proofs.append(proof)

    else:
        tokenizer = AutoTokenizer.from_pretrained(model_name)
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            device_map="auto",
            torch_dtype="bfloat16"
        ).eval()
        outputs = []
        for inputs_batch in tqdm(input_list, desc="Processing batches"):
            inputs = tokenizer(inputs_batch, return_tensors="pt").to("cuda:0")
            outputs_batch = model.generate(
                **inputs,
                pad_token_id=tokenizer.eos_token_id,
                max_new_tokens=1024,
                top_p=1,
                do_sample=True
            )
            outputs.append(outputs_batch[0])

        proofs = [
            tokenizer.decode(out, skip_special_tokens=True).split('lean4')[1].split('`')[0]
            for out in outputs
        ]

    return proofs

def extrac_code(inputs):
    try:
        return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)
    except:
        print('extrac_code failed')
        return "None"

def generate_kimina(model_name, input_list, use_vllm=True):
    if use_vllm:
        llm = LLM(model=model_name, seed=1, trust_remote_code=True,swap_space=8, max_model_len=4096, dtype="bfloat16")
        sampling_params = SamplingParams(
        temperature=0.6, #1
        max_tokens=8096, #2048
        top_p=0.95,
        )
        outputs = llm.generate(input_list, sampling_params,use_tqdm=True)
        proofs = []
        for output in outputs : 
          proofs.append(extrac_code(output.outputs[0].text))

    else:
        tokenizer = AutoTokenizer.from_pretrained(model_name)
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            device_map="auto",
            torch_dtype="bfloat16"
        ).eval()
        outputs = []
        for inputs_batch in tqdm(input_list, desc="Processing batches"):
            inputs = tokenizer(inputs_batch, return_tensors="pt").to("cuda:0")
            outputs_batch = model.generate(
                **inputs,
                pad_token_id=tokenizer.eos_token_id,
                max_new_tokens=1024,
                top_p=1,
                do_sample=True
            )
            outputs.append(outputs_batch[0])

        proofs = [
            tokenizer.decode(out, skip_special_tokens=True).split('lean4')[1].split('`')[0]
            for out in outputs
        ]
    return proofs
def get_prompt(theorem,tokenizer,is_kimina):
    LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
    if not is_kimina : 
        return  f"Complete the following Lean 4 code :\n```lean4\n{LEAN4_DEFAULT_HEADER}{theorem}"
    
    prompt = "Think about and solve the following problem step by step in Lean 4."
    prompt += f"\n# Problem:{str()}"""
    prompt += f"\n# Formal statement:\n```lean4\n{LEAN4_DEFAULT_HEADER}\n{theorem}\n```\n"
    messages = [
        {"role": "system", "content": "You are an expert in mathematics and Lean 4."},
        {"role": "user", "content": prompt}
    ]
    text = tokenizer.apply_chat_template(
        messages,
        tokenize=False,
        add_generation_prompt=True
    )
    return text

def get_theorem_name(ch) : 
  return ch.split('theorem')[1].split(' ')[1]

def main(model_name, n, pass_rate, is_vllm=True, push_to_hf=True, m=0, is_re=False, is_kimina=False) : 
    print(model_name, n, pass_rate, is_vllm, push_to_hf, m,is_re,is_kimina)
    assert m < n 
    dataset = load_dataset("Slim205/mathlib_benchmark",split='train').select(range(m,n))
    redundant_list = []
    theorem_list_names=[]
    theorem_list=[]
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    for example in dataset:
        input_text = get_prompt("theorem mathd_algebra_478 (b h v : \u211d) (h\u2080 : 0 < b \u2227 0 < h \u2227 0 < v) (h\u2081 : v = 1 / 3 * (b * h))\n    (h\u2082 : b = 30) (h\u2083 : h = 13 / 2) : v = 65 := by\n",tokenizer,is_kimina)
        redundant_list.extend([input_text] * pass_rate)
        theorem_list_names.append(get_theorem_name(example['theorem']))
        theorem_list.extend([get_theorem_name(example['theorem'])] * pass_rate)
    
    storage_file = f"benchmark/{model_name.split('/')[-1]}_{pass_rate}_{n}.json"
    proofs = load_proofs(storage_file)
    if proofs is None or is_re: 
        if is_kimina : 
            proofs = generate_kimina(model_name, redundant_list, use_vllm=is_vllm)
        else : 
            proofs = generate(model_name, redundant_list, use_vllm=is_vllm)
        save_proofs(proofs,storage_file)
    else : 
        print('Found existing proofs')

    nest_asyncio.apply()
    client = Lean4Client(base_url="http://0.0.0.0:12332")

    batch_size = 10
    proof_dict = [{"proof": proof, "custom_id": theorem_list[i] + 'NNN' + str(i) } for i,proof in enumerate(proofs) ]

    results_data = {
        "input": [],
        "llm_output": [],
        "result": [],
        "proof" : []
    }

    score_dict = {thm: 0 for thm in theorem_list_names}
    appear = {thm: 0 for thm in theorem_list_names}
    empty_proof = {thm: 0 for thm in theorem_list_names}
    for i in range(0, len(proof_dict), batch_size):
        batch = proof_dict[i:i+batch_size]
        response = client.verify(batch, timeout=200 * len(batch))
        compilation_results = change_result(response['results'])
        
        for res in compilation_results:
            theorem_name = res['custom_id'].split('NNN')[0]
            proof_idx = int(res['custom_id'].split('NNN')[1])
            
            # Add to results dataset
            results_data["input"].append(redundant_list[proof_idx])
            results_data["llm_output"].append(proofs[proof_idx])
            results_data["result"].append(1 if res['complete'] else 0)
            try : 
                proof = proofs[proof_idx].split('= by')[1].strip()
                results_data['proof'].append(proof) 
                if len(proof) == 0 : 
                    empty_proof[theorem_name] +=1
            except : 
                results_data['proof'].append("") 
                empty_proof[theorem_name] +=1
            if res['complete']:
                score_dict[theorem_name] += 1 
            appear[theorem_name] += 1

    # Create and push results dataset
    if push_to_hf : 
        results_dataset = Dataset.from_dict(results_data)
        results_dataset.push_to_hub(f"Slim205/math_res_{model_name.split('/')[-1]}_{pass_rate}_{n}")

    file_name_txt =f"benchmark_evaluation/scores_{model_name.split('/')[-1]}_{pass_rate}_{n}.txt"
    print(file_name_txt)
    with open(file_name_txt, 'w', encoding='utf-8') as f:
        f.write("Theorem Scores:\n")
        f.write("=========================\n")
        
        score_final = 0
        for k, v in score_dict.items():
            line = f'{k} : {v} ({empty_proof[k]})\n'
            f.write(line)
            if v > 0:
                score_final += 1
        
        f.write(f"\nTotal theorems with at least one successful proof: {score_final}\n")
        f.write(f"Out of total theorems: {len(theorem_list_names)} \n")
        f.write(f"Pass rate : {pass_rate} \n")

if __name__ == '__main__':
    fire.Fire(main)

    # python mathlib_bench.py --model_name "AI-MO/Kimina-Prover-Preview-Distill-1.5B" --n 10 --pass_rate 32 --is_vllm False --push_to_hf False
    # python mathlib_bench.py --model_name  "deepseek-ai/DeepSeek-Prover-V1.5-SFT" --n 10 --pass_rate 32 --is_vllm False