import json
from transformers import AutoModelForCausalLM, AutoTokenizer

def change_result(results):
    transformed_results = []
    for item in results:
        response = item["response"]
        messages = response["messages"]
        for m in messages :     
            print(m['data'])
        transformed = {
            "custom_id" : item['custom_id'],
            "complete": (not any(m["severity"] == "error" for m in messages) and 
                        not any("sorry" in m.get("data", "") for m in messages) and
                        not any("failed" in m.get("data", "") for m in messages if m["severity"] == "warning"))
        }
        transformed_results.append(transformed)

    return transformed_results

def read_jsonl_file(file_path):
    """Read a .jsonl file and return a list of dictionaries."""
    with open(file_path, 'r', encoding='utf-8') as f:
        return [json.loads(line) for line in f]

data_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/datasets/minif2f.jsonl"
dataset = read_jsonl_file(data_path)
print(len(dataset))

pass_number=1
input_list =[]
max_data_points = 2
idx = 0
theorem_list_names=[]
for data in dataset:
    if data['split'] == 'test' :
        idx+=1
        if idx ==1 :
            continue
        header = data['header']
        theorem0 = data['formal_statement']  
        hint =  'The rest modulo 3 of y^2 is either 0 or 1'
#        theorem2  ="theorem no_solutions_2x_plus_4y_eq_5 (x y : ℤ) : 2 * x + 4 * y ≠ 5 := by"
        theorem1 = 'theorem mathlib_200000_test (x y : ℤ) :  y^2 - 3 * x  ≠ 11 := by'
        theorem2 ="theorem square_mod_three (y : ℤ) : y^2 % 3 = 0 ∨ y^2 % 3 = 1 := by"
       # hint =f"/-{theorem2} -/"
        input_text = f"Complete the following Lean 4 code :\n```lean4\n{header}\n{theorem1}\n"
      #  input_text = f"Complete the following Lean 4 code :\n```lean4\n {theo_proof}```"
        print(input_text)
        for i in range(pass_number) : 
            input_list.append(input_text) 
            theorem_list_names.append(data['name'])       
        if idx == max_data_points :
            break 
print('Number of inputs : ',len(input_list))

assert len(input_list) > 0
model_name = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"  
tokenizer = AutoTokenizer.from_pretrained(model_name)

#model = AutoModelForCausalLM.from_pretrained(model_name,device_map="auto",  torch_dtype="bfloat16"  ).eval()

#batch_size = 1
#batched_input_list = [input_list[i:i +batch_size] for i in range(0,len(input_list)-1,batch_size )]
outputs = []
from tqdm import tqdm
for inputs_batch in tqdm(input_list) : 
    continue
    inputs = tokenizer(inputs_batch, return_tensors="pt").to("cuda:0")
    outputs_batch = model.generate(
        **inputs,
            pad_token_id=tokenizer.eos_token_id,
        max_length=1024,
    top_p=1,
    do_sample=True
    )
    outputs.append(outputs_batch[0])
    
print(len(outputs))

# proofs = [
#     tokenizer.decode(out, skip_special_tokens=True).split('lean4')[1].split('`')[0]
#     for out in outputs
# ]
proof0="""
import Mathlib.Tactic

theorem mathlib_200000_test (x y : ℤ) : y^2 - 3 * x ≠ 11 := by
  intro h
  -- Show that y² ≡ 2 mod 3
  have h_mod : y^2 % 3 = 2 := by
    rw [← h, sub_eq_add_neg, add_comm, add_assoc, neg_mul, add_zero]
    rw [Int.add_emod]
    simp only [Int.mul_emod, Int.emod_emod, zero_add]
    norm_num
  
  -- Show squares mod 3 can only be 0 or 1
  have square_mod3 : y^2 % 3 = 0 ∨ y^2 % 3 = 1 := by
    have h_range : -3 < y % 3 ∧ y % 3 < 3 := by
      exact Int.emod_lt_of_pos y (by decide : (0 : ℤ) < 3)
    interval_cases (y % 3)
    · left  -- case 0
      simp [sq]
    · right  -- case 1
      rfl
    · right  -- case 2
      simp [sq, show (2 * 2) % 3 = 1 by rfl]
    · right  -- case -1
      simp [sq, show ((-1) * (-1)) % 3 = 1 by rfl]
    · right  -- case -2
      simp [sq, show ((-2) * (-2)) % 3 = 1 by rfl]
  
  -- Obtain contradiction
  cases square_mod3 with
  | inl h0 => rw [h0] at h_mod; norm_num at h_mod
  | inr h1 => rw [h1] at h_mod; norm_num at h_mod  """
proofs=[proof0]

with open('lean_proofs1.txt', 'w', encoding='utf-8') as f:
    for i, proof in enumerate(proofs, 1):
        f.write(f"===== Proof {i} =====\n")
        f.write(proof)  
        f.write("\n\n")  
print('====================')
print(proofs[0])

import nest_asyncio
from client import Lean4Client
nest_asyncio.apply()
client = Lean4Client(base_url="http://0.0.0.0:12332")

batch_size=16 
proof_dict = [{"proof": proof, "custom_id": theorem_list_names[i] + 'NNN' + str(i) } for i,proof in enumerate(proofs) ]

score_dict={thm : 0 for thm in theorem_list_names}
appear =  {thm : 0 for thm in theorem_list_names}
for i in range(0,len(proof_dict),batch_size) : 
    batch = proof_dict[i:i+batch_size]
    response = client.verify(batch, timeout=200 * len(batch))
    compilation_results = change_result(response['results'])
    for  res in compilation_results : 
        if res['complete'] : 
            score_dict[res['custom_id'].split('NNN')[0]] += 1 
        appear[res['custom_id'].split('NNN')[0]] += 1 

for k,v in appear.items() : 
    assert v == pass_number
print('=========================')
print('final score')
for k,v in score_dict.items() : 
    print(f'{k} : {v}')

    #### on a lancé 4 + 1 * 8 =12 gpus ==>  3 * fois les ressources (estimation 1 jour et quart pour 1 round) 
    #### 4 + 1  * 16 = 20 gpus ==> 5 *plus 
    #### 4 * 8 = 32 gpus ==> 8 fois plus ==>  12h
    #### 4 * 16 = 64 gpus ==> 16 fois plus : 6h