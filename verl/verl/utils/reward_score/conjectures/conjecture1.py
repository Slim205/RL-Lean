from client.client import Lean4Client, batch_verify_proof
import traceback
import re
import requests
import json
import os

def get_verification_results(old_result) : 
    custom_id= old_result['custom_id']
    system_messages = old_result['error']
    old_result = old_result['response']
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
            "system_messages": system_messages,
            "tactics" : []
        }
    result['custom_id'] = custom_id
    return result

def get_complexity_scores(data_list,n,url,url_gpu) : 

    model_inputs = []
    for data in data_list:    
        text = "Complete the following Lean 4 code :\n\n```lean4\n{formal_statement}".format(
                formal_statement=data['proof'][:-6],
            )
        model_inputs.append(text)
    print(model_inputs[0])
    payload = {
        "inputs": model_inputs,
        "pass_n": n
    }
    try:
        response = requests.post(url_gpu, json=payload)
        response.raise_for_status()  
        model_outputs = response.json()            
    except requests.exceptions.RequestException as e:
        print(f"Error calling vLLM server: {e}")
        return []
    
    assert len(model_outputs) == len(model_inputs)

    def extrac_code(inputs):
        try:
            return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)
        except:
            return "None"
    is_correct = {}
    to_inference_codes = []
    for i in range(len(data_list)):
        data_list[i]["model_input"] = model_inputs[i]
        data_list[i]["model_outputs"] = [output for output in model_outputs[i]]
        data_list[i]["full_code"] = [extrac_code(model_inputs[i] + output) for output in model_outputs[i]] 

        to_inference_codes += [{"name": data_list[i]["custom_id"], "code": code} for code in data_list[i]["full_code"]]
        is_correct[data_list[i]["custom_id"]] = 0
    batch_size = 1
    num_proc = 64
    timeout = 60 
    client = Lean4Client(base_url=url, disable_cache=False)

    samples= []
    for i in range(len(to_inference_codes)):
        to_inference_codes[i]["custom_id"] = f"{to_inference_codes[i]['name']}_{i}"
        samples.append({"custom_id": to_inference_codes[i]["custom_id"] , "proof": to_inference_codes[i]["code"] })

    result = batch_verify_proof(
        samples=samples,
        client=client,
        timeout=timeout,
        num_proc=num_proc,
        batch_size=batch_size,
    )

    compilation_results =[]
    for res in result : 
        compilation_results.append(get_verification_results(res))

    compilation_dict = {result['custom_id']: result for result in compilation_results}
    for code in to_inference_codes:
        custom_id = code['custom_id']  
        if custom_id in compilation_dict:
            code['compilation_result'] = compilation_dict[custom_id]
            if code['compilation_result']['complete'] : 
                is_correct[code['name']] +=1
    return is_correct

def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

def get_cosine_sim(code1,code2) : 
    if extract_theorem(code2) == extract_theorem(code1) :
        #print('hello') 
        return 1.
    else : 
     #   return 0.
        from sentence_transformers import SentenceTransformer, util
        model = SentenceTransformer('all-MiniLM-L6-v2')  

        emb1 = model.encode(extract_theorem(code1), convert_to_tensor=True)
        emb2 = model.encode(extract_theorem(code2), convert_to_tensor=True)
        return util.cos_sim(emb1, emb2).item()

# def load_statements(filename):
#     if os.path.exists(filename):
#         with open(filename, 'r') as f:
#             return json.load(f)
#     return []

# def save_statements(statements, filename):
#     with open(filename, 'w') as f:
#         json.dump(statements, f, indent=2)

# def add_new_statements(new_statements, filename):
#     existing = load_statements(filename)
#     combined = existing + new_statements
#     save_statements(combined, filename)

def get_results(data) :
    split = data[0]['split']
    cosine_similarity = {}
    # path = f'/n/netscratch/amin_lab/Lab/slim/statements/{split}_V3.json'
    # statements = load_statements(path)
    # list_deduplicated_statements = []
    # statement_dict = {}
    for sample in data :
        cosine_similarity[sample['custom_id']] =  get_cosine_sim(sample['theorem'] ,sample['proof'])
        # theorem = extract_theorem(sample['proof'])
        # if  theorem not in statements  and theorem not in statement_dict.values()  :
        #     statement_dict[sample['custom_id']] = theorem
        # else : 
        #     list_deduplicated_statements.append(sample['custom_id'])
    samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
    
    url= "http://holy8a14201:12332"

    results = batch_verify_proof(
    samples=samples,
    client=Lean4Client(base_url=url,disable_cache=False),
    timeout=60,
    num_proc=64,
    batch_size=1,
)
    scores = []

    list_eval_complexity=[]
    for x in results :
        res = get_verification_results(x)
        #print(cosine_similarity[res['custom_id']])
        if res['pass'] and cosine_similarity[res['custom_id']] < 0.9  and cosine_similarity[res['custom_id']] > 0.4:  #and res['custom_id'] not in list_deduplicated_statements
            list_eval_complexity.append(res['custom_id']) 
        else : 
            scores.append({'custom_id' :  res['custom_id'] , 'score':   0 })
    new_samples = []
    for sample in samples : 
        if sample['custom_id'] in list_eval_complexity :
            new_samples.append(sample) # {custom_id : custom_id, code : theorem :=by sorry}
    ### get_complexity_scores
    n = 8
   # statements_to_save =[]
    if len(new_samples) > 0 : 
        complexity_scores = get_complexity_scores(new_samples,n,url,'http://holygpu8a22402:8000/generate')
        for x,y in complexity_scores.items() : 
           # print(y/n)
            if y > 0.5 * n or y == 0 :
                score = 0
            else : 
                score = 1
                #statements_to_save.append(statement_dict[x])
            scores.append({'custom_id' :  x , 'score':   score})
    # if len(statements_to_save) > 0 : 
    #     add_new_statements(statements_to_save,path)

    return scores
# header = "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n"
# #code = "theorem euler_4649 (a b : ℕ) (h₁ : a > 1) (h₂ : b > 1) (hab : a + b > 2) (h₃ : a * b = 2 ^ 3 * 3 ^ 4) : ∃ a' b', a' * b' = a * b ∧ a' ≤ 2 * a ∧ b' ≤ 2 * b ∧ a' > 1 ∧ b' > 1 ∧ a' + b' > 2:= by sorry" 
# old_code =  'theorem lean_workbook_39743 :   Int.floor (Real.sqrt 2021) = 44  := by'
# code = "theorem norm_num_tactic_form (n : ℕ) (hn : 1 < n) :    Int.floor (Real.sqrt 2021) = 44 ↔    44 * 44 ≤ 2021 ∧ 2021 < (44 + 1) * (44 + 1) := by sorry"
# #code = "theorem lean_workbook_6696 (x : ℝ) : (x - 1)^2 * (x^2 + x + 1)^2 + (x^2 + x + 1)^2 * (x - 1)^2 + (x^2 + x + 1)^2 * (x^2 - x - 1)^2 ≥ 0  := by sorry"
# # old_code = "theorem lean_workbook_26651 (p q : ℝ) : (p + q) ^ 3 = 4 * (p ^ 3 + q ^ 3) - 3 * (p + q) * (p - q) ^ 2 :=  by"
# # code = "theorem lean_workbook_26651 (p q : ℝ) : (p + q) ^ 3 = 4 * (p ^ 3 + q ^ 3) - 3 * (p + q) * (p - q) ^ 2 := by"
# print(get_results([{'custom_id' : '0', 'proof':header + code , 'theorem' : old_code }]))

