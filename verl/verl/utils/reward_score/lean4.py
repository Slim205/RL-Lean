from client.client import Lean4Client, batch_verify_proof
import traceback


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

def get_goals(res) : 
    goals = []
    if 'tactics' not in res.keys() : 
        return []
    for x in res['tactics'] : 
        goal = x['goals'].split('⊢')[-1]
        if goal not in goals : 
            goals.append(goal)
    return goals
# def get_results(data) : 
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     for sample in data :
#         split = sample['extra_info']['split']
#         break
#     proof_dict = {}
#     for x in samples : 
#         proof_dict[x['custom_id']] = x['proof']

#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14302:12332",disable_cache=False),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             if split == 'train' : 
#                 score = len(proof_dict[res['custom_id']].split('\n')) 
#             else :
#                 score = 1
#         else :
#             score = 0

#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

# def get_results(data) : 
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     for sample in data :
#         split = sample['extra_info']['split']
#         break

#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14107:12332",disable_cache=False),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             if split == 'train' : 
#                 goals = get_goals(res)
#                 score = len(goals) 
#             else :
#                 score = 1
#         else :
#             score = 0

#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

# def get_results(data) : 
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     for sample in data :
#         split = sample['extra_info']['split']
#         break

#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14107:12332",disable_cache=False),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             score = 1 
#         else :
#             if split == 'train' : 
#                 goals = get_goals(res) 
#                 score = min(len(goals) / 100 , 0.8)
#             else : 
#                 score = 0

#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

# def get_results(data) :
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     extra_info = {}
#     for sample in data :
#         extra_info[sample['custom_id']] =  sample['extra_info'] 

#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14103:12332",disable_cache=False),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             score = 1 
#         elif 'goals' in extra_info[res['custom_id']].keys()  :
#             ground_truth = extra_info[res['custom_id']]['goals']

#             if len(ground_truth) > 1 : 
#                 old_goals = ground_truth[1:] #remove the first goal as it need ot be included in both
#                 goals = get_goals(res) # it can be [] when it timeout
#                 ss = 0
#                 for goal in old_goals : 
#                     if goal in goals :
#                         ss +=1
#                 score = ss/ len(old_goals) 
#             else :
#                 score = 0
#         else :
#             score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

# def get_results(data) :
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     extra_info = {}
#     for sample in data :
#         extra_info[sample['custom_id']] =  sample['extra_info'] 
    
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14302:12332",disable_cache=False),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores=[]
#     for x in results :
#         res = get_verification_results(x)
#         if 'complexity' in extra_info[res['custom_id']].keys() : 
#             complexity = extra_info[res['custom_id']]['complexity']    
#         else : 
#             complexity = 0
#         if res['complete'] : 
             
#             score = 1 - complexity
#         else :
#             score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores



def get_results(samples) : 
    results = batch_verify_proof(
    samples=samples,
    client=Lean4Client(base_url="http://holy8a14401:12332",disable_cache=False),
    timeout=60,
    num_proc=64,
    batch_size=1,
)
    scores = []
    for x in results :
        res = get_verification_results(x)
        if res['complete'] : 
            score = 1 
        else :
            score = 0
        scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
    return scores

# code="""
# import Mathlib
# import Aesop
# set_option maxHeartbeats 0
# open BigOperators Real Nat Topology Rat

# theorem thm1 (x : ℝ ) ( h1 : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 )  (hx :  x ^ 2 + (18 * x + 45) > 0) : 
#     (Real.sqrt (x ^ 2 + (18 * x + 45)) - 5 ) *  (Real.sqrt (x ^ 2 + (18 * x + 45)) + 3 )  = 0 := by 
#     ring
#     rw [ Real.sq_sqrt]
#         · ring_nf at h1 ⊢
#         · linarith

#  """
# #code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Show that there are no integers $x$ and $y$ such that $4x^3 - 7y^3 = 2003$.-/\ntheorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by\n  norm_num\n  ring_nf\n  intro h\n  have h₁ : (x - y) ^ 2 * (4 * x + 4 * y) = 2003 := by\n    nlinarith\n  have h₂ : x - y = 1 ∧ 4 * x + 4 * y = 2003 ∨ x - y = -1 ∧ 4 * x + 4 * y = -2003 := by\n    apply mul_eq_one_or_mul_eq_neg_one_of_mul_eq_one\n    nlinarith\n  cases' h₂ with h₂ h₂ <;> nlinarith"
# goals = [ ' (√(x ^ 2 + (18 * x + 45)) - 5) * (√(x ^ 2 + (18 * x + 45)) + 3) = 0', 
# ' -15 - √(45 + x * 18 + x ^ 2) * 2 + √(45 + x * 18 + x ^ 2) ^ 2 = 0',
# ' -15 - √(45 + x * 18 + x ^ 2) * 2 + (45 + x * 18 + x ^ 2) = 0',
#   ' 30 + x * 18 + (x ^ 2 - √(45 + x * 18 + x ^ 2) * 2) = 0',
#   ' 0 ≤ x ^ 2 + (18 * x + 45)',
#   ' 0 ≤ 45 + x * 18 + x ^ 2'
# ]
# extra_info = {'new_goals' :goals, 'goals_before' : []}
# print(get_results([{'proof' :code  ,'custom_id' : '0' , 'extra_info' : extra_info}]))

# def get_results(samples) : 
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14201:12332"),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         use_meta_tactics = False
#         errors = res.get("errors", [])
#         for err in errors:
#             msg = err.get("data")
#             if msg:
#                 for x in ['linarith' ,'simp' , 'omega'] : 
#                     if x in msg :
#                         use_meta_tactics=True

#         if res['complete'] : 
#             score = 1 
#         elif  use_meta_tactics :
#             score = -1
#         else :
#             score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

# import numpy as np
# def get_results(data) :
#     samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
#     for sample in data :
#         split = sample['extra_info']['split']
#         break
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14201:12332"),
#     timeout=60,
#     num_proc=64,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         errors = res.get("errors", [])
#         pos_errors=[]
#         for err in errors:
#             msg = err.get("endPos")
#             if msg : 
#                 pos_errors.append(msg['line'])
#         if res['complete'] : 
#             score = 1 
#         else :
#             if len(pos_errors)> 0 and split == 'train' : 
#                 score =  np.exp(-40/pos_errors[0] )
#             else :
#                 score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores


# code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Show that there are no integers $x$ and $y$ such that $4x^3 - 7y^3 = 2003$.-/\ntheorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by\n  norm_num\n  ring_nf\n  intro h\n  have h₁ : (x - y) ^ 2 * (4 * x + 4 * y) = 2003 := by\n    nlinarith\n  have h₂ : x - y = 1 ∧ 4 * x + 4 * y = 2003 ∨ x - y = -1 ∧ 4 * x + 4 * y = -2003 := by\n    apply mul_eq_one_or_mul_eq_neg_one_of_mul_eq_one\n    nlinarith\n  cases' h₂ with h₂ h₂ <;> nlinarith"
# print(len(code.split('\n')))
# for x in code.split('\n') : 
#     print(x)
# print(get_results([{'proof' :code  ,'custom_id' : '0' }]))
