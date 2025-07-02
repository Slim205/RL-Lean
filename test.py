from client.client import Lean4Client, batch_verify_proof
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
#     extra_info = {}
#     for sample in data :
#         extra_info[sample['custom_id']] =  sample['extra_info'] 

#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14102:12332",disable_cache=True),
#     timeout=200,
#     num_proc=100,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             score = 1 
#         else :
#             goals_before = extra_info[res['custom_id']]['goals_before']
#             ground_truth = extra_info[res['custom_id']]['new_goals']

#             if len(ground_truth) > 0 : 
#                 goals = get_goals(res)
#                 new_goals = []
#                 for x in goals : 
#                     if x not in goals_before : 
#                         new_goals.append(x)
                
#                 ss = 0
#                 for goal in ground_truth : 
#                     if goal in new_goals :
#                         ss +=1
#                 score = ss/len(ground_truth)
#             else :
#                 score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

def get_results(data) :
    samples = [{'proof' : sample['proof']  , 'custom_id' : sample['custom_id']  } for sample in data] 
    for sample in data :
        split =   sample['split'] 
        break
    if split == 'train' : 
        disable_cache=True
        url = "http://holy8a14401:12332"
    else : 
        disable_cache=False
        url = "http://holy8a14107:12332"
    
    results = batch_verify_proof(
    samples=samples,
    client=Lean4Client(base_url=url,disable_cache=disable_cache),
    timeout=60,
    num_proc=100,
    batch_size=1,
)
    print(results)
    scores = []
    for x in results :
        res = get_verification_results(x)
        if res['complete'] : 
            score = 1 
        else :
            score = 0
        scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
    return scores

# def get_results(samples) : 
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14401:12332",disable_cache=True),
#     timeout=60,
#     num_proc=100,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         if res['complete'] : 
#             score = 1 
#         else :
#             score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores

code="""
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x^2 - 12 *x + 20)
    (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
  have h₂ : (f ⁻¹' {0}).toFinset = {2, 10} := by
    ext x
    simp only [Set.mem_toFinset, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_setOf_eq,
      h₀, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h₃ : x ^ 2 - 12 * x + 20 = 0 := h
      have h₄ : (x - 2) * (x - 10) = 0 := by linarith
      have h₅ : x - 2 = 0 ∨ x - 10 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₄
      cases h₅ with
      | inl h₅ => exact Or.inl (by linarith)
      | inr h₅ => exact Or.inr (by linarith)
    · intro h
      cases h with
      | inl h => rw [h]; norm_num
      | inr h => rw [h]; norm_num
  rw [h₂]
  norm_num
"""
#code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Show that there are no integers $x$ and $y$ such that $4x^3 - 7y^3 = 2003$.-/\ntheorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by\n  norm_num\n  ring_nf\n  intro h\n  have h₁ : (x - y) ^ 2 * (4 * x + 4 * y) = 2003 := by\n    nlinarith\n  have h₂ : x - y = 1 ∧ 4 * x + 4 * y = 2003 ∨ x - y = -1 ∧ 4 * x + 4 * y = -2003 := by\n    apply mul_eq_one_or_mul_eq_neg_one_of_mul_eq_one\n    nlinarith\n  cases' h₂ with h₂ h₂ <;> nlinarith"
goals = [ ' (√(x ^ 2 + (18 * x + 45)) - 5) * (√(x ^ 2 + (18 * x + 45)) + 3) = 0', 
' -15 - √(45 + x * 18 + x ^ 2) * 2 + √(45 + x * 18 + x ^ 2) ^ 2 = 0',
' -15 - √(45 + x * 18 + x ^ 2) * 2 + (45 + x * 18 + x ^ 2) = 0',
  ' 30 + x * 18 + (x ^ 2 - √(45 + x * 18 + x ^ 2) * 2) = 0',
  ' 0 ≤ x ^ 2 + (18 * x + 45)',
  ' 0 ≤ 45 + x * 18 + x ^ 2'
]
extra_info = {'new_goals' :goals, 'goals_before' : []}
print(get_results([{'proof' :code  ,'custom_id' : '0' , 'split' : 'train'}]))

# def get_results(samples) : 
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14202:12332"),
#     timeout=60,
#     num_proc=100,
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
#             score = -5
#         else :
#             score = 0
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores


# def get_results(samples) : 
#     results = batch_verify_proof(
#     samples=samples,
#     client=Lean4Client(base_url="http://holy8a14202:12332"),
#     timeout=60,
#     num_proc=1,
#     batch_size=1,
# )
#     scores = []
#     for x in results :
#         res = get_verification_results(x)
#         print(res)
#         errors = res.get("errors", [])
#         pos_errors=[]
#         for err in errors:
#             msg = err.get("endPos")
#             pos_errors.append(msg['line'])
#         print(pos_errors)
#         if res['complete'] : 
#             score = 1 
#         else :
#             score = pos_errors[0] / (pos_errors[-1]+ 1)/5
#         scores.append({'custom_id' :  res['custom_id'] , 'score':   score })
#     return scores


# code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Show that there are no integers $x$ and $y$ such that $4x^3 - 7y^3 = 2003$.-/\ntheorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by\n  norm_num\n  ring_nf\n  intro h\n  have h₁ : (x - y) ^ 2 * (4 * x + 4 * y) = 2003 := by\n    nlinarith\n  have h₂ : x - y = 1 ∧ 4 * x + 4 * y = 2003 ∨ x - y = -1 ∧ 4 * x + 4 * y = -2003 := by\n    apply mul_eq_one_or_mul_eq_neg_one_of_mul_eq_one\n    nlinarith\n  cases' h₂ with h₂ h₂ <;> nlinarith"
# print(len(code.split('\n')))
# for x in code.split('\n') : 
#     print(x)
# print(get_results([{'proof' :code  ,'custom_id' : '0' }]))
