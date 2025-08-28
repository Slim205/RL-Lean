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

def get_results(samples) : 
    results = batch_verify_proof(
    samples=samples,
    client=Lean4Client(base_url="http://holy8a14201:12332",disable_cache=False),
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

# code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Show that there are no integers $x$ and $y$ such that $4x^3 - 7y^3 = 2003$.-/\ntheorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by\n  norm_num\n  ring_nf\n  intro h\n  have h₁ : (x - y) ^ 2 * (4 * x + 4 * y) = 2003 := by\n    nlinarith\n  have h₂ : x - y = 1 ∧ 4 * x + 4 * y = 2003 ∨ x - y = -1 ∧ 4 * x + 4 * y = -2003 := by\n    apply mul_eq_one_or_mul_eq_neg_one_of_mul_eq_one\n    nlinarith\n  cases' h₂ with h₂ h₂ <;> nlinarith"
# print(len(code.split('\n')))
# for x in code.split('\n') : 
#     print(x)
# print(get_results([{'proof' :code  ,'custom_id' : '0' }]))
