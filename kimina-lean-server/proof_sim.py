from client.client import Lean4Client, batch_verify_proof
import traceback
import re
import requests
import json
import os
from ast_parser import lean4_parser

def get_verification_results(old_result,code) : 
    custom_id= old_result['custom_id']
    system_messages = old_result['error']
    old_result = old_result['response']
    try:
        ast_results = lean4_parser(code, old_result['ast']) if 'ast' in old_result and old_result['ast'] else {}

        result = {
            "sorries" : old_result.get('sorries', []), 
            "tactics" : old_result.get('tactics', []),
            "errors" : [m for m in old_result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in old_result.get('messages', []) if m['severity'] == 'warning'],
            "infos" : [m for m in old_result.get('messages', []) if m['severity'] == 'info'],
            'ast' :  ast_results,
            "verified_code" : code,
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
            'ast' : {'premises' : []}
        }
    result['custom_id']  =custom_id
    return result


path = '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/conjecture/conjecture_V9_200-test'
path = '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/conjecture/STP-test-leanworkbook'
path_to_proof = path + '/complexity_scores/code_compilation.json'
with open(path_to_proof, 'r', encoding='utf-8') as f:
    data = json.load(f)

samples = []
get_proof = {entry['name'] : [] for entry in data}
for entry in data:
    name = entry['name']
    code = entry['code']
    comp_res = entry['compilation_result']
    if  len(get_proof[name])< 1 and comp_res['complete']  : 
        samples.append({'proof' : code , 'custom_id' : name + f'$$$$$$$$${len(get_proof[name])}'  })
        get_proof[name].append(code)

url = "http://0.0.0.0:12332"
results = batch_verify_proof(
    samples=samples,
    client=Lean4Client(base_url=url,disable_cache=False),
    timeout=60,
    num_proc=32,
    batch_size=1,
    )

tactics_all = {entry['name'] : [] for entry in data}
for x in results :
    theorem_name = x['custom_id'].split('$$$$$$$$$')[0] 
    theorem_number = int(x['custom_id'].split('$$$$$$$$$')[1])
    res = get_verification_results(x,get_proof[theorem_name][theorem_number])
    if 'premises' in res['ast'].keys()  :
        # if len(res['ast']['premises'] ) == 0 :
        #     print(res['complete'])
        for y in res['ast']['premises'] : 
            tactics_all[theorem_name].append(y['fullName'])

p = 0
d_keys = {}
for d in tactics_all.keys() : 
    tactics_all[d] = list(set(tactics_all[d]))
    if len(tactics_all[d]) > 0 : 
        p+=1 
        if p< 10 :
            print(tactics_all[d] )
        ch = ''
        for xx in tactics_all[d] : 
            if xx in d_keys.keys() : 
                d_keys[xx] += 1
            else :
                d_keys[xx] = 1

for d in d_keys.keys() : 
    d_keys[d] = round(d_keys[d] / p,5)
print(p)

print(d_keys)
print('==')

print(max(d_keys.values()))
print('==')


# 353 {'And': 212, 'Iff': 296, 'Not': 353, 'Or': 170, 'Membership.mem': 7, 'Ne': 13, 'PSigma': 7, 'Inter.inter': 1, 'Exists': 13, 'EmptyCollection.emptyCollection': 2, 'Fin': 1, 'Nat': 2, 'exists_prop': 9, 'Dvd.dvd': 10, 'True': 2, 'gt_iff_lt': 9, 'not_and': 5, 'Nat.succ_mul': 1, 'true_and': 4, 'not_false_iff': 2, 'not_exists': 1, 'not_true': 2, 'Singleton.singleton': 2, 'ge_iff_le': 6, 'forall_const': 1, 'Insert.insert': 1, 'Union.union': 1, 'and_imp': 1, 'Bool.false': 1, 'and_true': 4, 'false_and': 1, 'false_or': 1, 'Bool.true': 1, 'Iff.mp': 1, 'or_comm': 1, 'or_assoc': 1, 'not_or': 2, 'Int.add_comm': 1, 'or_false': 1, 'or_true': 1, 'eq_self_iff_true': 1, 'true_or': 1, 'Nat.dvd_iff_mod_eq_zero': 1, 'Exists.intro': 1, 'Int': 1}

#160 {'And': 94, 'Exists': 32, 'And.intro': 8, 'Exists.intro': 6, 'dite': 6, 'Ne': 9, 'Fin.val': 1, 'PSigma': 3, 'Not': 20, 'EmptyCollection.emptyCollection': 1, 'Fin': 1, 'Membership.mem': 6, 'Or': 27, 'Dvd.dvd': 4, 'Iff': 15, 'Or.inl': 4, 'Nat': 1, 'True.intro': 4, 'True': 8, 'And.right': 1, 'False': 1, 'exists_prop': 1, 'Or.inr': 2, 'Or.intro_right': 1, 'rfl': 1, 'Bool.true': 1, 'Iff.intro': 1, 'Int': 1, 'gt_iff_lt': 1, 'and_imp': 1}

#237 {'Ne': 20, 'Exists': 187, 'And': 171, 'Exists.intro': 84, 'And.intro': 30, 'Iff': 12, 'Iff.intro': 2, 'EmptyCollection.emptyCollection': 1, 'Fin': 1, 'Or': 27, 'And.right': 2, 'And.left': 3, 'Membership.mem': 8, 'Dvd.dvd': 3, 'ite': 2, 'Not': 1, 'dite': 4, 'False': 1, 'PSigma': 2, 'Singleton.singleton': 2, 'HasSubset.Subset': 1, 'Insert.insert': 1, 'Or.inl': 1, 'rfl': 1, 'Nat.le_refl': 1, 'Nat.gcd': 1, 'Nat.lcm': 1, 'Nat.mul_succ': 1, 'Or.inr': 1}

# 196 {'Or': 82, 'And': 115, 'Exists': 22, 'Ne': 15, 'Insert.insert': 2, 'Membership.mem': 14, 'Fin': 2, 'Iff': 16, 'Dvd.dvd': 9, 'Or.inl': 13, 'And.intro': 12, 'dite': 10, 'Exists.intro': 8, 'Or.inr': 5, 'Nat.mul_sub_left_distrib': 1, 'Nat.mul_sub_right_distrib': 1, 'Nat.mul_comm': 1, 'Nat.sub_sub': 1, 'Not': 13, 'Nat.mul_div_cancel_left': 1, 'And.left': 2, 'or_comm': 1, 'not_and': 1, 'Singleton.singleton': 2, 'Nat': 2, 'PSigma': 2, 'exists_prop': 2, 'Fin.val': 1, 'Or.intro_right': 2, 'Subtype': 1, 'Iff.intro': 4, 'Or.intro_left': 3, 'or_iff_left_iff_imp': 1, 'or_iff_right_iff_imp': 1, 'not_exists': 1, 'not_or': 1, 'gt_iff_lt': 1, 'and_imp': 1, 'eq_comm': 1}