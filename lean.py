import json
from datasets import DatasetDict,load_dataset

def get_theorem_name(theorem_str: str) -> str:
    """Extracts theorem name safely from a Lean theorem string."""
    try:
        parts = theorem_str.split("theorem", 1)
        theorem_part = parts[1].strip()
        name = theorem_part.split()[0] if theorem_part else "unknown"
        return name
    except Exception as e:
        print(f"Error parsing theorem: {e}")
        return "error"
def get_original_theorem(theorem_name) : 
    p = 0
    for x in range(len(theorem_name)) : 
        if theorem_name[x] == '_' : 
            p = x
    return theorem_name[:p]

# Path to the JSON file
file_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/mathlib_train/deepseek-SFT/code_compilation.json"

# Load the list of dicts from the file
with open(file_path, "r", encoding="utf-8") as f:
    data = json.load(f)

# Collect all error messages from all items
all_errors = []

list_use_meta_tactics=[]
list_use_meta_tactics_no = []
for entry in data:
    compilation_result = entry.get("compilation_result", {})
    errors = compilation_result.get("errors", [])
    use_meta_tactics = False
    for err in errors:
        msg = err.get("data")
        if msg:
            for x in ['linarith' ,'simp' , 'omega'] : 
                if x in msg :
                    use_meta_tactics=True
    if  use_meta_tactics : 
        list_use_meta_tactics.append(get_original_theorem(compilation_result['custom_id']))
    else : 
        list_use_meta_tactics_no.append(get_original_theorem(compilation_result['custom_id']))

print(len(list_use_meta_tactics))
print(len(list_use_meta_tactics_no))
print(len(list_use_meta_tactics_no) + len(list_use_meta_tactics))
print('===================')

dataset = load_dataset("Slim205/mathlib_RL_v3", split='train')
inputs = []
p = 0
num_ds=0
num_ds2=0
ss = 0
ll = []
for sample in dataset:
    p+=1
    sample['meta_tactic_error'] = False
    theorem_name = get_theorem_name(sample['theorem']) +  str(p)
    if theorem_name in list_use_meta_tactics : 
        sample['meta_tactic_error'] = True
        num_ds+=1
        ss+=1
        for i in range(3) : 
            inputs.append(sample)

    elif  theorem_name in list_use_meta_tactics_no : 
        num_ds2+=1
        inputs.append(sample)

    else : 
        print(theorem_name)
        print(list_use_meta_tactics_no[p-1])
        print(list_use_meta_tactics[p-1])

    

import random
print(inputs[0])

random.shuffle(inputs)
print(inputs[0])
print(num_ds)
print(num_ds2)

from datasets import Dataset
ds_train = Dataset.from_list(inputs)
dataset_test = load_dataset("Slim205/mathlib_RL_v3", split='test')

dataset_test = dataset_test.map(lambda x: {'meta_tactic_error': False})

ds = DatasetDict({'train'  : ds_train , 'test' : dataset_test })
print(ds)

ds.push_to_hub('Slim205/mathlib_RL_v3_meta_tactic_3')
num_ds2=0
ss = 0
ll = []
p = 0
for sample in ds_train:
    p+=1
    if sample['meta_tactic_error'] : 
        ss+=1

    if p % 256 == 0 : 
        ll.append(ss)
        ss = 0
print(ll)
# Print the errors
# print(len(all_errors))
# dic = {}
# for i, error in enumerate(all_errors, 1):
#     if error not in dic.keys() :
#         dic[error] = 1
#     else :
#         dic[error] += 1


# sorted_errors = sorted(dic.items(), key=lambda x: x[1], reverse=True)

# # Print the top 5
# print("Top 5 most frequent errors:\n")
# for i, (err, count) in enumerate(sorted_errors, 1):
#     if count > 10 : 
#         print(f"{i}. Occurred {count} {round(count/len(all_errors)*100)}% times:\n{err}\n{'-'*80}")


# 1. Occurred 2920 11% times:
# application type mismatch
# --------------------------------------------------------------------------------
# 2. Occurred 2119 8% times:
# tactic 'rewrite' failed, did not find instance of the pattern in the target expression
# --------------------------------------------------------------------------------
# 3. Occurred 2092 8% times:
# unsolved goals
# --------------------------------------------------------------------------------
# 4. Occurred 1643 6% times:
# failed to synthesize
# --------------------------------------------------------------------------------
# 5. Occurred 1331 5% times:
# tactic 'rewrite' failed, equality or iff proof expected
# --------------------------------------------------------------------------------
# 6. Occurred 1311 5% times:
# type mismatch
# --------------------------------------------------------------------------------
# 7. Occurred 1101 4% times:
# simp made no progress
# --------------------------------------------------------------------------------
# 8. Occurred 877 3% times:
# invalid field notation, type is not of the form (C ...) where C is a constant
# --------------------------------------------------------------------------------
# 9. Occurred 797 3% times:
# function expected at
# --------------------------------------------------------------------------------
# 10. Occurred 664 3% times:
# no goals to be solved
# --------------------------------------------------------------------------------
# 11. Occurred 210 1% times:
# invalid constructor ⟨...⟩, expected type must be an inductive type 
# --------------------------------------------------------------------------------
# 12. Occurred 205 1% times:
# typeclass instance problem is stuck, it is often due to metavariables
# --------------------------------------------------------------------------------
# 13. Occurred 187 1% times:
# unexpected identifier; expected command
# --------------------------------------------------------------------------------
# 14. Occurred 183 1% times:
# invalid projection, structure expected
# --------------------------------------------------------------------------------
# 15. Occurred 163 1% times:
# The rfl tactic failed. Possible reasons:
# --------------------------------------------------------------------------------
# 16. Occurred 157 1% times:
# tactic 'introN' failed, insufficient number of binders
# --------------------------------------------------------------------------------
# 17. Occurred 142 1% times:
# tactic 'apply' failed, failed to unify
# --------------------------------------------------------------------------------
# 18. Occurred 90 0% times:
# stuck at solving universe constraint
# --------------------------------------------------------------------------------
# 19. Occurred 79 0% times:
# expected token
# --------------------------------------------------------------------------------
# 20. Occurred 78 0% times:
# unknown tactic
# --------------------------------------------------------------------------------
# 21. Occurred 77 0% times:
# tactic 'induction' failed, major premise type is not an inductive type 
# --------------------------------------------------------------------------------
# 22. Occurred 72 0% times:
# tactic 'subst' failed, invalid equality proof, it is not of the form (x = t) or (t = x)
# --------------------------------------------------------------------------------
# 23. Occurred 67 0% times:
# tactic 'assumption' failed
# --------------------------------------------------------------------------------
# 24. Occurred 63 0% times:
# no applicable extensionality theorem found for
# --------------------------------------------------------------------------------
# 25. Occurred 50 0% times:
# overloaded, errors 
# --------------------------------------------------------------------------------
# 26. Occurred 50 0% times:
# invalid binder annotation, type is not a class instance
# --------------------------------------------------------------------------------
# 27. Occurred 50 0% times:
# dsimp made no progress
# --------------------------------------------------------------------------------
# 28. Occurred 49 0% times:
# linarith failed to find a contradiction
# --------------------------------------------------------------------------------
# 29. Occurred 49 0% times:
# don't know how to synthesize implicit argument
# --------------------------------------------------------------------------------
# 30. Occurred 47 0% times:
# redundant binder annotation update
# --------------------------------------------------------------------------------
# 31. Occurred 44 0% times:
# ambiguous, possible interpretations 
# --------------------------------------------------------------------------------
# 32. Occurred 40 0% times:
# tactic 'rewrite' failed, pattern is a metavariable
# --------------------------------------------------------------------------------
# 33. Occurred 37 0% times:
# tactic 'split_ifs' failed, no if-then-else conditions to split
# --------------------------------------------------------------------------------
# 34. Occurred 36 0% times:
# tactic 'rewrite' failed, motive is not type correct
# --------------------------------------------------------------------------------
# 35. Occurred 35 0% times:
# tactic 'simp' failed, nested error:
# --------------------------------------------------------------------------------
# 36. Occurred 34 0% times:
# (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
# --------------------------------------------------------------------------------
# 37. Occurred 34 0% times:
# tactic 'cases' failed, nested error:
# --------------------------------------------------------------------------------
# 38. Occurred 30 0% times:
# fail to show termination for
# --------------------------------------------------------------------------------
# 39. Occurred 29 0% times:
# invalid use of field notation with `@` modifier
# --------------------------------------------------------------------------------
# 40. Occurred 26 0% times:
# invalid argument, variable is not a proposition or let-declaration
# --------------------------------------------------------------------------------
# 41. Occurred 25 0% times:
# unknown identifier 'h'
# --------------------------------------------------------------------------------
# 42. Occurred 22 0% times:
# applyExtTheorem only applies to equations, not
# --------------------------------------------------------------------------------
# 43. Occurred 22 0% times:
# omega could not prove the goal:
# --------------------------------------------------------------------------------
# 44. Occurred 21 0% times:
# unknown identifier 'x'
# --------------------------------------------------------------------------------
# 45. Occurred 20 0% times:
# tactic 'aesop' failed, failed to prove the goal after exhaustive search.
# --------------------------------------------------------------------------------
# 46. Occurred 20 0% times:
# unknown identifier 'a'
# --------------------------------------------------------------------------------
# 47. Occurred 20 0% times:
# unknown identifier 'i'
# --------------------------------------------------------------------------------
# 48. Occurred 19 0% times:
# type expected, got
# --------------------------------------------------------------------------------
# 49. Occurred 17 0% times:
# invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor 
# --------------------------------------------------------------------------------
# 50. Occurred 16 0% times:
# invalid `▸` notation, expected result type of cast is 
# --------------------------------------------------------------------------------
# 51. Occurred 16 0% times:
# cannot coerce
# --------------------------------------------------------------------------------
# 52. Occurred 16 0% times:
# expected type must not contain free or meta variables
# --------------------------------------------------------------------------------
# 53. Occurred 16 0% times:
# expected structure
# --------------------------------------------------------------------------------
# 54. Occurred 15 0% times:
# (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
# --------------------------------------------------------------------------------
# 55. Occurred 15 0% times:
# invalid `▸` notation, the equality
# --------------------------------------------------------------------------------
# 56. Occurred 15 0% times:
# unknown identifier 'p'
# --------------------------------------------------------------------------------
# 57. Occurred 14 0% times:
# rcases: scrutinee has type
# --------------------------------------------------------------------------------
# 58. Occurred 14 0% times:
# numerals are data in Lean, but the expected type is a proposition
# --------------------------------------------------------------------------------
# 59. Occurred 14 0% times:
# tactic 'constructor' failed, target is not an inductive datatype
# --------------------------------------------------------------------------------
# 60. Occurred 13 0% times:
# invalid `▸` notation, argument
# --------------------------------------------------------------------------------
# 61. Occurred 13 0% times:
# invalid field 'trans', the environment does not contain 'Membership.mem.trans'
# --------------------------------------------------------------------------------
# 62. Occurred 13 0% times:
# unknown identifier 'n'
# --------------------------------------------------------------------------------
# 63. Occurred 13 0% times:
# unknown identifier 'l'
# --------------------------------------------------------------------------------
# 64. Occurred 12 0% times:
# invalid constructor ⟨...⟩, insufficient number of arguments, constructs 'Eq.refl' does not have explicit fields, but #2 provided
# --------------------------------------------------------------------------------
# 65. Occurred 12 0% times:
# unknown identifier 'f'
# --------------------------------------------------------------------------------
# 66. Occurred 12 0% times:
# numerals are data in Lean, but the expected type is universe polymorphic and may be a proposition
# --------------------------------------------------------------------------------
# 67. Occurred 11 0% times:
# invalid constructor ⟨...⟩, insufficient number of arguments, constructs 'Eq.refl' does not have explicit fields, but #3 provided