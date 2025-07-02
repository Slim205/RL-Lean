from client import Lean4Client
import traceback
from ast_parser import lean4_parser

client = Lean4Client(base_url="http://0.0.0.0:12332",disable_cache=False)

#to prove that the version matters: https://github.com/leanprover-community/mathlib4/blob/v4.20.1/Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean
codde = """
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem thm1 (x : ℝ ) ( h1 : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 )  (hx :  x ^ 2 + (18 * x + 45) > 0) : 
    x = -9 - Real.sqrt 61 ∨ x = -9 + Real.sqrt 61  := by
    have h6 :     x = -9 - Real.sqrt 61 ∨ x = -9 + Real.sqrt 61  := by
      have h5 :     x ^ 2 + 18 * x + 20 = 0  := by
        have h2 :   (Real.sqrt (x ^ 2 + (18 * x + 45)) - 5 ) *  (Real.sqrt (x ^ 2 + (18 * x + 45)) + 3 )  = 0 := by 
          ring
          rw [ Real.sq_sqrt]
          · ring_nf at h1 ⊢
            nlinarith [sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (18 * x + 45) by linarith)]
          · linarith
        have h3 : ( Real.sqrt (x ^ 2 + (18 * x + 45)) + 3  = 0 ∨ Real.sqrt (x ^ 2 + (18 * x + 45)) - 5 = 0 ) := by  
            apply or_iff_not_imp_right.mpr
            intro h3
            apply mul_left_cancel₀ (sub_ne_zero.mpr h3)
            linarith
        cases' h3 with h4 h4
        · nlinarith [Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))]
        · nlinarith [Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))]
      apply or_iff_not_imp_left.mpr
      intro h
      apply mul_left_cancel₀ (sub_ne_zero.mpr h)
      ring_nf at h5 ⊢
      rw [Real.sq_sqrt] <;> nlinarith
    exact h6


theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (hx : ∀ x : ℝ, x ^ 2 + (18 * x + 45) > 0) (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
  have h₂ : f ⁻¹' {0} = { - 9 - Real.sqrt 61, - 9 + Real.sqrt 61} := by 
    ext x
    simp only [Set.mem_toFinset, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_setOf_eq,
      h₀, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h 
      have h5 := thm1 x h (hx x)
      cases' h5 with h5 h5 <;> simp [h5]
    . intro h 
"""

import re

def process_lean_code(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    return text
# implement remove sections


def get_verification_results(old_result,code) : 
    custom_id= old_result['custom_id']
    old_result = old_result['response']
    system_messages = ''
    try:
       # print(old_result['ast'])
        ast_results = lean4_parser(code, old_result['ast']) if 'ast' in old_result and old_result['ast'] else {}

        result = {
            "sorries" : old_result.get('sorries', []), 
            "tactics" : old_result.get('tactics', []),
            "errors" : [m for m in old_result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in old_result.get('messages', []) if m['severity'] == 'warning'],
          #  "infos" : [m for m in old_result.get('messages', []) if m['severity'] == 'info'],
           'ast' :  ast_results,
#            "verified_code" : code,
        #    "system_messages" : system_messages,
         #   "system_errors" : None,
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

comp ="""
ring
        rw [ Real.sq_sqrt]
        · ring_nf at h1 ⊢
          nlinarith [sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (18 * x + 45) by linarith)]
        · linarith
"""

code ="""
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
code ="""
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
theorem lean_workbook_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / Real.sqrt (a ^ 2 + 8 * b * c) + (c + a) / Real.sqrt (b ^ 2 + 8 * c * a) + (a + b) / Real.sqrt (c ^ 2 + 8 * a * b) ≥ 2 := by sorry
"""
#print(code.split('sorry')[0].strip())
#code=  "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- The least common multiple of two numbers is 3720, and their greatest common divisor is 8. Given that one of the numbers is 120, what is the other number? Show that it is 248.-/\ntheorem mathd_numbertheory_222 (b : \u2115) (h\u2080 : Nat.lcm 120 b = 3720) (h\u2081 : Nat.gcd 120 b = 8) :\n    b = 248 := by\n  have h\u2080' : 120 * b = 3720 := by simpa [Nat.lcm] using h\u2080\n  have h\u2081' : Nat.gcd 120 b = 8 := by simpa [Nat.gcd] using h\u2081\n  norm_num at h\u2080' h\u2081' \u22a2\n  omega"
response = client.verify([{"proof": code  , "custom_id": "1nkfdnksdn" }], timeout=30)
from pprint import pprint
res = get_verification_results(response['results'][0],code)
pprint(res)

# ground_truth = [ ' (√(x ^ 2 + (18 * x + 45)) - 5) * (√(x ^ 2 + (18 * x + 45)) + 3) = 0', 
# ' -15 - √(45 + x * 18 + x ^ 2) * 2 + √(45 + x * 18 + x ^ 2) ^ 2 = 0',
# ' -15 - √(45 + x * 18 + x ^ 2) * 2 + (45 + x * 18 + x ^ 2) = 0',
#   ' 30 + x * 18 + (x ^ 2 - √(45 + x * 18 + x ^ 2) * 2) = 0',
#   ' 0 ≤ x ^ 2 + (18 * x + 45)',
#   ' 0 ≤ 45 + x * 18 + x ^ 2'
# ]

def get_goals(res) : 
    goals = []
    for x in res['tactics'] : 
        goal = x['goals'].split('⊢')[-1]
        if goal not in goals : 
            goals.append(goal)
    return goals

pprint(get_goals(res))
# #ground_truth = list(set(ground_truth))
# pprint(get_goals(res) )
# goals = get_goals(res)
# score = 0
# for goal in goals : 
#   if goal in ground_truth :
#     score +=1
# print(score/len(ground_truth))
# print(score)
# print(len(ground_truth))



# ch = comp.split('\n')

# i = 0 
# for i in range(len(ch)) : 
#   lines= ''
#   for x in ch[:i+1] : 
#     if i > 0 : 
#       lines  = lines + '\n' + x
#     else : 
#         lines  = lines  + x

#   response = client.verify([{"proof": code + lines, "custom_id": "1nkfdnksdn" }], timeout=60)
#   res = get_verification_results(response['results'][0],code)
#   if res['complete'] == False : 
#     for error in res['errors'] : 
#       if 'unsolved goals' in error['data'] : 
#         msg = error['data'].split('⊢')[-1]
#         print(msg)

