from client import Lean4Client
import traceback
from ast_parser import lean4_parser

client = Lean4Client(base_url="http://0.0.0.0:12332",disable_cache=False)

import re

def process_lean_code(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    return text
# implement remove sections


def get_verification_results(old_result,code) : 
    custom_id= old_result['custom_id']
    system_messages = old_result['error']
    old_result = old_result['response']
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


code ="""
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x^2 - 12 *x + 20)
    (h₁ : Fintype (f ⁻¹' {0})) : 
    (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
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
coddde ="""import Mathlib
import Aesop

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem lean_workbook_plus_72097_V1 (α : Type u_1 A ) (B : Set α ) (hA : A = ∅ ) : A ×ˢ B = B ×ˢ A ↔ A = ∅ ∨ B = ∅ ∨ A = B := by sorry
"""
codex = """
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem le_total_2 (x : ℝ) :     3 / 4 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z ∨     x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z ≤ 3 / 4 := by
  cases' le_total (x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z) (3 / 4) with h h <;> simp_all
"""

codex = """
import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem lean_workbook_plus_70767 : ∃ k : ℤ, k < 1000 ∧ |k * Real.sqrt 2 - ↑⌊k * Real.sqrt 2⌋| < 1 / 1000   :=  by

  use 0
  simp [abs_of_nonneg]
"""
response = client.verify([{"proof": codex  , "custom_id": "1nkfdnksdn" }], timeout=60)
from pprint import pprint
res = get_verification_results(response['results'][0],code)
pprint(res)
print(len(res['errors']))

# import re
# path= '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/leanworkbook_test/deepseek-SFT-3/code_compilation.json'
# import json

# with open(path, 'r') as json_file:
#     codes = json.load(json_file)

# for x in codes : 
#   if 'lean_workbook_50790' == x['name'] and x['compilation_result']['complete'] : 
#     print(x['code']) 
# def process_state(ch) : 
#     goal = ch.split('⊢')[1]
#     hypo = ch.split('⊢')[0]

#     new_hypo = ''
#     for x in hypo.split(' : ') : 
#         pos = re.split(r'[ \n]', x)[-1]
#         for y in re.split(r'[ \n]', x)[:-1] : 
#             new_hypo += y + ' '
#         if pos == '' : 
#             continue
#         if pos[0] != '('  :
#             new_hypo += ') ('
#         new_hypo += pos + ' : '
#     return new_hypo[2:] + ") :" + goal
# ch ="f : ℝ → ℝ h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20 h₁ : Fintype ↑(f ⁻¹' {0}) ⊢ ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20"

#theorem aime_1983_p3 f : ℝ → ℝ h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20 h₁ : Fintype ↑(f ⁻¹' {0}) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by sorry
#theorem aime_1983_p3 (f : ℝ → ℝ) (h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20) (h₁ : Fintype ↑(f ⁻¹' {0})) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by sorry
#theorem aime_1983_p3 (f : ℝ → ℝ) (h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20) (h₁ : Fintype ↑(f ⁻¹' {0}) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by sorry
#print(code.split('sorry')[0].strip())
#code=  "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- The least common multiple of two numbers is 3720, and their greatest common divisor is 8. Given that one of the numbers is 120, what is the other number? Show that it is 248.-/\ntheorem mathd_numbertheory_222 (b : \u2115) (h\u2080 : Nat.lcm 120 b = 3720) (h\u2081 : Nat.gcd 120 b = 8) :\n    b = 248 := by\n  have h\u2080' : 120 * b = 3720 := by simpa [Nat.lcm] using h\u2080\n  have h\u2081' : Nat.gcd 120 b = 8 := by simpa [Nat.gcd] using h\u2081\n  norm_num at h\u2080' h\u2081' \u22a2\n  omega"
#pprint(res)


# new_codes=[]
# for i,x in enumerate(res['tactics']) : 
#   new_theorem =  x['goals']
#  # print(new_theorem)
#   new_code =f"""
# import Mathlib
# import Aesop

# set_option maxRecDepth 100000
# set_option maxHeartbeats 0
# open BigOperators Real
# Nat Topology Rat

# theorem aime_1983_p3 {process_state(new_theorem)} := by sorry
# """
#   new_codes.append({"proof": new_code  , "custom_id": i})

# new_theorems=[]
# response = client.verify(new_codes, timeout=60)
# from pprint import pprint
# #res = get_verification_results(response['results'][0],'')

# for res in response['results'] :
#   x = get_verification_results(res,'')
 
#   if x['pass'] : 
#     #print(x['custom_id'])
#     print(new_codes[x['custom_id']]['proof'].split('theorem aime_1983_p3 ')[1])
#     # if new_codes[x['custom_id']]['proof'] not in new_theorems : 
#     #   new_theorems.append(new_codes[x['custom_id']]['proof'])


# codde = """
# import Mathlib
# import Aesop
# set_option maxHeartbeats 0
# open BigOperators Real Nat Topology Rat

# theorem thm1 (x : ℝ ) ( h1 : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 )  (hx :  x ^ 2 + (18 * x + 45) > 0) : 
#     x = -9 - Real.sqrt 61 ∨ x = -9 + Real.sqrt 61  := by
#     have h6 :     x = -9 - Real.sqrt 61 ∨ x = -9 + Real.sqrt 61  := by
#       have h5 :     x ^ 2 + 18 * x + 20 = 0  := by
#         have h2 :   (Real.sqrt (x ^ 2 + (18 * x + 45)) - 5 ) *  (Real.sqrt (x ^ 2 + (18 * x + 45)) + 3 )  = 0 := by 
#           ring
#           rw [ Real.sq_sqrt]
#           · ring_nf at h1 ⊢
#             nlinarith [sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (18 * x + 45) by linarith)]
#           · linarith
#         have h3 : ( Real.sqrt (x ^ 2 + (18 * x + 45)) + 3  = 0 ∨ Real.sqrt (x ^ 2 + (18 * x + 45)) - 5 = 0 ) := by  
#             apply or_iff_not_imp_right.mpr
#             intro h3
#             apply mul_left_cancel₀ (sub_ne_zero.mpr h3)
#             linarith
#         cases' h3 with h4 h4
#         · nlinarith [Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))]
#         · nlinarith [Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))]
#       apply or_iff_not_imp_left.mpr
#       intro h
#       apply mul_left_cancel₀ (sub_ne_zero.mpr h)
#       ring_nf at h5 ⊢
#       rw [Real.sq_sqrt] <;> nlinarith
#     exact h6


# theorem aime_1983_p3 (f : ℝ → ℝ)
#     (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
#     (hx : ∀ x : ℝ, x ^ 2 + (18 * x + 45) > 0) (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
#   have h₂ : f ⁻¹' {0} = { - 9 - Real.sqrt 61, - 9 + Real.sqrt 61} := by 
#     ext x
#     simp only [Set.mem_toFinset, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_setOf_eq,
#       h₀, Finset.mem_insert, Finset.mem_singleton]
#     constructor
#     · intro h 
#       have h5 := thm1 x h (hx x)
#       cases' h5 with h5 h5 <;> simp [h5]
#     . intro h 
# """
# comp ="""
# ring
#         rw [ Real.sq_sqrt]
#         · ring_nf at h1 ⊢
#           nlinarith [sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (18 * x + 45) by linarith)]
#         · linarith
# """