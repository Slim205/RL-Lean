ch ="f : ℝ → ℝ h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20 h₁ : Fintype ↑(f ⁻¹' {0}) ⊢ ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20"
ch="""f : ℝ → ℝ
h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20
h₁ : Fintype ↑(f ⁻¹' {0})
h₂ : (f ⁻¹' {0}).toFinset = {2, 10}
⊢ ∏ x ∈ {2, 10}, x = 20
"""
ch="""case zero
f : ℕ → ℕ
h₁ : ∀ (x : ℕ), f (x + 1) = f x + 1
⊢ f 0 = f 0 + 0
case succ f : ℕ → ℕ h₁ : ∀ (x : ℕ), f (x + 1) = f x + 1 n : ℕ ih : f n = f 0 + n ⊢ f (n + 1) = f 0 + (n + 1)
"""
import re
def process_state(ch) : 
    try : 
      goal = ch.split('⊢')[1]
      hypo = ch.split('⊢')[0]
      new_hypo = ''
      if len(hypo) == 0 : 
        return ":" + goal
      for i, x in enumerate(hypo.split(' : ')) :
          if i == 0 : 
            new_hypo = '(' + x + ' : '
            continue

          pos = re.split(r'[ \n]', x)[-1]
          for y in re.split(r'[ \n]', x)[:-1] : 
              new_hypo += y + ' '
          if pos == '' : 
              continue
          if pos[0] != '('  :
              new_hypo += ') ('
          new_hypo += pos + ' : '
      return new_hypo + ") :" + goal
    except : 
        print(ch)
        return ch

print(ch)
import re

def case_0_case_succ(ch) : 
    between_match = re.search(r"case zero(.*?)case succ", ch, flags=re.S)
    between = between_match.group(1).strip() if between_match else ""
    after = ch.split("case succ", 1)[1].strip()  
    between1 = process_state(between)
    after1 = process_state(after)
    return between1,after1

def process_state_final(ch) : 
    if 'case zero' in ch : 
        return case_0_case_succ(ch)
    else : 
        return process_state(ch)