import traceback
import re
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
def format_lines(text: str) -> str:
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    return " ".join(f"({ln})" for ln in lines) 

def post_process(text) : 
    text =  text.replace('✝', 'o')
    text =  text.replace('π', 'Real.pi')
    text =  text.replace('o¹', 'oo')
    text =  text.replace('o²', 'ooo')
    
    return text
def process_state(ch) : 
    try :
        goal = ch.split('⊢')[1]
        hypo = ch.split('⊢')[0]
        new_hypo = ''        
        if len(hypo) == 0 : 
            return post_process(":" + goal)
        if '\n' in hypo : 
            hypo = hypo.replace(':\n', ':')
            hypo = hypo.replace('∧\n', '∧')
            hypo = hypo.replace('→\n', '→')
            hypo = hypo.replace('=\n', '=')
            hypo = hypo.replace('>\n', '>')
            hypo = hypo.replace('*\n', '*')
            hypo = hypo.replace('+\n', '+')
            hypo = hypo.replace('/\n', '/')

            return post_process(format_lines(hypo) + ':' + goal)

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
        return post_process(new_hypo + ") :" + goal)
    except : 
        print(ch)
        print(traceback.format_exc())
        return ch

def process_state_final(ch) : 
    try : 
        if 'case' in ch : 
            pattern = re.compile(
                r'^case\s+(\S+)\s*(.*?)(?=^case\s|\Z)',       
                flags=re.MULTILINE | re.DOTALL
            )

            list_hints = []                                        
            for m in pattern.finditer(ch):
                name = m.group(1)                             
                body = m.group(2).strip()                   
                list_hints.append(process_state(body))
            return list_hints
        elif len(ch.split('⊢')) > 2 : 
            final_result=[]
            for i in range( len(ch.split('⊢'))-1) : 
                hypo = ch.split('⊢')[i]
                if '\n' in ch.split('⊢')[i] : 
                    hypo = ''
                    for x in ch.split('⊢')[i].split('\n')[1:] : 
                        hypo += '\n' + x 
                    hypo = hypo[1:]
                
                goal = ch.split('⊢')[i+1].split('\n')[0]
                final_result.append(process_state(hypo + ' ⊢ ' + goal))
            return final_result
        else : 
            return [process_state(ch)]
    except : 

        print(ch)
        print(traceback.format_exc())

ch2 = 'f : ℕ → ℝ\nm n : ℕ\nh₁ : m < n\nh₂ : Odd m\nh₃ : Odd n\n⊢ |f n - f m| ≤ |f n - f (n - 1)| + |f (m + 1) - f m| + |f (2 * (n - 1) / 2) - f (2 * (m + 1) / 2)|'

import re

ch ="f : ℝ → ℝ h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20 h₁ : Fintype ↑(f ⁻¹' {0}) ⊢ ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20"

ch1="""f : ℝ → ℝ
h₀ : ∀ (x : ℝ), f x = x ^ 2 - 12 * x + 20
h₁ : Fintype ↑(f ⁻¹' {0})
h₂ : (f ⁻¹' {0}).toFinset = {2, 10}
⊢ ∏ x ∈ {2, 10}, x = 20
"""
#print(wrap_decls(ch2))
ch4 = "xyz x y z : ℝ hx : x > 0 hy : y > 0 hz : z > 0 h : x + y + z = 3 ⊢ 1 / x + 1 / y + 1 / z + 5 * xyz ^ (1 / 3) ≥ 8"
ch5="case inl.inl.inl.inr\nf : ℕ → ℝ\nm n : ℕ\nh₁ : m < n\nh₂ : Odd m\nh₃ : Odd n\nh : |f n - f m| = f n - f m ∧ 0 ≤ f n - f m\nh' : |f n - f (n - 1)| = f n - f (n - 1) ∧ 0 ≤ f n - f (n - 1)\nh'' : |f (m + 1) - f m| = f (m + 1) - f m ∧ 0 ≤ f (m + 1) - f m\nh''' :\n |f (2 * (n - 1) / 2) - f (2 * (m + 1) / 2)| = -(f (2 * (n - 1) / 2) - f (2 * (m + 1) / 2)) ∧\n f (2 * (n - 1) / 2) - f (2 * (m + 1) / 2) < 0\n⊢ |f n - f m| ≤ |f n - f (n - 1)| + |f (m + 1) - f m| + |f (2 * (n - 1) / 2) - f (2 * (m + 1) / 2)|"
ch6 ="⊢ (15 * π / 180).cos = (√6 + √2) / 4"
ch7 = "x y a : ℝ h₀ : a ≠ 0 u v : ℝ h₁ : u = x / a h₂ : v = y / a h₃ : u ^ 2 = (u - 1) * v ⊢ v = u ^ 2 / (u - 1)"
#print(ch7)
ch = "x y a : ℝ h₀ : a ≠ 0 u v : ℝ h₁ : u = x / a h₂ : v = y / a h₃ : u ^ 2 = (u - 1) * v"

ch8="case succ.succ.succ.succ.succ.succ\ny z n✝ : ℕ\nhx : n✝ + 1 + 1 + 1 + 1 + 1 + 1 + y + z = 6\n⊢ (n✝ + 1 + 1 + 1 + 1 + 1 + 1) * y ^ 2 * z ^ 3 ≤ 108"
ch9 = "a b c : ℝ\nhabc : a * b * c = 8\nha : a > 0\nhb : b > 0\nhc : c > 0\n⊢ 1 * ((a + 1) * (b + 1) * (c + 1)) ≤ (b + 1 + (a + 1)) * (c + 1) + (a + 1) * (b + 1)\na b c : ℝ habc : a * b * c = 8 ha : a > 0 hb : b > 0 hc : c > 0 ⊢ 0 < (a + 1) * (b + 1) * (c + 1)"

for x in process_state_final(ch10) : 
    print(x)
    print('===')

