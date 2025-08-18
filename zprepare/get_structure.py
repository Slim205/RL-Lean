
import re
import pandas as pd
import os
import json
# File paths

def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

def load_statements(filename):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    return []
def get_structure(body) : 
    ch = ''
    if '≥' in body or '≤' in body or '>' in body or '<' in body:
        ch =  'ineq' 
    elif '=' in body   : 
        ch =  'eq'
    elif '≠' in body : 
        ch = 'diff'
    elif '∣' in body :
        ch = 'devide'
    elif '≡' in body : 
        return 'eq(ZMOD)'
    elif '∈' in body : 
        return 'In'
    elif '∉' in body : 
        return 'Not In'
    elif '⊆' in body : 
        return 'Inc'
    elif 'Summable' in body : 
        return 'Summable'
    elif 'True' in body or 'true' in body: 
        return 'True'
    elif 'False' in body : 
        return 'False'
    elif 'Continuous' in body : 
        return 'Continuous'
    elif 'Prime' in body : 
        return 'Prime'
    elif 'Coprime' in body : 
        return 'Coprime'
    elif 'Bijective' in body : 
        return 'Bijective'
    elif 'Surjective' in body : 
        return 'Surjective'
    elif 'Injective' in body : 
        return 'Bijective'
    elif 'Infinite' in body : 
        return 'Infinite'
    elif 'Finite' in body : 
        return 'Finite'
    elif 'Odd' in body : 
        return 'Odd'
    elif 'Even' in body : 
        return 'Even'
    elif 'IsCompact' in body : 
        return 'IsCompact' 
    elif 'Submodule' in body :
        return 'Submodule'
    elif 'Units' in body :
        return 'Units'
    elif 'StrictAnti' in body : 
        return 'StrictAnti'
    elif 'CauchySeq' in body : 
        return 'CauchySeq'
    elif 'IsGreatest' in body : 
        return 'IsGreatest'
    elif 'Maximal' in body :
        return 'Maximal'
    elif 'Monotone' in body : 
        return 'Monotone'
    elif 'ZMod' in body : 
        return 'ZMod'
    elif 'Countable' in body : 
        return 'Countable'
    elif 'IsClosed' in body :
        return 'IsClosed'
    elif 'Dense' in body : 
        return 'Dense'
    elif 'IsLeast' in body :
        return 'IsLeast'
    elif 'IsIntegral' in body : 
        return 'IsIntegral'
    elif 'StrictMono' in body :
        return 'StrictMono'
    elif 'IsConnected' in body : 
        return 'IsConnected'
    elif 'Nonempty' in body :
        return 'Noempty'
    elif 'IsLUB' in body :
        return 'IsLUB'
    else : 
        return 'None'
    specials = ['cos','sin' , 'sqrt' ,'⌊', '∑']
    for x in specials : 
        if x in body : 
            if '(' not in ch : 
                ch = ch + '(' + x
            else : 
                ch = ch + ',' + x
    if '(' in ch : 
        ch = ch + ')'
    return ch


def get_goal_structure(goal) : 
    goal = re.sub(r'\{[^{}]*\}', '', goal)

    if ': ∀' == goal.strip()[:3] or '(∀' == goal.strip()[:2] or '∀' == goal.strip()[:1] : 
        return '∀ ' + get_goal_structure(','.join(goal.split(',')[1:]))
         
    elif '∃' in goal : 
        return '∃ ' + get_goal_structure(','.join(goal.split(',')[1:]))

    elif '↔' in goal : 
        parts = goal.split('↔')
        structure = [get_goal_structure(x) for x in parts]
        return f'{structure[0]}' + ' ↔ ' + str(structure[1])

    elif '→' in goal:
        parts = goal.split('→')
        structure = [get_goal_structure(x) for x in parts]
        if structure[0] == 'None' or structure[1] == 'None' : 
            return 'Function'
        # ch = ''
        # print(structure)
        # for x in structure : 
        #     ch  = str(x) + ' → ' 
        # return ch[:-3]
        return f'{structure[0]}' + ' → ' + str(structure[1])
    
    elif '∧' in goal:
        parts = re.findall(r'[^∧]+', goal)
        structure = [get_goal_structure(x) for x in parts]
        ch = structure[0]
        p= 0
        for x in structure : 
            if p > 0 : 
                ch = ch + ' ∧ '+ x
            p+=1
        return ch
    elif '∨' in goal:
        parts = re.findall(r'[^∨]+', goal)
        structure = [get_goal_structure(x) for x in parts]
        ch = structure[0]
        p = 0
        for x in structure : 
            if p > 0 :
                ch = ch + ' ∨ '+ x
            p+=1
        return ch
    elif '¬' in goal : 
        return '¬ ' + get_goal_structure(goal.split('¬')[1])

    else : 
        return get_structure(goal)


def extract_top_level_parens(s):
    groups = []
    depth = 0
    start = None
    for i, c in enumerate(s):
        if c == '(':
            if depth == 0:
                start = i
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(s[start+1:i])  # strip outer parentheses
    return groups

def get_hypo_structure(hypo,debug=False) : 
    if len(hypo) == 0 : 
        return ''

    #groups = [s.strip('()') for s in re.findall(r'\([^\(\)]+\)', hypo)]
    hypo = hypo.replace('{', '(')
    hypo = hypo.replace('}', ')')

    groups = extract_top_level_parens(hypo)
    if debug : 
        print(groups)
    ch = ''
    for x in groups : 
        
        after = ':'.join(x.split(':')[1:]).strip()
        before = x.split(':')[0].strip()
        if after in ['ℝ','ℂ','ℕ','ℤ','ℚ','Prop','Type','Type*','ℝ × ℝ','NNReal','Equiv ℝ ℝ'] or 'Set' == after[:3] or 'Matrix' == after[:6] or 'Finset' == after[:6] or 'Ideal' == after[:5] or 'Polynomial' == after[:10] :
            ch = ch + ' + ' + after + '^' + str(len(before.split(' ')))
        else : 
            ch = ch +  ' + ' + get_goal_structure(after)

    return ch[3:]

def get_final_structure(theorem,debug=False) :
    theorem = theorem.replace(':=  by','') 
    theorem = theorem.replace(':= by','') 
    is_negation=''
    # if ': ¬('  ==  extract_theorem(theorem)[:4] :
    #     theorem =  'theorem test : ' + extract_theorem(theorem)[4:-1]
    #     is_negation = '¬¬'
    if ':'  ==  extract_theorem(theorem)[0] :
        goal = extract_theorem(theorem)
        hypo = ''
    else : 
        theorem = theorem.replace( '):', ') : ')
        if ') : ' in theorem : 
            split_c = ') : '
            c_comp = ')'
        else : 
            split_c = ' : '
            c_comp = ''
        goal = split_c.join(theorem.split(split_c)[1:]).strip()
        hypo = extract_theorem(theorem).split(split_c)[0] + c_comp
    if debug : 
        print(theorem)
        print(goal)
        print(hypo)
    final_structure = is_negation + get_hypo_structure(hypo,debug) + ' : '+ get_goal_structure(goal)
    return final_structure
d= {}

theorem = 'theorem lean_workbook_15395 (a : ℝ) (ha : 0 < a) (hab : a ≤ 9) : 9 / (a + 9) ≥ 0 ∧ 9 / (a + 9) ≤ 1:= by'
# print(get_final_structure(theorem,debug=True))
# print('-' *10)

# new_lines = []
# path = '/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/conjecture/conjecture_V16_320-test'

# with open(f'{path}/output_readable.txt', 'r', encoding='utf-8') as file:
#     for line in file:
#         if line.startswith("New:"):
#             new_lines.append(line.strip())  # remove trailing newline characters
# p = 0
# for line in new_lines:
#     theorem = 'theorem test ' +  extract_theorem(line)
# from datasets import load_dataset
# ds = load_dataset("Slim205/lean_workbook_RL_V20",split='test')
# print(ds)
# p=0

# for sample in ds:
#     theorem = extract_theorem(sample['theorem'])
#     theorem = 'theorem test ' +  theorem
n = 28
path = f'/n/netscratch/amin_lab/Lab/slim/statements/train_V{n}.json'
path ='/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/datasets/minif2f.jsonl'
p=0
#statements = load_statements(path)
statements = []
with open(path, 'r') as file:
    for line in file:
        data = json.loads(line)
        
        statements.append(data)



for statement in statements : 
    p +=1
    # if p <= 12000 : 
    #     continue
    # 'theorem test ' + 
    theorem = statement['formal_statement']
    if p ==1 :
        print(theorem)
    st = get_final_structure(theorem)

    # if 'None' in st and 'hf : ∀ x, (x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x =' not in theorem and 'Type' not in theorem and 'Fin n → Bool' not in theorem  and '(a : E)' not in theorem and 'Fin n → ℤ) ' not in theorem and '∃ f : ℝ → ℝ, ∀ x ∈ Set.Icc 0 1' not in theorem and '(x : α)' not in theorem and '1 : ℝ)' not in theorem and '(x : X)' not in theorem and 'Prop' not in theorem and 'a : sin (2 * a) = 2 * sin a * cos a := by' not in theorem and 'X → Y ↔ ¬(X ∧ ¬Y)' not in theorem and '(x : F)' not in theorem and 'p ∨ q ↔ p → q' not in theorem :  
    #     print(theorem)
    #     print(st)
    #     print(p)
    #     break
#     if 'None' in st : 
#         p +=1
# print(p)
    if st not in d.keys():
        d[st] = 1
    else : 
        d[st] += 1
top_5 = sorted(d.items(), key=lambda item: item[1], reverse=True)[:10]

for x, y in top_5:
    print(x)
    print(y)
    #print('-' * 10)


# ----------12k
# ℝ^3 + ineq + ineq + ineq + eq : ineq
# 710
# ----------
# ℝ^3 : ineq
# 723
# ----------
# ℝ^3 + ineq + ineq + ineq : ineq
# 728
# ----------

# ----------
# ℝ^3 + ineq + ineq + ineq + eq : ineq
# 20
# ----------
# ℝ^3 : ineq
# 27
# ----------
# ℝ^3 + ineq + ineq + ineq : ineq
# 29
# ----------

#### sqrt : 
# ℝ^1 : ineq
# 279
# ----------
# ℝ^1 + ineq + ineq : ineq
# 257
# ----------
# ℝ^1 + ineq : ineq
# 230
# ----------
# ℝ^1 + ineq : ineq(sqrt)
# 195
# ----------

#For all V15
#  : ∀ ineq → ineq
# 1003
# ----------
#  : ¬ ∀ ineq
# 533
# ----------
#  : ¬ ∀ ineq ∧ ineq
# 124
# ----------
#  : ∀ ineq → ∀ ineq
# 114
# ----------

# Limitations 
# ℝ^1 + ineq + ineq : ineq
# 249
# ----------
#  : ¬ ∀ ineq
# 234
# ----------
# ℝ^1 + ineq + ineq : ineq(sqrt)
# 186
# ----------
# ℝ^1 : ineq
# 146
# ----------

# OR
# ℝ^1 : ineq ∨ ineq
# 3857
# ℝ^2 : ineq ∨ ineq
# 2041
# ℝ^3 : ineq ∨ ineq
# 615
# ℕ^1 : ineq ∨ ineq
# 509

# there exists. :
# ℝ^1 + ineq + ineq : ∃ ineq ∧ ineq ∧ ineq
# 92
# ℝ^1 + ineq : ∃ ineq ∧ ineq
# 91
# ℝ^1 + ineq + ineq : ineq
# 85
#  : ∀ ineq
# 84