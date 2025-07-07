import json

def get_original_theorem(theorem_name) : 
    p = 0
    for x in range(len(theorem_name)) : 
        if theorem_name[x] == '_' : 
            p = x
    return theorem_name[:p]

file_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/results/minif2f/leanworkbook_V1_160/code_compilation.json"

with open(file_path, "r", encoding="utf-8") as f:
    data = json.load(f)


error_num = 0
pp=0
total = 0
list_use_meta_tactics=[]
for entry in data:
    compilation_result = entry.get("compilation_result", {})
    errors = compilation_result.get("errors", [])
    use_meta_tactics = False
    if len(errors) > 0 : 
        error_num +=1
    elif compilation_result['complete'] : 
        pp +=1
    for err in errors:
        msg = err.get("data")
        if msg:
            for x in ['linarith' ,'simp' , 'omega'] : 
                if x in msg :
                    use_meta_tactics=True
    if  use_meta_tactics : 
        list_use_meta_tactics.append(get_original_theorem(compilation_result['custom_id']))
    total += 1

print(len(list_use_meta_tactics))
print(error_num)
print(pp)
print(total)

# SFT  :
# 118
# 167
# 75
# 244

# V9 :
# 115
# 165
# 79
# 244

# V10 1 epoch
# 117
# 168
# 76
# 244

#V12 4 epoch

# 106
# 166
# 77
# 244

#SFT LEANWORKBOOK
# 947
# 1304
# 197
# 1505

# SFT 32
# 29346
# 40867
# 6951
# 48160

# full lean_workbook
# 995
# 1369
# 104
# 1481
#=============
# SFT + train on 120 steps + -1
# 98
# 156
# 86
# 244
# 91 160 steps
# 154
# 86
# 244
#==================
# SFT + train on 120 steps (0/1)
# 112
# 156
# 87
# 244
# 108 (160 steps)
# 156
# 86
# 244
#========
# SFT  :
# 118
# 167
# 75
# 244
