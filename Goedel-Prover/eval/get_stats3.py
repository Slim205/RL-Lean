new_lines = []
path = './results/conjecture/STP-test-leanworkbook'

with open(f'{path}/output_readable.txt', 'r', encoding='utf-8') as file:
    for line in file:
        if line.startswith("Old:"):
            new_lines.append(line.strip())  # remove trailing newline characters
def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

s= 0 
for line in new_lines:
    theorem = extract_theorem(line)
    if 'sqrt' in theorem : 
        s+=1

print(s) # 137/434 (30 %)Vs 27/434 (6 %) Vs 25/434