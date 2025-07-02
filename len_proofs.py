from datasets import load_dataset

# Login using e.g. `huggingface-cli login` to access this dataset
ds = load_dataset("Slim205/mathlib_RL_v3",split='train')

def fe(sample) : 
  sample['num_lines']  = len(sample['proof'].split('\n'))
  return sample
def fe1(sample) : 
  return  len(sample['proof'].split('\n'))>3


dsl = ds.filter(fe1)
print(dsl)
list_length =  ds.map(fe)['num_lines']
from collections import Counter
counts = Counter(list_length)
s=0
# Display the results
for number, count in counts.items():
  if number > 3 : 
    s+= count

print(s)
print(len(list_length))