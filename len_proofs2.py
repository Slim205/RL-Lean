from datasets import load_dataset , DatasetDict

ds = load_dataset("Slim205/mathlib_RL_v3")

def fe(sample) : 
  p = 0 
  for x in sample['proof'].split('\n') : 
    if len(x) > 0 : 
      p +=1 
  sample['num_lines']  = p
  return sample

new_ds = ds.map(fe)
new_ds_traib = new_ds['train'].sort(['num_lines'])
new_ds_all = DatasetDict()
new_ds_all['train'] = new_ds_traib
new_ds_all['test'] = new_ds['test']

print(new_ds_all)

new_ds_all.push_to_hub('Slim205/mathlib_RL_v3_length')
# list_length =  new_ds['num_lines']
# from collections import Counter
# counts = Counter(list_length)
# for n in range(1,61,5):
#     total = sum(count for length, count in counts.items() if length <= n)
#     print(f"Less than {n} lines: {round(total/len(list_length)*100)}% ({total})")

# train
# Less than 1 lines: 32% (3294)
# Less than 6 lines: 78% (8078)
# Less than 11 lines: 90% (9257)
# Less than 16 lines: 94% (9709)
# Less than 21 lines: 96% (9911)
# Less than 26 lines: 97% (10024)
# Less than 31 lines: 98% (10107)
# Less than 36 lines: 98% (10139)
# Less than 41 lines: 99% (10179)
# Less than 46 lines: 99% (10207)
# Less than 51 lines: 99% (10233)
# Less than 56 lines: 99% (10247)

# Less than 1 lines: 34% (101)
# Less than 6 lines: 74% (223)
# Less than 11 lines: 89% (266)
# Less than 16 lines: 95% (285)
# Less than 21 lines: 97% (290)
# Less than 26 lines: 97% (292)
# Less than 31 lines: 99% (296)
# Less than 36 lines: 99% (296)
# Less than 41 lines: 99% (298)
# Less than 46 lines: 99% (298)
# Less than 51 lines: 99% (298)
# Less than 56 lines: 99% (298)
# Validation



# Less than 1 lines: 34% (104)
# Less than 6 lines: 82% (251)
# Less than 11 lines: 89% (272)
# Less than 16 lines: 93% (286)
# Less than 21 lines: 95% (292)
# Less than 26 lines: 97% (297)
# Less than 31 lines: 97% (298)
# Less than 36 lines: 98% (300)
# Less than 41 lines: 98% (301)
# Less than 46 lines: 99% (305)
# Less than 51 lines: 100% (306)
# Less than 56 lines: 100% (306)

# test




