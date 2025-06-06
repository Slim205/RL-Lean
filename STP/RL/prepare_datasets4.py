from datasets import load_dataset
from collections import defaultdict

# Load dataset with multiple processes and caching
dataset = load_dataset("kfdong/STP_Lean_0320", split="train")

def my_fun(sample) :
    return 'Lean 4' in sample['prompt']

print(dataset)
print(dataset.filter(my_fun,num_proc=64))