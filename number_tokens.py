from datasets import load_dataset
from transformers import AutoTokenizer

import re
def find_positions_end(text) : 
  l=[]
  for  i in range(len(text)-4) :
    if text[i:i+4] == 'end ' :
      l.append(i)
  return l 
def fin_position(ch,text) :
  for i in range(len(text)-len(ch)) :
    if text[i : i + len(ch)] == ch :
      return i
  return -1

def process_lean_code(text):
    # Step 1: Remove all /- ... -/ comments
    new_text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    return new_text
# Example usage:
def update_data(sample) :
    sample['Context'] = process_lean_code(sample['Context'])
    return sample

# Load dataset and tokenizer
dataset = load_dataset("Slim205/lean_workbook_RL_full", split='train')  # Adjust range
tokenizer = AutoTokenizer.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-RL")

# Count tokens in parallel
def count_tokens(sample):
    prompt = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
                    header= '',
                    formal_statement=sample['input'],
                )
    return {"token_count": len(tokenizer.encode(prompt))}

# def process_lean_code(text):
#     text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
#     return text
# def filter1(sample) : 

#   prompt = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
#                 header= sample["Context"] ,
#                 formal_statement=sample['theorem'],
#             )
#   return len(tokenizer.encode(prompt)) < 2048
#dataset = dataset.map(update_data, batched=False, num_proc=10)  # Use all CPU cores
#dataset = dataset.filter(filter1,batched=False,num_proc=10)
print(dataset)
#dataset.push_to_hub('Slim205/mathlib_bench_V1_2048')
dataset = dataset.map(count_tokens, batched=False, num_proc=10)  # Use all CPU cores
token_counts = dataset["token_count"]

# Define thresholds
thresholds = [1024, 2048, 4096, 8192,16384,32768]
thresholds = [128,256,512,1024,2048, 4096]

total_samples = len(token_counts)

# Calculate percentages
percentages = {}
for threshold in thresholds:
    count = sum(1 for tokens in token_counts if tokens < threshold)
    percentages[f"< {threshold} tokens"] = f"{(count / total_samples) * 100:.2f}% ====== ({count})"

# Print results
for k, v in percentages.items():
    print(f"{k}: {v}")

