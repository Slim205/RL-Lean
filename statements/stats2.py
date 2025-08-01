import pandas as pd
import os
import json
# File paths
from tqdm import tqdm
import matplotlib.pyplot as plt

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



path = '/n/netscratch/amin_lab/Lab/slim/statements/train_V7.json'
statements = load_statements(path)[12000:]
dicti = [0]
n = len(statements)
for i in tqdm(range(n), desc="Processing"):
    if i > 0 : 
        ch = ' \u2228 ' #") : \u2203"
        score = dicti[-1] * len(dicti)
        if ch  in statements[i]: 
            score +=1
        score = score / (len(dicti) + 1)
        dicti.append(score )  

plt.figure(figsize=(10, 6))
plt.plot(dicti)
plt.xlabel("Generated Statements")
plt.ylabel("Percentage of Examples with Patterns")
plt.title("Percentage of Examples with Patterns in new statements")
plt.grid(True)
plt.tight_layout()
plot_path = "plot4.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")
