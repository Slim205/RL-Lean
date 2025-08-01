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


def get_sim(code1,code2) : 
    emb1 = model.encode(code1, convert_to_tensor=True)
    emb2 = model.encode(code2, convert_to_tensor=True)

    sim = util.cos_sim(emb1, emb2).item()
    return sim

path = '/n/netscratch/amin_lab/Lab/slim/statements/test_V2.json'
statements = load_statements(path)#[:1000]
from sentence_transformers import SentenceTransformer, util
from tqdm import tqdm

# Step 1: Load model and encode all statements
model = SentenceTransformer('all-MiniLM-L6-v2')  # You can change the model
embeddings = model.encode(statements, convert_to_tensor=True)

# Step 2: Compute max similarity for each i (with i+1 to end)
dicti = {}
n = len(statements)
for i in tqdm(range(n), desc="Processing"):
    if i + 1 < n:
        sims = util.cos_sim(embeddings[i], embeddings[i+1:]).squeeze()  # (n-i-1,)
        dicti[i] = sims.max().item()

s = 0 
for x in dicti.values() : 
    if x > 0.9 : 
        s+=1
print(s) # 91% 6.2K