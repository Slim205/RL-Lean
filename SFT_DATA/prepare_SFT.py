import os
import json
import pickle
import numpy as np
from pathlib import Path
from typing import Dict
from tqdm.auto import tqdm  
import os
import json
import random
from utils.gcloud_utils import write_data
from utils.RL_utils import STORAGE

import datasets


import torch, numpy as np, datasets, faiss
from collections import defaultdict
from pathlib import Path
from tqdm import tqdm 

print("Loading dataset …")
ds = datasets.load_dataset("Slim205/mathlib_benchmark_v09", split="train")
thm_list = [row["theorem"] for row in ds]           # 50 000 theorems

emb_path = Path("mathlib_embeddings.pt")
emb = torch.load(emb_path, map_location="cpu").numpy().astype("float32")

# ---- L2-normalise once so that inner-product == cosine --------------
faiss.normalize_L2(emb)                             # in-place

d = emb.shape[1]                                    # embedding dim
index = faiss.IndexFlatIP(d)                        # exact - no compression
index.add(emb)                                      # ~1–2 s for 50 k × 768

SIM_LOW, SIM_HIGH = 0.75, 0.9

lim, D, I = index.range_search(emb, SIM_LOW)

neighbours = defaultdict(list)

for q_idx in tqdm(range(len(thm_list)),desc="Process: "):
    start, end = lim[q_idx], lim[q_idx + 1]
    for p in range(start, end):
        j = I[p]            
        if j == q_idx:      
            continue
        sim = D[p]          
        if sim < SIM_HIGH:  
            neighbours[thm_list[q_idx]].append(thm_list[j])

new_neighbours={}
for x,y in  neighbours.items() :
    if len(y) > 1 :
        new_neighbours[x] = y
print(f"Collected neighbours for {len(new_neighbours)} theorems")
print("max list length =", max((len(v) for v in new_neighbours.values()), default=0))
print("min list length =", min((len(v) for v in new_neighbours.values()), default=0))
print("avg list length =", np.mean([len(v) for v in new_neighbours.values()]))
print("New dataset =", sum(len(v) for v in new_neighbours.values()) )


START_THM   = '<theorem>'
END_THM     = '</theorem>'
START_CONJ  = '<conjecture>'
END_CONJ    = '</conjecture>'

# ── unchanged header & leading prompt text ─────────────────────────
def format_conjecture_example(context, theorem, conjecture):
    prompt = f'Complete the following Lean 4 code:\n\n```lean4\n{context.strip()}\n' \
             f'{START_THM}\n' \
             f'{theorem.strip()}\n' \
             f'{END_THM}\n' \
             f'{START_CONJ}\n'

    target = f'{conjecture.strip()}\n{END_CONJ}\n```'

    return {'prompt': prompt, 'target': target}


get_context = {sample["theorem"] :  sample['Context'] for sample in ds}     # 50 000 strings

conjecture_ds = []

for x,y in new_neighbours.items() : 
    context = get_context[x]
    for thm in y : 
        conjecture_ds.append(format_conjecture_example(context,x,thm))
print(conjecture_ds[0])
print(len(conjecture_ds))
# Step 1: Shuffle the dataset
random.seed(42)  # for reproducibility
random.shuffle(conjecture_ds)

train_size = 227328
train_ds = conjecture_ds[:train_size]
test_ds = conjecture_ds[train_size:]

print(f"Train set size: {len(train_ds)}")
print(f"Test set size: {len(test_ds)}")

# Step 3: Save the splits
train_path = os.path.join(STORAGE, "data/SFT/SFT_V2/train.json")
test_path = os.path.join(STORAGE, "data/SFT/SFT_V2/test.json")
print(train_path)
print(test_path)

write_data(json.dumps(train_ds), train_path,'json', no_compression=True)
write_data(json.dumps(test_ds), test_path,'json',no_compression=True)
