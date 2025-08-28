from datasets import load_dataset
from sentence_transformers import SentenceTransformer
import torch, numpy as np, faiss, pandas as pd

ds = load_dataset('kfdong/STP_Lean_0320')['train'].select(range(100000))

def filter1(s) : 
    return s['tag'] == "['conjecture']"

def extract_theorem(inputs):
    try:
        return  'theorem ' + ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split())
    except:
        return "None"

ds1 = ds.filter(filter1)
print(ds1)
def extract_fn(example):
    return {"conjecture": extract_theorem(example["prompt"])}

# apply to the whole dataset in parallel
ds1 = ds1.map(extract_fn, num_proc=64)  # adjust num_proc for CPU cores

# now you can access them as a column directly
conjectures = ds1["conjecture"]

print(conjectures[0])


# --- 1) Load LeanWorkbook theorem statements (for reporting nearest text) ---

fname = "/n/netscratch/amin_lab/Lab/slim/ZFT_DATA/mathlib_embeddings.pt"
fname = "leanworkbook_embeddings.pt"

corpus_emb = torch.load(fname, map_location='cpu')            # shape: (N, d) float32/float16
if corpus_emb.dtype != torch.float32:
    corpus_emb = corpus_emb.float()
corpus_emb = corpus_emb.numpy()                               # -> numpy for FAISS
print('Step 2')


# --- 3) L2-normalize corpus embeddings so dot product == cosine similarity ---
def l2norm(x):
    norms = np.linalg.norm(x, ord=2, axis=1, keepdims=True) + 1e-12
    return x / norms

corpus_emb = l2norm(corpus_emb).astype('float32')
d = corpus_emb.shape[1]
print('Step 3')
# --- 4) Build FAISS index for cosine = inner product on normalized vectors ---
index = faiss.IndexFlatIP(d)
index.add(corpus_emb)
print('Step 4')

# --- 6) Encode conjectures with the SAME model used for the corpus ---
model = SentenceTransformer('all-MiniLM-L6-v2')
# Get normalized embeddings directly (newer sentence-transformers supports this flag)
#try:
query_emb = model.encode(conjectures, convert_to_numpy=True, normalize_embeddings=True, batch_size=2048,show_progress_bar=True)
query_emb = query_emb.astype('float32')
print('Step 6')

# --- 7) Search nearest neighbor(s). top_k=1 gives the max-cosine match; use >1 if you want more context ---
scores, indices = index.search(query_emb, 1)   # scores = cosine (since normalized), shape: (M, k)
print('Step 7')

# --- 8) Build a results table with max similarity and the matching theorem ---
rows = []
for i, conj in enumerate(conjectures):
    best_idx = int(indices[i, 0])
    best_sim = float(scores[i, 0])                 # in [-1, 1]
    rows.append({
        "conjecture_idx": i,
        "conjecture": conj,
        "max_cos_sim": best_sim,
        "nearest_thm_idx": best_idx,
    })

df = pd.DataFrame(rows)
print('Step 8')


import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Plot histogram of max cosine similarity
plt.figure(figsize=(8,6))
plt.hist(df["max_cos_sim"], bins=30, edgecolor="black", alpha=0.7)
plt.xlabel("Max Cosine Similarity")
plt.ylabel("Frequency")
plt.title("Histogram of Max Cosine Similarity (Conjectures vs Mathlib)")
plt.grid(axis="y", linestyle="--", alpha=0.6)

# Save figure
out_fig = "mathlib2_100k.png"
plt.savefig(out_fig, dpi=300, bbox_inches="tight")
plt.close()

