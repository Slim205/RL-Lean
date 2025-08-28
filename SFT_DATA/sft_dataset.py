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
            neighbours[thm_list[q_idx]].append((thm_list[j], float(sim)))

new_neighbours={}
for x,y in  neighbours.items() :
    if len(y) > 1 :
        new_neighbours[x] = y
print(f"Collected neighbours for {len(new_neighbours)} theorems")
print("max list length =", max((len(v) for v in new_neighbours.values()), default=0))
print("min list length =", min((len(v) for v in new_neighbours.values()), default=0))
print("avg list length =", np.mean([len(v) for v in new_neighbours.values()]))
print("New dataset =", sum(len(v) for v in new_neighbours.values()) )

out_path = Path("thm_neighbours.txt")
with out_path.open("w", encoding="utf-8") as f:
    for thm, neigh_list in new_neighbours.items():
        f.write(f"{thm} :\n")
        # sort by descending similarity for readability
        for nb_thm, sim in sorted(neigh_list, key=lambda x: -x[1]):
            f.write(f"    {nb_thm}\t{sim:.4f}\n")
        f.write("\n")

print(f"Wrote neighbour lists → {out_path.resolve()}")

