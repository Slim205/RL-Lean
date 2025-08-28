import torch, numpy as np, datasets
from sklearn.cluster import AgglomerativeClustering
from collections import defaultdict
from pathlib import Path

print("Loading dataset …")
ds = datasets.load_dataset("Slim205/mathlib_benchmark_v09", split="train")
thm_list = [sample["theorem"] for sample in ds]      # 50 000 strings

emb_path = Path("mathlib_embeddings.pt")
emb = torch.load(emb_path, map_location="cpu").numpy().astype("float32")

# L2-normalise once so dot-product = cosine similarity
emb /= np.linalg.norm(emb, axis=1, keepdims=True)

print("Clustering …")
dist_thr = 0.25          # 1 − cosθmax   ==>  cosθ ≥ 0.75 inside clusters
clust = AgglomerativeClustering(
            metric="cosine",
            linkage="average",
            distance_threshold=dist_thr,
            n_clusters=None,          
        )

labels = clust.fit_predict(emb)      

buckets = defaultdict(list)
for lbl, thm in zip(labels, thm_list):
    buckets[lbl].append(thm)

print(f"Formed {len(buckets):,} clusters "
      f"(mean size ≈ {emb.shape[0]/len(buckets):.1f}).")

out_path = Path("mathlib_clusters_75.txt").resolve()
with out_path.open("w", encoding="utf-8") as f:
    for cid, theorems in sorted(buckets.items()):
        f.write(f"Cluster {cid}\n")
        for th in theorems:
            f.write(th.replace("\n", " ") + "\n")
        f.write("\n")                 # blank line between clusters

print(f"✓  Saved clusters to {out_path}")

# from datasets import load_dataset

# ds =load_dataset('Slim205/mathlib_benchmark_v09',split='train')

# print(ds)
# thm_list = []

# for sample in ds : 
#     thm_list.append(sample['theorem'])

# print(thm_list[0])
# from sentence_transformers import SentenceTransformer, util

# model = SentenceTransformer('all-MiniLM-L6-v2')  # or try 'BAAI/bge-small-en-v1.5'

# embeddings = model.encode(thm_list, convert_to_tensor=True)
# import torch, numpy as np, faiss, datasets


# fname = "mathlib_embeddings.pt"
#torch.save(embeddings.cpu(), fname)              


