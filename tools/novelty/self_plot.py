from sentence_transformers import SentenceTransformer
import torch, numpy as np, faiss, pandas as pd

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
# print('Step 4: compute per-statement max cosine to other statements')

# import numpy as np
# import pandas as pd
# import matplotlib.pyplot as plt
# S = corpus_emb @ corpus_emb.T          # cosine similarity matrix
# np.fill_diagonal(S, -np.inf)           # exclude self
# nn_idx = np.argmax(S, axis=1).astype('int64')
# max_cos_sim = S[np.arange(S.shape[0]), nn_idx].astype('float32')

# print('Step 5: build DataFrame')
# df = pd.DataFrame({
#     "idx": np.arange(len(max_cos_sim), dtype=np.int64),
#     "nn_idx": nn_idx,
#     "max_cos_sim": max_cos_sim,
# })

# print('Step 6: plot & save histogram')
# plt.figure(figsize=(8,6))
# plt.hist(df["max_cos_sim"], bins=30, edgecolor="black", alpha=0.7)
# plt.xlabel("Max Cosine Similarity")
# plt.ylabel("Frequency")
# plt.title("Histogram of Max Cosine Similarity (Leanworkbook vs Leanworkbook)")
# plt.grid(axis="y", linestyle="--", alpha=0.6)

# # Save figure
# out_fig = "leanworkbook_leanworkbook.png"
# plt.savefig(out_fig, dpi=300, bbox_inches="tight")
# plt.close()

print('Step 4: mean cosine to other statements (exclude diagonal)')

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

N, d = corpus_emb.shape
if N < 2:
    raise ValueError("Need at least 2 statements to compute mean excluding self.")

denom = float(N - 1)

# --- Option A: simple (uses O(N^2) memory). Fast but heavy for large N. ---
def mean_cosine_simple(E):
    S = E @ E.T                              # cosine similarity matrix
    np.fill_diagonal(S, 0.0)                 # remove self (was ~1.0)
    means = (S.sum(axis=1) / denom).astype('float32')
    return means

# --- Option B: memory-friendly block GEMM (no full NxN matrix kept in RAM). ---
def mean_cosine_blocked(E, target_bytes=200*1024*1024):
    # mean_i = (sum_j <e_i, e_j> - 1) / (N-1)
    # We compute row sums in blocks and subtract 1 for the self term.
    bytes_per_row = 4 * N  # float32
    block = max(1, int(target_bytes // bytes_per_row))
    means = np.empty(N, dtype=np.float32)
    for start in range(0, N, block):
        end = min(N, start + block)
        sims = E[start:end] @ E.T            # (B, N)
        row_sums = sims.sum(axis=1)          # (B,)
        means[start:end] = ((row_sums - 1.0) / denom).astype(np.float32)
    return means

# Try simple first; if it runs out of memory, fall back to blocked.
try:
    mean_cos_sim = mean_cosine_simple(corpus_emb)
    backend = "numpy_full_matrix"
except MemoryError:
    print("Full matrix too large; switching to blocked computation.")
    mean_cos_sim = mean_cosine_blocked(corpus_emb)
    backend = "blocked"

# Build/extend DataFrame
if 'df' in locals():
    df['mean_cos_sim'] = mean_cos_sim
else:
    df = pd.DataFrame({"idx": np.arange(N, dtype=np.int64),
                       "mean_cos_sim": mean_cos_sim})

print('Backend used for mean:', backend)
print('Step 5: plot & save histogram (mean)')

plt.figure(figsize=(8,6))
plt.hist(df["mean_cos_sim"], bins=30, edgecolor="black", alpha=0.7)
plt.xlabel("Mean Cosine Similarity (excluding self)")
plt.ylabel("Frequency")
plt.title("Histogram of Mean Cosine Similarity (Leanworkbook vs Leanworkbook)")
plt.grid(axis="y", linestyle="--", alpha=0.6)

out_fig = "leanworkbook_leanworkbook_mean.png"
plt.savefig(out_fig, dpi=300, bbox_inches="tight")
plt.close()

print('Saved figure to:', out_fig)
