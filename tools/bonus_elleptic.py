import json
import os
from pathlib import Path
import numpy as np
import torch
from sentence_transformers import SentenceTransformer
import matplotlib.pyplot as plt

def load_statements(filename: str):
    file = Path(filename)
    if file.is_file():
        with file.open("r", encoding="utf-8") as f:
            return json.load(f)
    return []


path = "/n/netscratch/amin_lab/Lab/slim/statements/train_V16.json"
statements_dict = load_statements(path)

# Pick only the statements from the latest global step
latest_step = 0#statements_dict[-1]["step"]
statements = [d["new"] for d in statements_dict if d["step"] == latest_step][:60]
print(f"{len(statements)} statements at step {latest_step}")

model = SentenceTransformer("all-MiniLM-L6-v2")
embeddings = model.encode(statements, convert_to_numpy=True, normalize_embeddings=True)

embeddings_dict = dict(zip(statements, embeddings))  # type: dict[str, np.ndarray]

lambda_1 = 0.1
dim = embeddings.shape[1]
Ct = lambda_1 * np.eye(dim)

for emb in embeddings:
    Ct += np.outer(emb, emb)
print(Ct[:5, :5])

Ct_inv = np.linalg.inv(Ct)
rewards = {s: float(emb.T @ Ct_inv @ emb) for s, emb in embeddings_dict.items()}

plt.figure(figsize=(6, 4))
plt.hist(list(rewards.values()), bins=30)
plt.xlabel("Reward")
plt.ylabel("Frequency")
plt.title(f"Distribution of statement rewards (step {latest_step})")


out_file = f"bonus_reward_hist_step_{latest_step}.png"
plt.savefig(out_file, dpi=300, bbox_inches="tight")   # high-res PNG
plt.close()

print(f"Histogram saved to: {out_file}")
