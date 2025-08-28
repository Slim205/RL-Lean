from datasets import load_dataset

ds =load_dataset('Slim205/mathlib_benchmark_v09',split='train')

print(ds)
thm_list = []

for sample in ds : 
    thm_list.append(sample['theorem'])

print(thm_list[0])
from sentence_transformers import SentenceTransformer, util

model = SentenceTransformer('all-MiniLM-L6-v2')  # or try 'BAAI/bge-small-en-v1.5'

embeddings = model.encode(thm_list, convert_to_tensor=True)
import torch, numpy as np, faiss, datasets
fname = "mathlib_embeddings.pt"
torch.save(embeddings.cpu(), fname)              


