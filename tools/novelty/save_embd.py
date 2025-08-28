from datasets import load_dataset

ds =load_dataset('Slim205/LeanWorkbook',split='train')

print(ds)
thm_list = []

for sample in ds : 
    thm_list.append(sample['formal_statement'])

print(thm_list[0])
from sentence_transformers import SentenceTransformer, util

model = SentenceTransformer('all-MiniLM-L6-v2')  

embeddings = model.encode(thm_list, convert_to_tensor=True)
import torch, numpy as np, faiss, datasets
fname = "leanworkbook_embeddings.pt"
torch.save(embeddings.cpu(), fname)              


