import pandas as pd
import numpy as np
import argparse
import json
import torch
from tqdm import tqdm
from transformers import AutoTokenizer, AutoModel
from sklearn.metrics.pairwise import cosine_similarity
import matplotlib.pyplot as plt

parser = argparse.ArgumentParser()
# 'results/test/code_compilation.json'
parser.add_argument('--input_path',  type=str)
# 'results/test/compilation_summarize.json
parser.add_argument('--output_path',  type=str)

parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()
def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"


input_file= args.input_path
df = pd.read_json(input_file)

print(df.columns) #Index(['name', 'code', 'custom_id', 'compilation_result', 'correct'], dtype='object')


from sentence_transformers import SentenceTransformer, util

model = SentenceTransformer('all-MiniLM-L6-v2')  


cosine_scores=[]
for i, sample in tqdm(df.iterrows(), total=len(df)):
    if i==0 : 
      print(extract_theorem(sample['code']))
    emb2 = model.encode(extract_theorem(sample['code']), convert_to_tensor=True)
    emb1 = model.encode(extract_theorem(sample['theorem']), convert_to_tensor=True)
    sim = util.cos_sim(emb1, emb2).item()
    cosine_scores.append(sim)

df["cosine_similarity"] = cosine_scores
plt.figure(figsize=(10, 6))
plt.hist(df["cosine_similarity"], bins=50, color="steelblue", alpha=0.8)
plt.xlabel("Cosine Similarity")
plt.ylabel("Frequency")
plt.title("Cosine Similarity Between Reference and Code Embeddings")
plt.grid(True)
plt.tight_layout()
plot_path = f"{'/'.join(input_file.split('/')[:-1])}/cosine_similarity_plot.png"
plt.savefig(plot_path)
print(f"Saved plot to {plot_path}")

df_grp = df.groupby("name")["cosine_similarity"].sum()


df_grp.reset_index()[["name", "cosine_similarity"]].to_csv(args.output_path.replace(".json", ".csv"), index=False, header=True, sep='\t', quoting=1, na_rep='Missing')
