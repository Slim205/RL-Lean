def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

from sentence_transformers import SentenceTransformer, util

# model = SentenceTransformer('all-MiniLM-L6-v2')  # or try 'BAAI/bge-small-en-v1.5'


#code1 =   "theorem xx1 : \u00ac(\u2200 (a b : \u211d) , |a| < 3 / 2 * |b| \u2194 a < 9 / 4 * b \u2228 a > -9 / 4 * b) := by"
code2 =   "theorem xx2 : \u00ac(\u2200 (n : \u2115) , 16 \u2223 (2 * n + 2)^2 - 24 * (2 * n + 2) + 140 \u2194 n = 1 \u2228 n = 2 \u2228 n \u2265 3 \u2228 n = 4 := by"
code1 = 'theorem xx1 : ∑ k in Finset.range 6, k ^ 2 * 2 ^ k ≥ 100'


# print(extract_theorem(code1))
# print(extract_theorem(code2))
# emb1 = model.encode(extract_theorem(code1), convert_to_tensor=True)
# emb2 = model.encode(extract_theorem(code2), convert_to_tensor=True)
# print(emb1.shape)
# sim = util.cos_sim(emb1, emb2).item()
# print(sim)  # 0.3

from transformers import AutoTokenizer, AutoModel
import torch
tokenizer = AutoTokenizer.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-SFT")
model = AutoModel.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-SFT")

code1 = "theorem xx1 : ∑ k in Finset.range 6, k ^ 2 * 2 ^ k ≥ 100"
code2 = "theorem xx2 : ¬(∀ (n : ℕ) , 16 ∣ (2 * n + 2)^2 - 24 * (2 * n + 2) + 140 ↔ n = 1 ∨ n = 2 ∨ n ≥ 3 ∨ n = 4 := by)"

def encode(text):
    inputs = tokenizer(text, return_tensors="pt", truncation=True, max_length=512)
    with torch.no_grad():
        outputs = model(**inputs)
    # Mean pooling over the last hidden state
    embeddings = outputs.last_hidden_state.mean(dim=1)
    return embeddings
emb1 = encode(code1)
emb2 = encode(code2)
from torch.nn.functional import cosine_similarity
sim = cosine_similarity(emb1, emb2).item() 
print(sim) # 0.963
#0.9690386056900024