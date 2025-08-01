from sentence_transformers import SentenceTransformer, util

model = SentenceTransformer('all-MiniLM-L6-v2')  # or try 'BAAI/bge-small-en-v1.5'
def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"


#code1 = '∑ k in Finset.range 6, k ^ 2 * 2 ^ k ≥ 100'
code1 =   "theorem xx1 : \u00ac(\u2200 (a b : \u211d) , |a| < 3 / 2 * |b| \u2194 a < 9 / 4 * b \u2228 a > -9 / 4 * b) := by"
code2 =   "theorem xx2 : \u00ac(\u2200 (n : \u2115) , 16 \u2223 (2 * n + 2)^2 - 24 * (2 * n + 2) + 140 \u2194 n = 1 \u2228 n = 2 \u2228 n \u2265 3 \u2228 n = 4 \u2228 n = 5 \u2228 n = 6 \u2228 n = 7 \u2228 n = 8 \u2228 n = 9 \u2228 n = 10 \u2228 n = 11 \u2228 n = 12 \u2228 n = 13 \u2228 n = 14 \u2228 n = 15 \u2228 n = 16 \u2228 n = 17 \u2228 n = 18 \u2228 n = 19 \u2228 n = 20) := by"


print(extract_theorem(code1))
print(extract_theorem(code2))
emb1 = model.encode(extract_theorem(code1), convert_to_tensor=True)
emb2 = model.encode(extract_theorem(code2), convert_to_tensor=True)

sim = util.cos_sim(emb1, emb2).item()
print(sim)  # should be < 0.3 ideally
