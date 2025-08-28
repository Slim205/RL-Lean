from datasets import load_dataset
from sentence_transformers import SentenceTransformer
import torch, numpy as np, faiss, pandas as pd

def extract_theorem(inputs):
    try:
        return  'theorem ' + ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split())
    except:
        return "None"


# ds = load_dataset('kfdong/STP_Lean_0320')['train']#.select(range(100000))
# def filter1(s) : 
#     return s['tag'] == "['conjecture']"
# ds1 = ds.filter(filter1)
# def extract_fn(example):
#     return {"conjecture": extract_theorem(example["prompt"])}
# ds1 = ds1.map(extract_fn, num_proc=64) 

# ds1 =load_dataset('Slim205/LeanWorkbook',split='train')
# def extract_fn(example):
#     return {"conjecture": extract_theorem(example["formal_statement"])}
# ds1 = ds1.map(extract_fn, num_proc=64) 

# ds1 =load_dataset('Slim205/mathlib_benchmark_v09',split='train')
# def extract_fn(example):
#     return {"conjecture": extract_theorem(example["theorem"])}
# ds1 = ds1.map(extract_fn, num_proc=64) 

ds1 =load_dataset('Slim205/minif2f',split='valid')
def extract_fn(example):
    return {"conjecture": example["formal_statement"]}
ds1 = ds1.map(extract_fn, num_proc=64) 
import re
from collections import defaultdict
import matplotlib.pyplot as plt

TOPICS = [
    "algebra","number_theory","analysis","topology","probability",
    "linear_algebra","combinatorics","set_theory_logic","category_theory",
    "geometry","cs_pl"
]

# Patterns are strings (not precompiled) so they’re easy to pickle with HF Datasets multiprocessing.
FEATURES = [
    # number theory
    (r'\b(Nat|ℕ|Int|ℤ|ZMod|Prime|Primes|Totient|LegendreSymbol|padic|GCD|gcd|lcm)\b', "number_theory", 3),
    (r'(?<!\w)mod(?!\w)|≡|∣', "number_theory", 2),
    (r'\bFermat\b', "number_theory", 3),

    # algebra
    (r'\b(Group|Monoid|Semiring|Ring|CommRing|Ideal|IsPrime|IsMaximal|Field|Module|Submodule|Algebra|Noetherian|UFD|PID|Adjoin)\b', "algebra", 3),
    (r'\b(Polynomial|PowerSeries)\b', "algebra", 2),

    # analysis
    (r'\b(Real|ℝ|Complex|ℂ|Normed|Metric|Cauchy|Tendsto|Continuous|Differentiable|Deriv|HasDerivAt|Series|Summable)\b', "analysis", 3),
    (r'∫', "analysis", 3),
    (r'\blim|limit|limsup|liminf\b', "analysis", 2),

    # topology
    (r'\b(TopologicalSpace|Homeomorph|IsOpen|IsClosed|Compact|Connected|Separable|Closure|Interior|Neighborhood)\b', "topology", 3),

    # probability / measure
    (r'\b(Probability|Measure|Measurable|AE|AlmostEverywhere|Expectation|Variance|Independent)\b', "probability", 3),

    # linear algebra
    (r'\b(Matrix|Vector|Basis|LinearMap|LinearIndependent|Span|Eigenvalue|Eigenvector|FiniteDimensional)\b', "linear_algebra", 3),
    (r'⟂', "linear_algebra", 2),

    # combinatorics
    (r'\b(Finset|Fintype|Multiset|SimpleGraph|Graph|Ramsey|Binomial|Choose|Catalan|Countable)\b', "combinatorics", 3),
    (r'∑|∏', "combinatorics", 1),
    (r'\b(card|Card)\b', "combinatorics", 1),

    # set theory / logic
    (r'\b(Set|Subset|sSubset|Cardinal|Ordinal|Zorn|WellFounded|Classical|Choice|Decidable|Prop)\b', "set_theory_logic", 3),
    (r'∀|∃|↔', "set_theory_logic", 1),

    # category theory
    (r'\b(Category|Functor|NaturalTransformation|Adjunction|Monoidal|Limits|Colimits|Yoneda|Monad)\b', "category_theory", 3),

    # geometry / manifolds
    (r'\b(Affine|Euclidean|Manifold|ChartedSpace|Smooth|LieGroup|Convex|Simplex|Hilbert)\b', "geometry", 3),

    # cs / PL
    (r'\b(List|Array|ByteArray|RBMap|RBTree|HashMap|IO|DecidableEq|Termination)\b', "cs_pl", 3),
]

RE_TYPECLASS = re.compile(r'\[[^\]]+\]')   # e.g., [Ring R], [TopologicalSpace X]
RE_TYPES     = re.compile(r':\s*([A-Za-z0-9_.α-ωℕℤℝℂ]+)')

def classify_statement(stmt: str, top_k: int = 1):
    s = (stmt or "").strip()
    if not s or s == "None":
        return {"topic": "unknown", "scores": "", "matched": ""}

    scores = defaultdict(int)
    matched = []

    # 1) Raw features
    for pattern, topic, w in FEATURES:
        hits = re.findall(pattern, s)
        if hits:
            scores[topic] += w * len(hits)
            matched.append(f"{topic}:{pattern}x{len(hits)}")

    # 2) Typeclass brackets [Ring R], [TopologicalSpace X], ...
    for m in RE_TYPECLASS.findall(s):
        if any(t in m for t in ["Ring","Field","Group","Module","Ideal"]):
            scores["algebra"] += 2; matched.append("algebra:[...]")
        if "TopologicalSpace" in m or "Uniform" in m or "Metric" in m:
            scores["topology"] += 2; matched.append("topology:[...]")
        if "Normed" in m:
            scores["analysis"] += 1; matched.append("analysis:[Normed ...]")
        if "Measure" in m:
            scores["probability"] += 2; matched.append("probability:[Measure ...]")
        if any(t in m for t in ["Matrix","LinearMap","Basis"]):
            scores["linear_algebra"] += 2; matched.append("linear_algebra:[...]")

    # 3) Simple type hints in binders: (x : ℝ), (n : ℕ), etc.
    for t in RE_TYPES.findall(s):
        if t in ["ℕ","Nat","ℤ","Int","ZMod"]:
            scores["number_theory"] += 2; matched.append(f"number_theory:type:{t}")
        if t in ["ℝ","Real","ℂ","Complex"]:
            scores["analysis"] += 2; matched.append(f"analysis:type:{t}")
        if t.startswith("Finset") or t.startswith("Multiset"):
            scores["combinatorics"] += 2; matched.append(f"combinatorics:type:{t}")
        if t.startswith("Matrix"):
            scores["linear_algebra"] += 2; matched.append(f"linear_algebra:type:{t}")
        if t.startswith("Set"):
            scores["set_theory_logic"] += 1; matched.append(f"set_theory_logic:type:{t}")

    # 4) Symbol-aware nudges
    if "∑" in s and "Finset" in s:
        scores["combinatorics"] += 1; matched.append("combinatorics:∑ with Finset")
    if "∫" in s:
        scores["probability"] += 1; matched.append("probability:∫")
    if scores["analysis"] and scores["probability"] and re.search(r'\b(AE|Measurable|a\.e\.)\b', s):
        scores["probability"] += 1; matched.append("probability:tiebreak(AE/Measurable)")
    if scores["combinatorics"] and scores["analysis"] and "Finset" in s:
        scores["combinatorics"] += 1; matched.append("combinatorics:tiebreak(Finset)")

    ranked = sorted(((t, sc) for t, sc in scores.items() if sc > 0), key=lambda kv: (-kv[1], kv[0]))
    top = ranked[0][0] if ranked else "unknown"
    return {
        "topic": top,
        "scores": ";".join(f"{t}:{sc}" for t, sc in ranked),
        "matched": ";".join(matched),
    }

# Map over your conjectures to assign a topic
def add_topic(example):
    res = classify_statement(example["conjecture"], top_k=1)
    return {"topic": res["topic"], "topic_scores": res["scores"], "topic_features": res["matched"]}

# You already have ds1 with a "conjecture" column
ds2 = ds1.map(add_topic, num_proc=64)  # adjust cores as you like
print(ds2)
# # Quick sanity check
print(ds2[0]["conjecture"])
print(ds2[0]["topic"], ds2[0]["topic_scores"])

# # --- Histogram of classes ---
# df = ds2.to_pandas()[["topic"]].copy()
# df["topic"] = df["topic"].replace("", "unknown").fillna("unknown")

# counts = df["topic"].value_counts().sort_values(ascending=False)
# print(counts)

# plt.figure(figsize=(15, 10))
# counts.plot(kind="bar")
# plt.title("Conjecture Topic Histogram")
# plt.xlabel("Topic")
# plt.ylabel("Count")
# plt.tight_layout()
# plt.xticks(rotation=0)   # rotate labels

# out_fig = "conjecturer-Topic2.png"
# plt.savefig(out_fig)
# plt.close()
import re, math
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from itertools import combinations

# Use the same topic universe you used in classification
TOPICS = [
    "algebra","number_theory","analysis","topology","probability",
    "linear_algebra","combinatorics","set_theory_logic","category_theory",
    "geometry","cs_pl","unknown"
]

# 1) Parse "topic_scores" like "algebra:7;number_theory:4;analysis:1"
def parse_scores(s: str):
    d = {}
    if not s:
        return d
    for part in s.split(";"):
        if not part.strip():
            continue
        if ":" not in part:
            # handle rare "topic" with no score
            d[part.strip()] = 1.0
            continue
        t, sc = part.split(":", 1)
        t = t.strip()
        try:
            d[t] = float(sc)
        except:
            d[t] = 1.0
    return d

# 2) Build data frame: one column per topic (scores, 0 if absent)
def to_matrix(ds2, topics=TOPICS):
    rows = []
    for s in ds2["topic_scores"]:
        d = parse_scores(s)
        rows.append([d.get(t, 0.0) for t in topics])
    X = pd.DataFrame(rows, columns=topics)
    # optional: drop statements with no signals at all (all zeros)
    if (X.sum(axis=1) == 0).any():
        X = X.loc[(X.sum(axis=1) > 0)].copy()
    return X

X = to_matrix(ds2, TOPICS)
print(X.shape)
# Weighted correlation (Pearson on scores)
corr_weighted = X.corr()

# Binary presence matrix
B = (X > 0).astype(int)
corr_binary = B.corr()

# Jaccard and Lift / PMI (on binary)
n = len(B)
co = B.T @ B                         # co-occurrence counts
freq = np.diag(co)                   # per-topic counts
jaccard = pd.DataFrame(np.zeros_like(co, dtype=float), index=TOPICS, columns=TOPICS)

for i, ti in enumerate(TOPICS):
    for j, tj in enumerate(TOPICS):
        inter = co.iloc[i, j]
        union = freq[i] + freq[j] - inter
        jaccard.iloc[i, j] = (inter / union) if union > 0 else 0.0

# Weighted correlation heatmap
plt.figure(figsize=(8,6))
plt.imshow(corr_weighted.values, aspect='auto')
plt.xticks(range(len(TOPICS)), TOPICS, rotation=45, ha='right')
plt.yticks(range(len(TOPICS)), TOPICS)
plt.title("Topic Correlation (weighted)")
plt.colorbar()
plt.tight_layout()
out_fig = "minif2f-Corr-weighted.png"
plt.savefig(out_fig)
plt.close()

plt.figure(figsize=(8,6))
plt.imshow(jaccard.values, aspect='auto')
plt.xticks(range(len(TOPICS)), TOPICS, rotation=45, ha='right')
plt.yticks(range(len(TOPICS)), TOPICS)
plt.title("Topic Correlation (jaccard)")
plt.colorbar()
plt.tight_layout()
out_fig = "minif2f-Corr-jaccard.png"
plt.savefig(out_fig)
plt.close()