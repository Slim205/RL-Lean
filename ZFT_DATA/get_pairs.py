# make_pairs_from_clusters.py
import json
from pathlib import Path
from itertools import combinations

txt_path = Path("mathlib_clusters_75.txt")        # the file you created earlier
pairs_jsonl = Path("mathlib_cluster_pairs.jsonl") # one JSON obj per line

clusters = {}            # {cluster_id: [theorem, ...]}
current_id = None

with txt_path.open("r", encoding="utf-8") as f:
    for line in f:
        line = line.rstrip("\n")
        if line.startswith("Cluster "):
            current_id = int(line.split()[1])
            clusters[current_id] = []
        elif line:                           # non-blank theorem line
            clusters[current_id].append(line)

# ----------------------------------------------------------------------
# 2.  De-duplicate inside each cluster
# ----------------------------------------------------------------------
m = 0
x= 0
for cid in clusters:
    unique_theorems = sorted(set(clusters[cid]))  # deterministic order
    clusters[cid] = unique_theorems
    if len(unique_theorems) > m :
        m = len(unique_theorems)
    if len(unique_theorems) == 1 : 
        x+=1

print(x/len(clusters))
print(m)


with pairs_jsonl.open("w", encoding="utf-8") as f:
    for cid, theorems in clusters.items():
        for A, B in combinations(theorems, 2):    # all C(n,2) pairs
            obj1 = {"cluster_id": cid, "theorem_A": A, "theorem_B": B}
            f.write(json.dumps(obj1, ensure_ascii=False) + "\n")

print(f"✓  Wrote {pairs_jsonl} "
      f"with {sum(len(list(combinations(t, 2))) for t in clusters.values()):,} pairs.")
