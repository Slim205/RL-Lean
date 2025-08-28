
#!/usr/bin/env python3
"""
Lean Statement Topic Classifier (statement-only, heuristic)

Usage:
  python lean_statement_classifier.py --in INPUT [--out out.csv] [--top 2]
  # INPUT can be:
  #   - a .txt (one statement per non-empty line)
  #   - a .csv with a column named "statement"
  # Omit --in to read from stdin (one per line).

What it does:
  - Takes only the text of each conjecture/theorem statement (Lean or near-Lean syntax).
  - Matches domain-specific types, objects, symbols, and keywords.
  - Outputs top-k topics with transparent scores and matched features.

No external dependencies. Python 3.8+.
"""

import argparse
import csv
import sys
import re
from pathlib import Path
from collections import defaultdict

# --- Topics we predict ---
TOPICS = [
    "algebra",
    "number_theory",
    "analysis",
    "topology",
    "probability",
    "linear_algebra",
    "combinatorics",
    "set_theory_logic",
    "category_theory",
    "geometry",
    "cs_pl",
]

# --- Heuristic features ---
# Weight = contribution to the topic score when a feature is present.
# Feel free to add/remove tokens for your codebase.
FEATURES = [
    # number theory
    (r'\b(Nat|ℕ|Int|ℤ|ZMod|Prime|Primes|Totient|LegendreSymbol|padic|GCD|gcd|lcm)\b', "number_theory", 3),
    (r'(?<!\w)mod(?!\w)|≡|∣', "number_theory", 2),  # mod, congruence, divides
    (r'\bFermat\b', "number_theory", 3),

    # algebra (abstract)
    (r'\b(Group|Monoid|Semiring|Ring|CommRing|Ideal|IsPrime|IsMaximal|Field|Module|Submodule|Algebra|Noetherian|UFD|PID|Adjoin)\b', "algebra", 3),
    (r'\b(Polynomial|PowerSeries)\b', "algebra", 2),

    # analysis
    (r'\b(Real|ℝ|Complex|ℂ|Normed|Metric|Cauchy|Tendsto|Continuous|Differentiable|Deriv|HasDerivAt|Series|Summable)\b', "analysis", 3),
    (r'∫', "analysis", 3),
    (r'lim|limit|limsup|liminf', "analysis", 2),

    # topology
    (r'\b(TopologicalSpace|Homeomorph|IsOpen|IsClosed|Compact|Connected|Separable|Closure|Interior|Neighborhood)\b', "topology", 3),

    # probability/measure
    (r'\b(Probability|Measure|Measurable|AE|AlmostEverywhere|Expectation|Variance|Independent)\b', "probability", 3),
    (r'𝓟|𝓜', "probability", 1),  # common fancy scripts, very light

    # linear algebra
    (r'\b(Matrix|Vector|Basis|LinearMap|LinearIndependent|Span|Eigenvalue|Eigenvector|FiniteDimensional)\b', "linear_algebra", 3),
    (r'⟂', "linear_algebra", 2),

    # combinatorics
    (r'\b(Finset|Fintype|Multiset|SimpleGraph|Graph|Ramsey|Binomial|Choose|Catalan|Countable)\b', "combinatorics", 3),
    (r'∑|∏', "combinatorics", 1),  # light; disambiguate later with finset
    (r'\b(card|Card)\b', "combinatorics", 1),

    # set theory / logic
    (r'\b(Set|Subset|sSubset|Cardinal|Ordinal|Zorn|WellFounded|Classical|Choice|Decidable|Prop)\b', "set_theory_logic", 3),
    (r'∀|∃|↔', "set_theory_logic", 1),  # very light (too generic otherwise)

    # category theory
    (r'\b(Category|Functor|NaturalTransformation|Adjunction|Monoidal|Limits|Colimits|Yoneda|Monad)\b', "category_theory", 3),

    # geometry / manifolds
    (r'\b(Affine|Euclidean|Manifold|ChartedSpace|Smooth|LieGroup|Convex|Simplex|Hilbert)\b', "geometry", 3),

    # cs / PL / data structures
    (r'\b(List|Array|ByteArray|RBMap|RBTree|HashMap|IO|DecidableEq|Termination)\b', "cs_pl", 3),
]

# Special symbols / types that boost multiple topics depending on context.
# We'll apply post-processing rules to refine.
SYMBOLS = {
    "sum": re.compile(r'∑'),
    "prod": re.compile(r'∏'),
    "integral": re.compile(r'∫'),
}

# Helpful detectors
RE_TYPECLASS = re.compile(r'\[[^\]]+\]')  # e.g., [Ring R] [TopologicalSpace X]
RE_TYPES     = re.compile(r':\s*([A-Za-z0-9_.α-ωℕℤℝℂ]+)')  # x : ℝ, (s : Set α), etc.

def classify_statement(stmt: str, top_k: int = 2):
    s = stmt
    scores = defaultdict(int)
    matched = []

    # 1) Raw features
    for pattern, topic, w in FEATURES:
        if re.search(pattern, s):
            c = len(re.findall(pattern, s))
            scores[topic] += w * c
            matched.append(f"{topic}:{pattern}x{c}")

    # 2) Typeclass brackets like [Ring R], [TopologicalSpace X]
    for m in RE_TYPECLASS.findall(s):
        # Coarsely route to topics by contents
        if any(t in m for t in ["Ring", "Field", "Group", "Module", "Ideal"]):
            scores["algebra"] += 2; matched.append("algebra:[...]")
        if "TopologicalSpace" in m or "Uniform" in m or "Metric" in m:
            scores["topology"] += 2; matched.append("topology:[...]")
        if "Normed" in m:
            scores["analysis"] += 1; matched.append("analysis:[Normed ...]")
        if "Measure" in m:
            scores["probability"] += 2; matched.append("probability:[Measure ...]")
        if any(t in m for t in ["Matrix", "LinearMap", "Basis"]):
            scores["linear_algebra"] += 2; matched.append("linear_algebra:[...]")

    # 3) Simple type tokens in binders (x : ℝ), (n : ℕ), etc.
    for m in RE_TYPES.findall(s):
        if m in ["ℕ", "Nat", "ℤ", "Int", "ZMod"]:
            scores["number_theory"] += 2; matched.append(f"number_theory:type:{m}")
        if m in ["ℝ", "Real", "ℂ", "Complex"]:
            scores["analysis"] += 2; matched.append(f"analysis:type:{m}")
        if m.startswith("Finset") or m.startswith("Multiset"):
            scores["combinatorics"] += 2; matched.append(f"combinatorics:type:{m}")
        if m.startswith("Matrix"):
            scores["linear_algebra"] += 2; matched.append(f"linear_algebra:type:{m}")
        if m.startswith("Set"):
            scores["set_theory_logic"] += 1; matched.append(f"set_theory_logic:type:{m}")

    # 4) Symbol-aware nudges
    if SYMBOLS["sum"].search(s) and "Finset" in s:
        scores["combinatorics"] += 1; matched.append("combinatorics:∑ with Finset")
    if SYMBOLS["integral"].search(s):
        scores["probability"] += 1; matched.append("probability:∫ (measure-theoretic)")

    # 5) Small tie-breakers
    # If both analysis and probability present and "AE"/"Measurable" appear, nudge probability.
    if scores["analysis"] and scores["probability"] and re.search(r'\b(AE|Measurable|a\.e\.)\b', s):
        scores["probability"] += 1; matched.append("probability:tiebreak(AE/Measurable)")

    # If both combinatorics and analysis present and Finset appears, nudge combinatorics.
    if scores["combinatorics"] and scores["analysis"] and "Finset" in s:
        scores["combinatorics"] += 1; matched.append("combinatorics:tiebreak(Finset)")

    # Rank topics
    ranked = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    ranked = [(t, s) for t, s in ranked if s > 0]
    top = [t for t, _ in ranked[:top_k]]

    return {
        "topics": ";".join(top),
        "scores": ";".join(f"{t}:{s}" for t, s in ranked),
        "matched_features": ";".join(matched),
    }

def read_input(path: str | None):
    if not path:
        # stdin lines
        for i, line in enumerate(sys.stdin, start=1):
            s = line.strip()
            if s:
                yield i, s
        return

    p = Path(path)
    if not p.exists():
        raise SystemExit(f"Input path not found: {p}")

    if p.suffix.lower() == ".txt":
        with p.open(encoding="utf-8") as f:
            for i, line in enumerate(f, start=1):
                s = line.strip()
                if s:
                    yield i, s
    elif p.suffix.lower() == ".csv":
        # read 'statement' column
        import csv
        with p.open(encoding="utf-8") as f:
            r = csv.DictReader(f)
            if "statement" not in r.fieldnames:
                raise SystemExit("CSV must have a 'statement' column.")
            for i, row in enumerate(r, start=1):
                s = (row.get("statement") or "").strip()
                if s:
                    yield i, s
    else:
        raise SystemExit("Only .txt or .csv are supported for --in (or use stdin).")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", default=None, help="Input .txt (one per line), .csv (column 'statement'), or stdin if omitted")
    ap.add_argument("--out", default="statement_topics.csv", help="Output CSV path")
    ap.add_argument("--top", type=int, default=2, help="How many topics to output per statement")
    args = ap.parse_args()

    rows = []
    for idx, stmt in read_input(args.inp):
        res = classify_statement(stmt, top_k=args.top)
        rows.append({
            "id": idx,
            "statement": stmt,
            "topics": res["topics"],
            "scores": res["scores"],
            "matched_features": res["matched_features"],
        })

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    with outp.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["id","statement","topics","scores","matched_features"])
        w.writeheader()
        for r in rows:
            w.writerow(r)

    print(f"Wrote {len(rows)} rows to {outp}")

if __name__ == "__main__":
    main()
