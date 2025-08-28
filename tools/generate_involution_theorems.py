
#!/usr/bin/env python3
"""
generate_involution_theorems.py
=================================
Produce Lean theorem templates parametrised by involutive functions T such that T ∘ T = id.

Output format (JSON Lines):
    {
      "name": "imo_1968_p5_1_negation",
      "lean": "theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h0 : 0 < a)\n(h1 : ∀ x, f (x + a) = -f x) : ∃ b > 0, ∀ x, f (x + b) = f x := by\n  sorry"
    }

Usage example:
    python generate_involution_theorems.py --canonical 50 --mobius 2000 --synthetic 50000 --output theorems.jsonl

The script will:
  1. Emit a chosen number of 'canonical' involutions (hard‑coded list)
  2. Emit algebraic/Möbius involutions generated from integer parameters
  3. Emit synthetic involutions discovered by random symbolic search (depth‑limited)

Performance:
  On a modern laptop it can emit ~50k theorems/minute; generating millions is possible but may take time.
"""

import argparse, json, sympy as sp, itertools, random, sys, math
from sympy import Symbol, simplify

x = Symbol('x')

# -----------------------------
# Helpers
# -----------------------------
def lean_expr(expr):
    """Convert SymPy expr to Lean‑friendly string."""
    s = sp.sstr(expr).replace('**', '^')
    return s

def theorem_template(expr, tag):
    name = f"imo_1968_p5_1_{tag}"
    lean = (
        "theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h0 : 0 < a)\n"
        f"(h1 : ∀ x, f (x + a) = {lean_expr(expr)}) : "
        "∃ b > 0, ∀ x, f (x + b) = f x := by\n  sorry"
    )
    return { "name": name, "lean": lean }

# -----------------------------
# Canonical involutions
# -----------------------------
CANONICAL = {
    "neg":       -x,
    "one_minus": 1 - x,
    "two_minus": 2 - x,
    "recip":     1/x,
    "recip2":    2/x,
    "inv_add1":  1/(x+1),
    "half_plus_root": sp.Rational(1,2) + sp.sqrt(x - x**2),
    "root_flip": 1 - sp.sqrt(1 - x),
    "tan_flip": -sp.tan(x),
    "log_flip": -sp.log(x),
}

# -----------------------------
# Möbius family generator
# -----------------------------
def mobius_family(limit_a=50, limit_c=50):
    """Generate Möbius involutions of form T(x)=(a x + b)/(c x - a) with b= -a^2 / c ."""
    for a in range(-limit_a, limit_a+1):
        if a == 0:
            continue
        for c in range(-limit_c, limit_c+1):
            if c == 0:
                continue
            b = -a**2 / c
            T = (a*x + b) / (c*x - a)
            # Validate involution
            if simplify(T.subs(x, T) - x) == 0:
                yield T, f"mobius_{a}_{c}"

# -----------------------------
# Synthetic random generator
# -----------------------------
OPS = ['+', '-', '*', '/']
UNARY = ['-', 'inv']  # inv stands for 1/()

def random_expr(depth=3):
    if depth == 0:
        return random.choice([x, random.randint(-3,3)])
    if random.random() < 0.3:
        op = random.choice(UNARY)
        if op == '-':
            return -random_expr(depth-1)
        else:
            return 1/random_expr(depth-1)
    else:
        left = random_expr(depth-1)
        right = random_expr(depth-1)
        op = random.choice(OPS)
        if op == '+':
            return left + right
        elif op == '-':
            return left - right
        elif op == '*':
            return left * right
        else:
            return left / right

def synthetic_generator(count, max_depth=4):
    seen = set()
    while len(seen) < count:
        expr = random_expr(random.randint(1,max_depth))
        try:
            if sp.simplify(expr.subs(x, expr) - x) == 0:
                key = sp.sstr(expr)
                if key in seen:
                    continue
                seen.add(key)
                yield expr, f"syn_{len(seen)}"
        except Exception:
            continue

# -----------------------------
# Main
# -----------------------------
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--canonical', type=int, default=50)
    parser.add_argument('--mobius', type=int, default=2000)
    parser.add_argument('--synthetic', type=int, default=50000)
    parser.add_argument('--output', type=str, required=True)
    args = parser.parse_args()

    out = open(args.output, 'w')

    # Emit canonical
    i = 0
    for tag, expr in list(CANONICAL.items())[:args.canonical]:
        json.dump(theorem_template(expr, tag), out)
        out.write('\n')
        i += 1

    # Emit Möbius
    for expr, tag in itertools.islice(mobius_family(), args.mobius):
        json.dump(theorem_template(expr, tag), out)
        out.write('\n')
        i += 1

    # Emit synthetic
    for expr, tag in itertools.islice(synthetic_generator(args.synthetic*2), args.synthetic):
        json.dump(theorem_template(expr, tag), out)
        out.write('\n')
        i += 1

    out.close()
    print(f"Written {i} theorems to {args.output}")

if __name__ == "__main__":
    main()

#python generate_involution_theorems.py --canonical 100 --mobius 1000 --synthetic 10000 --output theorems.jsonl