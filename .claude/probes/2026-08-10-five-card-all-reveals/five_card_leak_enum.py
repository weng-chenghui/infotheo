#!/usr/bin/env python3
"""Enumerate the 20-outcome den Boer sample space and compute I(Secret; View_A)
for every nonempty subset A of positions {0..4}, grouped by rotation orbit.

Mirrors five_card_program.v exactly:
  fc_encode b  = [T,F] if b else [F,T]
  fc_negate    = reverse
  fc_arrange a b = rev(fc_encode a) ++ [T] ++ fc_encode b
  fc_shuffle k s = rot k s  (MathComp rot: drop k ++ take k, cyclic LEFT rotation)
"""
from itertools import product, combinations
from fractions import Fraction
import math

def fc_encode(b): return [True, False] if b else [False, True]
def fc_arrange(a, b): return list(reversed(fc_encode(a))) + [True] + fc_encode(b)
def rot(k, s): return s[k:] + s[:k]

# 20 outcomes, uniform
outcomes = [(a, b, k) for a in (0, 1) for b in (0, 1) for k in range(5)]
def arr(w):
    a, b, k = w
    return rot(k, fc_arrange(bool(a), bool(b)))
def secret(w):
    a, b, _ = w
    return bool(a) and bool(b)

def mutual_info(A):
    """I(Secret; View_A) in bits, exact via Fractions on counts; returns
    (float value, dict of per-view counts) with counts (nv, nt, nf)."""
    views = {}
    for w in outcomes:
        v = tuple(arr(w)[i] for i in A)
        s = secret(w)
        nv, nt, nf = views.get(v, (0, 0, 0))
        views[v] = (nv + 1, nt + (1 if s else 0), nf + (0 if s else 1))
    # H(S) - H(S|V);  H(S|V) = sum_v (nv/20) * h(nt/nv, nf/nv)
    def h(counts, total):
        acc = 0.0
        for c in counts:
            if c:
                p = c / total
                acc -= p * math.log2(p)
        return acc
    HS = h([5, 15], 20)
    HSV = sum((nv / 20) * h([nt, nf], nv) for (nv, nt, nf) in views.values())
    return HS - HSV, views

def orbit(A):
    return frozenset(frozenset((i + r) % 5 for i in A) for r in range(5))

seen = set()
for k in range(1, 6):
    for A in combinations(range(5), k):
        ok = orbit(A)
        if ok in seen:
            continue
        seen.add(ok)
        mi, views = mutual_info(A)
        print(f"k={k} rep={A} orbit_size={len(ok)} I={mi:.6f}")
        for v, (nv, nt, nf) in sorted(views.items()):
            print(f"    view={''.join('T' if x else 'F' for x in v)}  nv={nv} nt={nt} nf={nf}")

# cross-check every subset individually equals its orbit rep (sanity for equivariance)
print("\nequivariance sanity (max |I(A) - I(rep)| over all subsets):")
worst = 0.0
for k in range(1, 6):
    reps = {}
    for A in combinations(range(5), k):
        ok = orbit(A)
        mi, _ = mutual_info(A)
        if ok in reps:
            worst = max(worst, abs(mi - reps[ok]))
        else:
            reps[ok] = mi
print(f"  {worst:.2e}")
