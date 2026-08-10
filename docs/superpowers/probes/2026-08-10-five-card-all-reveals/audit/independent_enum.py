#!/usr/bin/env python3
"""AUDIT: independent re-enumeration, written directly from the Rocq text of
five_card_program.v (NOT copied from five_card_leak_enum.py).

Rocq definitions mirrored:
  fc_encode b   = if b then [:: true; false] else [:: false; true]   (line 53-54)
  fc_negate cs  = rev cs                                             (line 57)
  fc_arrange a b = fc_negate (fc_encode a) ++ [:: true] ++ fc_encode b  (line 65-66)
  fc_shuffle k s = rot k s ; MathComp rot k s = drop k s ++ take k s (line 84)
  Omega = bool*bool*'I_5 uniform (five_card_leakage.v lines 50-62)
  Secret (a,b,k) = a && b                                            (line 73)
  ViewA/ViewS read positions in ascending order.

Checks performed:
  C1: {0,1,3} fibre table == spec table (exact integer counts).
  C2: every subset's MI equals the spec's fc_leak closed form (|diff|<1e-12),
      with the closed form chosen by (|A|, adjacency) as fc_leak does.
  C3: adjacency classification: for each 2-set, "exists i, A == {i, i+1 mod 5}"
      -- fc_adjacent's defining formula -- vs cyclic-distance-1.
  C4: the 26-entry leak_view_rest list + the 6 real-branch bit-patterns
      == all 32 bit-tuples, disjointly, no duplicates.
  C5: sanity: leak_k1..leak_k5 anchor fibre tables reproduce the Qed'd
      cardV/cardJ constants quoted in five_card_leakage.v.
"""
import math
from itertools import product, combinations

log2 = lambda x: math.log2(x)

def fc_encode(b):
    return [True, False] if b else [False, True]

def fc_negate(cs):
    return cs[::-1]

def fc_arrange(a, b):
    return fc_negate(fc_encode(a)) + [True] + fc_encode(b)

def rot(k, s):  # MathComp: drop k ++ take k
    return s[k:] + s[:k]

def fc_shuffle(k, s):
    return rot(k, s)

outcomes = [(a, b, k) for a in (False, True) for b in (False, True) for k in range(5)]
assert len(outcomes) == 20

def arr(w):
    a, b, k = w
    return fc_shuffle(k, fc_arrange(a, b))

def secret(w):
    a, b, _ = w
    return a and b

def fibres(A):
    """A ascending tuple of positions -> dict view -> (nv, nt, nf)."""
    d = {}
    for w in outcomes:
        row = arr(w)
        v = tuple(row[i] for i in A)
        nv, nt, nf = d.get(v, (0, 0, 0))
        if secret(w):
            nt += 1
        else:
            nf += 1
        d[v] = (nv + 1, nt, nf)
    return d

def H_bern(counts, tot):
    s = 0.0
    for c in counts:
        if c:
            s -= (c / tot) * log2(c / tot)
    return s

def MI(A):
    d = fibres(A)
    HS = H_bern([sum(x[1] for x in d.values()), sum(x[2] for x in d.values())], 20)
    HSV = sum((nv / 20) * H_bern([nt, nf], nv) for nv, nt, nf in d.values())
    return HS - HSV

# closed forms from the spec / fc_leak
V2ADJ = 27/10 - (1/4)*log2(5) - (7/10)*log2(7)
V2DIST = 5/2 - (3/20)*log2(3) - (1/2)*log2(5) - (7/20)*log2(7)
V3 = 6/5 - (9/20)*log2(3)
V45 = 2 - (3/4)*log2(3)

def succ5(i):
    return (i + 1) % 5

def fc_adjacent(A):
    """fc_adjacent's defining formula, literally."""
    S = frozenset(A)
    return any(S == frozenset({i, succ5(i)}) for i in range(5))

def fc_leak(A):
    n = len(A)
    if n <= 1:
        return 0.0
    if n == 2:
        return V2ADJ if fc_adjacent(A) else V2DIST
    if n == 3:
        return V3
    return V45

fail = 0

# C1: {0,1,3} fibre table
spec_013 = {  # view -> (nv, nt, nf); FFF absent (0,0,0)
    (False, False, True): (1, 1, 0),
    (False, True, False): (3, 0, 3),
    (False, True, True): (4, 1, 3),
    (True, False, False): (3, 0, 3),
    (True, False, True): (4, 1, 3),
    (True, True, False): (2, 2, 0),
    (True, True, True): (3, 0, 3),
}
got = fibres((0, 1, 3))
if got != spec_013:
    print("C1 FAIL:", got)
    fail += 1
else:
    print("C1 OK: {0,1,3} fibre table matches the spec exactly (7 fibres, FFF empty)")

# C2 + C3
worst = 0.0
for k in range(0, 6):
    for A in combinations(range(5), k):
        diff = abs(MI(A) - fc_leak(A))
        worst = max(worst, diff)
        if diff > 1e-12:
            print(f"C2 FAIL at {A}: MI={MI(A)} fc_leak={fc_leak(A)}")
            fail += 1
print(f"C2 OK: all 32 subsets (incl. empty) match fc_leak; worst |diff| = {worst:.2e}")

for A in combinations(range(5), 2):
    dist1 = min((A[1]-A[0]) % 5, (A[0]-A[1]) % 5) == 1
    if fc_adjacent(A) != dist1:
        print(f"C3 FAIL at {A}")
        fail += 1
adjs = [A for A in combinations(range(5), 2) if fc_adjacent(A)]
print(f"C3 OK: fc_adjacent formula == cyclic-distance-1 on all 10 pairs; adjacent = {adjs}")

# C4: coverage of the 32 bit-patterns
rest = [
    (1,1,1,1,0),(1,1,1,0,1),(1,1,1,0,0),(1,1,0,1,1),(1,1,0,1,0),(1,1,0,0,1),
    (1,1,0,0,0),(1,0,1,1,1),(1,0,1,1,0),(1,0,1,0,0),(1,0,0,1,1),(1,0,0,1,0),
    (1,0,0,0,0),(0,1,1,1,0),(0,1,1,0,1),(0,1,1,0,0),(0,1,0,1,1),(0,1,0,1,0),
    (0,1,0,0,1),(0,0,1,1,1),(0,0,1,1,0),(0,0,1,0,1),(0,0,1,0,0),(0,0,0,1,1),
    (0,0,0,1,0),(0,0,0,0,1)]
real = [(1,1,1,1,1),(1,0,1,0,1),(1,0,0,0,1),(0,1,1,1,1),(0,1,0,0,0),(0,0,0,0,0)]
allpat = set(product((0,1), repeat=5))
assert len(rest) == 26, f"rest has {len(rest)} entries"
assert len(set(rest)) == 26, "duplicates in rest"
assert len(set(real)) == 6
assert set(rest) & set(real) == set(), "overlap rest/real"
assert set(rest) | set(real) == allpat, "union misses patterns"
print("C4 OK: 26 rest + 6 real = all 32 patterns, disjoint, no duplicates")

# C5: anchor fibre tables vs the constants Qed'd in five_card_leakage.v
def tbl(A):
    return fibres(A)

t1 = tbl((0,))
assert t1[(True,)] == (12, 3, 9) and t1[(False,)] == (8, 2, 6)
t2 = tbl((0, 1))  # cardV2/cardJ2 of leak_k2_adj
assert t2[(True, True)] == (5, 2, 3) and t2[(True, False)] == (7, 1, 6)
assert t2[(False, True)] == (7, 1, 6) and t2[(False, False)] == (1, 1, 0)
t2d = tbl((0, 2))  # leak_k2_dist2
assert t2d[(True, True)] == (7, 1, 6) and t2d[(True, False)] == (5, 2, 3)
assert t2d[(False, True)] == (5, 2, 3) and t2d[(False, False)] == (3, 0, 3)
t3 = tbl((0, 1, 2))  # leak_k3 cardV3/cardJ3
assert t3[(True, True, True)] == (1, 1, 0)
assert t3[(True, True, False)] == (4, 1, 3)
assert t3[(True, False, True)] == (6, 0, 6)
assert t3[(True, False, False)] == (1, 1, 0)
assert t3[(False, True, True)] == (4, 1, 3)
assert t3[(False, True, False)] == (3, 0, 3)
assert t3[(False, False, True)] == (1, 1, 0)
assert (False, False, False) not in t3
print("C5 OK: anchor fibre tables reproduce the cardV/cardJ constants of five_card_leakage.v")

print("FAILURES:", fail)
