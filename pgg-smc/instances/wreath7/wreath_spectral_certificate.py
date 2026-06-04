#!/usr/bin/env python3
# infotheo: information theory and error-correcting codes in Rocq
# Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later
"""
wreath_spectral_certificate.py

External sum-of-squares certificate for the Z_7 wr S_2 wreath Schreier walk's
spectral bound. The Z_7 wr S_2 analogue of s5_spectral_certificate.py.

This script is the numerical component of the hybrid verification used by
pgg-smc/instances/wreath7/wreath_mixing.v.

THE WALK.
  The wreath cuts cut1, cut2 are 7-cycles, so the bare 3-generator Schreier
  transition [cut1; cut2; wswap] is not symmetric. wreath_mixing.v adjoins the
  inverses, giving the inverse-closed multiset
    wreath_sym_gens = [cut1; cut1^-1; cut2; cut2^-1; wswap],
  whose Schreier transition Q (14 x 14, uniform 1/5 generator sampling) IS
  symmetric and doubly stochastic. The same group Z_7 wr S_2 is generated.

THE CERTIFICATE.
  It computes an exact-rational LDL^T decomposition of the 13 x 13 reduced Gram
  matrix S := B^T (alpha^2 I - Q^2) B, where
    - Q is the 14 x 14 symmetric Schreier transition built below,
    - alpha = 17/20 is a rational upper bound on the second-largest eigenvalue
      modulus of Q (analytically 3/5 + (2/5) cos(2 pi / 7) ~ 0.84940; note
      17/20 = 0.85 > 0.84940 since cos(2 pi / 7) < 5/8),
    - B : 'M[rat]_(14,13) is the "differences" basis for the mean-zero
      hyperplane in Q^14, column j = e_j - e_{j+1}.

VERIFICATION.
  The script checks that Q is symmetric and doubly stochastic, that
  L D L^T = S holds exactly over Q, and that every pivot D_k is strictly
  positive. Positivity of all pivots witnesses that S is positive definite,
  equivalent to the Rayleigh bound <v, Q^2 v> <= alpha^2 <v,v> for v in the
  mean-zero hyperplane. That is the claim imported into wreath_mixing.v as the
  Axiom wreath_rayleigh_Qsq_R, around which the spectral-to-variation-distance
  chain is proved in Rocq.

  Re-run this script whenever alpha or Q changes. Do NOT edit the rational
  constant wreath_alpha_R in wreath_mixing.v by hand; regenerate it here so the
  certificate remains auditable.
"""

from fractions import Fraction


def F(n, d=1):
    return Fraction(n, d)


def matmul(A, B):
    n, m, k = len(A), len(B[0]), len(B)
    return [
        [sum((A[i][t] * B[t][j] for t in range(k)), F(0)) for j in range(m)]
        for i in range(n)
    ]


def transpose(X):
    return [[X[j][i] for j in range(len(X))] for i in range(len(X[0]))]


def diag(dv):
    n = len(dv)
    return [[dv[i] if i == j else F(0) for j in range(n)] for i in range(n)]


# --- The three wreath generators on 14 cards, as permutations (0-based).
#   cut1  = (0 1 2 3 4 5 6)   : i -> (i+1) mod 7 on pile 1, fixes pile 2.
#   cut2  = (7 8 9 10 11 12 13): j -> 7 + (j-7+1) mod 7 on pile 2, fixes pile 1.
#   wswap = (0 7)(1 8)...(6 13): i <-> i+7.
N = 14


def cut1(i):
    return (i + 1) % 7 if i < 7 else i


def cut2(i):
    return 7 + (i - 7 + 1) % 7 if i >= 7 else i


def inv(p):
    out = [0] * N
    for i in range(N):
        out[p(i)] = i
    return lambda i, out=out: out[i]


def wswap(i):
    return i + 7 if i < 7 else i - 7


# Inverse-closed five-generator multiset (mirrors wreath_sym_gens).
gens = [cut1, inv(cut1), cut2, inv(cut2), wswap]
G = len(gens)  # = 5

# --- Schreier transition Q : Q[i][j] = #{k : gens[k](i) = j} / G.
Q = [[F(0)] * N for _ in range(N)]
for i in range(N):
    for g in gens:
        Q[i][g(i)] += F(1, G)

# --- Sanity: Q symmetric and doubly stochastic.
assert all(Q[i][j] == Q[j][i] for i in range(N) for j in range(N)), \
    "Q is not symmetric (inverse-closure broken)"
assert all(sum(Q[i]) == F(1) for i in range(N)), "row sum != 1"
assert all(sum(Q[i][j] for i in range(N)) == F(1) for j in range(N)), \
    "col sum != 1"

Qsq = matmul(Q, Q)

# --- Spectral upper bound (rational): alpha >= 3/5 + (2/5) cos(2 pi / 7).
ALPHA = F(17, 20)
ALPHA2 = ALPHA * ALPHA

# --- M = alpha^2 * I - Q^2 (14 x 14 symmetric).
M = [
    [(ALPHA2 if i == j else F(0)) - Qsq[i][j] for j in range(N)]
    for i in range(N)
]

# --- B : 14 x 13 "differences" basis for the mean-zero hyperplane.
#   column j = e_j - e_{j+1}, j = 0 .. 12.
n = N - 1  # = 13
B = [[F(0)] * n for _ in range(N)]
for j in range(n):
    B[j][j] = F(1)
    B[j + 1][j] = F(-1)

# --- S = B^T M B  (13 x 13 rational symmetric Gram matrix).
S = matmul(matmul(transpose(B), M), B)

# --- LDL^T decomposition of S over the rationals.
D = [F(0)] * n
L = [[F(0) if i != j else F(1) for j in range(n)] for i in range(n)]
for k in range(n):
    D[k] = S[k][k] - sum((L[k][j] ** 2 * D[j] for j in range(k)), F(0))
    for i in range(k + 1, n):
        L[i][k] = (
            S[i][k] - sum((L[i][j] * L[k][j] * D[j] for j in range(k)), F(0))
        ) / D[k]

# --- Reconstruction check: L D L^T must equal S exactly.
Lt = transpose(L)
LDLt = matmul(matmul(L, diag(D)), Lt)
assert all(LDLt[i][j] == S[i][j] for i in range(n) for j in range(n)), \
    "LDL^T reconstruction failed"

# --- Positivity check: every pivot must be strictly positive.
assert all(d > 0 for d in D), f"non-positive pivot in LDL^T: {D}"


def fmt(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 \
        else f"{x.numerator}"


if __name__ == "__main__":
    print("# Z_7 wr S_2 wreath Schreier spectral certificate")
    print(f"# generators (inverse-closed): {G}")
    print(f"# state space N = {N}")
    print(f"# alpha   = {fmt(ALPHA)}")
    print(f"# alpha^2 = {fmt(ALPHA2)}")
    print()
    print("# Checks:")
    print("#   Q symmetric:                  PASS")
    print("#   Q doubly stochastic:          PASS")
    print("#   LDL^T reconstruction of S:    PASS")
    print(f"#   All {n} pivots strictly positive: PASS")
    print()
    print(f"# smallest pivot D_min = {fmt(min(D))}")
    print(f"# largest  pivot D_max = {fmt(max(D))}")
    print()
    print("# This alpha is the import basis for the Rocq Axiom")
    print("# wreath_rayleigh_Qsq_R in wreath_mixing.v (Definition")
    print("# wreath_alpha_R). See wreath_spectral_certificate.md for context.")
