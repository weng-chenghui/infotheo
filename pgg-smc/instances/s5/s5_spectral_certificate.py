#!/usr/bin/env python3
# infotheo: information theory and error-correcting codes in Rocq
# Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later
"""
s5_spectral_certificate.py

External sum-of-squares certificate for the S_5 adjacent-transposition
Schreier walk's spectral bound.

This script is the numerical component of the hybrid verification used by
pgg-smc/instances/s5/s5_mixing.v and pgg-smc/instances/s5/rigidity_s5_instance.v.

It computes an exact-rational LDL^T decomposition of the 4x4 reduced Gram
matrix S := B^T (alpha^2 I - Q^2) B, where
  - Q is the 5x5 Schreier transition matrix for the path-graph P_5
    (diagonal [3/4, 1/2, 1/2, 1/2, 3/4], adjacent off-diagonal 1/4),
  - alpha = 181/200 (a rational upper bound on the second-largest
    eigenvalue of Q, targeting 40-bit mixing at L=286),
  - B : 'M[rat]_(5,4) is the "differences" basis for the mean-zero
    hyperplane in Q^5, whose columns are (1,-1,0,0,0), (0,1,-1,0,0),
    (0,0,1,-1,0), (0,0,0,1,-1).

Output: the 4 diagonal pivots D_k and the 6 lower-triangular entries L_ij
of the LDL^T factorization, all as exact rationals.

Verification: the script also checks that L D L^T = S holds exactly over
Q, and that every pivot D_k is strictly positive. Both facts together
witness that S is positive semidefinite, which is equivalent to the
Rayleigh bound <v, Q^2 v> <= alpha^2 <v,v> for v in the mean-zero
hyperplane. This is the claim imported into s5_mixing.v as a Rocq
Hypothesis, and the claim around which the rest of the spectral-to-
variation-distance chain is proved in Rocq.

Re-run this script whenever alpha or Q changes. Do NOT edit the rational
constants in s5_mixing.v by hand; regenerate them from this script so the
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


# --- Schreier transition matrix Q for P_5 with uniform 1/4 generator sampling
Q = [
    [F(3, 4), F(1, 4), F(0), F(0), F(0)],
    [F(1, 4), F(1, 2), F(1, 4), F(0), F(0)],
    [F(0), F(1, 4), F(1, 2), F(1, 4), F(0)],
    [F(0), F(0), F(1, 4), F(1, 2), F(1, 4)],
    [F(0), F(0), F(0), F(1, 4), F(3, 4)],
]

Qsq = matmul(Q, Q)

# --- Spectral upper bound (rational)
ALPHA = F(181, 200)                         # alpha
ALPHA2 = ALPHA * ALPHA                      # alpha^2 = 32761 / 40000

# --- M = alpha^2 * I - Q^2 (5x5 symmetric)
M = [
    [(ALPHA2 if i == j else F(0)) - Qsq[i][j] for j in range(5)]
    for i in range(5)
]

# --- B : 5 x 4 "differences" basis for the mean-zero hyperplane.
# Columns are (1,-1,0,0,0), (0,1,-1,0,0), (0,0,1,-1,0), (0,0,0,1,-1).
B = [
    [F(1), F(0), F(0), F(0)],
    [F(-1), F(1), F(0), F(0)],
    [F(0), F(-1), F(1), F(0)],
    [F(0), F(0), F(-1), F(1)],
    [F(0), F(0), F(0), F(-1)],
]

# --- S = B^T M B  (4 x 4 rational symmetric Gram matrix)
S = matmul(matmul(transpose(B), M), B)

# --- LDL^T decomposition of S over the rationals.
n = 4
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
LD = matmul(L, diag(D))
LDLt = matmul(LD, Lt)
assert all(LDLt[i][j] == S[i][j] for i in range(n) for j in range(n)), \
    "LDL^T reconstruction failed"

# --- Positivity check: every pivot must be strictly positive.
assert all(d > 0 for d in D), f"non-positive pivot in LDL^T: {D}"


def fmt(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


if __name__ == "__main__":
    print("# S_5 Schreier spectral certificate")
    print(f"# alpha   = {fmt(ALPHA)}")
    print(f"# alpha^2 = {fmt(ALPHA2)}")
    print()
    print("# LDL^T pivots (all strictly positive):")
    for k in range(n):
        print(f"#   D_{k} = {fmt(D[k])}")
    print()
    print("# Lower-triangular L (unit diagonal, only nonzero entries shown):")
    for i in range(n):
        for j in range(i):
            print(f"#   L_{i}{j} = {fmt(L[i][j])}")
    print()
    print("# Checks:")
    print("#   LDL^T reconstruction of S:    PASS")
    print("#   All pivots strictly positive: PASS")
    print()
    print("# These values are the import basis for the Rocq `Hypothesis` block")
    print("# in rigidity_s5_instance.v via the `Axiom`-like parametric import")
    print("# in s5_mixing.v. See s5_spectral_certificate.md for context.")
