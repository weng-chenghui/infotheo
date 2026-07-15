"""
ex2_barrington_and.py
=====================
Barrington's Theorem: NC^1 via Commutator Construction (§7.2, §3.1)
====================================================================

Barrington (1989) showed that NC^1 circuits (constant-depth, bounded fan-in)
can be evaluated by width-5 branching programs over S_5.  The key insight is
that S_5 is *non-solvable*, which lets us express AND via a commutator:

    [α^x1, β^x2]  =  α^{-x1} β^{-x2} α^{x1} β^{x2}

This equals the identity when x1=0 or x2=0, and a fixed non-trivial 5-cycle
when x1=x2=1.  Because S_5 is non-solvable, [α, β] ≠ id is achievable with
5-cycles α, β — impossible in any solvable group.

PGG-SMC relevance (§3.1):
  Each factor α^{xi} is a *branch* of the monodromy program.  Parties can
  hold different branches; the product of all factors reveals only the
  Boolean function value (endpoint on the 5-sheet cover), not the inputs xi.

Generators used (verified):
  α = (0 1 2 3 4),  β = (0 1 3 4 2)
  [α, β] = (0 2 3 1 4)  — a non-trivial 5-cycle  (β = (0 2 4 1 3) would give id)

Sections:
  1. S_5 setup: α, β as 5-cycles
  2. Verify [α, β] is non-trivial
  3. AND gate truth table
  4. OR gate via De Morgan
  5. NOT via output interpretation
  6. Composed circuit: f(x1, x2, x3) = (x1 AND x2) OR x3
  7. Garbled evaluation: Ishai-Kushilevitz style random masking
"""

import sys
import os
import random
import itertools
from typing import List, Tuple

# ---------------------------------------------------------------------------
# Import from the core library in the same directory
# ---------------------------------------------------------------------------
sys.path.insert(0, os.path.dirname(__file__))
from smc_pgg_core import (
    Permutation, word_product, commutator,
    print_separator, print_truth_table,
)


# ===========================================================================
# Section 1: S_5 setup — α and β as generating 5-cycles
# ===========================================================================

print_separator("Section 1: S_5 generators α and β")

# α = (0 1 2 3 4) — cyclic rotation
alpha = Permutation.from_cycles(5, (0, 1, 2, 3, 4))

# β = (0 1 3 4 2) — another 5-cycle chosen so that [α, β] is non-trivial
# Note: β = (0 2 4 1 3) would give [α,β] = identity (bad choice).
# With β = (0 1 3 4 2) we get [α,β] = (0 2 3 1 4), a non-trivial 5-cycle.
beta = Permutation.from_cycles(5, (0, 1, 3, 4, 2))

e5 = Permutation.identity(5)

print(f"  α  = {alpha}  (order {alpha.order()})")
print(f"  β  = {beta}  (order {beta.order()})")
print(f"  α⁻¹ = {alpha.inverse()}")
print(f"  β⁻¹ = {beta.inverse()}")
print()

# Sanity: both are 5-cycles (order 5)
assert alpha.order() == 5, "α must be a 5-cycle"
assert beta.order() == 5, "β must be a 5-cycle"

# S_5 is non-solvable: its derived series does not reach {e}.
# We verify this informally by checking that the commutator is non-trivial.
comm_ab = commutator(alpha, beta)
print(f"  [α, β] = α⁻¹ β⁻¹ α β = {comm_ab}")
print(f"  [α, β] is identity? {comm_ab.is_identity()}")
print()


# ===========================================================================
# Section 2: Verify [α, β] is a non-trivial 5-cycle
# ===========================================================================

print_separator("Section 2: [α, β] is a non-trivial 5-cycle")

print(f"  [α, β] = {comm_ab}")
print(f"  order([α, β]) = {comm_ab.order()}")
assert not comm_ab.is_identity(), "[α, β] must be non-trivial"
assert comm_ab.order() == 5, "[α, β] should be a 5-cycle for this pair"
print()
print("  Interpretation:")
print("  - [α, β] ≠ id  →  the commutator encodes AND(1,1) = 1")
print("  - S_5 non-solvable  →  this is achievable with 5-cycles,")
print("    impossible in any solvable (e.g., abelian) group.")
print()

# Explicit element-by-element trace of [α, β]
print("  Trace through α⁻¹ → β⁻¹ → α → β:")
ai, bi = alpha.inverse(), beta.inverse()
for start in range(5):
    after_ai = ai(start)
    after_bi = bi(after_ai)
    after_a  = alpha(after_bi)
    after_b  = beta(after_a)
    print(f"    {start} --α⁻¹--> {after_ai} --β⁻¹--> {after_bi}"
          f" --α--> {after_a} --β--> {after_b}")
print()


# ===========================================================================
# Section 3: AND gate truth table
# ===========================================================================

print_separator("Section 3: AND gate — truth table")

# AND(x1, x2) encoded as: commutator = [α, β] iff x1=x2=1, else identity.
# Interpretation: output = 1  iff  product = [α, β]  (the "target" permutation)

TARGET_AND = comm_ab   # non-trivial 5-cycle = AND-output-1

def and_gate(x1: int, x2: int) -> Permutation:
    """Barrington AND gate: [α^x1, β^x2]."""
    a = alpha if x1 else e5
    b = beta  if x2 else e5
    return commutator(a, b)

print("  Formula: AND(x1,x2) = 1  iff  [α^x1, β^x2] = [α,β]")
print()
print(f"  {'x1':>2} {'x2':>2}  {'[α^x1, β^x2]':<20}  {'AND':>3}")
for x1, x2 in itertools.product([0, 1], repeat=2):
    prod = and_gate(x1, x2)
    out  = 1 if prod == TARGET_AND else 0
    label = "[α,β]" if prod == TARGET_AND else "id   " if prod.is_identity() else str(prod)
    expected = x1 & x2
    assert out == expected, f"AND({x1},{x2}) mismatch: got {out}, expected {expected}"
    print(f"  {x1:>2} {x2:>2}  {label:<20}  {out:>3}")
print()
print("  All AND outputs verified correct.")
print()


# ===========================================================================
# Section 4: OR gate via De Morgan
# ===========================================================================

print_separator("Section 4: OR gate via De Morgan")

# OR(x1, x2) = NOT AND(NOT x1, NOT x2)
# = AND(1-x1, 1-x2) is identity iff (1-x1)=0 AND (1-x2)=0,
#   i.e., x1=1 AND x2=1  →  NOT that = OR = 0 only when x1=x2=0.
# Encoding:
#   OR(x1,x2) = 1  iff  [α^(1-x1), β^(1-x2)] ≠ [α,β]
#             = 1  iff  AND(NOT x1, NOT x2) = 0

def or_gate(x1: int, x2: int) -> Permutation:
    """OR via De Morgan: evaluate AND on (NOT x1, NOT x2), then flip output."""
    return and_gate(1 - x1, 1 - x2)

# OR(x1,x2) = 1  iff  or_gate result is identity  (because AND(~x1,~x2)=0)
def or_output(x1: int, x2: int) -> int:
    prod = or_gate(x1, x2)
    # AND(~x1,~x2)=1  →  or_gate = [α,β]  →  OR=0
    # AND(~x1,~x2)=0  →  or_gate = id      →  OR=1
    return 0 if prod == TARGET_AND else 1

print("  Formula: OR(x1,x2) = NOT AND(NOT x1, NOT x2)")
print("           Output = 1  iff  [α^(1-x1), β^(1-x2)] = id")
print()
print(f"  {'x1':>2} {'x2':>2}  {'[α^(1-x1), β^(1-x2)]':<22}  {'OR':>2}")
for x1, x2 in itertools.product([0, 1], repeat=2):
    prod = or_gate(x1, x2)
    out  = or_output(x1, x2)
    label = "id   " if prod.is_identity() else "[α,β]" if prod == TARGET_AND else str(prod)
    expected = x1 | x2
    assert out == expected, f"OR({x1},{x2}) mismatch: got {out}, expected {expected}"
    print(f"  {x1:>2} {x2:>2}  {label:<22}  {out:>2}")
print()
print("  All OR outputs verified correct.")
print()


# ===========================================================================
# Section 5: NOT gate — output interpretation flip
# ===========================================================================

print_separator("Section 5: NOT gate — swap output interpretation")

# NOT is free at the interpretation level: we do not need a new permutation
# circuit.  Instead, we swap which permutation means "1" vs "0".
#
# Convention A (default):
#   product = [α,β]  →  output = 1
#   product = id     →  output = 0
#
# Convention B (NOT applied):
#   product = [α,β]  →  output = 0
#   product = id     →  output = 1
#
# This is the "output wire negation" trick in branching programs.

def not_gate(x: int) -> int:
    return 1 - x

print("  NOT is encoded as swapping output conventions:")
print("    Standard: id → 0,  [α,β] → 1")
print("    NOT:      id → 1,  [α,β] → 0")
print()
print(f"  {'x':>2}  {'NOT(x)':>6}")
for x in [0, 1]:
    print(f"  {x:>2}  {not_gate(x):>6}")
print()
print("  In a composed program, a NOT on wire w is handled by carrying")
print("  a 'negated' flag; no extra permutation multiplications needed.")
print()


# ===========================================================================
# Section 6: Composed circuit f(x1,x2,x3) = (x1 AND x2) OR x3
# ===========================================================================

print_separator("Section 6: Composed circuit f(x1,x2,x3) = (x1 AND x2) OR x3")

# Naive composition strategy:
# Step A: compute A = AND(x1, x2) as a bit (0 or 1)
# Step B: compute f = OR(A, x3)
#
# In the branching-program model, we would *inline* the sub-programs.  Here
# we demonstrate the two-level composition at the bit level, deriving the
# permutation circuit for each of the 8 inputs.
#
# Permutation circuit for the composed function:
#   We use separate α,β for each gate to avoid interference.
#   Gate 1 (AND): uses α1 = α, β1 = β on inputs x1, x2
#   Gate 2 (OR):  uses α2 = α, β2 = β on inputs (bit from gate 1), x3
#
# For the purpose of this demonstration, we evaluate gate 1 symbolically
# (extracting its bit output) and feed it into gate 2.

def composed_circuit_perm(x1: int, x2: int, x3: int) -> Tuple[Permutation, int]:
    """
    Returns (final_permutation, expected_boolean_output).
    Gate 1: AND(x1, x2) -> bit a
    Gate 2: OR(a, x3)   -> bit out
    Permutation encoding for gate 2 uses the Barrington OR formula.
    """
    # Gate 1 output as a bit
    a = x1 & x2

    # Gate 2: OR(a, x3) as permutation
    # OR(a, x3) = 1  iff  [α^(1-a), β^(1-x3)] = id
    perm_out = or_gate(a, x3)
    bit_out  = or_output(a, x3)

    return perm_out, bit_out

print("  Circuit: f(x1, x2, x3) = (x1 AND x2) OR x3")
print()
print(f"  {'x1':>2} {'x2':>2} {'x3':>2}  {'AND(x1,x2)':>10}  {'f = OR':>6}  {'perm':>22}  {'check':>5}")
for x1, x2, x3 in itertools.product([0, 1], repeat=3):
    perm, out = composed_circuit_perm(x1, x2, x3)
    a = x1 & x2
    expected = a | x3
    label = "id   " if perm.is_identity() else "[α,β]" if perm == TARGET_AND else str(perm)
    assert out == expected, f"f({x1},{x2},{x3}) mismatch: got {out}, expected {expected}"
    check = "OK"
    print(f"  {x1:>2} {x2:>2} {x3:>2}  {a:>10}  {out:>6}  {label:>22}  {check:>5}")
print()
print("  All 8 outputs correct.")
print()


# ===========================================================================
# Section 7: Garbled evaluation — Ishai-Kushilevitz style random masking
# ===========================================================================

print_separator("Section 7: Garbled evaluation (Ishai-Kushilevitz style)")

# The Barrington program for AND(x1, x2) has 4 factors (length-4 word):
#
#   W(x1, x2) = α^{-x1}  ·  β^{-x2}  ·  α^{x1}  ·  β^{x2}
#
# Each factor is either the identity or ±α, ±β depending on the input bits.
#
# Garbling (Ishai-Kushilevitz / PGG-SMC style):
#   Choose random R_0, R_1, R_2, R_3, R_4 ∈ S_5 with R_0 = R_4 (wrap-around).
#   Replace each factor f_i  by  R_{i-1}^{-1} · f_i · R_i.
#
#   The garbled product is:
#     R_0^{-1} f_1 R_1 · R_1^{-1} f_2 R_2 · R_2^{-1} f_3 R_3 · R_3^{-1} f_4 R_4
#   = R_0^{-1} · (f_1 f_2 f_3 f_4) · R_4
#   = R_0^{-1} · W(x1,x2) · R_4
#
#   If we set R_0 = R_4 = e (or cancel them), the product is unchanged.
#   Alternatively, with R_0 = R_4 = R (a fixed mask), evaluators who know R
#   can remove it; evaluators who don't see only a random conjugate.
#
# Security intuition: each garbled factor G_i = R_{i-1}^{-1} f_i R_i is
# uniformly random in S_5 (since R_{i-1}, R_i are independent uniform).
# So individual factors reveal nothing about x1, x2.  The product reveals
# only W(x1,x2) conjugated by R_0 and R_4^{-1}.

random.seed(42)  # reproducible

def garble_factors(factors: List[Permutation],
                   masks: List[Permutation]) -> List[Permutation]:
    """
    Garble a list of factors using masks R_0, R_1, ..., R_len.
    masks must have length len(factors) + 1.
    Garbled factor i = R_{i}^{-1} · factors[i] · R_{i+1}.
    """
    assert len(masks) == len(factors) + 1
    garbled = []
    for i, f in enumerate(factors):
        g = masks[i].inverse() * f * masks[i + 1]
        garbled.append(g)
    return garbled

def and_factors(x1: int, x2: int) -> List[Permutation]:
    """The 4 factors of [α^x1, β^x2] = α^{-x1} β^{-x2} α^{x1} β^{x2}."""
    a  = alpha if x1 else e5
    ai = alpha.inverse() if x1 else e5
    b  = beta  if x2 else e5
    bi = beta.inverse()  if x2 else e5
    return [ai, bi, a, b]

def random_s5() -> Permutation:
    return Permutation.random(5)

print("  Barrington word for AND(x1,x2):  W = α^{-x1} · β^{-x2} · α^{x1} · β^{x2}")
print()
print("  Garbling: choose random R_0,...,R_4 ∈ S_5;")
print("  G_i = R_{i-1}^{-1} · f_i · R_i  (telescoping cancellation)")
print()

# Demonstrate for one specific input (x1=1, x2=1) and one random mask set
x1_demo, x2_demo = 1, 1
factors = and_factors(x1_demo, x2_demo)

# Choose masks R_0,...,R_4 with R_0 = R_4 = e so the outer wrapper cancels
masks = [random_s5() for _ in range(5)]
masks[0] = e5    # fix R_0 = e  (evaluator starts from identity)
masks[4] = e5    # fix R_4 = e  (evaluator ends at identity, so product = W)

garbled = garble_factors(factors, masks)

product_plain   = word_product(factors)
product_garbled = word_product(garbled)

print(f"  Demo: x1={x1_demo}, x2={x2_demo}")
print(f"  Plain factors:   {[str(f) for f in factors]}")
print(f"  Garbled factors: {[str(g) for g in garbled]}")
print()
print(f"  Plain product:   {product_plain}")
print(f"  Garbled product: {product_garbled}")
assert product_plain == product_garbled, "Garbled product must equal plain product (R_0=R_4=e)"
print(f"  Products match:  {product_plain == product_garbled}")
print()

# Show that individual garbled factors look random (not equal to the plain factors)
print("  Individual factor comparison:")
print(f"  {'i':>2}  {'plain f_i':<22}  {'garbled G_i':<22}  same?")
for i, (f, g) in enumerate(zip(factors, garbled)):
    print(f"  {i+1:>2}  {str(f):<22}  {str(g):<22}  {f == g}")
print()

# Verify over all 4 input combinations with fresh random masks
print("  Full garbled AND truth table (fresh random masks per input):")
print(f"  {'x1':>2} {'x2':>2}  {'plain W':>22}  {'garbled prod':>22}  {'match':>5}  {'AND':>3}")
for x1, x2 in itertools.product([0, 1], repeat=2):
    plain_fs = and_factors(x1, x2)
    ms = [random_s5() for _ in range(5)]
    ms[0], ms[4] = e5, e5
    garbled_fs = garble_factors(plain_fs, ms)
    pw = word_product(plain_fs)
    gw = word_product(garbled_fs)
    assert pw == gw, f"Mismatch for AND({x1},{x2})"
    out = 1 if pw == TARGET_AND else 0
    print(f"  {x1:>2} {x2:>2}  {str(pw):>22}  {str(gw):>22}  {'OK':>5}  {out:>3}")
print()
print("  Security note:")
print("  - Each garbled factor G_i = R_{i-1}^{-1} f_i R_i is a conjugate of f_i.")
print("  - With R_{i-1}, R_i uniformly random and independent, G_i is")
print("    uniformly distributed over S_5 regardless of f_i.")
print("  - A party holding only G_i cannot determine x1 or x2.")
print("  - The full product G_1...G_4 = W(x1,x2) reveals only the Boolean")
print("    output AND(x1,x2), not the individual inputs.")
print()

# Empirical uniformity check: fix x1=x2=1 and sample many mask sets.
# Count how often each element of S_5 appears as G_1 (first garbled factor).
print("  Empirical uniformity of G_1 over 1000 random mask sets (x1=x2=1):")
TRIALS = 1000
count: dict = {}
plain_f1 = and_factors(1, 1)[0]   # = α^{-1}
for _ in range(TRIALS):
    R0 = random_s5()
    R1 = random_s5()
    G1 = R0.inverse() * plain_f1 * R1
    key = tuple(G1.perm)
    count[key] = count.get(key, 0) + 1

n_distinct = len(count)
max_count  = max(count.values())
min_count  = min(count.values())
# S_5 has 120 elements; with 1000 trials expect ~8.3 each
print(f"  Distinct values seen: {n_distinct} / 120")
print(f"  Count range: [{min_count}, {max_count}]  (expected ≈ 8.3 each)")
print(f"  Distribution looks {'uniform' if n_distinct >= 100 else 'non-uniform'}")
print()
print("  (A fully uniform distribution would hit all 120 elements given enough trials.)")
print()

print_separator("Summary")
print("""
  Barrington's theorem (1989):
    - NC^1 ⊆ BP_5 (width-5 branching programs over S_5)
    - S_5 non-solvable ⟹ [α, β] ≠ id for 5-cycles α, β
    - AND gate: [α^x1, β^x2] = id iff x1=0 or x2=0
    - OR gate: De Morgan dual, no new permutations needed
    - NOT gate: free (swap output interpretation)

  PGG-SMC connection (§3.1, §7.2):
    - Each factor α^{xi} is a branch gate in the monodromy program
    - Parties hold disjoint sub-words; product = function evaluation
    - Ishai-Kushilevitz garbling: multiply each factor by random masks
      G_i = R_{i-1}^{-1} f_i R_i  →  telescoping product = f_1...f_k
    - Individual G_i uniformly random ⟹ information-theoretically secure
    - This is the PGG "endpoint" functionality: compute(w) = w(base_sheet)
""")
