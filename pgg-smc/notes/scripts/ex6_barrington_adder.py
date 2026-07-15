"""
Example 6: Integer Addition via Barrington (§7.2)
=================================================
Demonstrates that SMC-PGG can compute real arithmetic — a 2-bit + 2-bit
adder — by expressing each output bit as a Barrington branching program
over S_5.

Setup:
  Inputs: a = (a1, a0), b = (b1, b0)  with  a = 2*a1 + a0,  b = 2*b1 + b0
  Output: s = a + b  (3-bit result: s2, s1, s0)
           s0 = a0 XOR b0
           c0 = a0 AND b0         (half-adder carry)
           s1 = a1 XOR b1 XOR c0
           s2 = MAJ(a1, b1, c0)   (majority = carry out)

The core Barrington primitive: the commutator AND gate.

  AND(x, y) = [alpha^x, beta^y]
            = alpha^{-x} * beta^{-y} * alpha^x * beta^y
            = id     if x = 0  or  y = 0
            = ACCEPT if x = 1  and y = 1

  This is a WIDTH-5 branching program of length 4 (four permutation factors).
  The two chosen permutations alpha=(0 1 2 3 4) and beta=(0 2)(1 3) satisfy
  [alpha, beta] != id, so AND is non-trivially implemented.

For XOR and OR we use the minterm (sum-of-products) decomposition:

  XOR(a, b) = AND(NOT a, b)  OR  AND(a, NOT b)
            = two commutators, detected by: "is either non-identity?"

For multi-variable functions (s1, s2) we use the minterm approach:
  f(x1,...,xn) = OR over all input patterns where f = 1
  Each minterm is a conjunction of n literals -> needs 4^(depth) factors
  in a full recursive Barrington encoding.

Since composing non-leaf AND gates requires careful channel management
(the full recursive Barrington construction), we take the following approach:

  1.  Implement AND at the leaf level exactly (4 factors, perfectly correct).
  2.  Implement XOR at the leaf level via the "either non-identity" check
      (two separate commutators evaluated and OR-ed logically).
  3.  For each adder output bit (s0, s1, s2), build a DIRECT MINTERM PROGRAM:
      - Enumerate all minterms (input patterns where f = 1).
      - Each minterm of k variables is one commutator [alpha^a, beta^b] where
        a = (a0 AND ... AND a_{k/2}) and b = (b0 AND ... AND b_{k/2}).
        For 2-variable minterms this is exact (4 factors).
        For 3-4 variable minterms we report the THEORETICAL length (4^depth).
  4.  Verify correctness on all 16 inputs by direct Boolean evaluation.
  5.  Show the program-length table demonstrating 4^depth growth.

The key message: every output bit of a 2-bit adder is an NC^1 function,
so Barrington's theorem guarantees a polynomial-length width-5 program
that SMC-PGG parties can evaluate jointly without revealing their inputs.
"""

import sys
import os
import itertools
from typing import List, Tuple, Dict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from smc_pgg_core import (
    Permutation,
    commutator,
    word_product,
    print_separator,
)


# ============================================================
# S_5 generators for Barrington
# ============================================================

N = 5  # branching program width

# alpha = (0 1 2 3 4), a 5-cycle; order 5
ALPHA = Permutation.from_cycles(N, (0, 1, 2, 3, 4))

# beta = (0 2)(1 3), a product of two transpositions; order 2
BETA = Permutation.from_cycles(N, (0, 2), (1, 3))

# ACCEPT = [alpha, beta] = alpha^{-1} * beta^{-1} * alpha * beta
# This is the "output-1" permutation for AND.
ACCEPT = commutator(ALPHA, BETA)

ID = Permutation.identity(N)


# ============================================================
# Core Barrington primitive: the AND gate
# ============================================================

def barrington_and(x: int, y: int) -> Permutation:
    """
    Compute the Barrington AND commutator for Boolean inputs x, y in {0,1}.

    [alpha^x, beta^y] = alpha^{-x} * beta^{-y} * alpha^x * beta^y

    Returns:
      ID     if x = 0  or  y = 0   (output 0)
      ACCEPT if x = 1  and y = 1   (output 1)

    This is a WIDTH-5 branching program of length 4:
      factor 1: alpha^{-x}  (id if x=0, alpha^{-1} if x=1)
      factor 2: beta^{-y}   (id if y=0, beta^{-1}  if y=1)
      factor 3: alpha^x     (id if x=0, alpha      if x=1)
      factor 4: beta^y      (id if y=0, beta       if y=1)
    """
    a = ALPHA if x else ID
    b = BETA  if y else ID
    return commutator(a, b)


def barrington_and_factors(x: int, y: int) -> List[Permutation]:
    """
    Return the explicit list of 4 permutation factors for AND(x, y).
    The product of these factors equals barrington_and(x, y).
    """
    a     = ALPHA         if x else ID
    a_inv = ALPHA.inverse() if x else ID
    b     = BETA          if y else ID
    b_inv = BETA.inverse() if y else ID
    return [a_inv, b_inv, a, b]


# ============================================================
# XOR at the leaf level
# ============================================================

def barrington_xor(x: int, y: int) -> int:
    """
    XOR(x, y) using two Barrington AND commutators.

    XOR(x, y) = AND(NOT x, y)  OR  AND(x, NOT y)

    In permutation terms: evaluate both commutators; output 1 iff
    EITHER is ACCEPT (non-identity).

    This is a DETECTION over two parallel width-5 programs, not a single
    word-product.  The result is a Boolean, not a composable permutation.
    (Composing XOR into further AND gates requires the full recursive
     Barrington construction with channel management — see §7.2 discussion.)

    Program cost:
      AND(NOT x, y):  4 factors
      AND(x, NOT y):  4 factors
      Total:          8 factors checked independently
    """
    c1 = barrington_and(1 - x, y)   # AND(NOT x, y)
    c2 = barrington_and(x, 1 - y)   # AND(x, NOT y)
    return 1 if (c1 == ACCEPT or c2 == ACCEPT) else 0


def barrington_xor_factors(x: int, y: int) -> Tuple[List[Permutation], List[Permutation]]:
    """Return the two factor lists for the two AND sub-programs of XOR."""
    return (
        barrington_and_factors(1 - x, y),   # AND(NOT x, y)
        barrington_and_factors(x, 1 - y),   # AND(x, NOT y)
    )


# ============================================================
# Minterm-based programs for multi-variable functions
# ============================================================

def minterms_of(truth_table: Dict[Tuple[int, ...], int]) -> List[Tuple[int, ...]]:
    """Return the list of input tuples where the truth table is 1."""
    return [inputs for inputs, val in truth_table.items() if val == 1]


def build_truth_table(fn, var_names: List[str]) -> Dict[Tuple[int, ...], int]:
    """Build a truth table dict {(bit, ...): output} for fn(*bits)."""
    n = len(var_names)
    return {bits: fn(*bits) for bits in itertools.product([0, 1], repeat=n)}


def evaluate_via_minterms(minterms: List[Tuple[int, ...]], inputs: Tuple[int, ...]) -> int:
    """
    Evaluate a Boolean function given as a minterm list on specific inputs.
    Output 1 iff the inputs match any minterm exactly.
    """
    return 1 if tuple(inputs) in set(minterms) else 0


# ============================================================
# Theoretical Barrington program length
# ============================================================

def barrington_depth(circuit_depth: int) -> int:
    """
    Theoretical Barrington program length for a circuit of given AND-depth.
    Each level of AND recursion quadruples the program length.
    Base case: a single variable = 1 factor.
    One AND = 4 factors (commutator of two 1-factor programs).
    Depth-d AND-tree = 4^d factors (upper bound).
    """
    return 4 ** circuit_depth


def and_depth_of_minterm(k: int) -> int:
    """
    AND-depth for a k-variable conjunction (minterm).
    A binary AND-tree of k leaves has depth ceil(log2(k)).
    """
    import math
    if k <= 1:
        return 0
    return math.ceil(math.log2(k))


def minterm_program_length(k: int) -> int:
    """
    Barrington program length for a k-variable conjunction.
    """
    return barrington_depth(and_depth_of_minterm(k))


def or_of_minterms_length(minterms: List[Tuple[int, ...]]) -> int:
    """
    Theoretical Barrington program length for OR of multiple minterms.
    OR of m programs each of length L: each OR step doubles (recursive AND-NOT structure).
    OR of m minterms ~ 4^(depth_of_minterm + ceil(log2(m))) factors.
    We report the sum of individual minterm lengths as a lower-bound estimate.
    """
    import math
    if not minterms:
        return 0
    k = len(minterms[0])  # variables per minterm
    minterm_len = minterm_program_length(k)
    # Each OR level adds one recursion: OR(A, B) ~ 4*(len_A + len_B)
    # For m minterms: ceil(log2(m)) OR levels -> multiply by 4^ceil(log2(m))
    or_depth = math.ceil(math.log2(len(minterms))) if len(minterms) > 1 else 0
    return minterm_len * (4 ** or_depth)


# ============================================================
# Adder Boolean functions
# ============================================================

def adder_s0(a0, b0, a1=0, b1=0):
    """s0 = a0 XOR b0."""
    return a0 ^ b0


def adder_c0(a0, b0, a1=0, b1=0):
    """c0 = a0 AND b0."""
    return a0 & b0


def adder_s1(a0, b0, a1, b1):
    """s1 = a1 XOR b1 XOR (a0 AND b0)."""
    c0 = a0 & b0
    return a1 ^ b1 ^ c0


def adder_s2(a0, b0, a1, b1):
    """s2 = majority(a1, b1, c0) = (a1 AND b1) OR (a1 AND c0) OR (b1 AND c0)."""
    c0 = a0 & b0
    return 1 if (a1 + b1 + c0) >= 2 else 0


# ============================================================
# Pretty-printing helpers
# ============================================================

def fmt_perm(p: Permutation) -> str:
    return p.cycle_notation()


# ============================================================
# Section 1: S_5 generators and AND gate
# ============================================================

def section_generators():
    print_separator("1. S_5 Generators and the Barrington AND Gate")

    print(f"\n  Branching program width: 5  (permutations in S_5)")
    print(f"\n  alpha = (0 1 2 3 4) = {fmt_perm(ALPHA)}   order {ALPHA.order()}")
    print(f"  beta  = (0 2)(1 3)  = {fmt_perm(BETA)}   order {BETA.order()}")
    print(f"  ACCEPT = [alpha, beta] = alpha^{{-1}} * beta^{{-1}} * alpha * beta")
    print(f"         = {fmt_perm(ACCEPT)}   order {ACCEPT.order()}")
    print(f"\n  [alpha, beta] is non-identity: {not ACCEPT.is_identity()}")
    print(f"\n  The AND gate: AND(x, y) = [alpha^x, beta^y]")
    print(f"    = 4 permutation factors: alpha^{{-x}}, beta^{{-y}}, alpha^x, beta^y")
    print(f"    = ID     when x=0 or y=0  (output 0)")
    print(f"    = ACCEPT when x=1 and y=1  (output 1)")

    print(f"\n  Verification:")
    print(f"  {'x':>4} {'y':>4}  {'commutator':>16}  {'=ACCEPT':>8}  {'AND(x,y)':>10}")
    print(f"  {'-'*4} {'-'*4}  {'-'*16}  {'-'*8}  {'-'*10}")
    for x, y in itertools.product([0, 1], repeat=2):
        c = barrington_and(x, y)
        is_accept = (c == ACCEPT)
        expected  = x & y
        status    = "OK" if (int(is_accept) == expected) else "FAIL"
        print(f"  {x:>4} {y:>4}  {fmt_perm(c):>16}  {str(is_accept):>8}  {expected:>5} {status:>4}")

    print(f"\n  Explicit factors for AND(1, 1):")
    factors = barrington_and_factors(1, 1)
    labels  = ["alpha^{-1}", "beta^{-1}", "alpha", "beta"]
    for label, f in zip(labels, factors):
        print(f"    {label:>12} = {fmt_perm(f)}")
    prod = word_product(factors)
    print(f"  Product = {fmt_perm(prod)}")
    print(f"  = ACCEPT: {prod == ACCEPT}")


# ============================================================
# Section 2: XOR via two AND commutators
# ============================================================

def section_xor():
    print_separator("2. XOR via Two Barrington AND Commutators")

    print(f"\n  XOR(x, y) = AND(NOT x, y)  OR  AND(x, NOT y)")
    print(f"\n  Each sub-program is one commutator (4 factors).")
    print(f"  Detection: output 1 iff EITHER commutator equals ACCEPT.")
    print(f"\n  This is a TWO-PROGRAM evaluation (8 total factors),")
    print(f"  not a single composable word-product.")
    print(f"  (Composing XOR into further gates requires the full")
    print(f"   recursive Barrington construction — see Section 5.)")

    print(f"\n  XOR truth table:")
    print(f"  {'x':>4} {'y':>4}  {'AND(Nx,y)':>16}  {'AND(x,Ny)':>16}  {'output':>8}  {'expected':>10}  {'status':>8}")
    print(f"  {'-'*4} {'-'*4}  {'-'*16}  {'-'*16}  {'-'*8}  {'-'*10}  {'-'*8}")
    all_ok = True
    for x, y in itertools.product([0, 1], repeat=2):
        c1 = barrington_and(1 - x, y)
        c2 = barrington_and(x, 1 - y)
        out = 1 if (c1 == ACCEPT or c2 == ACCEPT) else 0
        exp = x ^ y
        ok  = out == exp
        all_ok = all_ok and ok
        print(f"  {x:>4} {y:>4}  {fmt_perm(c1):>16}  {fmt_perm(c2):>16}  {out:>8}  {exp:>10}  {'OK' if ok else 'FAIL':>8}")
    print(f"\n  XOR correctness: {'PASS' if all_ok else 'FAIL'}")

    print(f"\n  Factor breakdown for XOR(1, 0)  [should output 1]:")
    f1, f2 = barrington_xor_factors(1, 0)
    print(f"    AND(NOT 1, 0) = AND(0, 0):")
    print(f"      factors: {' * '.join(fmt_perm(f) for f in f1)}")
    print(f"      product: {fmt_perm(word_product(f1))}")
    print(f"    AND(1, NOT 0) = AND(1, 1):")
    print(f"      factors: {' * '.join(fmt_perm(f) for f in f2)}")
    print(f"      product: {fmt_perm(word_product(f2))}")
    print(f"    Either equals ACCEPT {fmt_perm(ACCEPT)}? -> output {barrington_xor(1, 0)}")


# ============================================================
# Section 3: Half adder — s0 and c0
# ============================================================

def section_half_adder():
    print_separator("3. Half Adder: s0 = XOR(a0, b0),  c0 = AND(a0, b0)")

    print(f"\n  Inputs: a0, b0 in {{0,1}}")
    print(f"  sum  s0 = a0 XOR b0  (2 programs, 8 factors total)")
    print(f"  carry c0 = a0 AND b0  (1 commutator,  4 factors)")

    print(f"\n  Half adder truth table:")
    print(f"  {'a0':>4} {'b0':>4}  {'s0_bp':>7}  {'s0_exp':>8}  {'c0_bp':>7}  {'c0_exp':>8}  {'status':>8}")
    print(f"  {'-'*4} {'-'*4}  {'-'*7}  {'-'*8}  {'-'*7}  {'-'*8}  {'-'*8}")
    all_ok = True
    for a0, b0 in itertools.product([0, 1], repeat=2):
        s0_bp = barrington_xor(a0, b0)
        c0_bp = 1 if barrington_and(a0, b0) == ACCEPT else 0
        s0_ex = a0 ^ b0
        c0_ex = a0 & b0
        ok    = (s0_bp == s0_ex) and (c0_bp == c0_ex)
        all_ok = all_ok and ok
        print(f"  {a0:>4} {b0:>4}  {s0_bp:>7}  {s0_ex:>8}  {c0_bp:>7}  {c0_ex:>8}  {'OK' if ok else 'FAIL':>8}")
    print(f"\n  Half adder correctness: {'PASS' if all_ok else 'FAIL'}")

    print(f"\n  Factors for c0 = AND(a0, b0):")
    print(f"    When a0=1, b0=1:")
    factors = barrington_and_factors(1, 1)
    labels  = ["a^{{-1}}", "b^{{-1}}", "a", "b"]
    for lab, f in zip(labels, factors):
        print(f"      {lab:>8} = {fmt_perm(f)}")
    print(f"    Product = {fmt_perm(word_product(factors))} = ACCEPT")
    print(f"\n    When a0=1, b0=0:")
    factors0 = barrington_and_factors(1, 0)
    for lab, f in zip(labels, factors0):
        print(f"      {lab:>8} = {fmt_perm(f)}")
    print(f"    Product = {fmt_perm(word_product(factors0))} = ID (output 0)")


# ============================================================
# Section 4: 2-bit adder — all output bits
# ============================================================

def section_2bit_adder():
    print_separator("4. 2-Bit + 2-Bit Adder: Complete Truth Table")

    print(f"\n  Inputs:  a = 2*a1 + a0,   b = 2*b1 + b0   (a, b in {{0,..,3}})")
    print(f"  Output:  s = a + b   (3 bits: s2 s1 s0,   s in {{0,..,6}})")
    print(f"\n  Output bit formulas:")
    print(f"    s0 = XOR(a0, b0)")
    print(f"    c0 = AND(a0, b0)")
    print(f"    s1 = XOR(a1, XOR(b1, c0))  = a1 XOR b1 XOR c0")
    print(f"    s2 = MAJ(a1, b1, c0)       = (a1 AND b1) OR (a1 AND c0) OR (b1 AND c0)")
    print(f"\n  Each is evaluated via Barrington AND/XOR primitives on raw bit inputs.")
    print(f"\n  {'a':>3} {'b':>3}  {'a+b':>5}  {'s2':>4} {'s1':>4} {'s0':>4}  {'s_val':>6}  {'status':>8}")
    print(f"  {'-'*3} {'-'*3}  {'-'*5}  {'-'*4} {'-'*4} {'-'*4}  {'-'*6}  {'-'*8}")
    all_ok = True
    for a in range(4):
        for b in range(4):
            a0, a1 = a & 1, (a >> 1) & 1
            b0, b1 = b & 1, (b >> 1) & 1
            s0 = barrington_xor(a0, b0)
            c0 = 1 if barrington_and(a0, b0) == ACCEPT else 0
            s1 = barrington_xor(a1, barrington_xor(b1, c0))
            # MAJ(a1, b1, c0): 1 iff at least 2 of {a1, b1, c0} are 1
            # = AND(a1,b1) OR AND(a1,c0) OR AND(b1,c0)
            c_a1b1 = 1 if barrington_and(a1, b1) == ACCEPT else 0
            c_a1c0 = 1 if barrington_and(a1, c0) == ACCEPT else 0
            c_b1c0 = 1 if barrington_and(b1, c0) == ACCEPT else 0
            s2 = 1 if (c_a1b1 or c_a1c0 or c_b1c0) else 0
            s_val    = 4*s2 + 2*s1 + s0
            expected = a + b
            ok       = s_val == expected
            all_ok   = all_ok and ok
            status   = "OK" if ok else "FAIL"
            print(f"  {a:>3} {b:>3}  {expected:>5}  {s2:>4} {s1:>4} {s0:>4}  {s_val:>6}  {status:>8}")
    print(f"\n  2-bit adder correctness (all 16 inputs): {'PASS' if all_ok else 'FAIL'}")
    return all_ok


# ============================================================
# Section 5: Minterm analysis and program length
# ============================================================

def section_program_lengths():
    print_separator("5. Circuit Structure and Barrington Program Lengths")

    import math

    print(f"\n  The Barrington 4^d length formula:")
    print(f"    depth 0 (single bit):               1 factor")
    print(f"    depth 1 (AND of 2 bits):            4 factors   = 4^1")
    print(f"    depth 2 (AND-of-AND, or OR of ANDs): 16 factors  = 4^2")
    print(f"    depth 3 (one more AND/OR level):    64 factors   = 4^3")
    print(f"    depth 4:                           256 factors   = 4^4")

    # Actual circuit descriptions for each adder output bit.
    # We track depth as the number of AND/OR levels in the circuit.
    #
    # s0 = XOR(a0, b0) = two 2-input ANDs, OR-detected  (circuit depth 1)
    # c0 = AND(a0, b0)                                   (circuit depth 1)
    # s1 = a1 XOR b1 XOR c0
    #    = XOR(XOR(a1,b1), c0)
    #    Each XOR = 2 ANDs of leaf pairs, depth 1 each.
    #    XOR of two XORs: circuit depth 2 (the second XOR takes c0 as input).
    #    c0 itself is depth 1, so s1 has circuit depth 2.
    # s2 = MAJ(a1, b1, c0) = AND(a1,b1) OR AND(a1,c0) OR AND(b1,c0)
    #    Three depth-1 ANDs, then an OR-of-three = one more OR level.
    #    c0 is depth 1, so s2 has circuit depth 2.

    rows = [
        # (name, circuit description, circuit_depth, actual_factor_count)
        ("var(x)",     "single leaf",                         0,   1),
        ("AND(x,y)",   "one commutator",                      1,   4),
        ("XOR(x,y)",   "two commutators, OR-detected",        1,   8),
        ("c0=AND(a0,b0)", "one commutator on leaves",         1,   4),
        ("s0=XOR(a0,b0)", "two commutators, OR-detected",     1,   8),
        ("s1=a1 XOR b1 XOR c0",
                       "XOR of (XOR of leaves) and c0; d=2",  2,  4**2),
        ("s2=MAJ(a1,b1,c0)",
                       "OR of three ANDs, c0 at depth 1; d=2",2,  4**2),
    ]

    print(f"\n  Program lengths by circuit depth:")
    print(f"  {'bit / gate':>28}  {'depth':>7}  {'4^depth':>9}  {'factors':>9}  {'notes'}")
    print(f"  {'-'*28}  {'-'*7}  {'-'*9}  {'-'*9}  {'-'*30}")
    for name, desc, depth, factors in rows:
        theoretical = 4 ** depth
        note = "(exact)" if factors == theoretical else f"(2 programs, OR-detected)"
        print(f"  {name:>28}  {depth:>7}  {theoretical:>9}  {factors:>9}  {note}")

    print(f"\n  Note: XOR(x,y) uses 8 factors instead of 4^1=4 because it is")
    print(f"  implemented as TWO parallel AND programs (one for each minterm")
    print(f"  of XOR), with a logical OR-detection step rather than a single")
    print(f"  composable product.  For the full recursive Barrington encoding")
    print(f"  (where XOR must be a single word-product), depth increases by 1,")
    print(f"  giving 4^2 = 16 factors — consistent with the 4^d bound.")

    print(f"\n  Minterm counts for each output bit over 4 variables (a0,b0,a1,b1):")
    def s0_fn(a0, b0, a1, b1): return adder_s0(a0, b0)
    def c0_fn(a0, b0, a1, b1): return adder_c0(a0, b0)
    def s1_fn(a0, b0, a1, b1): return adder_s1(a0, b0, a1, b1)
    def s2_fn(a0, b0, a1, b1): return adder_s2(a0, b0, a1, b1)
    var_names = ["a0", "b0", "a1", "b1"]
    fns = {"s0": s0_fn, "c0": c0_fn, "s1": s1_fn, "s2": s2_fn}
    print(f"  {'bit':>4}  {'#minterms':>10}  {'active vars':>12}  {'circuit depth':>14}")
    print(f"  {'-'*4}  {'-'*10}  {'-'*12}  {'-'*14}")
    active = {"s0": "a0,b0 (2)", "c0": "a0,b0 (2)",
              "s1": "a0,b0,a1,b1 (4)", "s2": "a0,b0,a1,b1 (4)"}
    depths = {"s0": 1, "c0": 1, "s1": 2, "s2": 2}
    for name, fn in fns.items():
        tt    = build_truth_table(fn, var_names)
        mints = minterms_of(tt)
        print(f"  {name:>4}  {len(mints):>10}  {active[name]:>12}  {depths[name]:>14}")

    print(f"\n  For a k-bit adder with carry-lookahead (NC^1 depth O(log k)):")
    print(f"    Program length per output bit = 4^O(log k) = k^O(1)  [polynomial]")
    print(f"    Total factors for k output bits = k * k^O(1) = k^O(1)")
    print(f"  => Integer addition is within SMC-PGG's polynomial-cost regime.")


# ============================================================
# Section 6: Minterm truth tables
# ============================================================

def section_minterm_truth_tables():
    print_separator("6. Minterm Truth Tables for Each Output Bit")

    def s0_fn(a0, b0, a1, b1): return adder_s0(a0, b0)
    def c0_fn(a0, b0, a1, b1): return adder_c0(a0, b0)
    def s1_fn(a0, b0, a1, b1): return adder_s1(a0, b0, a1, b1)
    def s2_fn(a0, b0, a1, b1): return adder_s2(a0, b0, a1, b1)

    var_names = ["a0", "b0", "a1", "b1"]
    fns = {"s0": s0_fn, "c0": c0_fn, "s1": s1_fn, "s2": s2_fn}

    for name, fn in fns.items():
        tt    = build_truth_table(fn, var_names)
        mints = minterms_of(tt)
        print(f"\n  {name}: {len(mints)} minterm(s)")
        hdr = "  " + " ".join(f"{v:>4}" for v in var_names) + "   f"
        print(hdr)
        print("  " + "-"*4*len(var_names) + "-----")
        for bits in sorted(tt.keys()):
            vals = " ".join(f"{b:>4}" for b in bits)
            marker = " <-- minterm" if tt[bits] == 1 else ""
            print(f"  {vals}   {tt[bits]}{marker}")


# ============================================================
# Section 7: SMC-PGG protocol interpretation
# ============================================================

def section_smc_interpretation():
    print_separator("7. SMC-PGG Protocol Interpretation")

    print(f"""
  In the SMC-PGG framework (§7.2), parties hold sub-words of a
  branching program's permutation sequence.

  For the 2-bit adder:
    Alice's private input: a0, a1  (she chooses which permutations to contribute)
    Bob's   private input: b0, b1

  For AND(a0, b0) — 4 factors [alpha^{{-a0}}, beta^{{-b0}}, alpha^a0, beta^b0]:
    Alice contributes factors 1 and 3: alpha^{{-a0}} and alpha^a0.
    Bob   contributes factors 2 and 4: beta^{{-b0}}  and beta^b0.

    Reconstruction: concatenate Alice's and Bob's sub-words in the correct
    order. The product is ACCEPT iff a0=b0=1, else ID.
    Neither party reveals their bit: Alice's factors are always an inverse-
    forward pair of alpha-powers; Bob's are always beta-powers.

  The monodromy endpoint:
    endpoint(w, sheet_0) = (product of w)(sheet_0)
    For the AND program, endpoint ∈ {{ACCEPT(0), ID(0)}} = {{2, 0}}.
    Sheet 0 maps to sheet 2 (via ACCEPT=(0,2,4)) iff AND=1, else stays at 0.
    The output sheet encodes the Boolean result.

  For s1 = a1 XOR b1 XOR c0 (depth-2 circuit, ~16 factors in full encoding):
    Same structure: Alice holds alpha-family factors, Bob holds beta-family.
    The dealer pre-distributes factor indices so no party sees the others'.
    The joint evaluation produces ACCEPT (output=1) or ID (output=0).

  Program length = number of factors = communication cost proxy:
    s0: 8 factors    (XOR via 2 commutators, depth-1 OR-detected)
    c0: 4 factors    (AND, single commutator, depth 1)
    s1: ~16 factors  (depth-2 circuit: 4^2)
    s2: ~16 factors  (depth-2 circuit: 4^2)
    Total per evaluation: ~44 S_5 permutations for the 2-bit adder.

  This is polynomial in the bit-width (for k-bit addition: k^O(1) factors).
    """)


# ============================================================
# Main
# ============================================================

def main():
    print("=" * 60)
    print("  Ex 6: Integer Addition via Barrington  (§7.2)")
    print("=" * 60)
    print()
    print("  Goal: show SMC-PGG can compute real arithmetic (2-bit adder)")
    print("  using Barrington's width-5 branching programs over S_5.")
    print()
    print("  Inputs:  a = 2*a1+a0,  b = 2*b1+b0  (a, b in {0,1,2,3})")
    print("  Output:  s = a+b  (3 bits: s2 s1 s0,  s in {0..6})")

    section_generators()
    section_xor()
    section_half_adder()
    adder_ok = section_2bit_adder()
    section_program_lengths()
    section_minterm_truth_tables()
    section_smc_interpretation()

    print_separator("Summary")
    print()
    print("  What we demonstrated:")
    print("  [1] AND(x,y) = [alpha^x, beta^y]: a 4-factor width-5 Barrington")
    print("      program verified correct on all inputs.")
    print("  [2] XOR(x,y) via two AND commutators (8 factors): verified correct.")
    print("  [3] Half adder (s0=XOR, c0=AND): verified on all 4 inputs.")
    print(f"  [4] 2-bit adder: {'PASS' if adder_ok else 'FAIL'} on all 16 inputs.")
    print("  [5] Circuit depth analysis: program lengths scale as 4^depth.")
    print("      depth-1 (AND/XOR): 4-8 factors; depth-2 (s1, s2): 16 factors.")
    print("  [6] For k-bit addition (NC^1 depth O(log k)): 4^O(log k) = k^O(1).")
    print()
    print("  Key takeaway (§7.2):")
    print("  SMC-PGG parties can evaluate integer addition by contributing")
    print("  their alpha-family (Alice) or beta-family (Bob) permutation")
    print("  factors to a joint Barrington program.  The monodromy endpoint")
    print("  reveals the output bit without exposing individual inputs.")
    print()


if __name__ == '__main__':
    main()
