"""
Example 5: RAAG Trace Monoid Parallelism (§8)
=============================================
Demonstrates how the independence graph of a trace monoid determines
parallel execution via Foata normal form.

Setup
-----
G = S_5, generators σ1..σ4 = adjacent transpositions (i, i+1):
  σ1 = (0 1),  σ2 = (1 2),  σ3 = (2 3),  σ4 = (3 4)

Independence relation:
  σ_i and σ_j are independent iff |i - j| >= 2
  Independent pairs:  (σ1, σ3), (σ1, σ4), (σ2, σ4)
  Dependent pairs:    (σ1, σ2), (σ2, σ3), (σ3, σ4)   [adjacent, don't commute]

The independence graph encodes which generators can execute in parallel
without affecting the outcome (trace equivalence).
"""

import itertools
from typing import List, Tuple, Set, Dict
from smc_pgg_core import (
    Permutation, MonodromyGroup, TraceMonoid,
    word_product, print_separator
)


# ============================================================
# Section 1: Setup — S_5 with adjacent transpositions
# ============================================================

def setup_s5() -> Tuple[MonodromyGroup, Dict[str, Permutation]]:
    """
    Build S_5 with generators σ1..σ4 = adjacent transpositions.
    σ_k swaps positions k-1 and k (0-indexed: σ1 swaps 0,1; σ2 swaps 1,2; etc.)
    """
    n = 5
    gens = {
        'σ1': Permutation.transposition(n, 0, 1),  # (0 1)
        'σ2': Permutation.transposition(n, 1, 2),  # (1 2)
        'σ3': Permutation.transposition(n, 2, 3),  # (2 3)
        'σ4': Permutation.transposition(n, 3, 4),  # (3 4)
    }
    mono = MonodromyGroup(n_sheets=n, generators=gens)
    return mono, gens


def make_trace_monoid_partial() -> TraceMonoid:
    """Physical independence: |i - j| >= 2."""
    alphabet = ['σ1', 'σ2', 'σ3', 'σ4']
    independence = {
        ('σ1', 'σ3'),
        ('σ1', 'σ4'),
        ('σ2', 'σ4'),
    }
    return TraceMonoid(alphabet, independence)


# ============================================================
# Section 2: Verify independence — commutativity check
# ============================================================

def verify_independence(gens: Dict[str, Permutation]) -> None:
    print_separator("Section 2: Verify independence via commutativity")

    pairs_independent = [('σ1', 'σ3'), ('σ1', 'σ4'), ('σ2', 'σ4')]
    pairs_dependent   = [('σ1', 'σ2'), ('σ2', 'σ3'), ('σ3', 'σ4')]

    print("\nClaim: σ_i and σ_j commute iff |i - j| >= 2\n")
    print("  Pair         Commutes?   Expected")
    print("  " + "-" * 38)
    for a, b in pairs_independent:
        commutes = gens[a].commutes_with(gens[b])
        status = "YES" if commutes else "NO "
        check  = "OK" if commutes else "FAIL"
        print(f"  ({a}, {b})   {status}         independent  [{check}]")
    for a, b in pairs_dependent:
        commutes = gens[a].commutes_with(gens[b])
        status = "YES" if commutes else "NO "
        check  = "OK" if not commutes else "FAIL"
        print(f"  ({a}, {b})   {status}         dependent    [{check}]")


# ============================================================
# Section 3: Foata normal form of w = σ1 σ3 σ2 σ4 σ1 σ3
# ============================================================

def foata_of_word(mono: MonodromyGroup, tm: TraceMonoid) -> List[str]:
    """Compute and display Foata NF of the target word."""
    print_separator("Section 3: Foata normal form of w = σ1 σ3 σ2 σ4 σ1 σ3")

    word = ['σ1', 'σ3', 'σ2', 'σ4', 'σ1', 'σ3']
    fnf  = tm.foata_normal_form(word)

    print(f"\n  Word:  {' '.join(word)}")
    print(f"  Length: {len(word)} letters\n")
    print("  Foata normal form — parallel execution schedule:")
    print()
    for round_idx, block in enumerate(fnf, 1):
        gens_str  = ', '.join(block)
        is_plural = len(block) > 1
        note      = "(independent, execute in parallel)" if is_plural else "(single step)"
        print(f"    Round {round_idx}: [{gens_str}]    {note}")
    print()
    print(f"  Total: {len(fnf)} rounds instead of {len(word)} sequential steps")
    print(f"  Speedup factor: {len(word)}/{len(fnf)} = {len(word)/len(fnf):.1f}x")

    return word


# ============================================================
# Section 4: Trace-equivalent words evaluate to the same group element
# ============================================================

def trace_equivalent_words(mono: MonodromyGroup, tm: TraceMonoid,
                            original_word: List[str]) -> None:
    print_separator("Section 4: Trace-equivalent words give the same group element")

    def swap_independent(w: List[str], i: int) -> List[str]:
        """Swap w[i] and w[i+1] if they are independent (valid trace step)."""
        if i + 1 < len(w) and tm.are_independent(w[i], w[i + 1]):
            new_w = w[:]
            new_w[i], new_w[i + 1] = new_w[i + 1], new_w[i]
            return new_w
        return w

    # Generate a family of trace-equivalent words by bubble-sorting
    # using only valid independent swaps.
    words = [original_word[:]]
    seen  = {tuple(original_word)}

    # BFS over reachable words by single independent adjacent swaps
    queue = [original_word[:]]
    while queue:
        w = queue.pop(0)
        for i in range(len(w) - 1):
            w2 = swap_independent(w, i)
            if tuple(w2) not in seen:
                seen.add(tuple(w2))
                words.append(w2)
                queue.append(w2)

    print(f"\n  Original word:  {' '.join(original_word)}")
    print(f"  Found {len(words)} trace-equivalent words by adjacent independent swaps.\n")

    reference = mono.evaluate_word(original_word)
    print(f"  Reference evaluation: {reference}")
    print()
    all_equal = True
    for w in words:
        val   = mono.evaluate_word(w)
        match = "OK" if val == reference else "MISMATCH"
        print(f"    {' '.join(w)}  ->  {val}  [{match}]")
        if val != reference:
            all_equal = False

    print()
    if all_equal:
        print("  All trace-equivalent words evaluate to the SAME group element.")
    else:
        print("  ERROR: some words gave a different result — independence check failed.")


# ============================================================
# Section 5: Compare Foata depth under different independence graphs
# ============================================================

def compare_independence_graphs(mono: MonodromyGroup) -> None:
    print_separator("Section 5: Foata depth vs. independence graph")

    word = ['σ1', 'σ3', 'σ2', 'σ4', 'σ1', 'σ3']
    alphabet = ['σ1', 'σ2', 'σ3', 'σ4']

    # Three independence graphs
    I_empty   = set()                                           # (a) no independence
    I_partial = {('σ1', 'σ3'), ('σ1', 'σ4'), ('σ2', 'σ4')}   # (b) physical
    all_pairs = set()
    for a in alphabet:
        for b in alphabet:
            if a != b:
                all_pairs.add((a, b))
    I_full    = all_pairs                                        # (c) all commute (abelian)

    configs = [
        ("I = ∅  (no independence — fully sequential)",    I_empty),
        ("I = {(σ1,σ3),(σ1,σ4),(σ2,σ4)}  (physical)",      I_partial),
        ("I = Σ×Σ\\diag  (full independence — abelian)",    I_full),
    ]

    print(f"\n  Word: {' '.join(word)}  (length {len(word)})\n")
    print(f"  {'Config':<46}  Depth  FNF blocks")
    print("  " + "-" * 72)

    for label, indep in configs:
        tm    = TraceMonoid(alphabet, indep)
        fnf   = tm.foata_normal_form(word)
        depth = len(fnf)
        blocks_str = '  |  '.join('[' + ', '.join(b) + ']' for b in fnf)
        print(f"  {label:<46}  {depth}      {blocks_str}")

    print()
    print("  Observation:")
    print("    More independence -> shallower Foata depth -> fewer parallel rounds.")
    print("    But independence requires generators to genuinely commute in G,")
    print("    which constrains the group structure (see Section 6).")


# ============================================================
# Section 6: The abelian trade-off — can't compute AND
# ============================================================

def abelian_tradeoff(gens: Dict[str, Permutation]) -> None:
    print_separator("Section 6: Abelian trade-off — full independence limits computation")

    print("""
  Barrington's theorem: NC1 = width-5 branching programs = words in S_5.
  The key ingredient is a non-abelian generator pair with [σ_i, σ_j] != id.

  If all generators commute (abelian monodromy group), then:
    - Every commutator [a, b] = a^{-1} b^{-1} a b = id
    - Barrington's AND construction collapses: [α^x, β^y] = id for all x, y
    - The protocol can only compute affine (linear) functions, not AND

  We verify this concretely with the abelian group Z/2 x Z/2 x Z/2.
""")

    # Abelian example: Z_2^3 embedded as bit-flip permutations on {0..7}
    # Each generator flips one bit: f_k(x) = x XOR 2^k
    n_ab  = 8
    gens_ab = {
        'a': Permutation([1, 0, 3, 2, 5, 4, 7, 6]),  # flip bit 0
        'b': Permutation([2, 3, 0, 1, 6, 7, 4, 5]),  # flip bit 1
        'c': Permutation([4, 5, 6, 7, 0, 1, 2, 3]),  # flip bit 2
    }

    print("  Abelian group (Z_2)^3 — generators flip bits:")
    for name, g in gens_ab.items():
        print(f"    {name}: {g}")

    print("\n  Commutativity check (all must commute for full independence):")
    for (na, ga), (nb, gb) in itertools.combinations(gens_ab.items(), 2):
        commutes = ga.commutes_with(gb)
        comm_val = ga.inverse() * gb.inverse() * ga * gb
        print(f"    [{na}, {nb}] = {comm_val}   commutes={commutes}")

    print("""
  In the abelian case, every commutator is the identity.
  A Barrington-style AND gate requires [α, β] = target != id.
  Since no such pair exists in an abelian group, AND is not computable
  by this method — the group is "too commutative" for general NC1.
""")

    # Contrast: in S_5, adjacent transpositions DO have non-trivial commutators
    print("  Contrast — S_5 adjacent transpositions (non-abelian case):")
    n = 5
    sigma = {
        'σ1': Permutation.transposition(n, 0, 1),
        'σ2': Permutation.transposition(n, 1, 2),
    }
    comm12 = sigma['σ1'].inverse() * sigma['σ2'].inverse() * sigma['σ1'] * sigma['σ2']
    print(f"    [σ1, σ2] = {comm12}   (non-trivial — AND is computable)")
    print()
    print("  Trade-off summary:")
    print("    Full independence (I = Σ×Σ\\diag) -> abelian group -> Foata depth = 1")
    print("    But abelian groups cannot compute AND -> limited computational power")
    print("    Partial independence (physical I) -> non-abelian group -> computes NC1")
    print("    This is the fundamental parallelism vs. expressiveness trade-off.")


# ============================================================
# Main
# ============================================================

def main():
    print("=" * 60)
    print("  Example 5: RAAG Trace Monoid Parallelism (§8)")
    print("=" * 60)
    print("""
  We work in S_5 with generators σ1..σ4 (adjacent transpositions).
  The independence graph encodes which generators commute and can
  therefore execute in parallel without changing the result.

  Independence: σ_i ind σ_j  iff  |i - j| >= 2
    Independent: (σ1,σ3), (σ1,σ4), (σ2,σ4)
    Dependent:   (σ1,σ2), (σ2,σ3), (σ3,σ4)
""")

    mono, gens = setup_s5()
    tm_partial = make_trace_monoid_partial()

    # Section 2: verify commutativity matches the independence claim
    verify_independence(gens)

    # Section 3: Foata NF of the example word
    word = foata_of_word(mono, tm_partial)

    # Section 4: trace-equivalent words give the same group element
    trace_equivalent_words(mono, tm_partial, word)

    # Section 5: Foata depth under three independence graphs
    compare_independence_graphs(mono)

    # Section 6: abelian trade-off
    abelian_tradeoff(gens)

    print_separator("Summary")
    print("""
  Key results demonstrated:
  1. Independence graph determines which generators can fire in parallel
     (σ_i ind σ_j iff they commute as permutations, i.e., |i-j| >= 2).

  2. Foata normal form groups letters into maximal antichains —
     each block executes in one parallel round.

  3. The example word σ1 σ3 σ2 σ4 σ1 σ3 has Foata depth 3 (not 6):
       Round 1: [σ1, σ3]   Round 2: [σ2, σ4]   Round 3: [σ1, σ3]

  4. All words in the same trace (reachable by independent adjacent swaps)
     evaluate to the same group element — trace equivalence is sound.

  5. Richer independence -> shallower Foata depth -> more parallelism.
     But full independence forces an abelian group, which cannot compute
     AND (Barrington's construction collapses). The physical independence
     graph |i-j| >= 2 is the sweet spot: partial parallelism + NC1 power.
""")


if __name__ == '__main__':
    main()
