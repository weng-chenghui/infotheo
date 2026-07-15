"""
Example 4: Abelian Group Regime — Modular Counting with Z/5Z
=============================================================
Demonstrates §3.2 / §8 of the SMC-PGG paper:

  - G = Z/5Z (cyclic, abelian), realised as cyclic permutations in S_5
  - Function: MOD_5 counting — f(x1,...,xn) = (x1+...+xn) mod 5
  - Abelian groups CAN compute modular arithmetic (ACC^0 functions)
  - Abelian groups CANNOT compute AND via Barrington (commutators are trivial)

The PGG picture:
  - Generator σ = (0 1 2 3 4) represents "+1 mod 5" in Z/5Z
  - σ^k represents "+k mod 5"
  - Word product σ^{x1} · σ^{x2} · ... · σ^{xn} = σ^{x1+...+xn}
  - Endpoint(w, 0) = (x1+...+xn) mod 5   (reading off sheet 0)
"""

from smc_pgg_core import (
    Permutation, MonodromyGroup, word_product, commutator,
    print_separator
)
from typing import List, Tuple


# ============================================================
# Section 1: Set up Z/5Z as a cyclic group in S_5
# ============================================================

def setup_z5() -> MonodromyGroup:
    """
    Z/5Z realised as <σ> ≤ S_5, where σ = (0 1 2 3 4).
    σ^k sends sheet 0 to sheet k, so endpoint(σ^k, 0) = k.
    """
    sigma = Permutation.from_cycles(5, (0, 1, 2, 3, 4))
    # Build σ^0 ... σ^4 as explicit generators for use in words
    generators = {}
    g = Permutation.identity(5)
    for k in range(5):
        generators[f"s{k}"] = g   # s0=id, s1=σ, s2=σ^2, s3=σ^3, s4=σ^4
        g = g * sigma
    return MonodromyGroup(n_sheets=5, generators=generators)


def show_group_structure(G: MonodromyGroup):
    print_separator("Z/5Z — Group Structure")
    sigma  = G.generators["s1"]
    print(f"  Generator σ = s1: {sigma}")
    print(f"  Order of σ:       {sigma.order()} (should be 5)")
    print()
    print("  Powers of σ:")
    for k in range(5):
        sk = G.generators[f"s{k}"]
        ep = sk(0)   # endpoint from sheet 0
        print(f"    σ^{k} = {str(sk):<20}  endpoint(σ^{k}, 0) = {ep}")
    print()
    print(f"  |Z/5Z| = {G.order()} elements (all σ^k for k in Z/5Z)")


# ============================================================
# Section 2: MOD_5 Counting with 4 Parties
# ============================================================

def mod5_word(inputs: List[int]) -> List[str]:
    """
    Build the word σ^{x1} · σ^{x2} · ... · σ^{xn} as a list of generator names.
    Each party i contributes letter s{x_i}.
    """
    return [f"s{x % 5}" for x in inputs]


def compute_mod5(G: MonodromyGroup, inputs: List[int]) -> int:
    """
    Evaluate MOD_5(x1,...,xn) via the word product in Z/5Z.
    Returns (sum of inputs) mod 5.
    """
    word = mod5_word(inputs)
    return G.endpoint(word, start_sheet=0)


def show_mod5_counting(G: MonodromyGroup):
    print_separator("MOD_5 Counting — 4 Parties")
    print("  Protocol: party i contributes σ^{x_i}, product = σ^{sum(inputs)}")
    print("  Endpoint from sheet 0 = (x1+x2+x3+x4) mod 5")
    print()

    test_cases: List[Tuple[List[int], int]] = [
        ([0, 0, 0, 0], 0),
        ([1, 0, 0, 0], 1),
        ([1, 1, 1, 1], 4),
        ([2, 3, 0, 0], 0),   # 2+3=5≡0
        ([1, 2, 3, 4], 0),   # 1+2+3+4=10≡0
        ([3, 3, 3, 3], 2),   # 12≡2
        ([4, 4, 4, 4], 1),   # 16≡1
        ([1, 2, 1, 2], 1),   # 6≡1
        ([0, 0, 3, 4], 2),   # 7≡2
        ([2, 2, 2, 4], 0),   # 10≡0 (not 5!)  actually 10≡0 mod5
    ]

    # Re-verify expected values programmatically
    print(f"  {'Inputs':<22}  {'Word':<22}  {'Endpoint':<10}  {'Direct sum':<12}  OK?")
    print(f"  {'-'*22}  {'-'*22}  {'-'*10}  {'-'*12}  {'-'*4}")
    all_ok = True
    for inputs, _ in test_cases:
        word = mod5_word(inputs)
        endpoint = compute_mod5(G, inputs)
        direct = sum(inputs) % 5
        ok = (endpoint == direct)
        all_ok = all_ok and ok
        word_str = " ".join(word)
        print(f"  {str(inputs):<22}  {word_str:<22}  {endpoint:<10}  {direct:<12}  {'YES' if ok else 'FAIL'}")

    print()
    if all_ok:
        print("  All test cases: PASS — endpoint matches (sum mod 5) in every case.")
    else:
        print("  WARNING: some test cases FAILED — check implementation.")


# ============================================================
# Section 3: Order Independence (Abelian = Full CPS)
# ============================================================

def show_order_independence(G: MonodromyGroup):
    print_separator("Order Independence — Abelian Property")
    print("  In Z/5Z every pair of elements commutes: a*b = b*a.")
    print("  This means the word product is invariant under all permutations")
    print("  of the parties' contributions — a complete partial commutation")
    print("  system (CPS) with every pair of letters independent.")
    print()

    import itertools

    inputs = [1, 2, 3, 4]   # sum = 10 ≡ 0
    word   = mod5_word(inputs)
    perms  = list(itertools.permutations(word))

    endpoints = set()
    for perm_word in perms:
        ep = G.endpoint(list(perm_word), start_sheet=0)
        endpoints.add(ep)

    expected = sum(inputs) % 5
    print(f"  Inputs: {inputs}  (sum mod 5 = {expected})")
    print(f"  Number of orderings of the word: {len(perms)}")
    print(f"  Distinct endpoints across all orderings: {sorted(endpoints)}")
    if endpoints == {expected}:
        print(f"  Result: ALL orderings give endpoint {expected} — any evaluation order works.")
        print(f"  This is a full CPS (complete partial commutation system).")
    else:
        print(f"  Unexpected: orderings disagree — check implementation.")

    print()
    print("  Pairwise commutativity check for all generator pairs:")
    gen_names = list(G.generators.keys())
    non_commuting = []
    for i, a in enumerate(gen_names):
        for b in gen_names[i+1:]:
            ga, gb = G.generators[a], G.generators[b]
            if not ga.commutes_with(gb):
                non_commuting.append((a, b))
    if non_commuting:
        print(f"  WARNING: non-commuting pairs found: {non_commuting}")
    else:
        print(f"  All {len(gen_names)*(len(gen_names)-1)//2} pairs commute — Z/5Z is fully abelian. (CPS)")


# ============================================================
# Section 4: Limitation — Commutators in Z/5Z Are Always Trivial
# ============================================================

def show_abelian_limitation(G: MonodromyGroup):
    print_separator("Limitation — Barrington's AND Gate Fails in Z/5Z")
    print("  Barrington's AND: [alpha^x1, beta^x2] = id  if  x1=0 or x2=0")
    print("                                         = [alpha, beta]  if  x1=x2=1")
    print("  For this to encode AND we need [alpha, beta] != id for some alpha, beta.")
    print()
    print("  But Z/5Z is abelian: a*b = b*a for all a,b, so")
    print("  [a, b] = a^{-1} b^{-1} a b = a^{-1} a b^{-1} b = id  always.")
    print()

    print("  Commutator table [sigma^i, sigma^j] for i,j in {0,1,2,3,4}:")
    id_perm = Permutation.identity(5)
    all_trivial = True
    header = "        " + "  ".join(f"s{j}" for j in range(5))
    print(f"  {header}")
    for i in range(5):
        row_str = f"  s{i}  [ "
        for j in range(5):
            a = G.generators[f"s{i}"]
            b = G.generators[f"s{j}"]
            c = commutator(a, b)
            is_id = c == id_perm
            if not is_id:
                all_trivial = False
            row_str += "id  " if is_id else f"{c}  "
        row_str += "]"
        print(row_str)

    print()
    if all_trivial:
        print("  Every commutator [sigma^i, sigma^j] = id in Z/5Z.")
        print()
        print("  Consequence: Barrington's AND construction requires")
        print("    [alpha, beta] = (target for AND=1) != id.")
        print("  Since Z/5Z has only trivial commutators, no such alpha,beta exist.")
        print()
        print("  => Cannot implement AND gate using Z/5Z monodromy.")
        print("  => Cannot compute NC^1-complete functions (like n-bit AND) in Z/5Z.")
    else:
        print("  WARNING: found non-trivial commutator — check implementation.")

    # Concrete attempt: try every pair as (alpha, beta) for a Barrington AND gate
    print()
    print("  Exhaustive check: try all (alpha, beta) pairs as AND gate:")
    non_trivial_pairs = 0
    for i in range(5):
        for j in range(5):
            a = G.generators[f"s{i}"]
            b = G.generators[f"s{j}"]
            c = commutator(a, b)
            if not (c == id_perm):
                non_trivial_pairs += 1
    print(f"    Pairs with [alpha, beta] != id: {non_trivial_pairs} / 25")
    if non_trivial_pairs == 0:
        print("    Confirmed: no usable pair — AND gate impossible in Z/5Z.")


# ============================================================
# Section 5: Contrast with S_5 (Non-abelian, can do AND)
# ============================================================

def show_s5_contrast():
    print_separator("Contrast — S_5 CAN Compute AND (Barrington)")
    print("  In S_5, take alpha = (1 2 3 4 5) and beta = (1 2 3)(4 5).")
    print("  Their commutator [alpha, beta] is a specific non-identity permutation.")
    print("  Barrington uses: AND(x1, x2) = [alpha^x1, beta^x2]")
    print("    x1=0 or x2=0 => one factor is id => commutator = id")
    print("    x1=x2=1      => commutator = [alpha, beta] != id")
    print()

    # Standard Barrington generators for S_5
    # Use sigma=(1 2 3 4 5) and tau=(1 2 3) as 5-cycle and 3-cycle
    # Classic choice: alpha=(1 2 3 4 5), beta=(1 2 3) (indices 0-based: shift by 1)
    alpha = Permutation.from_cycles(5, (0, 1, 2, 3, 4))          # 5-cycle
    beta  = Permutation.from_cycles(5, (0, 1, 2))                 # 3-cycle
    c = commutator(alpha, beta)
    id5 = Permutation.identity(5)

    print(f"  alpha = {alpha}  (5-cycle in S_5, order {alpha.order()})")
    print(f"  beta  = {beta}  (3-cycle in S_5, order {beta.order()})")
    print(f"  [alpha, beta] = {c}")
    print(f"  [alpha, beta] is identity: {c == id5}")
    print()
    print("  AND truth table via commutator [alpha^x1, beta^x2]:")
    for x1 in [0, 1]:
        for x2 in [0, 1]:
            a = alpha if x1 else id5
            b = beta  if x2 else id5
            result = commutator(a, b)
            is_target = (result == c)
            is_id     = (result == id5)
            label = "= [alpha,beta] (AND=1)" if is_target else "= id (AND=0)"
            print(f"    x1={x1}, x2={x2}: {result}  {label}")
    print()
    print("  S_5 is non-solvable (simple), so Barrington's theorem applies:")
    print("  any NC^1 Boolean circuit can be computed by a width-5 branching program.")


# ============================================================
# Section 7: Hybrid AND + MOD in S_5 — Single Monodromy Walk
# ============================================================

def show_hybrid_computation():
    print_separator("Hybrid AND + MOD in S_5 — Single Monodromy Walk")
    print("  S_5 contains Z/5Z as <σ> (σ = (0 1 2 3 4)), AND can also compute")
    print("  Barrington AND via non-trivial commutators — all in one group.")
    print()
    print("  Generators:")
    print("    α = (0 1 2 3 4),  β = (0 1 3 4 2)  — Barrington AND pair (ex2)")
    print("    σ = (0 1 2 3 4) = α                 — Z/5Z generator for MOD")
    print()
    print("  Hybrid word for (x1, x2, x3, x4):")
    print("    w = α^{-x1} · β^{-x2} · α^{x1} · β^{x2} · σ^{x3} · σ^{x4}")
    print("      = [α^x1, β^x2]  ·  σ^{x3+x4}")
    print("    First 4 factors = commutator part (encodes AND(x1,x2))")
    print("    Last 2 factors  = cyclic part     (encodes (x3+x4) mod 5)")
    print()

    alpha = Permutation.from_cycles(5, (0, 1, 2, 3, 4))
    beta  = Permutation.from_cycles(5, (0, 1, 3, 4, 2))
    sigma = alpha                          # same permutation; alias for clarity
    id5   = Permutation.identity(5)
    comm  = commutator(alpha, beta)        # = [α, β], the AND=1 target

    print(f"  α          = {alpha}  (order {alpha.order()})")
    print(f"  β          = {beta}  (order {beta.order()})")
    print(f"  [α, β]     = {comm}  (AND=1 target)")
    print(f"  [α, β] ≠ id: {comm != id5}")
    print()

    # Truth table header
    print(f"  {'x1':>2} {'x2':>2} {'x3':>2} {'x4':>2}  "
          f"{'AND(x1,x2)':>10}  {'(x3+x4)%5':>10}  {'endpoint':>8}  "
          f"{'expected':>8}  {'OK':>4}")
    print("  " + "-" * 68)

    all_ok = True
    for x1 in [0, 1]:
        for x2 in [0, 1]:
            for x3 in [0, 1]:
                for x4 in [0, 1]:
                    # commutator factor = [α^x1, β^x2]
                    a  = alpha if x1 else id5
                    ai = alpha.inverse() if x1 else id5
                    b  = beta  if x2 else id5
                    bi = beta.inverse()  if x2 else id5
                    comm_part = ai * bi * a * b   # = [α^x1, β^x2]

                    # cyclic factor = σ^{x3+x4}
                    mod_exp = (x3 + x4) % 5
                    cyc_part = id5
                    for _ in range(mod_exp):
                        cyc_part = cyc_part * sigma

                    # Combined endpoint from sheet 0
                    combined = comm_part * cyc_part
                    endpoint = combined(0)

                    # Expected endpoint: [α,β]·σ^{x3+x4} if AND=1, else σ^{x3+x4}
                    and_val  = 1 if (x1 == 1 and x2 == 1) else 0
                    and_factor = comm if and_val else id5
                    exp_perm = and_factor * cyc_part
                    expected = exp_perm(0)

                    ok = (endpoint == expected)
                    all_ok = all_ok and ok
                    print(f"  {x1:>2} {x2:>2} {x3:>2} {x4:>2}  "
                          f"{and_val:>10}  {mod_exp:>10}  {endpoint:>8}  "
                          f"{expected:>8}  {'YES' if ok else 'FAIL':>4}")

    print()
    if all_ok:
        print("  All 16 cases: PASS — endpoint encodes AND(x1,x2) and (x3+x4) mod 5.")
    else:
        print("  WARNING: some cases FAILED — check implementation.")
    print()
    print("  Why Z/5Z alone cannot do this:")
    print("    Section 4 showed every commutator in Z/5Z is trivial,")
    print("    so [α^x1, β^x2] = id regardless of x1, x2.")
    print("    AND information is completely lost — impossible in any abelian group.")
    print()
    print("  Why two separate protocols are unnecessary:")
    print("    A separate AND protocol (S_5 walk) + a separate MOD protocol (Z/5Z walk)")
    print("    would require two independent monodromy evaluations and then combining")
    print("    the outputs.  S_5 unifies both in a single word of length 6,")
    print("    because <σ> ≤ S_5 already supplies the cyclic Z/5Z subgroup.")


# ============================================================
# Section 6: Summary
# ============================================================

def show_summary():
    print_separator("Summary — Abelian vs Non-abelian Groups")
    print("""
  Abelian group (Z/5Z):
    + Computes modular arithmetic: f(x1,...,xn) = (sum xi) mod 5
    + Any evaluation order works (full CPS, Foata depth = 1)
    + Security: random sharing hides individual contributions
    - All commutators trivial => cannot implement AND gate
    - Cannot compute NC^1-hard functions
    => Computes exactly the ACC^0 functions (mod-counting circuits)

  Non-abelian group (S_5, A_5, ...):
    + Non-trivial commutators => Barrington AND gate works
    + Can compute all NC^1 Boolean functions
    + PGG monodromy enables arbitrary branching program evaluation
    - Non-abelian => evaluation order matters (CPS is strict subset)
    => Computes NC^1  (= polynomial-width branching programs)

  Key theorem (Barrington 1989):
    NC^1 = languages accepted by width-5 branching programs
         = monodromy programs over any non-solvable group
    ACC^0 ⊂ NC^1, and the inclusion is strict (assuming standard conjectures).

  In the SMC-PGG framework:
    - Abelian G: appropriate for modular-arithmetic MPC (e.g., secret sharing in Z/p)
    - Non-abelian G (e.g., S_5): appropriate for general NC^1 function evaluation
""")


# ============================================================
# Main
# ============================================================

def main():
    print("=" * 60)
    print("  Example 4: Abelian Group Regime (Z/5Z)")
    print("  Modular Counting and the Limits of Abelian Groups")
    print("=" * 60)

    G = setup_z5()

    show_group_structure(G)
    show_mod5_counting(G)
    show_order_independence(G)
    show_abelian_limitation(G)
    show_s5_contrast()
    show_hybrid_computation()
    show_summary()


if __name__ == "__main__":
    main()
