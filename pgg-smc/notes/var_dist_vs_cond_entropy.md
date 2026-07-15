# PGG-SMC: Variational Distance vs Conditional Entropy for Security

*2026-03-07*

## How far from conditional-entropy-based security?

**Short answer: the current `var_dist` approach is arguably the *right* metric for PGG, and conditional entropy doesn't fit naturally.**

### Why `var_dist` works well for PGG

The PGG collusion bound says: an adversary observing T-1 shares can't distinguish the remaining share from uniform, up to epsilon. This is exactly what variational distance measures -- it directly bounds the adversary's distinguishing advantage:

```
Adv(A) <= var_dist(real, ideal) <= epsilon + 2(T-1)/N
```

### Why conditional entropy is awkward here

DSDP's entropy proof works because:
1. The constraint `s = u1*v1 + u2*v2 + u3*v3` over Z/pqZ is **linear** -> fiber size is exactly m
2. Given the constraint, the secret is **perfectly uniform** over the fiber -> `H(secret | view) = log(m)` exactly

PGG doesn't have this structure:
- The "constraint" is a **group word** `sigma_{w1} * sigma_{w2} * ... * sigma_{w_L}` -- a nonlinear, non-commutative composition
- The distribution over permutations is **not exactly uniform** on achievable -- it's only *close* to uniform (that's the whole point of epsilon)
- There's no clean fiber decomposition because orbits under centralizers don't have uniform cardinality

### What Pinsker would give you

You could convert via Pinsker: `var_dist(P,Q) <= sqrt(1/2 * D(P||Q))`, which gives `D(P||Q) >= 2 * var_dist^2`. Then:
```
H(uniform) - H(real) <= D(real || uniform) <= ...
```

But this goes the *wrong direction* -- Pinsker bounds var_dist in terms of divergence, not the reverse. You'd get a **weaker** bound, not a stronger one. And the result would still be an approximation, not an exact `log(m)`.

### Bottom line

| Approach | PGG fit | DSDP fit |
|----------|---------|----------|
| `var_dist <= epsilon` | Natural (distinguishing advantage) | Overkill |
| `H(X\|view) = log(m)` | Doesn't hold exactly | Perfect (linear fibers) |

The `var_dist` framework we have is the standard metric for statistical security (information-theoretic indistinguishability). PGG's security is **statistical**, not computational: the bound holds against unbounded adversaries with no hardness assumption. The information literally isn't there (up to epsilon), regardless of compute power. This is one tier below DSDP's **perfect** security (epsilon = 0), but strictly stronger than computational security (which assumes bounded adversaries).

Conditional entropy is ideal for *perfect* information-theoretic security (like DSDP), but PGG's security is inherently *statistical* (epsilon > 0 unless the generated subgroup equals S_N).

In PGG, generators are concrete permutations in S_N, so the generated group is always a subgroup of S_N. The question is how large that subgroup is:
- If <<sigma_1,...,sigma_T>> = S_N (full symmetric group), then enough words cover all permutations -> epsilon -> 0
- If <<sigma_1,...,sigma_T>> is a proper subgroup, then epsilon > 0 always

Note: "L-free" (our formalization) is not the same as "free group". L-free means all words of length <= L evaluate to distinct permutations (the group looks free up to length L). Free groups are infinite; our groups are finite subgroups of S_N with relations at longer lengths. Abelian groups give *worse* security due to the abelian collapse (many words map to the same permutation, shrinking the search space).

**When epsilon -> 0:** If T^L -> N! (the group word space covers nearly all permutations), PGG approaches perfect security. For generators that span all of S_N with L large enough, epsilon is negligible. For RAAGs with independent set size k, the growth rate is k^L, so epsilon shrinks as L grows -- but never reaches 0 (since k^L < N! for any proper subgroup).

### Recommendation

Keep `var_dist` for PGG. If we want an entropy-flavored statement for the paper narrative, we could add a corollary via Pinsker:
```
H(target | adversary_view) >= log(N) - f(epsilon)
```
as a derived statement, but it would be strictly weaker than what we already have.

### Infrastructure available in infotheo (if needed later)

| Purpose | File |
|---------|------|
| Conditional entropy `H(Y\|X)` | `information_theory/entropy.v` (lines 361-600) |
| Pinsker's inequality | `probability/pinsker.v` |
| KL divergence | `information_theory/conditional_divergence.v` |
| Mutual information `I(X;Y)` | `information_theory/entropy.v` (lines 866-995) |
| Entropy fiber framework (Z/pqZ) | `dumas2017dual/entropy_fiber/entropy_fiber_zpq.v` |
| DSDP conditional entropy proof | `dumas2017dual/dsdp/dsdp_entropy.v` |
