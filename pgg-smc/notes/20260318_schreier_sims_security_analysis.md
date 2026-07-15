# Security Analysis: PGG-SMC vs Schreier-Sims Attacks

**Date**: 2026-03-18
**Summary**: Analysis of whether the Schreier-Sims algorithm (polynomial-time BSGS computation for permutation groups) can break the PGG-SMC protocol's security guarantees.

## Verdict

**Schreier-Sims does NOT break PGG-SMC.** The security bounds are information-theoretic and hold against computationally unbounded adversaries, including those with access to Schreier-Sims or any other group-theoretic algorithm.

## Protocol Recap

PGG-SMC uses monodromy representations of permutation groups for secret sharing:
- **Public**: generators `sigma_1, ..., sigma_Tg` in `S_N`
- **Secret**: a uniformly random word `w = [i_1, ..., i_L]` over `{1..Tg}`
- **Evaluation**: `word_eval(w) = sigma_{i_1} * ... * sigma_{i_L}` (a permutation)
- **Endpoint**: for starting sheet `s`, the endpoint is `word_eval(w)(s)`
- **Adversary**: observes `T-1` out of `T` endpoints, tries to learn the `T`-th

## Analysis

### 1. Schreier-Sims Cannot Improve on the Formalized Bounds

The Schreier-Sims algorithm computes a BSGS for `G = <sigma_1, ..., sigma_Tg>`, enabling:
- Efficient membership testing in G
- Computing |G|
- (Nearly) uniform random element generation from G

However, the protocol's security does NOT rely on hiding the group structure. The generators are public parameters. The security comes entirely from the **randomness of the word w**.

The formalized security bound (`collusion_bound_unconditional` in `pgg_collusion_bound.v`) proves:

```
var_dist(adversary_marginal, uniform) <= epsilon
```

via the **Data Processing Inequality** (`var_dist_fdistmap`). This is an information-theoretic bound that holds for ANY adversary strategy -- including one that:
- Enumerates all group elements via Schreier-Sims
- Computes the exact fiber distribution
- Uses optimal Bayesian inference

### 2. The Epsilon Values Are Tight

The fiber-counted epsilon (`raag_fiber_eps_nat`) computes the **exact** worst-case statistical distance between the endpoint distribution and uniform. This IS the adversary's optimal distinguishing advantage -- no algorithm can do better.

| Group | epsilon | Interpretation |
|-------|---------|----------------|
| NCycle(4) | 3/2 | Adversary gains significant advantage |
| Abelian | 1 | Boundary case (d_TV = 1/2) |
| OC | 1 | Boundary case |
| S5 | 6/5 | Moderate advantage |
| Star(m) | 2(m+1)/(m+3) -> 2 | Approaches trivial as m grows |
| Monster | ~0 | Near-perfect security |

### 3. Security Is Information-Theoretic, Not Computational

Unlike HE-based SMC (relies on Ring-LWE) or garbled circuits (relies on OT + hash), PGG-SMC security makes **no computational assumptions**. The tradeoff:

| Property | PGG-SMC | Shamir SS | HE-based SMC | Garbled Circuits |
|----------|---------|-----------|--------------|------------------|
| Security type | Info-theoretic (bounded) | Info-theoretic (perfect) | Computational | Computational |
| Adversary model | Unbounded | Unbounded | Poly-time | Poly-time |
| Epsilon | > 0 in general | = 0 (k-of-n) | N/A | N/A |
| Group knowledge helps? | No (already public) | N/A | No (hardness) | No (different model) |

### 4. What About achievable(L) vs G?

`achievable(L) = {word_eval(w) | w in Tg^L}` is the L-ball in the Cayley graph, not the full group G. Schreier-Sims computes BSGS for G but does not directly compute achievable(L). However, this distinction is **irrelevant** because:

- For small L, the adversary can enumerate all `Tg^L` words directly (more efficient than Schreier-Sims)
- The security bound already assumes the adversary knows the exact distribution over achievable(L)
- The fiber-counted epsilon captures the exact optimal attack

### 5. L* and Collision Structure

Beyond L* (the turning point where `weval_inj` fails), word collisions occur. Schreier-Sims does NOT help exploit this -- the collision structure is fully determined by the generators (public) and can be computed by direct word enumeration. The fiber-counted epsilon at L* already accounts for all collisions.

## Conclusion

The PGG-SMC security model is sound against Schreier-Sims and all other group-theoretic attacks because:

1. **Generators are public** -- no group structure to discover
2. **Bounds are information-theoretic** -- hold against unbounded adversaries
3. **Epsilon is tight** -- equals the optimal attack advantage
4. **Security comes from word randomness** -- analogous to one-time pad

The only "attack" is the trivial one: compute the exact endpoint distribution P_s (which the adversary can do since generators are public) and use Bayesian inference. The epsilon bound IS the advantage of this optimal attack.
