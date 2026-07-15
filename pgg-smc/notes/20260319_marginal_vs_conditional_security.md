# Marginal vs Conditional Entropy Security (2026-03-19)

## Key observation

The entropy security analysis in `pgg_entropy_security.v` uses **marginal** entropy
H(P_s) — the entropy of one party's endpoint ignoring other parties — not
**conditional** entropy H(s_target | s_0, ..., s_{T-2}).

A proper information-theoretic security statement would use the conditional form:
how much does the unobserved party's endpoint leak **given** the other T-1 parties'
endpoints?

## What is actually proved

The formalized bound is:

```
var_dist(adversary_marginal, uniform) <= eps + 2(T-1)/N
```

where:
- `adversary_marginal` is the **marginal** distribution of the unobserved party's
  endpoint (not conditioned on observed endpoints)
- `eps` is the statistical distance between the per-sheet endpoint distribution and
  uniform, determined by fiber counts
- `+2(T-1)/N` is an additive slack term covering the conditioning gap (distance
  between uniform on all N sheets and uniform on remaining N-(T-1) sheets)

The proof chain:
1. H(P_s) marginal entropy (pgg_entropy_security.v)
2. D = log N - H (entropy gap = KL divergence)
3. var_dist_marginal <= sqrt(2D) (Pinsker)
4. var_dist <= eps + 2(T-1)/N (collusion_bound, triangle inequality + DPI)

## Paper claim

We can claim: a **universal** security bound that is looser than exact conditional
entropy but applies uniformly to **all** finite groups with a monodromy representation.

Selling points:
- **Universal**: holds for any finite group G — no structural assumptions (abelian,
  solvable, simple, etc.). Pure DPI + triangle inequality.
- **Computable**: eps determined by fiber counts, computable for any concrete instance.
- **Information-theoretic**: no computational assumptions.
- **Honest about the gap**: marginal, not conditional. The +2(T-1)/N is the price for
  avoiding conditional analysis. Negligible for large N (Monster: ~10^{-20}), but
  nontrivial for small N (S5: N=5, T=4 gives 6/5).

The gap is a feature: conditional entropy H(s_target | s_0,..,s_{T-2}) requires
analyzing correlations between sheets under the group action — the joint distribution
of endpoints. This is much harder to formalize generically. The marginal approach
decouples sheets and gives a uniform framework.

## Two complementary security analyses

The formalization provides two ways to bound eps, addressing different paper needs:

### Fiber/entropy analysis (pgg_entropy_security.v) — concrete, per-L

At a specific word length L, compute fiber counts c_x = |{sigma in achievable(L) :
sigma(s) = x}| for each sheet s. These give:
- **Exact eps**: var_dist = 2(N - |{x : c_x > 0}|) / N
- **Exact entropy**: H(P_s) = log(Tg^L) - (1/Tg^L) sum c_x log c_x
- **Pinsker bridge**: var_dist <= sqrt(2 * (log N - H))

Paper role: fills **tables** with concrete numbers for specific instances (Star, OC,
S5, Monster) at specific L values. Demonstrates the theory works.

### Spectral/Schreier analysis (pgg_schreier.v) — asymptotic, all L

The spectral gap lambda_gap of the Schreier graph on 'I_N governs convergence:
- **Rate bound**: eps(L) <= sqrt(N) * (1 - lambda_gap)^L
- **Parameter selection**: L >= log(sqrt(N)/eps) / log(1/(1 - lambda_gap))
- **Monotonicity**: eps(L) decreases geometrically; more steps = more secure

The Schreier graph works directly on N sheets (not |G| group elements), giving
prefactor sqrt(N) instead of sqrt(|G|). For the Monster: sqrt(N) ~ 10^10 vs
sqrt(|G|) ~ 10^26. The spectral gap of the Schreier graph is at least as large
as the Cayley graph's (eigenvalue subset property; Ceccherini-Silberstein et al.
2008, Thm 5.5.3), so no tightness is lost.

Paper role: the **main theorem** that the protocol converges for any transitive group.
Answers the reviewer question "how do you know this works at scale?"

### Both are marginal

Neither analysis addresses conditional entropy H(s_target | s_0,..,s_{T-2}).
Both bound the marginal endpoint distribution. The +2(T-1)/N slack in collusion_bound
covers the conditioning gap in both cases.

### Monotonicity: exact vs. envelope

The **exact** var_dist(L) is NOT monotonic in L. With transposition generators, at
L=2 the identity enters the achievable set (σ² = id), concentrating mass on the
diagonal and spiking var_dist above its L=1 value:

```
exact var_dist: 0.8  1.2  0.6  0.3  0.1  ...  (non-monotone, spike at L=2)
spectral bound: 3.0  2.4  1.9  1.5  1.2  ...  (monotone geometric envelope)
```

The fiber/entropy analysis computes the exact (non-monotone) value at each L.
The spectral/Schreier analysis provides a monotone upper bound √N·(1−gap)^L.
Both are correct — the spectral bound is an envelope over a non-monotone quantity.
The envelope is coarse at small L but eventually tight (both converge to 0
geometrically for transitive groups).

### Suggested paper structure

1. **Main theorem** (collusion_bound): universal marginal bound, eps + 2(T-1)/N
2. **Convergence theorem** (spectral): eps decays geometrically, dealer chooses L
3. **Concrete instances** (fiber/entropy): tables for Star, OC, S5, Monster
4. **Separation result** (abelian): abelian groups don't converge — non-abelianity
   is necessary, not just sufficient

## Future work

Tighten to conditional entropy for specific group families where the joint structure
is known (e.g., transitive groups where the conditional distribution converges to
uniform on remaining sheets).

## Files updated

- `pgg_entropy_security.v`: revised comment (lines 31-43) to clarify marginal vs
  conditional, explain H(s_target | s_0,..,s_{T-2}) as the tighter alternative
- `pgg_pismc.v`: revised header comment to clarify types (generator index vs group
  element vs sheet ID) and the lookup-table protocol structure
