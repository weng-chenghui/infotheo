# Question: Are monodromy-based computation security and AG-code-based reconstruction security two independent layers?

In PGG-SMC, the monodromy walk (permutation of sheet IDs) combined with partial lookup table distribution and group structure (Free, RAAG, non-Abelian) provides security against adversarial parties during the computation phase — with strength depending on the secret word's length L. However, for the reconstruction phase, algebraic geometry codes on deck transforms achieve a (k, T)-threshold. These appear to be two entirely unrelated security mechanisms. The original expectation was that the choice of group structure alone would determine both per-party computation security and the (k, T)-reconstruction threshold, but the threshold seems to be decided entirely by the splitting/reconstruction algorithm.

---

After reviewing issue #36 and all 7 related pgg-smc issues (#36-#42), plus the reconstruction codebase, here's what's going on:

## You have two distinct security properties, not one

**Layer 1 — Computation security (group structure)**
- During the protocol, parties execute monodromy walks on sheets
- The group structure (Free, RAAG, non-Abelian) determines what a coalition can deduce from *partial traces* of the computation
- Cartier-Foata / trace monoid theory bounds this: word length L, commutation independence graph, collusion bounds
- This protects the *intermediate computation*

**Layer 2 — Data security (sharing/reconstruction scheme)**
- How the secret is split into shares and reconstructed
- Currently: sum-mod-N gives (T,T)-threshold (all parties needed)
- Planned: AG codes on covering curves give (k,T)-threshold with k < T
- This protects the *secret data* at rest

## They ARE connected — via `rss_compatible`

Your `pgg_sharing_framework.v` already has the bridge: the `rss_compatible` predicate requires that the monodromy group action *preserves* the sharing scheme's algebraic structure. So they're not independent — the group G must be compatible with the reconstruction method.

## Your original intuition is right — for the AG-on-covers approach

Issue #39 (covering bridge) is exactly where the two layers *unify*:

- **Covering curve** C → B with deck transformation group G
- **Fiber points** = sheet IDs (= parties)
- **AG code evaluation on fiber** = share distribution
- **Deck transformations** = monodromy action
- **AG code parameters [n+1, k, d]** determine the threshold

In this picture, **G determines both**: the covering's deck group constrains which AG codes you can define on the fiber, which constrains the achievable (k, T)-threshold. The group structure isn't just about computation security — it's the *geometric substrate* on which the code lives.

## Why it looks like two independent layers right now

Because **Phase 0** (`sum_mod_scheme`) is a trivial sharing scheme that works with *any* group — it only needs "σ preserves sum mod N", which is weak. So the group structure choice feels orthogonal to reconstruction.

Once you implement Phase 2-3 (AG-on-covers), the connection becomes tight:
- The covering space topology (determined by G and ρ) constrains the genus
- The genus constrains what AG codes exist (Riemann-Roch)
- The AG code parameters determine (k, T)-threshold
- So **G → genus → code parameters → threshold**

## Summary

| Phase | Group choice affects threshold? | Why |
|-------|---|----|
| Current (sum-mod-N) | No — always (T,T) | Trivial scheme, any G works |
| Planned (AG-on-covers) | **Yes** — G determines covering geometry | Threshold comes from code on the covering curve |

Your confusion is valid: in the *current* formalization they look decoupled. But the roadmap (issues #37→#38→#39→#40) is precisely about making the group structure determine the threshold through algebraic geometry. The `SharingScheme` abstraction in #42 was designed for this — swap the instance from sum-mod-N to AG-on-covers, and suddenly G drives everything.
