# PGG Theorem Completeness Audit

**Date:** 2026-03-23
**Method:** Mathematical expert review of 58 Rocq files, 21.8K LOC

## Summary

The formalization covers a novel card-based cryptographic protocol with 58 files, approximately 21,800 lines, 0 Admitted, and 11 axioms. The mathematical content spans random walks on groups, algebraic geometry of coverings, information theory, and combinatorics on words.

## Per-Category Assessment

| Category | Completeness | Significance | Literature Relation | Notes |
|---|---|---|---|---|
| **A. Protocol Correctness** | **Complete** | Standard infrastructure | Specialized to PGG (no direct textbook analogue) | Evaluation bijectivity, distinctness, and sum-mod reconstruction are fully proved. The `prescribed` counting lemma uses S_N k-transitivity (proved from scratch). Standard permutation group theory applied to a novel protocol model. |
| **B. Security Bounds** | **Mostly Complete** | Central result; novel combination | Diaconis 1988 (Ch. 3B) for spectral convergence; DPI is standard | The collusion bound `d(adv, U) <= eps + 2(T-1)/N` is the main theorem. The var_dist triangle inequality and data processing inequality are proved from scratch. The Schreier spectral bound relies on one axiom (`schreier_walk_eq_endpoint`), which is a standard matrix-convolution correspondence from Diaconis 1988. **Gap**: the matrix-power axiom is the most significant unproved piece in the security pipeline (would require matrix analysis infrastructure absent from MathComp). |
| **C. Abelian Collapse** | **Complete** | Novel impossibility result | No direct literature precedent | One endpoint determines the full permutation under regular action. Clean negative result, fully proved, no axioms. |
| **D. Cartier-Foata** | **Mostly Complete** | Substantial effort; classical combinatorics | Cartier-Foata (1969), Mazurkiewicz traces (1977) | Foata NF existence, soundness, idempotency all proved. The `dv_leq` total order (transitivity, antisymmetry, totality) proved. Chain `search_space(L) <= n_traces(L) <= Tg^L` proved. **Gap**: uses computable normal form rather than classical bijection between traces and heaps. Adequate for application but is a specialized variant. |
| **E. Information Theory** | **Mostly Complete** | Standard infrastructure applied well | Pinsker inequality, entropy of pushforward | Fiber entropy formula (general and injective) proved. Bridge `var_dist <= sqrt(2*D(P||U))` uses Infotheo's Pinsker. **Gap**: conditional entropy analysis `H(s_target | observed)` is missing; the `+2(T-1)/N` slack covers this, but a conditional analysis would give tighter bounds. |
| **F. Algebraic Rigidity** | **Mostly Complete** | Novel structural theorem | Chen-Cramer (CRYPTO 2006) for AG secret sharing; Riemann-Hurwitz is classical | Dichotomy (genus-0 bounded vs genus>0 gap) proved. Five instances constructed. **Gap**: Hurwitz automorphism bound axiomatized (requires complex analysis not in MathComp). CoveringScheme axiomatizes `cs_perm_compatible` and `cs_gap` encoding the Goppa bound without Riemann-Roch. |
| **G. Coding Theory** | **Mostly Complete** | Solid infrastructure | AG codes (Goppa 1981), Reed-Solomon, Massey (1993) | AG code Singleton bound proved from axiomatized Goppa weight. RS privacy via Lagrange interpolation fully proved. PGL cardinality proved using MathComp's card_GL_2. Hyperelliptic Goppa bound proved via polynomial resultant (novel technique avoiding Riemann-Roch). **Gap**: general Goppa weight for non-hyperelliptic curves axiomatized. |
| **H. Grover Mitigation** | **Complete** | Elementary but useful | Standard quantum computing folklore | Free group ball size formula proved at nat level (multiplicative form avoiding division). Grover mitigation follows from ball_size_lower and isqrt_expn. All fully proved. |
| **I. Permutation Uniformity** | **Complete** | Key combinatorial lemma | Classical (counting argument for S_N) | `card(prescribed(s,v)) = (N-1)!` proved using S_N k-transitivity. Conditional uniformity and collusion adversary uniformity derived. This is the combinatorial backbone enabling the DPI-based security argument. |

## Axiom Assessment

| Axiom | Source | Risk |
|---|---|---|
| `schreier_walk_eq_endpoint` | Diaconis 1988, Ch. 3A | **Low**: standard result, requires matrix analysis not in MathComp |
| `hurwitz_bound` | Hurwitz 1893 | **Low**: classical, requires complex analysis |
| `oc_entropy_bound_axiom` | Instance-specific (OC(2,3) at L=2) | **Low**: verifiable by finite computation |
| Monster axioms (8) | Steinberg, Conway-Norton 1979, Griess 1982 | **Low**: Monster is not computationally enumerable; axiomatization is the only viable approach |

The axiom budget is disciplined: each axiom either (a) encodes a classical theorem whose proof machinery is absent from MathComp, (b) encodes per-instance numerical facts, or (c) encodes existence of a computationally intractable object. No axiom hides a gap in the argument structure.

## Notable Gaps

1. **Conditional security analysis**: works with marginal entropy rather than conditional entropy. The additive slack covers this but a conditional analysis would be tighter.
2. **Matrix-convolution correspondence** (`schreier_walk_eq_endpoint`): the single most consequential axiom. Proving it would require spectral theory for finite stochastic matrices in MathComp.
3. **General Goppa bound**: axiomatized for non-hyperelliptic curves. Full formalization would require Riemann-Roch.
4. **Cartier-Foata bijection**: computable NF variant used instead of classical bijection to heaps. Sufficient for application.
5. **Star instance deleted**: `rigidity_star_instance.v` removed from git (appears in `git status` as deleted).

## Overall Assessment

**Rating: Substantial**

The work sits at the intersection of four mathematical domains (permutation groups, algebraic geometry of coverings, information theory, combinatorics on words) and provides machine-checked proofs connecting them. The main security theorem (collusion bound via Schreier spectral gaps) is a novel combination of Diaconis's random walk theory with card-based cryptographic protocols.

The depth is uneven: permutation uniformity and protocol correctness are fully self-contained and deep; Cartier-Foata represents substantial effort in combinatorics; the hyperelliptic Goppa bound via resultant is a nice proof-theoretic contribution; the algebraic rigidity dichotomy connecting group size, genus, and threshold gap appears to be new.

Compared to existing ITP cryptography formalizations (CertiCrypt, EasyCrypt, Jasmin), this work is unusual in being algebraic/combinatorial rather than computational/game-based. The closest comparison in style is the Feit-Thompson formalization (Gonthier et al. 2013), a large MathComp formalization of deep group theory, though at much smaller scale.
