# AG Axiomatization: Paper Framing and Reviewer Risk Assessment

## Question

If I write a paper, will the unproven AG code parts (goppa_wt, ag_priv_surj, share_compatible, ag_mult, genus0_pgl) be a weakness that causes rejection, since the AG reconstruction scheme is not fully proven?

## Assessment: It will be fine, but framing matters

### Why it's NOT a weakness

The standard in formalization papers is **not** "prove everything down to the axioms of CIC." Virtually every serious formalization project axiomatizes *something*. What reviewers care about is:

1. **Is the axiomatization boundary principled?** Ours is. The boundary is exactly "algebraic geometry of curves" -- Riemann-Roch, function fields, covering maps. These are well-known classical results from a completely different area of mathematics. The formalization contribution is the *protocol-algebraic layer*, not the AG code construction itself.

2. **Are the axioms consistent and believable?** Yes -- they're standard textbook facts (Goppa bound, multiplicative property of evaluation codes, Aut(P^1) = PGL(2,q)). No reviewer will doubt their mathematical truth.

3. **Does the formalization still catch real bugs?** Yes -- the `cast_tuple`/dependent-type issues, the `rewrite !` blowup, the `'Z_(p*q)` rewrite problem hit in DSDP -- these are exactly the kind of subtle errors that formalization catches, and they live in the *protocol layer* that is fully proved.

### Precedents that got published

- **Feit-Thompson in Coq** (Gonthier et al.) axiomatized character theory results
- **CompCert** axiomatizes the hardware model and some float semantics
- **Hales' Flyspeck/Kepler** axiomatized extensive numerical computations
- Most crypto formalizations (EasyCrypt, CryptHOL, FCF) axiomatize the underlying hard problems (DDH, LWE, etc.) -- directly analogous to our situation

### How to frame it in the paper

Don't hide the axioms -- **feature them as a design decision**:

> *"We axiomatize five properties of AG codes (Goppa bound, privacy surjectivity, monodromy compatibility, multiplicative closure, PGL bound) that follow from classical algebraic geometry (Riemann-Roch, covering theory). This cleanly separates the protocol-algebraic layer -- which is fully verified -- from the curve-arithmetic layer, which is orthogonal to the security argument and whose formalization would require a Riemann-Roch library that does not yet exist in any proof assistant."*

Then emphasize what IS proved:
- The entire protocol correctness chain (PGGInterface -> ThresholdScheme -> reconstruction)
- The security-threshold tradeoff (genus -> gap, fully proved from CoveringScheme axioms)
- The Massey construction, Lagrange interpolation, RS privacy
- The multiplicative extension (`ag_massey_mult`, formerly the last Admitted, now proved)
- Zero `Admitted` in `pgg-smc/reconstruct/`

### The one thing that COULD draw criticism

If a reviewer thinks the paper is *about AG codes specifically* rather than *about the protocol framework parameterized by AG codes*, then the axioms look like you're assuming your main result. So the framing must make clear that the contribution is the **modular framework** (MonodromyReprType -> CoveringScheme -> ThresholdScheme -> PGGInterface -> security tradeoff), not the AG code construction per se. The AG code is an *instantiation witness* showing the framework is non-vacuous.

## The 5 axioms ranked by provability

| Axiom | Math depth | MathComp gap | Feasibility |
|-------|-----------|-------------|-------------|
| `genus0_pgl` | Undergraduate | PGL construction | **Most feasible** -- could be a standalone project |
| `ag_mult` | Undergraduate | Function fields | Medium -- needs evaluation map formalization |
| `goppa_wt` | Graduate (Riemann-Roch) | Divisors, R-R | Hard -- flagship formalization target |
| `ag_priv_surj` | Graduate (dual R-R) | Same as above | Hard -- follows from `goppa_wt` machinery |
| `share_compatible` | Research-level | Covering theory | **Hardest** -- requires algebraic covers of curves |

The fundamental bottleneck is that MathComp has no theory of **algebraic curves over finite fields** -- no function fields, no divisors, no Riemann-Roch, no covering maps. The current axiomatization boundary is exactly at the "linear algebra meets algebraic geometry" interface, which is a reasonable and principled place to draw the line.

## Bottom line

A well-framed paper with explicit axioms at a principled boundary is standard practice and publishable. A paper that tries to hide the axioms or claims more than it proves will be rejected. We are in the former category.
