# Explore-Audit Report: PGG Paper Framing

**Date:** 2026-03-23
**Directions explored:** 3

## Executive Summary

Three paper framing directions were explored and adversarially audited for the PGG formalization (58 Rocq files, 21.8K LOC, 0 Admitted). Direction 1 (ITP/CPP formalization paper) emerged as the strongest — zero Admitted proofs confirmed, no prior ITP card-crypto work found, and core security theorems fully proved. Direction 2 (crypto theory for ASIACRYPT/TCC) is viable as supplementary narrative. Direction 3 (algebraic rigidity for Journal of Cryptology) has genuine mathematical content but key claims (Galois interpretation, genus-1 universality) failed audit.

## Direction 1: ITP/CPP Formalization Paper

### Research Findings
The PGG codebase achieves zero-Admitted formal verification of card-based cryptographic protocol security. No prior ITP/CPP work exists on formalized card-based cryptography (Koch et al. 2019 uses SAT-based BMC, not ITP). The formalization extends Diaconis's shuffle fairness to k-coalition resistance via Schreier spectral gaps — an unexplored intersection of formal methods and card-based crypto.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Zero Admitted proofs | TRUE | grep confirms 0 Admitted across all 58 files |
| C2: Diaconis extension to k-coalition | TRUE | Explicit formalization in pgg_schreier.v; cites genuine literature |
| C3: Five concrete instances | TRUE | Cyclic, Abelian, OC, S5, Monster all present (Star deleted) |
| C4: Three-layer infrastructure | TRUE | Documented in architecture overview |
| C5: Schreier sqrt(N) vs sqrt(\|G\|) | TRUE | Mathematically sound; axiomatized per-instance |
| C6: Modular security pipeline | TRUE (qualified) | CollisionBound decouples; weval_inj needed downstream |
| C7: No prior ITP card-crypto work | TRUE | Koch et al. 2019 uses BMC/SAT, not ITP |
| C8: Narrative tension ITP vs crypto | UNFALSIFIABLE | Meta-claim about positioning |

### Bottom Line
**Strongest direction.** All core claims verified. Recommended primary framing.

## Direction 2: Crypto Theory Paper (ASIACRYPT/TCC)

### Research Findings
The mathematical contribution — Schreier spectral analysis for k-coalition fairness with sqrt(N) prefactor — is substantive enough for a theory paper. The entropy pipeline (fiber counting → Pinsker → var_dist) connects permutation algebra to information-theoretic security. Five instances demonstrate breadth.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: eps(L) ≤ sqrt(N)(1-gap)^L | SUSPICIOUS | Axiomatized in SchreierCertificate, not derived |
| C2: Collusion bound proved | TRUE | Theorem collusion_bound fully proved (lines 239-246) |
| C3: Entropy + Pinsker | TRUE | Entropy proved; Pinsker axiomatized (standard) |
| C4: Algebraic rigidity coupling | TRUE | ar_search_gap_tradeoff, ar_gap_bound proved |
| C5: Monster L*=67 perfect security | SUSPICIOUS | L*=67 axiomatized; 2^67 > 10^20 not formally verified |
| C6: OC smooth convergence | TRUE | Valid instance from Schreier theory |
| C7: Five-card Z_5 foundational | TRUE | Correctly formalized as PGG instance |
| C8: Schreier > Cayley | TRUE (qualitative) | Quantitative superiority not proved in Rocq |

### Bottom Line
Viable as supplementary narrative within the ITP paper. Not strong enough standalone for a top crypto venue without new protocols.

## Direction 3: Algebraic Rigidity (Journal of Cryptology)

### Research Findings
AlgebraicRigidity bundles SecurityWitness + ThresholdWitness, showing one algebraic choice (G, ρ, σ) determines complexity, security, and threshold. The covering genus controls the tradeoff: genus 0 → exact threshold (bounded group), genus > 0 → gap ≤ 2g.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Complexity ≤ \|G\| | TRUE | Fully proved from group structure |
| C2: PGL bound N(N²-1) | SUSPICIOUS | Per-instance hypothesis, not universal theorem |
| C3: Gap ≤ 2g via Riemann-Hurwitz | TRUE (qualified) | Gap is axiom of CoveringScheme, RH connection conceptual |
| C4: Five instances demonstrate tradeoff | TRUE | All five present with AlgebraicRigidity records |
| C5: Endpoint security direct bound | TRUE | Only for injective cases (correctly scoped) |
| C6: Fiber-counted security | TRUE | OC (ε=1), S5 (ε=6/5) via case analysis |
| C7: Galois-theoretic interpretation | FALSE | Comments only — zero formal theorems |
| C8: Three-regime threshold landscape | PARTIALLY TRUE | Genus-1 not universal; requires per-instance axioms |

### Bottom Line
Genuine mathematical content, but key selling points (Galois interpretation, genus-1 universality) don't survive audit. Better as a section within the ITP paper than a standalone submission.

## Cross-Cutting Analysis

### What survived audit
- Zero Admitted proofs (independently confirmed across all 3 audits)
- Collusion bound theorem (fully proved, cited correctly)
- Five concrete instances (all present and compiling)
- No prior ITP work on card-based crypto formalization
- Schreier sqrt(N) improvement (mathematically sound)

### What failed audit
- Galois-theoretic interpretation (FALSE — comments only, no formal theorems)
- Genus-1 universality (SUSPICIOUS — requires per-instance AG code axioms, no automatic constructor)
- Monster L*=67 "proven" (SUSPICIOUS — axiomatized, 2^67 > N not formally verified)

### Suspicious claims requiring further investigation
- SchreierCertificate convergence bound (axiomatized per-instance, cited from Diaconis 1988 / Ceccherini-Silberstein 2008 — acceptable for paper if clearly stated)
- PGL(2,N) bound for genus-0 (classical result, axiomatized per-instance — acceptable if cited as folklore)

## Recommendation

**Write a single paper targeting ITP 2026 or CPP 2027**, with:
1. **Primary narrative**: Formalization achievement (0 Admitted, 58 files, first ITP card-crypto)
2. **Mathematical content**: Schreier spectral fairness extending Diaconis to k-coalitions
3. **Architectural contribution**: Three-layer HB mixin design for protocol formalization
4. **Honest axiom inventory**: Explicitly list all axiomatized results (Schreier gaps, PGL bound, Monster structure, Pinsker inequality)

**Avoid**: Overclaiming Galois interpretation, genus-1 universality, or Monster L*=67 as "proven."

Paper created at: `pgg-smc/provsecMay31/20260323_pgg_itp_paper/main.tex`
