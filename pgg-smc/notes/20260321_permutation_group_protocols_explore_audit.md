# Explore-Audit Report: Permutation Group Ideas as CS Protocols vs. PGG-SMC

**Date:** 2026-03-21
**Directions explored:** 5

## Executive Summary

We investigated whether permutation group ideas have been published as computer science protocols, and how close/far they are from the current PGG-SMC formalization. Five directions were explored: (1) group-theoretic secret sharing, (2) random walks on Cayley graphs in crypto, (3) non-abelian group-based cryptography, (4) covering spaces / monodromy / AG codes in crypto, and (5) formally verified MPC protocols.

**Bottom line:** Each individual building block of PGG-SMC exists in prior literature (AG codes for threshold schemes, spectral gap mixing, non-abelian group crypto platforms, monodromy in algebraic geometry, formal MPC verification). However, **no published protocol combines monodromy representation + covering space geometry + AG code threshold schemes + information-theoretic fiber-entropy security into a unified pipeline**. PGG-SMC's novelty is architectural integration, not any single technique. It is weaker than Shamir/SPDZ on practical metrics (NC^1 vs P, eps > 0 vs perfect privacy) but offers unique algebraic structure (one group choice determines complexity class, security convergence, and threshold gap).

---

## Direction 1: Group-Theoretic and Permutation-Based Secret Sharing

### Research Findings

Three separate research streams exist:
- **Black-box group schemes** (Desmedt-Frankel 1994, Cramer-Fehr 2002): threshold secret sharing over abelian groups, no covering spaces
- **Word-problem schemes** (Kahrobaei et al. 2012): non-abelian groups (RAAGs) for computational-hardness-based secret sharing
- **AG code schemes** (Goppa 1982, Chen-Cramer 2006): threshold via curve genus, no explicit monodromy

PGG unifies all three layers (monodromy + covering + AG codes). The NC^1 connection via Barrington's theorem is correctly positioned as a foundations contribution.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: No prior unification of monodromy + covering + AG codes | **TRUE** | All cited papers verified; novel synthesis confirmed |
| C2: Spectral gap not formalized for secret-sharing security | **TRUE** | Literature real; PGG formalization is original |
| C3: Non-abelian groups necessary for PGG security | **SUSPICIOUS** | Codebase proves search-space collapse for abelian groups, but does NOT prove eps lower bound. Claim goes beyond what is formally proved |
| C4: Covering spaces = monodromy = deck transformations | **TRUE** | Classical algebraic geometry (SGA1, Szamuely 2009) |
| C5: AG codes give threshold gap T <= k + 2g | **TRUE** | Goppa bound is classical; correctly formalized |
| C6: Barrington's theorem: non-solvable => NC^1 | **TRUE** | Paper exists (1989), theorem correctly stated |
| C7: Standard MPC computes P; PGG computes NC^1 | **TRUE** | All MPC papers verified; NC^1 claim conditional on unformalized extension |
| C8: Kahrobaei computational vs. PGG information-theoretic | **TRUE** | Security model distinction is accurate |

### Bottom Line
7/8 claims TRUE, 1 SUSPICIOUS (C3 overstates formal results on abelian necessity). No fabrication detected. The honest assessment: PGG's novelty is architectural integration of known components.

---

## Direction 2: Random Walks on Cayley Graphs in Cryptography

### Research Findings

Strong prior art exists:
- **Cayley hash functions** (Zemor 1991, Tillich-Zemor 1994): random walks for collision resistance; broken by Grassl et al. (2009), Petit (2009)
- **Expander hash functions** (Charles-Goren-Lauter 2006): Ramanujan graphs via isogeny, provably secure
- **Spectral gap theory** (Diaconis-Shahshahani 1981, Kassabov-Lubotzky-Nikolov 2006): non-abelian simple groups are expanders

PGG differs by using **Schreier graphs** (on N sheets) instead of Cayley graphs (on |G| elements), reducing prefactor from sqrt(|G|) to sqrt(N). This is mathematically significant (Monster: 10^10 vs 10^26).

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Spectral gap controls mixing via representation theory | **TRUE** | Diaconis-Shahshahani, Saloff-Coste verified |
| C2: Cayley hashes broken by Grassl/Petit | **TRUE** | Papers real; chronology slightly compressed but accurate |
| C3: Charles-Goren-Lauter isogeny expanders | **TRUE** | Paper exists (Journal of Cryptology 2007) |
| C4: Mixing time essential for secret sharing | **SUSPICIOUS** | TRUE within PGG, but overstated as general principle; standard secret sharing doesn't use mixing time |
| C5: Non-abelian simple groups are expanders | **TRUE (OUTDATED)** | Kassabov-Lubotzky-Nikolov 2006 verified; but 2021 work (arXiv:2105.01149) shows abelian expander sets exist |
| C6: Schreier refines Cayley; sqrt(N) vs sqrt(|G|) | **TRUE** | Ceccherini-Silberstein et al. 2008 Thm 5.5.3 verified |
| C7: Entropy dual to spectral via Pinsker | **TRUE** | Classical inequality; PGG bridges verified in code |
| C8: Word length couples mixing + threshold | **TRUE (PGG-specific)** | Hurwitz bound + Goppa gap are classical; coupling is PGG's contribution |

### Bottom Line
6/8 TRUE, 1 OUTDATED (abelian expanders exist since 2021), 1 OVERSTATED (mixing-threshold coupling is PGG-specific, not general doctrine). PGG's Schreier-graph innovation is genuine and significant.

---

## Direction 3: Non-Abelian Group-Based Cryptography

### Research Findings

Active field with multiple broken protocols:
- **Braid group crypto** (Ko-Lee 2000, AAG 1999): conjugacy search problems; broken by length-based attacks and Cheon's polynomial-time algorithm
- **RAAG crypto** (arXiv 1610.06495): NP-complete subgroup isomorphism; more recent, no major attacks yet
- **Thompson groups, polycyclic groups**: mixed security results
- **Finite simple groups** (2024 survey): emerging interest in post-quantum era

PGG is **orthogonal**: it uses permutation fiber uniformity (information-theoretic), not conjugacy/decomposition problems (computational). No prior non-abelian crypto uses covering space reconstruction.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Braid group crypto broken (Ko-Lee, AAG) | **TRUE** | Standard knowledge; orthogonal to PGG (infinite vs finite groups) |
| C2: Length-based attacks compromise protocols | **TRUE** | PGG's info-theoretic model is immune to these |
| C3: RAAGs proposed for crypto (NP-complete problems) | **PARTIALLY TRUE** | Paper exists, but PGG uses RAAGs for trace counting, not NP-hardness |
| C4: Thompson/polycyclic studied with mixed results | **TRUE** | Not addressed in PGG codebase; irrelevant to project |
| C5: Finite simple groups (incl. Monster) for quantum-era crypto | **SUSPICIOUS** | The "2024 La Matematica paper" exists (doi:10.1007/s44007-024-00096-z), but Monster instance in PGG is **original work**, not derived from it |
| C6: Permutation group crypto underdeveloped | **TRUE** | PGG is first rigorous formalization |
| C7: No prior fiber uniformity + covering reconstruction | **TRUE** | Verified; covering reconstruction is axiomatized in PGG |
| C8: PGG info-theoretic vs conjugacy-computational | **TRUE** | Zero computational assumptions in PGG confirmed across 9 security files |

### Bottom Line
6/8 TRUE, 1 PARTIALLY TRUE (RAAG usage differs), 1 SUSPICIOUS (Monster prior art attribution unclear). PGG's information-theoretic model is genuinely orthogonal to all existing non-abelian group crypto.

---

## Direction 4: Covering Spaces, Monodromy, and AG Codes in Crypto

### Research Findings

Strong mathematical foundations, limited crypto applications:
- **AG codes for secret sharing**: Chen-Cramer (CRYPTO 2006) is the direct predecessor — quasi-threshold with gap 2g
- **Riemann-Hurwitz**: classical topology relating group order to genus
- **Hurwitz bound**: |G| <= 84(g-1) constrains group size for genus > 1
- **Garcia-Stichtenoth towers**: explicit AG code families approaching Drinfeld-Vladut bound
- **Monodromy**: standard tool in algebraic geometry, NOT previously used in cryptographic protocols

PGG's novel contribution: interpreting monodromy as a cryptographic protocol actor and linking covering genus to threshold gap in a formalized pipeline.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: AG codes standard for threshold secret sharing | **TRUE** | Chen-Cramer (CRYPTO 2006) verified at Springer |
| C2: Branched coverings = Galois groups foundation | **TRUE** | Szamuely (2009), SGA1 verified; canonical references |
| C3: Riemann-Hurwitz relates group order to genus | **TRUE** | Standard topology; correctly axiomatized in codebase |
| C4: Genus determines threshold gap T <= k + 2g | **TRUE** | Goppa bound classical; Chen-Cramer confirms quasi-threshold |
| C5: Hurwitz bound |G| <= 84(g-1) | **TRUE** | Classical result (1893); correctly used in pgg_protocol_landscape.v |
| C6: Garcia-Stichtenoth towers | **TRUE (minor citation gap)** | Papers exist (1995 and 1996); report should cite both |
| C7: Monodromy standard for covering spaces | **TRUE** | nLab, standard topology verified |
| C8: Topological secret sharing exists but is separate | **TRUE** | Picture-hanging puzzles, differential manifold approaches are real but unrelated to AG+coverings |

### Bottom Line
8/8 TRUE (one with minor citation gap). This is the strongest direction — all claims verified with no fabrication. PGG's use of monodromy as a cryptographic protocol object is genuinely novel.

---

## Direction 5: Formally Verified MPC Protocols

### Research Findings

Multiple frameworks exist but target different goals:
- **EasyCrypt**: computational MPC (BGW, Maurer), game-based proofs
- **FCF** (Coq): computational primitives (El Gamal, HMAC)
- **SSProve** (Coq): state-separating modular crypto proofs
- **CertiCrypt** (Coq, NOT Isabelle): OAEP/FDH public-key schemes
- **Infotheo**: Shannon theorems, now extended to MPC security (FORTE 2025)

PGG is unique in combining: session-typed protocols + information-theoretic security + algebraic rigidity. No prior system formalizes AG code threshold schemes.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: EasyCrypt formalizes computational MPC, not info-theoretic | **TRUE** | BGW and Maurer formalized; no info-theoretic secret sharing |
| C2: FCF proves El Gamal/HMAC/SSE, not threshold schemes | **TRUE** | Confirmed from FCF paper (Cornell) |
| C3: Infotheo includes first info-theoretic MPC pipeline (ITP 2024) | **SUSPICIOUS** | **Venue error**: MPC security paper is FORTE 2025 (Springer), NOT ITP 2024. ITP 2024 paper is about robust mean estimation (unrelated) |
| C4: CertiCrypt (Isabelle/HOL) formalizes OAEP/FDH | **FALSE (platform)** | CertiCrypt is **Coq-based**, not Isabelle/HOL. OAEP/FDH claims are correct |
| C5: SSProve uses state-separating proofs, different from PGG | **TRUE** | ACM TOPLAS 2023; orthogonal methodology |
| C6: Session types + monodromy + native_compute duality is novel | **TRUE** | No prior combination found in literature |
| C7: No formalization of AG code threshold with genus tradeoffs | **TRUE** | No prior work found in any proof assistant |
| C8: UC framework vs algebraic rigidity are fundamentally different | **TRUE** | Canetti (2000) confirmed; orthogonal approaches |

### Bottom Line
5/8 TRUE, 1 FALSE (CertiCrypt platform), 1 SUSPICIOUS (venue error), 1 TRUE with caveat. Two factual errors detected: CertiCrypt is Coq not Isabelle, and the infotheo MPC paper is FORTE 2025 not ITP 2024. Despite errors, the core claim holds: PGG's combination is unique among verified MPC systems.

---

## Cross-Cutting Analysis

### What Survived Audit (TRUE across directions)

1. **No prior protocol combines monodromy + covering spaces + AG codes** — confirmed across all 5 directions
2. **Chen-Cramer (CRYPTO 2006) is the closest predecessor** — AG codes for threshold secret sharing, but no monodromy or covering space structure
3. **PGG's information-theoretic model is orthogonal to computational non-abelian crypto** — confirmed; zero computational assumptions
4. **Schreier graph innovation is genuine** — sqrt(N) vs sqrt(|G|) prefactor improvement is mathematically significant
5. **AG code threshold with covering-genus tradeoff is novel in formal verification** — no prior proof assistant formalization found
6. **Barrington-Therien classification as protocol design knob** — correctly established, unique to PGG
7. **All major mathematical foundations are correctly cited** — Goppa, Hurwitz, Riemann-Hurwitz, Szamuely, SGA1, Diaconis-Shahshahani all verified

### What Failed Audit

1. **CertiCrypt platform**: Research agent claimed Isabelle/HOL; it's actually Coq
2. **Infotheo venue**: FORTE 2025, not ITP 2024 — two different papers conflated
3. **Garcia-Stichtenoth citation**: incomplete (should cite both 1995 and 1996 papers)

### Suspicious Claims Requiring Further Investigation

1. **"Non-abelian groups are necessary for PGG security" (Direction 1, C3)**: Codebase proves abelian search-space collapse but does NOT prove epsilon lower bound. The claim goes beyond what is formally proved. Would need: either a formal lower bound on eps for all abelian groups, or rewording to "search space collapses" instead of "security vanishes."

2. **"Abelian groups are not expanders" (Direction 2, C5)**: Outdated since 2021 (arXiv:2105.01149 shows abelian expander constructions exist). PGG's abelian collapse result is about trace counting, not expansion per se — should be stated more precisely.

3. **"Mixing time essential for secret sharing" (Direction 2, C4)**: Overstated as general principle when it's PGG-specific design choice. Standard Shamir secret sharing has no mixing-time parameter.

4. **"La Matematica 2024 paper on Monster for quantum-era crypto" (Direction 3, C5)**: Paper likely exists (doi:10.1007/s44007-024-00096-z), but PGG's Monster instance is original work, not derived from it. Attribution needs clarification.

---

## Proximity Ranking: Prior Work vs. PGG-SMC

| Prior Work | Distance | What's Shared | What's Missing from PGG |
|-----------|----------|---------------|------------------------|
| **Chen-Cramer (CRYPTO 2006)** | **CLOSEST** | AG codes for threshold, genus-dependent gap | No monodromy, no covering spaces, no fiber-entropy security |
| **Cayley/Schreier spectral analysis** (Diaconis, Ceccherini-Silberstein) | **CLOSE** (foundations) | Spectral gap bounds, mixing time theory | Not applied to secret sharing; PGG's Schreier application is new |
| **Kahrobaei et al. RAAG crypto** (2012) | **MEDIUM** | Same group family (RAAGs), secret sharing goal | Computational security model; no monodromy, no covering spaces |
| **Barrington's theorem** (1989) | **MEDIUM** (theory) | NC^1 = non-solvable groups; branching programs | Not a protocol; PGG extends to protocol design knob |
| **Braid group crypto** (Ko-Lee, AAG) | **FAR** | Non-abelian groups | Infinite groups, conjugacy problems, computational model; mostly broken |
| **EasyCrypt/SSProve/FCF verified MPC** | **FAR** | Formal verification of MPC | Computational model, no AG codes, no monodromy, no group actions |
| **Charles-Goren-Lauter expander hashing** | **FAR** | Expander graphs, spectral gap | Hash functions not secret sharing; isogeny not monodromy |
| **Standard MPC (Yao, BGW, SPDZ)** | **FAR** | Secret sharing goal | Compute all of P (vs NC^1); no group-theoretic structure |

---

## Recommendation

**PGG-SMC occupies a genuinely novel position** — no published protocol combines its three layers (monodromy representation, covering space geometry, AG code threshold). The closest prior work is Chen-Cramer (2006), which uses AG codes for threshold but without the covering-space and monodromy structure.

**For positioning a paper:**
1. **Lead with the unified pipeline** (monodromy -> covering -> AG code -> threshold + security) as the core contribution
2. **Cite Chen-Cramer 2006 as direct predecessor** and explain what PGG adds (monodromy parameterization, Riemann-Hurwitz coupling, fiber-entropy security)
3. **Acknowledge practical limitations honestly**: NC^1 < P, eps > 0 vs perfect privacy, axiomatized covering reconstruction
4. **Strengthen the abelian impossibility result**: either prove a formal eps lower bound or soften the claim to "search space collapse"
5. **Correct factual errors found in audit**: CertiCrypt is Coq-based; infotheo MPC paper is FORTE 2025; Garcia-Stichtenoth needs both 1995+1996 citations
6. **Target venue**: Formalization conferences (ITP, CPP) or crypto theory (TCC, CRYPTO theory track) where the algebraic rigidity theorem and formal verification methodology are valued

**The honest framing**: PGG-SMC is an information-theoretic formalization that proves, for the first time, how one algebraic choice (G, rho, sigmas) simultaneously determines a protocol's complexity class, security convergence rate, and threshold gap — a structural result absent from circuit-based MPC.
