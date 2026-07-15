# Paper Review: SMC-PGG vs General MPC — An Honest Expert Analysis

**Reviewed:** 2026-03-13
**File:** `pgg-smc/notes/20260313_smc_pgg_vs_general_mpc.md`

## 1. Domain Assessment

**Domains:** Secure multiparty computation (MPC), computational complexity theory, algebraic cryptography, formal verification

**Reviewer Personas:** MPC theorist, complexity theorist, algebraic cryptographer

**Key Terms:** SMC-PGG, monodromy walk, NC^1, garbled circuits, Barrington branching program, Krohn-Rhodes decomposition, RAAG (right-angled Artin group), Cartier-Foata normal form, fiber uniformity, algebraic geometry codes, secret sharing, SPDZ, GMW/BGW

---

## 2. Reasoning Verification

### Summary
- **True claims:** 7
- **False claims:** 9
- **Suspicious claims:** 22
- **Opus overrides:** 5 (F2 overturned False→True; F5 downgraded False→Suspicious; S12 escalated Suspicious→False; S17 escalated Suspicious→False; S20 escalated Suspicious→False)

### False Claims

| ID | Location | Claim | Explanation |
|----|----------|-------|-------------|
| F1 | §2 para 3 | "Functions in P \ NC^1 include integer multiplication" | Integer multiplication is in TC^0 ⊆ NC^1; it is not an example of a function outside NC^1. |
| F3 | §5 Claim 1 table | "Abelian (e.g., Z/nZ) → ACC^0 ∩ commutative" | "ACC^0 ∩ commutative" is not a standard complexity class. Abelian groups characterize ACC^0 by Barrington-Thérien; the intersection notation is non-standard and misleading. |
| F4 | §5 Claim 1 caveat | "The NC^1 claim requires width exactly 5" | Width 5 is *sufficient* (Barrington 1989 uses S_5), not *necessary*. Any non-solvable group works; "exactly 5" implies minimality which is not what Barrington states. |
| F6 | §8.4 | "A protocol designer using garbled circuits…knows nothing structural about what they've built: how many rounds are needed" | Yao's garbled circuits achieve well-known O(1) rounds; GMW's round complexity equals multiplicative depth. Claiming designers "know nothing structural" is false. |
| F7 | §9 | "lattices (algebraic geometry)" | Lattice-based cryptography belongs to the geometry of numbers / algebraic number theory, not algebraic geometry. This is a mathematical misclassification. |
| F8 | §5 Claim 2 | Full commutativity (I = Σ × Σ) → "computational class drops" to abelian/ACC^0 | Conflates the independence relation I (round structure) with the group variety G (computational class). Making I fully commutative does not change G or its associated complexity class. These are orthogonal parameters. *(Opus override: was Suspicious)* |
| F9 | §5 Claim 3 | Uniform conditional property "has no analogue in additive or Shamir sharing" | Shamir secret sharing has an exact analogue: conditioned on the secret, any t shares are uniformly distributed over consistent share vectors. The exclusivity claim is false. *(Opus override: was Suspicious)* |
| F10 | §7.2 | "depth d requires 4^d permutation factors" (implying exponential blowup) | For NC^1 circuits, d = O(log n), so 4^d = n^{O(1)} is *polynomial*, not exponential. Presenting 4^d as a practical blowup is misleading for the intended domain of SMC-PGG. *(Opus override: was Suspicious)* |
| F11 | Ref. 5 | SPDZ co-author listed as "Warinschi" | The correct fourth author is Zakarias (Damgård, Pastro, Smart, Zakarias, CRYPTO 2012). *(Opus override: was Suspicious)* |

### Suspicious Claims

| ID | Location | Claim | Concerns |
|----|----------|-------|----------|
| S1 | §1.1 | Security proof composability via algebraic structure | Asserted without specifying a composition framework (UC, hybrid, sequential). Composability is non-trivial and requires explicit proof. |
| S2 | §1.2 | "CPS-computable" as a complexity class; "No other MPC framework has this" | CPS-computable is non-standard and undefined. GMW round complexity = multiplicative depth is also an algebraic characterization. Uniqueness claim unsupported. |
| S3 | §1.3 | Aperiodic K-R layers handled by "threshold broadcast" | The mapping from aperiodic monoid components to threshold broadcast protocols is asserted without justification or construction. |
| S4 | §1.4 | Covering space → AG code → threshold chain | Conflates three distinct mathematical constructions without explicit connecting maps. "Better threshold parameters" is speculative without quantification. |
| S5 | §2 | NC^1 as SMC-PGG's computational boundary | The NC^1 claim is conditional on a protocol extension (input-dependent permutation selection) that has not been formalized or security-analyzed. Presenting it as an established boundary is misleading. |
| S6 | §3 table | "Matrix multiplication" listed as not in NC^1 | P-completeness applies to *iterated* matrix product, not single matrix multiplication (which is in NC^2). The table conflates these. |
| S7 | §3 | "many practical MPC applications" are naturally in NC^1 | No citation or empirical evidence. Standard practical MPC applications (ML inference, database queries) heavily involve multiplication and matrix operations outside NC^1. |
| S8 | §4 table | GMW security model: "IT (honest majority) or computational" | Conflates GMW (computational, OT-based) with BGW (IT, honest-majority). These are distinct protocols with different security models. |
| S9 | §4 table | SPDZ security: "IT with preprocessing" | Imprecise — SPDZ's preprocessing phase uses SHE/OT (computational). Only the online phase achieves IT security given preprocessed MACs. |
| S10 | §4 table | SMC-PGG communication: O(ℓ · log N) | Variables ℓ and N are undefined. The bound is unverifiable without derivation. |
| S11 | §4 table | "Formal verification: None at protocol level" for Yao/GMW/SPDZ | Machine-checked proofs for garbling schemes exist (EasyCrypt, CryptoVerif). The comparison is not apples-to-apples. |
| S13 | §5 Claim 2 | "No other MPC framework exposes this knob" | Depth-width trade-offs in circuit complexity are well-studied. The novelty claim is plausible for the specific RAAG formulation but overstated without comparison. |
| S14 | §5 Claim 3 | "The entropy of the adversary's uncertainty is log₂|L_g|" | This equality holds only under uniform distribution over the fiber, which is an unstated assumption. |
| S15 | §5 Claim 3 | "The fiber L_g corresponds to the set of loops in the base space that lift to paths ending at sheet g" | Imprecise topology: fibers of a covering space are preimages of points, not loops. The description conflates elements of π₁ with the discrete fiber. |
| S16 | §5 Claim 3 | Uniform conditional property holds for S_5 with 4 generators | This requires justification; it does not hold for arbitrary generators and word lengths without a mixing or structural argument. |
| S18 | §6 | "What you can't compute: anything outside NC^1 (provably, not just 'we don't know how')" | Implies NC^1 ≠ P, which is an open problem. The upper bound (NC^1) is provable; the existence of functions in P \ NC^1 is not. *(Opus override: was False — downgraded because the upper bound IS provable)* |
| S19 | §6 table | Circuit-MPC uses "ad hoc simulation arguments" | Rhetorically loaded. Simulation-based security is a systematic, principled methodology — not "ad hoc." |
| S21 | §8.1 | "The computational restriction is not binding" for NC^1-natural functions | Ignores that even NC^1 functions suffer the Barrington encoding blowup (4^{O(log n)} = poly(n) but potentially large constants). |
| S22 | §8.2 | SMC-PGG's IT security is a "genuine advantage" | BGW (1988) already provides IT security for *all of P* with honest majority. SMC-PGG's NC^1 restriction is a limitation, not an advantage, relative to BGW. |
| S23 | §8.3 | Verifying garbled circuits in Coq is "a much larger undertaking" | EasyCrypt formalizations of garbled circuits exist. The claim is asserted without citation or comparison to actual formalization efforts. |
| S24 | §9 | SMC-PGG adds "algebraic automata theory" as a new foundation for MPC | Barrington (1989) already centrally uses algebraic automata theory. The novelty claim should be scoped more precisely. |
| S26 | Ref. 7 context | Ishai-Kushilevitz (2002) constant-round NC^1 protocols | This result gives O(1)-round IT-secure protocols for NC^1, directly undercutting any round-complexity advantage for SMC-PGG over existing IT-MPC for the same class. |

### True Claims
T1 (§2: NC^1 ⊆ L ⊆ NL ⊆ P chain), T2 (§3: addition O(log n) depth), T3 (§3: directed s-t reachability P-complete), T4 (§5: Foata depth = rounds), T5 (§5: convolution formula), T6 (§5: fiber security is reformulation not strengthening), T7 (§7.3: maturity assessment)

---

## 3. Academic Writing Critique

1. **Missing contribution statement.** No explicit distinction between (a) novel SMC-PGG contributions, (b) survey of known results (Barrington 1989, Barrington-Thérien 1988, Krohn-Rhodes 1965), and (c) conjectured extensions. Add a structured contributions paragraph after §1 preamble using an Established/Conjectured/Proposed taxonomy.

2. **BGW omission — the most critical comparative gap.** §4's "SMC-PGG wins on security model" claim and §8.2's IT-security advantage both fail to mention BGW (1988), which achieves IT security for *all of P* with honest majority and no preprocessing. This is the single most relevant counterpoint. Add a BGW row to Table 4 and revise the key observations accordingly.

3. **Conflation of G-variety and I-graph as computational-class determinants.** §1.2 attributes computational power jointly to I and G; §5 Claim 1 attributes it solely to G. These are inconsistent. Add a clarifying statement: "The computational class is determined by G alone; I controls only round complexity."

4. **Fixed monodromy word conflated with input-dependent Barrington program (§2).** The unconditional assertion precedes the conditionality caveat. Reorder: state the extension as conditional first, then invoke Barrington's theorem, then mark the formalization gap.

5. **Non-standard terminology used without definition.** "CPS-computable" (§1.2, §5) and "ACC^0 ∩ commutative" (§5 table) are undefined non-standard terms. Define or replace at first use.

6. **Rhetorically loaded comparisons.** "Ad hoc simulation arguments" (§6 table), "knows nothing structural" (§8.4), "hope for the best" (§6) are evaluative rather than technical. Replace with precise characterizations.

7. **No Related Work section.** Inline comparisons miss key works (BGW, Ishai-Kushilevitz constant-round NC^1, EasyCrypt garbling proofs). A dedicated section would anchor the comparative claims.

8. **Cross-references to companion notes are not self-contained.** "Concrete demonstration (from Examples note, Ex. 3 §5)" is unresolvable without the companion document open. Either reproduce the key result inline or make the argument self-contained.

9. **Reference [6] (Agarwal et al. 2019) is never cited in the text.** Either cite in context or remove.

10. **"Honest caveat" labels are informal.** The §5 structure (Status: True / Honest caveat:) reads as a review checklist, not a technical note. Restructure as numbered claims with discussion subsections.

11. **Missing definitions for key concepts.** Monodromy walk, Foata depth, trace monoid are used without definition. A reader without the companion notes cannot parse §1.2.

12. **Ishai-Kushilevitz (2002) omission.** Ref. [7] is listed but never discussed in context of round complexity. This result gives constant-round IT-secure MPC for NC^1 — directly relevant to §5 Claim 2 and §8.

---

## 4. Section Formality Distance

| Section | Rating (1–5) | Justification |
|---------|:---:|---------------|
| §1 preamble | 4 | No contribution statement; motivational/sales-pitch framing |
| §1.1 Algebraic security proofs | 3 | Technically accurate but no formal definitions; composability asserted not proved |
| §1.2 RAAG parallelism–power | 3 | Substantive but conflates I/G; CPS undefined; "formal knob" informal |
| §1.3 Krohn-Rhodes | 3 | Correct high-level; aperiodic→broadcast unjustified; "principled" evaluative |
| §1.4 AG connection | 4 | Speculative; no theorem cited; chain of constructions not justified |
| §2 Computational Boundary | 3 | Barrington stated correctly at high level; conditional claim placed after unconditional assertion |
| §3 NC^1 tables | 2 | Well-structured reference material; integer multiplication error; practical interpretation needs citation |
| §4 Comparison Table | 3 | Useful but GMW/BGW conflated; SPDZ imprecise; BGW absent; "wins on" informal |
| §5 Claim 1 (G-variety) | 3 | Barrington-Thérien cited correctly; non-standard notation; "width exactly 5" imprecise |
| §5 Claim 2 (I→rounds) | 2 | Core claim sound (Foata depth = rounds); I/G conflation in examples; CPS undefined |
| §5 Claim 3 (fiber security) | 3 | Core math accurate; Shamir analogue claim false; topology imprecise; uniformity unstated |
| §6 Correct Framing | 3 | Apt lattice-RSA analogy; structural table clear; "provably" overstated; "ad hoc" loaded |
| §7.1 NOT more powerful | 2 | Accurate, concise, well-qualified |
| §7.2 NOT more efficient | 3 | 4^d claim misleading; otherwise honest comparison |
| §7.3 NOT deployment-ready | 1 | Accurate, appropriately sobering maturity table |
| §8.1 NC^1 applications | 2 | Honest enumeration; needs citation for "many practical applications" claim |
| §8.2 IT security | 3 | Accurate but omits BGW as the direct comparator |
| §8.3 Formal verification | 2 | Accurate scope description; should cite existing garbling proofs |
| §8.4 Structural guarantees | 3 | Overstates circuit-MPC designer ignorance; UC framework not mentioned |
| §9 Broader Lesson | 2 | Good analogical framing; well-posed closing question; lattice misclassification |
| References | 3 | One wrong author; one uncited entry; inconsistent formatting |

*(1 = publication-ready, 5 = informal notes / far from formal)*

---

## 5. Constructive Suggestions

### Critical

- **[F1] §2 para 3 (restatement)**: Replace "integer multiplication" with a genuine P\NC^1 example (e.g., circuit value problem, CVP) or delete the example and note the P vs NC^1 separation is open.
  - *Confidence*: definite

- **[F8] §5 Claim 2 (proof-repair)**: Rewrite to clearly separate the independence relation I (round structure) from the group G (computational class). Remove the implication that full commutativity of I changes the complexity class.
  - *LaTeX sketch*: "The computational class is determined by G alone (Barrington-Thérien). The independence graph I controls round complexity (Foata depth), not the set of computable functions."
  - *Confidence*: definite

- **[F9] §5 Claim 3 (restatement)**: Remove the uniqueness claim ("has no analogue in Shamir sharing"). Replace with: "While Shamir sharing has an analogous uniformity property, the covering-space perspective provides additional topological structure connecting security to the fundamental group."
  - *Confidence*: definite

- **[F11] Ref. 5 (notation)**: Correct "Warinschi" to "Zakarias" in the SPDZ reference.
  - *Confidence*: definite

- **[S1] §1.1 (hypothesis-insertion)**: Either prove composability within a recognized framework (UC, GNUC) or downgrade to a conjecture with explicit statement of what framework is needed.
  - *Options*: A: Full UC proof. B: Restrict to sequential composability and prove directly. C: Add explicit open-problem statement and remove composability from contribution claims.
  - *Confidence*: definite

- **[S18] §6 (restatement)**: Replace "provably, not just 'we don't know how'" with "assuming NC^1 ⊊ P (an open problem in complexity theory)."
  - *Confidence*: definite

### Major

- **[F3] §5 table (restatement)**: Replace "ACC^0 ∩ commutative" with "ACC^0" and cite Barrington-Thérien (1988). Add footnote if a strict subclass is intended.
  - *Confidence*: definite

- **[F4] §5 Claim 1 (restatement)**: Replace "width exactly 5" with "width at most 5 (width 5 is sufficient by Barrington's theorem using S_5)."
  - *Confidence*: definite

- **[F6] §8.4 (restatement)**: Delete or qualify "knows nothing structural about rounds." Yao's O(1) rounds and GMW's rounds = multiplicative depth are well-known.
  - *Options*: A: Restrict claim to absence of *algebraic* (group-theoretic) structure. B: Delete the sentence.
  - *Confidence*: definite

- **[F10] §7.2 (restatement)**: Add: "For NC^1 circuits where d = O(log n), this gives 4^d = n^{O(1)} factors — polynomial, not exponential."
  - *Confidence*: definite

- **[S8] §4 table (restatement)**: Separate GMW (computational, OT-based) from BGW (IT, honest-majority) into distinct rows.
  - *Confidence*: definite

- **[S9] §4 table (restatement)**: Replace SPDZ security with "Computational offline / IT online (with preprocessed MACs)."
  - *Confidence*: definite

- **[S22] §8.2 (restatement)**: Acknowledge BGW provides IT security for all of P; reframe SMC-PGG's advantage in terms of algebraic structure, not IT security per se.
  - *Confidence*: definite

- **[S26] §8/related work (structural)**: Add paragraph addressing Ishai-Kushilevitz (2002) constant-round NC^1 protocols and how SMC-PGG's round complexity compares.
  - *Confidence*: definite

- **[S3] §1.3 (proof-repair)**: Provide a formal construction or lemma for the aperiodic monoid → threshold broadcast mapping, or downgrade to conjecture.
  - *Confidence*: possible

- **[S4] §1.4 (structural)**: Separate the three constructions (covering space, AG codes, threshold sharing) with explicit connecting maps and citations at each transition.
  - *Confidence*: possible

### Minor

- **[F7] §9 (restatement)**: Replace "lattices (algebraic geometry)" with "lattices (geometry of numbers)."
  - *Confidence*: definite

- **[S2] §1.2 (notation)**: Define "CPS-computable" formally at first use; cite GMW round complexity = multiplicative depth as a known result.
  - *Confidence*: definite

- **[S7] §3 (structural)**: Add citations for "many practical MPC applications are in NC^1" or qualify with "we believe."
  - *Confidence*: definite

- **[S10] §4 table (notation)**: Define ℓ and N in a table footnote.
  - *Confidence*: definite

- **[S11] §4 (structural)**: Add footnote citing EasyCrypt garbling proofs and note that formal MPC verification is an active area.
  - *Confidence*: definite

- **[S14] §5 Claim 3 (hypothesis-insertion)**: Add "assuming uniform distribution over the fiber L_g" before the entropy equality.
  - *Confidence*: definite

- **[S15] §5 Claim 3 (restatement)**: Use precise topological language or replace with algebraic fiber description.
  - *Confidence*: possible

- **[S19] §6 table (remark-elimination)**: Replace "ad hoc simulation arguments" with "protocol-specific simulation proofs."
  - *Confidence*: definite

- **[S24] §9 (structural)**: Acknowledge Barrington (1989) as prior use of algebraic automata theory in MPC context; scope the novelty claim precisely.
  - *Confidence*: definite

- **[W1] §1 (structural)**: Add numbered contributions list at end of introduction.
  - *Confidence*: definite

- **[W2] After §1 (structural)**: Add a dedicated Related Work section covering BGW, Ishai-Kushilevitz, EasyCrypt garbling proofs.
  - *Confidence*: definite

---

## 6. Summary Verdict

The note's analytical framework — honestly positioning SMC-PGG's algebraic advantages against its NC^1 computational limitation — is well-conceived and the self-critical tone is genuinely unusual and praiseworthy. However, the reasoning contains **9 false claims** (most critically: integer multiplication misclassified as outside NC^1, the I/G conflation in Claim 2, the false Shamir uniqueness claim, and the 4^d misrepresentation) and **22 suspicious claims** (most critically: composability asserted without a proof framework, BGW omitted from the IT-security comparison, and the "provably" overstatement regarding NC^1 ≠ P). The most damaging structural omission is the absence of BGW from the comparison, which undermines the central "IT security advantage" argument. After fixing the false claims and addressing the major suspicious items, the note would be a strong internal technical document; reaching publication quality would additionally require formal definitions, a related work section, and a contribution taxonomy.

---

## 7. Fix Manifest

```yaml
fixes:
  - id: "F1"
    category: "restatement"
    severity: "critical"
    target: "§2 para 3"
    location: "Functions in P \\ NC^1 include integer multiplication, matrix multiplication, and linear programming"
    description: "Integer multiplication is in TC^0 ⊆ NC^1; not an example of P\\NC^1"
    suggestions:
      - "Replace with: 'Functions believed to lie in P\\NC^1 include P-complete problems such as the circuit value problem (CVP), assuming NC^1 ⊊ P.'"
      - "Delete the parenthetical list entirely and note that the P vs NC^1 separation is open"

  - id: "F3"
    category: "restatement"
    severity: "major"
    target: "§5 Claim 1 table"
    location: "ACC^0 ∩ commutative"
    description: "Non-standard complexity class notation; abelian groups characterize ACC^0 by Barrington-Thérien"
    suggestions:
      - "Replace table entry with 'ACC^0' and cite Barrington-Thérien (1988)"

  - id: "F4"
    category: "restatement"
    severity: "major"
    target: "§5 Claim 1 caveat"
    location: "NC^1 claim requires width exactly 5"
    description: "Width 5 is sufficient, not necessary; 'exactly 5' implies incorrect minimality"
    suggestions:
      - "Replace 'exactly 5' with 'at most 5 (width 5 suffices by Barrington's theorem)'"

  - id: "F6"
    category: "restatement"
    severity: "major"
    target: "§8.4"
    location: "knows nothing structural about what they've built: how many rounds are needed"
    description: "Yao O(1) rounds and GMW rounds = multiplicative depth are well-known structural results"
    suggestions:
      - "Replace with: 'the structural guarantees come from circuit-level metrics rather than algebraic parameters of the computation target'"

  - id: "F7"
    category: "restatement"
    severity: "minor"
    target: "§9"
    location: "lattices (algebraic geometry)"
    description: "Lattices in crypto belong to geometry of numbers, not algebraic geometry"
    suggestions:
      - "Replace 'algebraic geometry' with 'geometry of numbers'"

  - id: "F8"
    category: "proof-repair"
    severity: "critical"
    target: "§5 Claim 2"
    location: "computational class drops — abelian groups give only modular counting"
    description: "Conflates independence relation I (round structure) with group G (computational class)"
    suggestions:
      - "Rewrite to separate I and G: 'The computational class is determined by G alone. I controls round structure only.'"
      - "Remove implication that full commutativity of I changes the complexity class"

  - id: "F9"
    category: "restatement"
    severity: "critical"
    target: "§5 Claim 3"
    location: "has no analogue in additive or Shamir sharing"
    description: "Shamir sharing has an exact analogue (uniform shares conditioned on secret)"
    suggestions:
      - "Replace with: 'While Shamir sharing has an analogous uniformity property, the covering-space perspective provides additional topological structure.'"

  - id: "F10"
    category: "restatement"
    severity: "major"
    target: "§7.2"
    location: "depth d requires 4^d permutation factors"
    description: "For NC^1 (d=O(log n)), 4^d = n^O(1) is polynomial, not exponential"
    suggestions:
      - "Add clarification: 'For NC^1 circuits where d = O(log n), this gives polynomial (not exponential) length.'"

  - id: "F11"
    category: "notation"
    severity: "critical"
    target: "References"
    location: "Warinschi, S."
    description: "SPDZ fourth author is Zakarias, not Warinschi"
    suggestions:
      - "Replace 'Warinschi' with 'Zakarias'"

  - id: "S1"
    category: "hypothesis-insertion"
    severity: "critical"
    target: "§1.1"
    location: "the security of a sub-protocol reduces to an algebraic property"
    description: "Composability asserted without a formal framework (UC, GNUC, hybrid)"
    suggestions:
      - "Add explicit Assumption/Conjecture box citing UC framework"
      - "Or remove composability from contribution claims and mark as future work"

  - id: "S2"
    category: "notation"
    severity: "major"
    target: "§1.2"
    location: "CPS-computable functions"
    description: "Non-standard term used without definition"
    suggestions:
      - "Define CPS-computable formally at first use"

  - id: "S3"
    category: "proof-repair"
    severity: "major"
    target: "§1.3"
    location: "aperiodic layers by threshold broadcast"
    description: "Mapping from aperiodic monoid components to threshold broadcast is unjustified"
    suggestions:
      - "Add formal construction or lemma, or downgrade to conjecture"

  - id: "S4"
    category: "structural"
    severity: "major"
    target: "§1.4"
    location: "covering space → AG code → threshold chain"
    description: "Three distinct constructions conflated without explicit connecting maps"
    suggestions:
      - "Separate with explicit maps and citations at each transition"

  - id: "S8"
    category: "restatement"
    severity: "major"
    target: "§4 comparison table"
    location: "IT (honest majority) or computational"
    description: "GMW and BGW conflated in security model row"
    suggestions:
      - "Separate into distinct GMW and BGW rows"

  - id: "S9"
    category: "restatement"
    severity: "major"
    target: "§4 comparison table"
    location: "IT with preprocessing"
    description: "SPDZ preprocessing uses computational primitives; only online phase is IT"
    suggestions:
      - "Replace with 'Computational offline / IT online (with preprocessed MACs)'"

  - id: "S18"
    category: "restatement"
    severity: "critical"
    target: "§6"
    location: "provably, not just \"we don't know how\""
    description: "Implies NC^1 ≠ P which is an open problem"
    suggestions:
      - "Replace with 'assuming NC^1 ⊊ P (an open problem in complexity theory)'"

  - id: "S22"
    category: "restatement"
    severity: "major"
    target: "§8.2"
    location: "SMC-PGG's IT security is a genuine advantage"
    description: "BGW provides IT security for all of P with honest majority; NC^1 restriction is a limitation"
    suggestions:
      - "Acknowledge BGW and reframe advantage in terms of algebraic structure, not IT security"

  - id: "S26"
    category: "structural"
    severity: "major"
    target: "§8"
    location: "round complexity claims"
    description: "Ishai-Kushilevitz (2002) gives constant-round IT-secure NC^1 protocols, undercutting round advantages"
    suggestions:
      - "Add paragraph explicitly comparing with Ishai-Kushilevitz (2002)"

  - id: "W1"
    category: "structural"
    severity: "minor"
    target: "§1"
    location: "introduction"
    description: "No numbered contributions list or contribution taxonomy"
    suggestions:
      - "Add structured contributions paragraph (Established/Conjectured/Proposed)"

  - id: "W2"
    category: "structural"
    severity: "minor"
    target: "after §1"
    location: "related work"
    description: "No dedicated related work section"
    suggestions:
      - "Add Related Work section covering BGW, Ishai-Kushilevitz, EasyCrypt"

  - id: "S19"
    category: "remark-elimination"
    severity: "minor"
    target: "§6 table"
    location: "Ad hoc simulation arguments per protocol"
    description: "Rhetorically loaded; simulation-based proofs are systematic"
    suggestions:
      - "Replace with 'protocol-specific simulation proofs'"

  - id: "S24"
    category: "structural"
    severity: "minor"
    target: "§9"
    location: "algebraic automata theory as the foundation for secure computation"
    description: "Barrington (1989) already uses algebraic automata theory in MPC-relevant context"
    suggestions:
      - "Acknowledge lineage and scope novelty claim precisely"
```
