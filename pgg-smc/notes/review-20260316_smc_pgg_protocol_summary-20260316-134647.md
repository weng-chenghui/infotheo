# Paper Review: SMC-PGG Protocol Summary (Meeting Brief)

**Reviewed:** 2026-03-16
**File:** `pgg-smc/notes/20260316_smc_pgg_protocol_summary.md`

## 1. Domain Assessment

**Primary domains:** Secure Multi-Party Computation (MPC), Algebraic Topology (covering spaces, monodromy), Algebraic Geometry (AG codes, Riemann-Hurwitz), Formal Verification (Rocq/Coq + MathComp)

**Review personas:**
- Cryptographic protocol designer (MPC adversary models, threshold schemes, security bounds)
- Algebraic geometer (covering spaces, monodromy representations, AG codes)
- Formal verification specialist (Rocq/Coq, HB mixins, axiomatization strategy)

**Key technical terms:** monodromy representation, covering space, fiber structure, AlgebraicRigidity, ThresholdScheme, collusion bound, variational distance, RAAG (Right-Angled Artin Group), Foata normal form, Barrington-Therien classification, AG code, Riemann-Hurwitz formula

## 2. Reasoning Verification

### Summary
- **True claims:** 56
- **False claims:** 12
- **Suspicious claims:** 14
- **Opus overrides:** 4 (C4, C30, C58 escalated Suspicious→False; C82 downgraded Suspicious→True)

### False Claims

| ID | Claim | Issue |
|----|-------|-------|
| C4 | `word_eval w := σ_{w_0} · ... · σ_{w_{L-1}}` | Presented as if `w` contains group elements. Actually `w : L.-tuple 'I_Tg` (tuple of generator *indices*); formula should state lookup into `sigmas`. *(Opus override: was Suspicious)* |
| C16 | "Larger \|G\| → larger covering genus → worse threshold" | Direction not established. Riemann-Hurwitz: `g = (R + 2 - 2|G|)/2` for base genus 0 — genus *decreases* in \|G\| for fixed ramification. Code only proves contrapositive: genus-0 bounds \|G\| above. |
| C20 | "Complete (clique) graph → 1 round" | Overstates. For word `s_1 s_1` (repeated generators), Foata depth = 2 since `comm` is irreflexive. "1 round" only holds for words with all-distinct generator indices. |
| C26 | "For genus 0, \|G\| ≤ PGL(2,N)" | (a) This is **axiomatized** (`genus0_aut_pgl`), not proved; (b) N must be a prime-power field size; (c) it is one arm of a disjunction in the tradeoff theorem, not standalone. |
| C30 | "Four protocol properties determined simultaneously" | `AlgebraicRigidity` record bundles only `SecurityWitness` + `ThresholdWitness`. Round complexity is not a field or derived lemma of the record. Only three properties are formalized. *(Opus override: was Suspicious)* |
| C36 | `var_dist(adversary_view, uniform)` | The Coq identifier is `adversary_marginal`, not `adversary_view`. The term `adversary_view` does not exist in the codebase. |
| C41 | "Chooses word basis W -- a set of group elements" | Contradictory naming. `W : seq gT` is a sequence of group elements, not words. "Word basis" does not correspond to any Coq definition. |
| C46 | "3 remaining axioms" | Conflates framework-level (1: `genus0_aut_pgl`) with instance-level axioms (2 star + 5 monster). Total is 8 `Axiom` declarations. |
| C58 | "2-generated (Steinberg)" | Steinberg (1962) proved 2-generation for groups of Lie type only. The general result for all finite simple groups requires CFSG (Aschbacher-Guralnick et al.). *(Opus override: was Suspicious)* |
| C60 | "threshold gap ~ 10^53" | Conflates genus with gap. Gap ≤ 2 × genus (not = genus). The ~10^53 figure is the group order, not the genus or gap directly. |
| C73 | "Barrington-based: polynomial in branching program size" | Should be "linear in branching program length." "Polynomial" is imprecise. |
| C77 | "S_5 is the smallest non-solvable group" | A_5 (order 60) is the smallest non-solvable group. S_5 (order 120) is the smallest non-solvable *symmetric* group. |

### Suspicious Claims

| ID | Claim | Concern |
|----|-------|---------|
| C5 | Conflates M-level and PI-level operations | `endpoint`, `word_eval` are M-level; `start_sheet`, `share`, `compute` require `PGGInterface`. Not distinguished. |
| C7 | Adversary "sees" T-1 endpoints | Describes the conditional model (Section 5 of code) but the main `collusion_bound` theorem is unconditional on observed values. |
| C13 | "L-free (word_eval injective)" | Minor: `lfree L` is injectivity on `pgg_word L = L.-tuple 'I_Tg`, not on arbitrary words. |
| C22 | "Threshold gap = T - k" | Code stores `ts_T'` and `ts_k'` (predecessor-encoded). Definition is correct but off-by-one encoding worth noting. |
| C27 | "Large G → strong security" | `search_space ≤ |G|` is an *upper* bound. Large |G| means the bound is large, but actual search space could be much smaller. |
| C29 | "No further degrees of freedom" | `sw_L` (word length) and `sw_rho_dist` (sampling distribution) are free parameters in `SecurityWitness`. |
| C35 | AlgebraicRigidity as unified witness | It is a product of two independent sub-records, not a monolithic constraint. |
| C37 | "Fiber uniformity" computable via Cayley graph | Not formalized in Rocq. The security result is a collusion bound, not a fiber-uniformity theorem. |
| C38 | Grover mitigation "cost >= kappa^L" | Specific to free-group ball size, not the general adversary search space. |
| C39 | "Strictly weaker than simulation-based" | Not formally proved in the codebase. Informal claim. |
| C43 | "Recovers secret via AG code" | Framework is parametric over `ThresholdScheme`; AG code is one instance. |
| C63 | "ZAS correlations (Beimel et al. 2021)" | Year likely wrong. ZAS primitive is from Beimel-Ishai-Kushilevitz-Orlov 2012. |
| C65 | "Oblivious shuffling/matrix mult" | "Matrix multiplication" framing may be conflation with a different paper. |
| C75 | "42 Rocq files, 3 geometric axioms" | Actually 43 files. Axiom count understated (8 total across framework + instances). |

### True Claims

C1, C2, C3, C6, C8, C9, C10, C11, C12, C14, C15, C17, C18, C19, C21, C23, C24, C25, C28, C31, C32, C33, C34, C37 (bound itself), C40, C42, C44, C45, C47, C48, C49, C50, C51, C52, C53, C54, C55, C56, C57, C59, C61, C62, C64, C66, C67, C68, C69, C71, C72, C74, C76, C78, C79, C80, C81, C82, C83, C84, C85, C86, C87, C88, C90, C91, C92, C93, C94, C95, C96

## 3. Academic Writing Critique

1. **No problem statement.** The document opens with "What is SMC-PGG?" but never states the problem being solved (N parties wish to jointly compute a function without revealing inputs to coalitions). Add a one-sentence problem statement before any protocol description.

2. **Contribution framing delayed.** The honest summary ("SMC-PGG is not a better protocol on any operational axis... contribution is a mathematical framework") comes at the very end. Earlier sections (especially the comparison table) use language implying competitive advantage. Lead with the framework framing.

3. **`adversary_view` does not exist.** Line 116 uses `adversary_view` but the Coq identifier is `adversary_marginal`. Fix throughout.

4. **"Four properties" vs three in record.** Lines 97 and 101-108 claim four simultaneous properties, but `AlgebraicRigidity` formalizes only three (complexity, security, threshold). Round complexity is informal.

5. **"Word basis W" contradicts its type.** "Chooses word basis W -- a set of group elements" is self-contradictory. W is `seq gT` in the code. Rename to "generator sequence" or "group element list."

6. **Missing definitions at first use.** `Tg`, `NC^1`, `Foata normal form`, `L_g`, `s_target`, and HB mixins are all used before being defined (or never defined).

7. **Genus-monotonicity claim is wrong.** "Larger |G| → larger genus" is not a theorem. Genus depends jointly on |G|, ramification, and base genus. State the actual Riemann-Hurwitz dependency.

8. **PGL bound presented without context.** The genus-0 PGL constraint is axiomatized and is one arm of a disjunction, but presented as a simple standalone fact.

9. **Unconditional vs conditional bound conflated.** The main `collusion_bound` is unconditional on observed values; the conditional bound is a separate theorem (Section 5 of the code). The summary presents only the conditional interpretation.

10. **Missing citations.** Comparison table references "Ishai-Kushilevitz 2000," "Beimel et al. 2021," "Attrapadung et al. 2021" without venues. "ZAS 2021" year is likely wrong (2012).

11. **A_5, not S_5.** The smallest non-solvable group is A_5 (order 60), not S_5 (order 120).

12. **Steinberg attribution.** The 2-generation result for all finite simple groups is due to CFSG + Aschbacher-Guralnick, not Steinberg alone (who proved it for Lie type only).

13. **"No further degrees of freedom" overstated.** SecurityWitness has free parameters (word length L, sampling distribution rho_dist).

14. **Fiber uniformity not formalized.** Item 2 under "Security notions achieved" presents fiber uniformity as a result, but it is not a formal theorem in the codebase. The formalized security result is the collusion bound.

15. **Complete graph "1 round" oversimplified.** Needs qualification: only for words with all-distinct generator indices (comm is irreflexive).

16. **Section ordering.** "What the dealer prepares" appears after "Security notions achieved" but is logically prior. "How to embed a new group" is too implementation-detailed for a meeting brief.

17. **"Secret is hidden in fiber structure" imprecise.** The secret is a group element/sheet index. Security comes from ambiguity in which word produced the observed endpoint, not from the secret being "hidden."

18. **Axiom count understated.** "3 remaining axioms" only covers the star instance + 1 framework axiom. Monster instance adds 5 more. Total: 8.

## 4. Section Formality Distance

| Section | Rating (1-5) | Justification |
|---------|:---:|---------------|
| What is SMC-PGG? | 3 | No problem statement; "secret hidden in fiber" imprecise; missing party/adversary context |
| Protocol — What it computes | 2 | Clear and code-faithful; minor: Tg undefined, w presented as group elements |
| Protocol — Adversary model | 2-3 | Correct bound but uses wrong identifier (`adversary_view`); conflates unconditional/conditional |
| Protocol — Search space | 2 | Well-structured; all bounds match proved lemmas |
| Protocol — Round complexity | 3 | "Complete → 1 round" oversimplified; Foata depth undefined |
| Protocol — Threshold gap | 3 | Gap table clear; PGL constraint drops disjunction context; genus-monotonicity claim wrong |
| Protocol — Tradeoff | 2-3 | Core insight well-stated; overstates monotone relationship |
| What distinguishes from MPC? | 3 | Useful table but "four properties" doesn't match record; mixes proved/informal |
| Security notions achieved | 3-4 | Wrong identifier (C36); L_g undefined; fiber uniformity unformalized; Grover scope unclear |
| What the dealer prepares | 3 | "Word basis" naming contradicts type; placed after security (wrong order) |
| Axiom boundary status | 2 | Most precise section; grounded in commits; axiom count needs update |
| How to embed — Design principle | 2 | Well-structured; HB vocabulary needs gloss |
| How to embed — Main ladder | 2 | Levels 1-6 match source; code-faithful |
| How to embed — RAAG refinement | 2 | Accurate; graph topology table informative |
| Running examples — Star | 2 | Code blocks faithful; axiom count correct |
| Running examples — Monster | 2-3 | Axiom count correct; Steinberg attribution wrong; gap conflation |
| Comparison — Table | 3 | Missing citations; ZAS year suspect; S_5/A_5 error |
| Comparison — 5 differences | 2-3 | Difference 2 (Shamir = genus-0) strongest; Difference 4 overstates "exactly" |
| What PGG-SMC contributes | 3 | File count as metric; items 1-2 well-stated |
| What PGG-SMC does NOT contribute | 2 | Honest and precise; all four negatives code-consistent |
| Honest summary | 2 | Best paragraph; "understanding vs capability" exactly right |

*(1 = publication-ready, 5 = informal notes / far from formal)*

## 5. Constructive Suggestions

### Critical

- **[F-C36] `adversary_view` (notation)**: Replace all occurrences of `adversary_view` with `adversary_marginal` — the former does not exist in the codebase.
  - *Confidence*: definite

- **[F-C4] word_eval formula (restatement)**: Restate that `w` is a tuple of generator indices (`'I_Tg`), not group elements; the product is formed by index lookup into `sigmas`.
  - *Confidence*: definite

- **[F-C41] "word basis W" (restatement)**: Rename to "group element sequence W" and correct type description to `seq gT`.
  - *Options*: A) "generator sequence W" / B) "group element list W"
  - *Confidence*: definite

- **[F-C16] genus monotonicity (restatement)**: Remove "Larger |G| → larger genus." Replace with: genus depends jointly on |G|, ramification R, and base genus via Riemann-Hurwitz. The code proves only the contrapositive: genus-0 bounds |G| from above.
  - *Confidence*: definite

- **[F-C26] PGL bound context (restatement)**: Mark as axiomatized; note N must be a field size; present as one arm of a disjunction.
  - *Confidence*: definite

- **[F-C20] complete graph → 1 round (restatement)**: Qualify: depth ≥ 2 when word contains repeated generator indices, because comm is irreflexive.
  - *Confidence*: definite

- **[F-C77] S_5 → A_5 (restatement)**: A_5 (order 60) is smallest non-solvable group; S_5 (order 120) is smallest non-solvable symmetric group.
  - *Confidence*: definite

- **[F-C58] Steinberg attribution (restatement)**: Attribute Lie-type 2-generation to Steinberg; general result to CFSG (Aschbacher-Guralnick et al.).
  - *Confidence*: definite

- **[F-C46] axiom count (restatement)**: Replace "3 remaining axioms" with precise breakdown: 1 framework + 2 star + 5 monster = 8 total. Distinguish levels.
  - *Confidence*: definite

- **[F-C73] branching program complexity (restatement)**: Replace "polynomial in branching program size" with "linear in branching program length."
  - *Confidence*: definite

- **[F-C60] threshold gap conflation (restatement)**: Clarify gap ≤ 2 × genus (not = genus); ~10^53 is group order, not genus or gap directly.
  - *Confidence*: definite

- **[F-C75] file/axiom count (restatement)**: Correct to 43 files; update axiom count to 8.
  - *Confidence*: definite

### Major

- **[S-C30] "four properties" → three (restatement)**: Change to three, matching `AlgebraicRigidity` record, or annotate round complexity as informal.
  - *Options*: A) remove round complexity from list / B) annotate as "not in record"
  - *Confidence*: definite

- **[S-C29] "no further degrees of freedom" (restatement)**: Remove or qualify — `sw_L` and `sw_rho_dist` are free parameters.
  - *Confidence*: definite

- **[S-C37] fiber uniformity (restatement)**: Add caveat: not formalized in Rocq; security result is collusion bound.
  - *Confidence*: definite

- **[S-C7] unconditional vs conditional (restatement)**: Label bound as conditional on distribution assumption.
  - *Confidence*: definite

- **[W1] missing problem statement (structural)**: Add opening paragraph: N parties, coalition adversary, security goal.
  - *Confidence*: definite

- **[W21] NC^1 undefined (notation)**: Define at first use (polylog-depth, poly-size circuits).
  - *Confidence*: definite

- **[W22] Foata normal form undefined (notation)**: Define at first use with one-sentence gloss.
  - *Confidence*: definite

- **[W29] Tg undefined (notation)**: Define before first formula use.
  - *Confidence*: definite

- **[W13] "exactly how many rounds" (restatement)**: Replace with "upper bound on round complexity under the RAAG independence model."
  - *Confidence*: definite

- **[W18] "information-theoretic" qualifier (restatement)**: Qualify with distribution assumption.
  - *Confidence*: definite

### Minor

- **[W28] |G| vs #|G| (notation)**: Standardize throughout.
  - *Confidence*: definite

- **[W15] L_g undefined (notation)**: Define at first use.
  - *Confidence*: definite

- **[W4] missing citations (structural)**: Add author-venue-year for comparison table references.
  - *Confidence*: definite

- **[S-C63] ZAS year (structural)**: Verify and correct (likely 2012, not 2021).
  - *Confidence*: possible

- **[W25] section ordering (structural)**: Move "What the dealer prepares" before "Security notions achieved."
  - *Confidence*: definite

- **[S-C13] lfree precision (restatement)**: Clarify injectivity is on tuples of generator indices.
  - *Confidence*: definite

- **[S-C43] "via AG code" (restatement)**: Restate as parametric; AG code is one instance.
  - *Confidence*: possible

- **[S-C27] large G → strong security (restatement)**: "increases upper bound" not "guarantees strong security."
  - *Confidence*: definite

- **[W30] rho re-introduction (notation)**: Re-introduce with type in later sections.
  - *Confidence*: definite

- **[S-C39] "strictly weaker" (restatement)**: Add caveat: not formally proved.
  - *Confidence*: definite

## 6. Summary Verdict

The document is a solid meeting brief with accurate core technical content (search space bounds, collusion bound, threshold scheme, AlgebraicRigidity structure). However, it contains **12 false claims** — most are imprecisions rather than fundamental errors, but several are mathematically wrong (genus-monotonicity in |G|, A_5 vs S_5, Steinberg attribution, PGL bound context). The most critical protocol-level issue is the conflation of "larger group → larger genus" (C16), which inverts the actual Riemann-Hurwitz dependency and misrepresents the security/threshold tradeoff direction. The document also uses the undefined identifier `adversary_view` where the code has `adversary_marginal`, and claims "four properties" where only three are formalized. After fixing the 12 false claims, 4-5 major suspicious claims (fiber uniformity proof status, degrees-of-freedom overstatement, unconditional/conditional bound conflation), and adding missing definitions (NC^1, Tg, Foata, L_g), this would be a reliable internal reference document.

## 7. Fix Manifest

```yaml
fixes:
  - id: "F-C36"
    category: "notation"
    severity: "critical"
    target: "adversary_view"
    location: "var_dist(adversary_view, uniform)"
    description: "adversary_view does not exist in codebase; should be adversary_marginal"
    suggestions:
      - "Replace all occurrences of adversary_view with adversary_marginal"

  - id: "F-C4"
    category: "restatement"
    severity: "critical"
    target: "word_eval formula"
    location: "word_eval w := σ_{w_0}"
    description: "w is presented as containing group elements; actually contains generator indices"
    suggestions:
      - "Restate: w is a tuple of generator indices; word_eval looks up each index in sigmas"

  - id: "F-C41"
    category: "restatement"
    severity: "critical"
    target: "word basis W"
    location: "Chooses word basis W -- a set of group elements"
    description: "Contradictory naming: calls it word basis but W : seq gT (group elements)"
    suggestions:
      - "Rename to 'group element sequence W'"
      - "Rename to 'generator list W'"

  - id: "F-C16"
    category: "restatement"
    severity: "critical"
    target: "genus monotonicity"
    location: "larger |G| also means larger covering genus"
    description: "Direction not established; genus depends on ramification, not |G| alone"
    suggestions:
      - "Replace with: genus depends jointly on |G|, ramification R, and base genus"
      - "State only the contrapositive: genus-0 bounds |G| from above"

  - id: "F-C26"
    category: "restatement"
    severity: "critical"
    target: "PGL bound"
    location: "|G| ≤ PGL(2,N)"
    description: "Drops axiom status, field constraint, and disjunction context"
    suggestions:
      - "Mark as axiomatized; note N must be field size; present as one arm of disjunction"

  - id: "F-C20"
    category: "restatement"
    severity: "critical"
    target: "complete graph 1 round"
    location: "Complete (clique) | 1 (fully parallel)"
    description: "Overstates: repeated generators have Foata depth > 1 (comm is irreflexive)"
    suggestions:
      - "Qualify: 1 round only for words with all-distinct generator indices"

  - id: "F-C77"
    category: "restatement"
    severity: "critical"
    target: "S_5 smallest non-solvable"
    location: "Fixed S_5"
    description: "A_5 (order 60) is the smallest non-solvable group, not S_5 (order 120)"
    suggestions:
      - "Correct to A_5, or clarify S_5 is smallest non-solvable symmetric group"

  - id: "F-C58"
    category: "restatement"
    severity: "critical"
    target: "2-generated (Steinberg)"
    location: "2 generators, by Steinberg"
    description: "Steinberg proved 2-generation for Lie type only; general result is CFSG"
    suggestions:
      - "Attribute to CFSG (Aschbacher-Guralnick et al.) for all finite simple groups"

  - id: "F-C46"
    category: "restatement"
    severity: "critical"
    target: "3 remaining axioms"
    location: "3 remaining axioms (all geometric existence statements)"
    description: "Conflates framework and instance axioms; total is 8"
    suggestions:
      - "Break down: 1 framework + 2 star + 5 monster = 8 total Axiom declarations"

  - id: "F-C73"
    category: "restatement"
    severity: "critical"
    target: "polynomial in branching program size"
    location: "Polynomial in branching program size"
    description: "Should be linear in branching program length"
    suggestions:
      - "Replace with: linear in branching program length"

  - id: "F-C75"
    category: "restatement"
    severity: "critical"
    target: "42 Rocq files, 3 axioms"
    location: "42 Rocq files, 3 geometric axioms"
    description: "Actually 43 files; axiom count is 8, not 3"
    suggestions:
      - "Correct to 43 files and 8 axiom declarations"

  - id: "F-C60"
    category: "restatement"
    severity: "critical"
    target: "threshold gap ~ 10^53"
    location: "Threshold: catastrophic (genus ~ 10^53, so gap ~ 10^53)"
    description: "Gap ≤ 2*genus, not = genus; ~10^53 is group order not genus"
    suggestions:
      - "State gap ≤ 2*genus; genus is bounded by group-theoretic data, not equal to |G|"

  - id: "S-C30"
    category: "restatement"
    severity: "major"
    target: "four protocol properties"
    location: "determines four protocol properties simultaneously"
    description: "AlgebraicRigidity record has only three; round complexity not formalized"
    suggestions:
      - "Change to three properties"
      - "Annotate round complexity as informal, not in the record"

  - id: "S-C29"
    category: "restatement"
    severity: "major"
    target: "no further degrees of freedom"
    location: "No further degrees of freedom exist"
    description: "sw_L and sw_rho_dist are free parameters in SecurityWitness"
    suggestions:
      - "Remove or qualify: word length and sampling distribution remain free"

  - id: "S-C37"
    category: "restatement"
    severity: "major"
    target: "fiber uniformity"
    location: "Fiber uniformity: Under uniform word distribution"
    description: "Not formalized in Rocq; security result is collusion bound"
    suggestions:
      - "Add caveat: informal motivation, not a formal theorem"

  - id: "S-C7"
    category: "restatement"
    severity: "major"
    target: "unconditional bound"
    location: "Information-theoretic -- no computational assumptions"
    description: "Conflates unconditional marginal bound with conditional interpretation"
    suggestions:
      - "Label as conditional on the word sampling distribution"

  - id: "W1"
    category: "structural"
    severity: "major"
    target: "opening"
    location: "# SMC-PGG Protocol Summary"
    description: "No problem statement defining parties, adversary, or security goal"
    suggestions:
      - "Add one-paragraph problem statement before protocol description"

  - id: "W21"
    category: "notation"
    severity: "major"
    target: "NC^1"
    location: "Group variety (Barrington-Therien) -> NC^1"
    description: "NC^1 used without definition"
    suggestions:
      - "Define at first use: polylog-depth, poly-size Boolean circuits"

  - id: "W22"
    category: "notation"
    severity: "major"
    target: "Foata normal form"
    location: "Foata normal form depth"
    description: "Foata normal form used without definition"
    suggestions:
      - "Define at first use with one-sentence gloss"

  - id: "W29"
    category: "notation"
    severity: "major"
    target: "Tg"
    location: "search_space(L) ≤ Tg^L"
    description: "Tg (generator count) used before definition"
    suggestions:
      - "Define Tg at first use: number of generators"

  - id: "W13"
    category: "restatement"
    severity: "major"
    target: "exactly how many rounds"
    location: "tells you exactly how many rounds"
    description: "Foata depth is an upper bound, not exact round count"
    suggestions:
      - "Replace 'exactly' with 'an upper bound on'"

  - id: "W18"
    category: "restatement"
    severity: "major"
    target: "information-theoretic qualifier"
    location: "Information-theoretic -- no computational assumptions"
    description: "Bound holds given specific word sampling; not unconditional"
    suggestions:
      - "Qualify with distribution assumption"
```
