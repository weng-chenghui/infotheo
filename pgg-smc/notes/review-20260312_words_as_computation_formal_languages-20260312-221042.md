# Paper Review: Words as Computation: Formal Language Theory and SMC-PGG

**Reviewed:** 2026-03-12
**File:** `pgg-smc/notes/20260312_words_as_computation_formal_languages.md`

---

## 1. Domain Assessment

**Primary research domains:**
- Formal Language Theory (varieties of languages, decision problems, Eilenberg correspondence)
- Algebraic Automata Theory (Krohn-Rhodes decomposition, permutation automata, transformation monoids)
- Cryptographic Secure Multi-Party Computation (SMC protocol design, privacy/security)
- Trace Monoid Theory / Concurrency Theory

**Reviewer persona:**
Senior algebraic automata theorist specializing in Eilenberg variety theory, trace monoids, and Krohn-Rhodes decomposition, with expertise in cryptographic protocol formalization.

**Key technical terms:**
1. Mazurkiewicz trace monoid
2. Syntactic monoid / group language
3. Eilenberg variety theorem
4. Piecewise testable / star-free languages
5. V-separability
6. Krohn-Rhodes decomposition
7. Permutation automaton
8. Monodromy group / covering space
9. Straubing-Thérien (dot-depth) hierarchy
10. FO-definable trace languages (Diekert-Gastin)

---

## 2. Reasoning Verification

### Summary
- **True claims:** 9
- **False claims:** 7
- **Suspicious claims:** 17
- **Opus overrides:** 5

### False Claims

| ID | Section | Claim | Explanation |
|----|---------|-------|-------------|
| F1 | §6.1 | `n_traces(L) = clique_polynomial(Γ, L)` gives polynomial-time trace counting | The clique polynomial encodes the growth series of the *full* trace monoid M(Σ,I), not of an arbitrary sublanguage L_g. Counting traces in a specific fiber requires transfer-matrix methods with exponential state space. |
| F3 | §7.3 | FO-definability is preserved under morphisms | False as stated. Preserved under *inverse* morphisms and *non-erasing* morphisms, but NOT under arbitrary (erasing) forward morphisms. |
| F4 | §7b | Aperiodic components need only reset/**counter** operations | "Counter operations" directly contradicts "counter-free." Aperiodic = syntactic monoid has no non-trivial groups = no counting ability. |
| F5 | §7b | Level 0 = Boolean combinations of A\*aA\* | Boolean combinations of A\*aA\* characterize level 1/2 (or level 1). Level 0 = {∅, Σ\*} (trivial languages only). |
| S1→F | §2 | Membership of group languages "Decidable (Eilenberg)" | *(Opus override: was Suspicious)* Eilenberg's variety theorem is structural, not algorithmic. Decidability follows from computing the syntactic monoid and checking the group condition — an elementary observation, not Eilenberg's theorem. |
| S8→F | §7 | Sub-alphabet projection preserves FO-definability | *(Opus override: was Suspicious)* Projection (letter-erasing morphism) does NOT preserve FO-definability in general. The *inverse* direction (preimage) does. |
| S18→F | §7b | Dot-depth = protocol round complexity | *(Opus override: was Suspicious)* No meaningful correspondence exists. Dot-depth measures language-theoretic structural complexity; MPC round complexity depends on protocol design and computational model. A high dot-depth language could be recognized in constant rounds with the right group structure. |

### Suspicious Claims

| ID | Section | Claim | Concerns |
|----|---------|-------|----------|
| S2 | §2 | Czerwiński+ '19 for PT-separability | Date approximately correct but imprecise; main result appeared at LICS 2017 / journal ~2019. |
| S3 | §2 | Measurability row in decidability table | "V-measurability" is undefined — conflates topological (clopen/Borel) and measure-theoretic (Haar) notions. All three entries unverifiable as stated. |
| S4 | §3/§4 | Recognizable subsets of M ←→ Fiber languages L_g | Requires the unstated hypothesis I ⊆ ker(eval): independent generators must commute in G. Without this, trace-equivalent words could map to different group elements. Critical gap. |
| S5 | §4 | Diekert-Gastin theorem applies to our fiber languages | Conditional on S4. The theorem requires L_g to be a trace language (closed under ~_I), which holds only if the independence relation is respected by eval. |
| S6 | §4 | Eilenberg variety theory on fibers | Argument compressed; notation collision between **G** (variety of group languages) and G (specific group). The underlying claim is correct per Opus audit. *(Opus override: was more severe from one Sonnet reviewer — F2 overturned to True; the syntactic monoid of L_g = φ⁻¹(g) is indeed a group dividing G, since divisors of groups are groups.)* |
| S7 | §4 | Separability as privacy | The language-theoretic separability model (deterministic word classification) and cryptographic adversary model (probabilistic, adaptive, computational bounds) are fundamentally different frameworks. No formal reduction connects them. |
| S9 | §5 | Transformation monoid = Monodromy group G | Assumes the protocol generators span G. This is a design assumption, not a theorem — must be stated explicitly. |
| S10 | §5 | L_{s→t} is a group language — "theorem (Eilenberg)" | Correct result, wrong attribution. This is an elementary observation about permutation automata, not Eilenberg's variety theorem. |
| S11 | §5 | "Protocol recognizes a group language" | Justified operationally ("read off acceptance from endpoint") rather than algebraically (syntactic monoid is a group). The operational justification is not the reason it's a group language. |
| S13 | §6 | L-freeness "doesn't seem to have been studied" | Likely false — closely related to cogrowth series (Grigorchuk 1980), small cancellation theory, and Dehn functions in geometric group theory. |
| S14 | §6 | "Protocol IS a distributed group language recognizer" | Strong identification claim without formal reduction specifying input alphabet, acceptance condition, and characteristic function computation. |
| S15 | §7b | SMC-PGG recognizes group languages | Conflates computing a group element g = φ(w) with recognizing a specific language L_g = φ⁻¹(g). Minor but worth clarifying. |
| S16 | §7b | SMC-PGG handles K-R group layers natively | K-R decomposes into *simple* group components. Monodromy group may not be simple; needs simplicity/primitivity argument. |
| S17 | §7b | Cascading gives secure recognition of all regular languages | Requires: (1) secure protocols per layer, (2) secure composition preserving privacy, (3) wreath product wiring between layers. Each is non-trivial. |
| S19 | §7b | Universal cover of wedge of circles = pushdown structure | Analogy between tree-structured universal cover and pushdown stack is suggestive but vague. No concrete construction. |
| S20–S22 | §8 | Various summary table ratings | "Tier 1–2" for variety→security is optimistic; adversary class V has no construction; "no natural structure" for CFL contradicts §7b discussion. |

### True Claims (confirmed)

T1: Trace monoid = FLT object (Mazurkiewicz); T2: RAAG word problem linear-time; T3: Each party is a permutation automaton; T4: Straubing-Thérien hierarchy union = star-free = aperiodic = FO[<]-definable; T5: Fiber cardinality via Cartier-Foata (full monoid); T6: CFL irrelevance assessment (Tier 3 self-assessment correct); T7: "Choosing ≠ computing" self-critique correct; T8: Variety hierarchy chain correct; T9: Cartier-Foata as bijective decomposition for trace enumeration (S12 overturned by Opus).

---

## 3. Academic Writing Critique

1. **No contribution statement.** §1 describes what the note "maps out" but never states what it contributes. Missing: "We establish X, conjecture Y, and show Z is vacuous." Add a two-sentence contribution statement distinguishing formal results from research agenda.

2. **Related work is name-dropping, not comparison.** References to Eilenberg, Schützenberger, Simon are invoked as authority without citing prior work connecting FLT to cryptographic MPC (e.g., Barrington's theorem, secure automata evaluation). No statement of novelty.

3. **Multiple false technical claims.** Seven claims are incorrect (see §2 above): the clique polynomial formula, FO-definability under morphisms (stated twice), "counter operations," Straubing-Thérien level 0, Eilenberg misattribution, and dot-depth = round complexity.

4. **Critical unstated hypothesis.** The independence-evaluation compatibility condition (I ⊆ ker(eval)) is silently assumed throughout §3–§5. Without it, the entire trace-monoid/fiber-language correspondence breaks down.

5. **Notation collisions.** L = language vs L = word length throughout. **G** = variety of group languages vs G = specific group in §4. Both must be disambiguated.

6. **Self-containedness.** Relies on `pgg_raag.v` Coq definitions (`trace_equiv`, `n_traces`, `search_space`, `trace_equiv_dec`) without standalone mathematical definitions. A reader without the codebase cannot verify Tier 1 claims.

7. **"§7b" is non-standard section numbering.** Signals the section was an afterthought. Should be renumbered.

8. **Diagram arrow inconsistency.** The "Variety classification ←→ Security parameters" arrow in §3 is drawn as genuine (solid) but no theorem establishes this connection anywhere in the note.

9. **Japanese section title.** "形式言語の４つの決定問題" appears untranslated in an English document. Should be translated or footnoted.

10. **Summary table conflates tier systems.** "Tier 1–2" as a direction maturity rating conflates per-claim confidence tiers (defined in §4) with research-direction readiness. Use a separate scale.

11. **References incomplete.** Pin (2022) is unpublished lecture notes (unlabeled); Diekert-Gastin (2006) missing editors (Flum, Grädel, Wilke); Czerwiński+ year uncertain.

12. **"FLT gains an application" (§6) is circular.** Claims variety-theoretic properties determine distinguishing hardness, but this presupposes the separability-as-privacy correspondence listed as Tier 2 / unproven.

---

## 4. Section Formality Distance

| Section | Rating (1–5) | Justification |
|---------|:---:|---------------|
| §1 Introduction | 4 | No contribution statement; informal tier taxonomy without mathematical setup |
| §2 Four Decision Problems | 2 | Precise table of decidability results; formal problem definitions; minor Eilenberg misattribution |
| §3 Correspondence Diagram | 4 | Effective structure but not a formal mapping; mixes genuine/speculative arrows; legend misplaced |
| §4 Rigorous Assessment | 3 | Tier 1 items stated as theorems without proofs or precise citations; Tier 2–3 items honest but qualitative |
| §5 Party Computation | 2 | Well-structured table; automaton-transducer identification precise; minor attribution issues |
| §6 Direction 1 (SMC-PGG → FLT) | 4 | Aspirational prose; false clique polynomial claim; undefined "L-freeness"; no concrete results |
| §7 Direction 2 (FLT → SMC-PGG) | 3 | Three subsections with explicit status labels; false FO-morphism claim; otherwise reasonably structured |
| §7b Direction 2 Extended | 4 | K-R subsection promising but dot-depth/CFL subsections speculative; "counter operations" error |
| §8 Summary | 3 | Useful table but inconsistent tier scale and unsupported "High" ratings |
| §9 References | 3 | 11 entries covering relevant literature; missing editors, inconsistent formatting, one unpublished source |

*(1 = publication-ready, 5 = informal notes / far from formal)*

---

## 5. Constructive Suggestions

### Critical

- **[F1] §6.1 trace counting (restatement)**: Replace the clique-polynomial trace counting claim with a correct statement that the clique polynomial encodes the full trace monoid growth series, not trace counts in an arbitrary sublanguage L_g. *Options*: (A) Restrict to trace monoid growth rate, cite Krob-Mairesse-Michos; (B) Delete complexity claim, retain combinatorial identity. *Confidence*: definite

- **[F3] §7.3 FO-definability (proof-repair)**: Restrict the FO-definability morphism-closure claim to inverse morphisms and non-erasing morphisms; add a counterexample footnote for the erasing case. *Options*: (A) Replace with "preserved under inverse morphisms" (Straubing, Thérien); (B) Delete the closure claim and note inverse-morphism direction is operative. *Confidence*: definite

- **[F4] §7b aperiodic characterization (restatement)**: Delete "counter operations" (contradicts counter-free); replace with "aperiodic components correspond to counter-free automata, characterized by absence of non-trivial groups in the syntactic monoid." *Confidence*: definite

- **[F5] §7b Straubing-Thérien levels (proof-repair)**: Correct Level 0 definition to {∅, Σ\*}; reassign Boolean combinations of A\*aA\* to Level 1/2 or Level 1; audit all dot-depth level assignments in §7b. *Confidence*: definite

- **[S1→F] §2 Eilenberg misattribution (hypothesis-insertion)**: Remove Eilenberg citation from decidability claim; attribute to Pin or present as folklore with proof sketch ("compute syntactic monoid; check group condition"). *Options*: (A) Retain Eilenberg only for variety correspondence; (B) Add proof sketch, cite as folklore. *Confidence*: definite

- **[S8→F] §7 projection preserves FO (proof-repair)**: Remove or qualify the sub-alphabet projection claim; add non-erasing hypothesis, or replace with correct closure under inverse morphisms. *Confidence*: definite

- **[S18→F] §7b dot-depth = rounds (remark-elimination)**: Delete the equation "dot-depth = protocol round complexity"; replace with explicitly labeled open question or move to speculative directions with disclaimer. *Confidence*: definite

### Major

- **[S4] §3–4 unstated hypothesis (hypothesis-insertion)**: Insert the explicit hypothesis I ⊆ ker(eval) — that independent generators commute in G — as a stated assumption before invoking fiber-language/trace-language equivalence. *Confidence*: definite

- **[S5] §4 Diekert-Gastin conditional (hypothesis-insertion)**: Add a sentence confirming I ⊆ ker(eval) holds in the protocol context before invoking the theorem. *Confidence*: definite

- **[S7] §4 separability ≠ privacy (restatement)**: Add a paragraph distinguishing language-theoretic separability (deterministic word classification) from cryptographic adversary model (probabilistic, adaptive), and state which reduction connects them or label as informal analogy. *Confidence*: definite

- **[S9] §5 generators span G (hypothesis-insertion)**: Add the explicit assumption that protocol generators span G as a subgroup of Sym(Q). *Confidence*: definite

- **[S10] §5 "theorem (Eilenberg)" (restatement)**: Relabel as "Proposition" or "Observation"; replace Eilenberg attribution with Pin or Sakarovitch. *Confidence*: definite

- **[S14] §6 distributed recognizer (hypothesis-insertion)**: Provide a formal reduction showing protocol implements the characteristic function of the group language, or demote to informal analogy. *Confidence*: definite

- **[S16] §7b K-R simplicity (hypothesis-insertion)**: Add the simplicity/primitivity argument for K-R group layers, or restrict to "related to" rather than "equal to." *Confidence*: definite

- **[S17] §7b cascade composability (hypothesis-insertion)**: Add the composability condition for secure cascade; cite Krohn-Rhodes (1965) and identify protocol-specific conditions. *Confidence*: definite

- **[W8] §3 diagram arrow (structural)**: Downgrade "Variety classification ←→ Security parameters" from solid to dashed arrow; add caption "Conjectured; no theorem established." *Confidence*: definite

- **[W1] §1 contribution statement (structural)**: Add contributions paragraph distinguishing formal results from research agenda. *Confidence*: definite

- **[S6] §4 notation collision (notation)**: Use bold **G** for variety, italic *G* for specific group; add notation table. *Confidence*: definite

- **[W2] §3–7 L collision (notation)**: Reserve L for languages; use ℓ or |w| for word length throughout. *Confidence*: definite

### Minor

- **[S2] §2 Czerwiński citation (restatement)**: Verify and complete with full author list, venue (LICS 2017), and journal year. *Confidence*: possible
- **[S3] §2 measurability definition (restatement)**: Split into topological vs measure-theoretic rows, or add qualifying note. *Confidence*: definite
- **[S11] §5 operational justification (hypothesis-insertion)**: Add algebraic justification (syntactic monoid is a group) alongside operational argument. *Confidence*: possible
- **[S13] §6 L-freeness novelty (restatement)**: Replace "hasn't been studied" with "to our knowledge, not studied in the protocol context"; cite cogrowth/small cancellation. *Confidence*: definite
- **[S15] §7b computation vs recognition (restatement)**: Add sentence distinguishing computing φ(w) ∈ G from recognizing L_g ⊆ Σ\*. *Confidence*: definite
- **[S19] §7b universal cover (restatement)**: Formalize or relabel as heuristic. *Confidence*: possible
- **[S20] §8 tier rating (restatement)**: Downgrade variety→security to Tier 3, or restrict Tier 1–2 to FLT component only. *Confidence*: possible
- **[S21] §8 adversary class V (hypothesis-insertion)**: Define V explicitly or move to open problems. *Confidence*: definite
- **[S22] §8 CFL inconsistency (structural)**: Reconcile "no natural structure" with §7b universal cover discussion. *Confidence*: definite
- **[W3] §7b numbering (structural)**: Renumber to §7.2 or §8. *Confidence*: definite
- **[W4] §3 legend placement (structural)**: Move arrow legend above diagram. *Confidence*: definite
- **[W5] Self-containedness (structural)**: Add standalone math definitions for Coq-imported concepts. *Confidence*: definite
- **[W6] Japanese title (structural)**: Translate or footnote. *Confidence*: definite
- **[W7] References (structural)**: Audit for missing editors, venues, years; label unpublished sources. *Confidence*: definite
- **[W9] Summary table scale (structural)**: Use separate scale for direction maturity vs per-claim tiers. *Confidence*: definite
- **[W10] §6 "FLT gains an application" (remark-elimination)**: Replace with specific statement of what the connection enables. *Confidence*: definite

---

## 6. Summary Verdict

The note's **core observation is genuine and valuable**: monodromy words in SMC-PGG are objects of formal language theory, fiber languages L_g are group languages in the Eilenberg variety sense, and the trace monoid framework (Mazurkiewicz/Cartier-Foata) applies directly. However, the note contains **7 false claims** — most seriously the clique polynomial formula for sublanguages, the unqualified FO-definability-under-morphisms assertion (stated twice), and the "counter operations" / Straubing-Thérien level errors — and **17 suspicious claims** stemming primarily from a critical unstated hypothesis (I ⊆ ker(eval)) and imprecise mappings between language-theoretic and cryptographic adversary models.

The note is well-organized as internal research notes (formality distance ~3.2/5) but requires substantial correction before any external presentation: fix the false claims, state the independence-evaluation compatibility hypothesis, disambiguate notation, and add a contribution statement distinguishing theorems from conjectures. The genuine kernel — fiber languages as group languages, separability as a conceptual model for privacy, and the Krohn-Rhodes cascade direction — can support a 4–6 page workshop note after these corrections.

---

## 7. Fix Manifest

```yaml
fixes:
  - id: "F1"
    category: "restatement"
    severity: "critical"
    target: "§6.1 clique polynomial claim"
    location: "n_traces(L) = clique_polynomial"
    description: "Clique polynomial formula applies to full trace monoid, not arbitrary sublanguages"
    suggestions:
      - "Restrict claim to trace monoid growth rate; cite Krob-Mairesse-Michos"
      - "Delete complexity claim; retain combinatorial identity only"

  - id: "F3"
    category: "proof-repair"
    severity: "critical"
    target: "§7.3 FO-definability under morphisms"
    location: "FO-definability is preserved under morphisms"
    description: "FO-definability not preserved under arbitrary morphisms; only inverse/non-erasing"
    suggestions:
      - "Replace with 'preserved under inverse morphisms' (Straubing, Thérien)"
      - "Delete closure claim; note inverse-morphism direction is operative"

  - id: "F4"
    category: "restatement"
    severity: "critical"
    target: "§7b aperiodic characterization"
    location: "reset/counter operations"
    description: "'Counter operations' contradicts 'counter-free'; aperiodic = no non-trivial groups"
    suggestions:
      - "Replace with 'counter-free automata with no non-trivial groups in syntactic monoid'"

  - id: "F5"
    category: "proof-repair"
    severity: "critical"
    target: "§7b Straubing-Thérien level 0"
    location: "Level 0 (Boolean combinations of A*aA*)"
    description: "Boolean combinations of A*aA* are level 1/2, not level 0; level 0 = {∅, Σ*}"
    suggestions:
      - "Correct level assignment to 1/2 or 1"

  - id: "S1F"
    category: "hypothesis-insertion"
    severity: "critical"
    target: "§2 Eilenberg decidability attribution"
    location: "Decidable (Eilenberg)"
    description: "Eilenberg's theorem is structural, not algorithmic; decidability is elementary"
    suggestions:
      - "Retain Eilenberg only for variety correspondence; attribute decidability to folklore/Pin"
      - "Add proof sketch and cite as folklore"

  - id: "S8F"
    category: "proof-repair"
    severity: "critical"
    target: "§7 sub-alphabet projection preserves FO"
    location: "FO-definability is preserved under morphisms"
    description: "Projection does not preserve FO-definability; inverse morphisms do"
    suggestions:
      - "Replace with correct closure under inverse morphisms"

  - id: "S18F"
    category: "remark-elimination"
    severity: "critical"
    target: "§7b dot-depth = round complexity"
    location: "protocol complexity = dot-depth"
    description: "No meaningful correspondence between dot-depth and MPC round complexity"
    suggestions:
      - "Move to speculative directions with explicit disclaimer"
      - "Delete entirely"

  - id: "S4"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§3-4 independence-evaluation compatibility"
    location: "Trace monoid M(Σ,I)"
    description: "Requires unstated hypothesis I ⊆ ker(eval)"
    suggestions:
      - "Insert explicit hypothesis before fiber-language/trace-language equivalence"

  - id: "S5"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§4 Diekert-Gastin applicability"
    location: "Diekert-Gastin theorem applies"
    description: "Conditional on I ⊆ ker(eval); must confirm in protocol context"
    suggestions:
      - "Add sentence confirming hypothesis holds in SMC-PGG"

  - id: "S7"
    category: "restatement"
    severity: "major"
    target: "§4 separability-as-privacy"
    location: "V-inseparability means privacy"
    description: "Language separability ≠ cryptographic adversary model"
    suggestions:
      - "Add paragraph distinguishing the two models; label connection as informal analogy"

  - id: "S9"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§5 transformation monoid"
    location: "Transformation monoid | Monodromy group G"
    description: "Assumes generators span G; must be stated"
    suggestions:
      - "Add explicit assumption that protocol generators span G"

  - id: "S10"
    category: "restatement"
    severity: "major"
    target: "§5 Eilenberg attribution"
    location: "This is a theorem (Eilenberg)"
    description: "Elementary fact about permutation automata, not Eilenberg's theorem"
    suggestions:
      - "Relabel as Proposition; cite Pin or Sakarovitch"

  - id: "S14"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§6 distributed recognizer claim"
    location: "protocol IS a distributed group language recognizer"
    description: "Needs formal reduction or demotion to informal analogy"
    suggestions:
      - "Provide formal reduction or demote to interpretation"

  - id: "S16"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§7b K-R group layers"
    location: "SMC-PGG handles the group layers natively"
    description: "K-R uses simple groups; monodromy group may not be simple"
    suggestions:
      - "Add simplicity argument or restrict to 'related to'"

  - id: "S17"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§7b cascade composability"
    location: "secure recognition of ALL regular languages"
    description: "Wreath product protocol design is non-trivial"
    suggestions:
      - "Add composability condition; identify protocol-specific requirements"

  - id: "W8"
    category: "structural"
    severity: "major"
    target: "§3 diagram arrow"
    location: "Variety classification"
    description: "Solid arrow for unproven correspondence"
    suggestions:
      - "Downgrade to dashed arrow with caption"

  - id: "W1"
    category: "structural"
    severity: "major"
    target: "§1 contribution statement"
    location: "Introduction"
    description: "No contribution statement"
    suggestions:
      - "Add contributions paragraph distinguishing formal results from agenda"

  - id: "S6"
    category: "notation"
    severity: "major"
    target: "§4 variety vs group notation"
    location: "variety of group languages **G**"
    description: "Notation collision: G = variety vs G = specific group"
    suggestions:
      - "Use bold G for variety, italic G for specific group; add notation table"

  - id: "W2"
    category: "notation"
    severity: "major"
    target: "§3-7 L collision"
    location: "L used for both language and length"
    description: "L = language and L = word length throughout"
    suggestions:
      - "Reserve L for languages; use ℓ or |w| for length"

  - id: "S2"
    category: "restatement"
    severity: "minor"
    target: "§2 Czerwiński citation"
    location: "Czerwiński+ '19"
    description: "Date approximate; attribution incomplete"
    suggestions:
      - "Verify; complete with full author list and venue (LICS 2017)"

  - id: "S3"
    category: "restatement"
    severity: "minor"
    target: "§2 measurability definition"
    location: "Measurability row"
    description: "Conflates topological and measure-theoretic notions"
    suggestions:
      - "Split into two rows or add qualifying note"

  - id: "S13"
    category: "restatement"
    severity: "minor"
    target: "§6 L-freeness novelty"
    location: "doesn't seem to have been studied"
    description: "Related to cogrowth, small cancellation, Dehn functions"
    suggestions:
      - "Qualify with 'to our knowledge, in the protocol context'"

  - id: "S15"
    category: "restatement"
    severity: "minor"
    target: "§7b computation vs recognition"
    location: "implicitly recognizes group languages"
    description: "Conflates computing φ(w) with recognizing L_g"
    suggestions:
      - "Add clarifying sentence"

  - id: "W3"
    category: "structural"
    severity: "minor"
    target: "§7b section numbering"
    location: "## 7b"
    description: "Non-standard section label"
    suggestions:
      - "Renumber to §7.2 or §8"

  - id: "W4"
    category: "structural"
    severity: "minor"
    target: "§3 arrow legend"
    location: "Arrow legend"
    description: "Legend placed below diagram; reader confusion"
    suggestions:
      - "Move above diagram"

  - id: "W5"
    category: "structural"
    severity: "minor"
    target: "General self-containedness"
    location: "trace_equiv, n_traces, search_space references"
    description: "Relies on Coq definitions without standalone math defs"
    suggestions:
      - "Add mathematical definition box for key concepts"

  - id: "W6"
    category: "structural"
    severity: "minor"
    target: "§2 Japanese title"
    location: "形式言語の４つの決定問題"
    description: "Untranslated Japanese in English document"
    suggestions:
      - "Translate or footnote"

  - id: "W7"
    category: "structural"
    severity: "minor"
    target: "§9 references"
    location: "References section"
    description: "Missing editors, inconsistent formatting, unpublished source unlabeled"
    suggestions:
      - "Audit all entries; label unpublished sources"

  - id: "W9"
    category: "structural"
    severity: "minor"
    target: "§8 summary table"
    location: "Tier 1–2"
    description: "Conflates per-claim tiers with direction maturity"
    suggestions:
      - "Use separate scale for direction maturity"

  - id: "W10"
    category: "remark-elimination"
    severity: "minor"
    target: "§6 circular claim"
    location: "FLT gains an application"
    description: "Unsupported/circular claim"
    suggestions:
      - "Replace with specific statement of what the connection enables"

  - id: "S22"
    category: "structural"
    severity: "minor"
    target: "§8 CFL inconsistency"
    location: "no natural structure"
    description: "Contradicts §7b universal cover discussion"
    suggestions:
      - "Reconcile or retract one statement"
```
