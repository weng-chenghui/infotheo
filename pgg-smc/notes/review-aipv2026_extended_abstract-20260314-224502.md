# Paper Review: Inverting the Formalization Workflow: Prototyping an MPC Protocol in Rocq with an LLM

**Reviewed:** 2026-03-14
**File:** pgg-smc/notes/aipv2026_extended_abstract.tex

## 1. Domain Assessment

**Domains:** Formal methods / proof assistants, LLM-assisted theorem proving, secure multi-party computation, algebraic topology (covering spaces, monodromy), algebraic geometry (AG codes), combinatorics (RAAGs, Cartier-Foata), information theory

**Personas:** Formal verification researcher, cryptographic protocol designer, LLM+formalization methodology specialist

**Key terms:** Monodromy representation (ρ : G → S_N), covering space / fiber structure, Right-Angled Artin Group (RAAG) / trace equivalence, Cartier-Foata theorem, hyperelliptic AG codes, Massey secret sharing, algebraic rigidity, dependent-type checking, collusion bound / total variation distance, axiomatization boundary

## 2. Reasoning Verification

### Summary
- **True claims:** 10
- **False claims:** 0
- **Suspicious claims:** 4 (after Opus audit; originally 18 Suspicious + 1 False from Sonnet)
- **Opus overrides:** 15 (1 False→True, 10 Suspicious→True/Acceptable, 4 Suspicious confirmed but downgraded to minor)

### False Claims

None after Opus audit.

*(Opus override: F1 "abelian collapse theorem" was originally marked FALSE by Sonnet for omitting a regularity hypothesis. Opus overturned to TRUE: regularity is the standard assumption for monodromy actions in covering space theory, and omitting it from a one-line summary in a 2-page abstract is acceptable shorthand.)*

### Suspicious Claims

| ID | Claim | Concern | Severity |
|----|-------|---------|----------|
| S11 | "information distance ≤ ε + 2(T−1)/N" | Formalization uses `var_dist` (total variation distance), not information-theoretic divergence. **Genuine terminological error.** | Substantive |
| S13 | "one algebraic choice determines four protocol parameters" | ε and ρ_dist are free inputs to the AlgebraicRigidity record, not derived from the graph/genus choice. Slightly overstates rigidity. | Mild |
| S1/S4 | "reveals exactly which assumptions/structure" (×2) | "Exactly" is rhetorical overclaim; type errors are informative but not uniquely diagnostic. | Minor nit |
| S5 | "if it compiles with zero Admitted, the logical structure holds" | True relative to stated axioms, but elides the specification-adequacy distinction. | Minor nit |

### True Claims

All other claims confirmed true or acceptable for extended-abstract standards: monodromy representation notation (S_N = {perm 'I_N}), Cartier-Foata axiom-free (confirmed zero Axiom in dependency chain), exact trace counts via clique recurrence (full RAAG generality), "avoiding Riemann-Roch" (accurate for weight-bound computation), five axiomatized properties (accurate enumeration), zero Admitted (confirmed by grep), 42 Rocq files (confirmed by find), abelian collapse theorem, Grover mitigation, covering-space analogy, compilation-as-confidence, software-engineering analogy, "prover accepts no shortcuts."

## 3. Academic Writing Critique

1. **No explicit contribution statement.** The paper never declares what it contributes. Add a sentence at the end of "The inverted workflow" or the start of "Case study": e.g., "We report two contributions: (a) a formal account of this inverted workflow, and (b) a 42-file Rocq formalization of the resulting protocol."

2. **No related work or citations.** Zero references. Directly relevant prior work exists: LLM-assisted proving (Lean Copilot, Draft-Sketch-Prove, ReProver), formal crypto (EasyCrypt, CryptHOL), and formalization methodology (Gonthier's Feit-Thompson). Even 2–3 inline citations would establish novelty.

3. **"Information distance" is wrong terminology.** The formalization computes total variation distance (`var_dist`). "Information distance" refers to Kolmogorov-complexity-based metrics.

4. **Security bound variables undefined.** The bound ε + 2(T−1)/N appears with no inline definition of ε, T, or N. Define them parenthetically.

5. **"Axiom-free" phrasing risks contradiction.** Line 50 says the Cartier-Foata theorem is "proved axiom-free," while line 62 discloses five axioms. The Cartier-Foata proof is genuinely axiom-free in its own dependency chain, but the juxtaposition creates a confusing reading. Change to "proved without additional axioms" or "proved from MathComp primitives alone."

6. **"One algebraic choice" overstates rigidity.** A graph and a genus are two inputs. And ε/ρ_dist are free parameters, not derived. Rephrase: "a single pair (graph, genus) constrains the threshold and automorphism bound."

7. **No artifact/repository pointer.** A methodology paper about formalization should link to the development. Add a URL or anonymized artifact note.

8. **RAAG trace-equivalence role unexplained.** Why does counting computation histories correspond to RAAG traces? One sentence of explanation would help.

9. **"The prover accepts no shortcuts" is vague.** The intended meaning (every step must compile under the type checker) should be stated directly.

10. **Abelian collapse theorem not characterized.** What collapses? The search space falls from exponential to polynomial? State this.

11. **Session-type system unidentified.** Rocq has no built-in session types. Name the encoding or library.

12. **"Learned through formalization" claim is asserted, not evidenced.** Give one concrete instance (e.g., "The Cartier-Foata theorem was introduced by the LLM to solve a trace-counting obligation").

13. **LLM identity unspecified.** Which LLM(s) were used? This matters for reproducibility.

14. **"verdicts" used as a verb** (line 23). Nonstandard. Use "checks" or "accepts or rejects."

15. **No `\begin{abstract}` block.** Workshop proceedings typically require one.

## 4. Section Formality Distance

| Section | Rating (1–5) | Justification |
|---------|:---:|---------------|
| "The timeline problem." | 3 | Well-written motivation but no citations, no formal setup, "verdicts" is nonstandard |
| "The inverted workflow." (para 1) | 3 | Covering-space analogy asserted but not defined; acceptable for abstract if citing formal development |
| "The inverted workflow." (para 2) | 3 | "Exactly" overclaims twice; "iteration after iteration" is rhetorical padding |
| "The inverted workflow." (para 3, three roles) | 2 | Crisp decomposition; minor imprecision on "logical structure holds" |
| "Case study: SMC-PGG" (protocol layer) | 2 | Technically precise; loses a point for unexplained session-type system |
| "Case study: SMC-PGG" (search-space layer) | 3 | RAAG/Cartier-Foata named but not explained; "axiom-free" risks contradiction |
| "Case study: SMC-PGG" (reconstruction layer) | 3 | "One algebraic choice" overstates; "avoiding Riemann-Roch" unexplained for non-specialists |
| "Case study: SMC-PGG" (security layer) | 3 | Wrong terminology ("information distance"), undefined variables in bound, abelian collapse uncharacterized |
| "Case study: SMC-PGG" (42 files summary) | 2 | Factual and specific; no repo pointer |
| "Observations." (para 1) | 2 | Concrete feedback-loop description; "years of domain study" is overclaim |
| "Observations." (para 2, limits) | 2 | Honest and specific limitations |
| "Broader implication." (para 1) | 3 | Software analogy apt but underdeveloped |
| "Broader implication." (para 2, closing) | 3 | "No shortcuts" is vague; thesis deserves more than one closing sentence |

*(1 = publication-ready, 5 = informal notes / far from formal)*

**Overall: 2.5** — Sound technical content with structural deficits (no contributions statement, no related work, undefined symbols, wrong terminology in one place).

## 5. Constructive Suggestions

### Critical

- **C1: "information distance" → "total variation distance" (proof-repair)**: Replace "information distance" with "total variation distance" to match the Rocq formalization's `var_dist`.
  - *LaTeX sketch*: `a collusion bound (total variation distance $\leq \varepsilon + 2(T{-}1)/N$)`
  - *Confidence*: definite

### Major

- **M1: "one algebraic choice determines four" (restatement)**: Clarify that the graph/genus determine threshold and automorphism bound, while ε and ρ_dist are user-supplied inputs.
  - *Options*: (A) "constrains four protocol parameters, with ε as a user-supplied input" / (B) "determines the threshold pair (k,T) and the automorphism bound"
  - *Confidence*: definite

- **M2: "the logical structure holds" (hypothesis-insertion)**: Add "relative to the five stated axioms" to acknowledge the axiomatization boundary.
  - *LaTeX sketch*: `the logical structure holds relative to the five stated axioms.`
  - *Confidence*: definite

- **M3: No related work (structural)**: Add a brief paragraph or inline citations situating against LLM-assisted proving (Lean Copilot, Draft-Sketch-Prove) and formal crypto (EasyCrypt, CryptHOL).
  - *Options*: (A) Dedicated paragraph before "Broader implication" / (B) Inline citations in "The inverted workflow"
  - *Confidence*: definite

- **M4: No contribution statement (structural)**: Add an explicit sentence enumerating contributions: (1) inverted workflow methodology, (2) SMC-PGG 42-file formalization, (3) empirical observations.
  - *Confidence*: definite

- **M5: LLM identity unspecified (structural)**: Name the specific LLM(s) used (e.g., Claude Opus/Sonnet) via footnote or parenthetical.
  - *Confidence*: definite

### Minor

- **m1: "verdicts" as verb (restatement)**: Replace "A dependent type checker verdicts each draft" with "A dependent type checker checks each draft."
  - *Confidence*: definite

- **m2: "exactly" ×2 (restatement)**: Soften or remove "exactly" in at least one of the two rhetorical uses.
  - *Options*: (A) Remove from both / (B) Keep in Observations (empirical), remove from para 2 (rhetorical)
  - *Confidence*: possible

- **m3: No affiliation (structural)**: Confirm affiliation is present or intentionally omitted per venue policy.
  - *Confidence*: possible

## 6. Summary Verdict

The paper's reasoning is sound — no false claims after Opus audit, and the one genuine error ("information distance" for total variation distance) is terminological, not logical. The main structural weaknesses are: (1) no related work or citations, (2) no explicit contribution statement, (3) undefined variables in the security bound, and (4) the LLM used is not named. These are fixable within the 2-page limit. The technical content is compelling and appropriate for AIPV 2026; with the fixes above, the abstract would be ready for submission.

## 7. Fix Manifest

```yaml
fixes:
  - id: C1
    category: proof-repair
    severity: critical
    target: "collusion bound terminology"
    location: "information distance $\\leq \\varepsilon + 2(T{-}1)/N$"
    description: "'information distance' should be 'total variation distance' to match var_dist in formalization"
    suggestions:
      - "Replace 'information distance' with 'total variation distance'"

  - id: M1
    category: restatement
    severity: major
    target: "algebraic rigidity claim"
    location: "one algebraic choice---a graph and its genus---determines four protocol parameters"
    description: "epsilon and rho_dist are inputs to AlgebraicRigidity, not derived from graph/genus"
    suggestions:
      - "Change to 'constrains four protocol parameters, with $\\varepsilon$ as a user-supplied input'"
      - "Change to 'determines the threshold pair $(k,T)$ and the automorphism bound'"

  - id: M2
    category: hypothesis-insertion
    severity: major
    target: "zero-Admitted guarantee scope"
    location: "the logical structure holds."
    description: "Claim elides axiomatization boundary; should note soundness is relative to five stated axioms"
    suggestions:
      - "Append 'relative to the five stated axioms'"

  - id: M3
    category: structural
    severity: major
    target: "missing related work"
    location: "entire paper — no citations present"
    description: "No related work or references; cannot assess novelty"
    suggestions:
      - "Add paragraph before Broader implication citing LLM-assisted proving and formal crypto work"
      - "Add inline citations in The inverted workflow paragraph"

  - id: M4
    category: structural
    severity: major
    target: "missing contribution statement"
    location: "end of The inverted workflow paragraph"
    description: "No explicit enumeration of contributions"
    suggestions:
      - "Add sentence listing contributions: workflow methodology, 42-file formalization, empirical observations"

  - id: M5
    category: structural
    severity: major
    target: "LLM identity"
    location: "first mention of 'LLM' in paragraph 1"
    description: "Which LLM was used is not specified; needed for reproducibility"
    suggestions:
      - "Add footnote or parenthetical naming the LLM(s) used"

  - id: m1
    category: restatement
    severity: minor
    target: "'verdicts' as verb"
    location: "A dependent type checker verdicts each draft within minutes."
    description: "'verdicts' is nonstandard as a verb"
    suggestions:
      - "Replace 'verdicts' with 'checks'"

  - id: m2
    category: restatement
    severity: minor
    target: "'exactly' overclaim"
    location: "reveals exactly which assumptions are missing"
    description: "'exactly' implies unique diagnostics; type errors are informative but not uniquely diagnostic"
    suggestions:
      - "Remove 'exactly' from both occurrences"
      - "Keep one instance, remove the other"

  - id: m3
    category: structural
    severity: minor
    target: "author affiliation"
    location: "\\author{Cheng-Hui Weng}"
    description: "No affiliation listed"
    suggestions:
      - "Add affiliation or confirm venue allows omission"
```
