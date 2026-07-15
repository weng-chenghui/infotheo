# Paper Review: Word Composition as Computation: SMC-PGG in the MPC Landscape

**Reviewed:** 2026-03-13
**File:** `pgg-smc/notes/20260313_word_computation_mpc_landscape.md`

## 1. Domain Assessment

- **Primary domains:** Multiparty computation (MPC), complexity theory (circuit complexity, branching programs), algebraic automata theory, cryptography (randomized encodings, FHE, obfuscation)
- **Reviewer persona:** MPC theorist and complexity theorist specializing in branching programs, algebraic automata theory, information-theoretic secure computation, and randomized encodings
- **Key technical terms:** Barrington's theorem, branching programs, NC^1, commuting permutation systems (CPS), NIMPC, trace monoids, RAAG, randomized encodings, Krohn-Rhodes decomposition, monodromy group, Eilenberg varieties

## 2. Reasoning Verification

### Summary
- **True claims:** 5
- **False claims:** 8
- **Suspicious claims:** 11
- **Opus overrides:** 2 (F8: FALSE->SUSPICIOUS, F9: FALSE->TRUE)

### False Claims

| ID | Location | Claim | Explanation |
|----|----------|-------|-------------|
| F1 | §2 table | "Branching program \| GL_k(F) \| P (unrestricted width)" | Underspecified. Polynomial-length, unrestricted-width BPs capture P, but the table omits that k must grow and conflates width with length. The "matrix monoid GL_k(F)" description doesn't specify that k varies. |
| F2 | §3.2 table | "Commutative monoid -> ACC^0 cap comm / symmetric functions only" | **Wrong.** Commutative monoids include cyclic groups Z/nZ, which recognize MOD-n languages. The word problem depends on the Parikh image (letter counts), which is far richer than "symmetric functions." |
| F3 | §3.3 | "If G is non-solvable, the word-product can compute any NC^1 function" | Barrington's theorem says for any NC^1 function there *exists* a width-5 BP computing it with freely chosen instructions. In SMC-PGG, the word structure is constrained by protocol geometry. The conclusion requires showing SMC-PGG can instantiate arbitrary Barrington-style BPs -- no such construction is provided. |
| F4 | §4.2 | "per Barrington-Therien, non-commutativity is exactly what enables NC^1" | **Substantive mathematical error.** What enables NC^1 is *non-solvability*, not non-commutativity. Non-commutative solvable groups (e.g., S_3, dihedral groups) do NOT capture NC^1. The attribution to Barrington-Therien is also incorrect -- the relevant result is Barrington (1989). |
| F5 | §5.1 | "each individual garbled factor is uniformly random given only the product" | **Wrong security statement.** The security guarantee is simulation-based: the *joint distribution* of all garbled factors is simulatable from f(x) alone. Individual factors are not uniformly random; they have the distribution R_{j-1} * M_j(x) * R_j^{-1}. |
| F6 | §7.3 | "Composing rounds could extend SMC-PGG beyond NC^1 to all regular language recognition" | **Inverted containment.** REG subset NC^1 (all regular languages are already in NC^1 via DFA simulation in O(log n) depth). "Extending beyond NC^1 to regular languages" is incoherent. |
| F7 | §9.2 | "The non-solvability of A_5 (same as Barrington) is essential for computational completeness [in Nuida's FHE]" | Nuida's FHE uses different algebraic mechanisms (conjugacy search problem, word problem in non-commutative groups). The A_5 non-solvability is Barrington's construction, not Nuida's. |
| S10->F | §11 | "Any NC^1 function can be securely evaluated by composing monodromy permutations" | *(Opus override: was Suspicious)* Conflates computational expressibility (Barrington: NC^1 = width-5 BPs) with *secure evaluation* (requires simulation argument). Security of such a protocol is the central open question, not a concluded result. |

### Suspicious Claims

| ID | Location | Claim | Concerns |
|----|----------|-------|----------|
| S1 | §1 | "width-5 branching programs (= words over S_5)" | A BP is a sequence of input-dependent instructions selecting permutations based on input bits. A "word over S_5" is a fixed element. The parenthetical conflates the two. |
| S2 | §3.1 | "the commutator [alpha, beta] where alpha, beta are 5-cycles produces another 5-cycle" | False for arbitrary 5-cycles (e.g., [sigma, sigma] = id). Holds for *suitably chosen* pairs; existence follows from simplicity of A_5. |
| S3 | §3.2 table | "Finite group of exponent p -> MOD_p" | Too broad. Elementary abelian p-groups give MOD_p. Non-abelian groups of exponent p (e.g., Heisenberg group over F_p) may recognize strictly more. |
| S4 | §4.1 | "f admits NIMPC iff f has CPS" | Applies to the specific model: deterministic functions, perfect security, server-aided NIMPC. Not all NIMPC notions. |
| S5 | §4.2 | "CPS subset SMC-PGG" where I = Sigma x Sigma | Requires every CPS to be realizable as an SMC-PGG instance with fully commuting RAAG. No construction or proof provided. |
| F8->S | §9.3 | "Ciphertext size depends on input length and BP length, not BP width" | *(Opus override: was False)* In Barrington-based constructions width is constant (5), so width doesn't appear as a variable parameter. Defensible in that specific context but misleading for general BPs. |
| S6 | §5.2 | "Random sheet assignment acts like random matrices R_i" | Loose analogy with no formal correspondence. The security mechanisms differ: group action on sheets vs. matrix conjugation. |
| S7 | §8 | "more commutativity -> less computational power" | Qualitative direction is supported by Barrington-Therien for group word problems, but the note conflates two notions of commutativity (generator-level RAAG commutativity vs. group-level commutativity). |
| S8 | §8 | "free group" for I = empty | Should be "free monoid" (if no inverses) or clarify that the RAAG with I=empty is the free group, while the monodromy group (a finite quotient) is not free. |
| S9 | §10.2 | "I = empty -> NC^1 for non-solvable G" | Omits the width constraint. Barrington requires width >= 5 specifically. |
| S11 | §11 | "SMC-PGG generalizes CPS" | Stated as established fact. This is an unproven conjecture -- structural similarity is suggestive but formal containment requires a construction. |

### True Claims

- T1: Barrington's theorem statement (NC^1 = width-5 polynomial-length BPs)
- T2: CPS definition from Agarwal-Anand-Prabhakaran 2019
- T3: Current SMC-PGG is secret sharing only (word encodes group element, endpoint = share)
- T4: §4.3 "SMC-PGG computable functions: Intermediate -- open" (accurately flagged as open)
- F9->T: §7.2 "NC^1 includes integer comparison, addition, sorting networks, majority" *(Opus override: was False)* -- all listed functions are indeed in NC^1

## 3. Academic Writing Critique

1. **Contribution statement is vague.** The three contributions (survey, locate, extend) are activities, not results. The "three-way correspondence" in §11 is never formalized. Either state as a precise conjecture or demote to "exposition."

2. **Central claim "CPS subset SMC-PGG" is presented as a theorem but is an unproven conjecture.** Appears in §4.2, §11 as established fact. Must be labeled as a conjecture with explicit proof obligations.

3. **§3.2 table has factual errors** and conflates complexity classes with security properties in the same column. The "Commutative monoid" and "group of exponent p" rows are incorrect.

4. **§7.3 states an inverted complexity containment** (REG vs NC^1). This is a fundamental error in the main technical narrative.

5. **§5.1 security statement is wrong.** Individual garbled factors are not uniformly random; the correct statement is simulation-based joint indistinguishability.

6. **SMC-PGG is never defined** in the note. A reader without the companion note cannot parse the technical claims.

7. **RAAG is never defined.** Appears in §4.2, §4.3, §8, §10 without explanation.

8. **No security model is specified anywhere.** Security claims ("information-theoretically secure," "reveals nothing") float without formal grounding (no adversary class, no simulation paradigm, no corruption threshold).

9. **Non-commutativity vs. non-solvability confusion** pervades the note. The key algebraic condition enabling NC^1 is non-solvability, but the note repeatedly says "non-commutativity" (§3.3, §4.2, §8).

10. **§4.3 "Full (abelian)" is wrong.** CPS requires pairwise commutativity of generators, which does not imply the group is abelian.

11. **§8 "G abelian -> symmetric functions" is imprecise.** Should be "modular counting functions."

12. **§9.2 GRAFHEN (2025) citation is unverifiable** -- no author names, suspicious ePrint number from the future.

13. **§9.4 mischaracterizes PSM** as inherently word-product computation; this only holds for BP-structured functions.

14. **§10 Direction 5 confuses bounded-width with polynomial-width** branching programs. The algebraic characterization of NC^2 via monoids is open.

15. **§11 repeats §1** almost verbatim without synthesizing the body's findings.

16. **§6 bidirectional arrow** between trace monoids and SMC-PGG suggests equivalence; the actual relationship is one-directional (SMC-PGG uses trace monoid structure).

17. **§9.1 degree-2 vs degree-3 comparison is misleading** -- "degree-2" refers to Yao's garbled circuits (a protocol), not to randomized encodings of circuits.

18. **"Honest assessment" paragraphs** in §7.3 and §10 are stylistically inconsistent with the technical body. Should be integrated as formal remarks or collected in a limitations section.

## 4. Section Formality Distance

| Section | Rating (1-5) | Justification |
|---------|:---:|---------------|
| §1 Introduction | 3 | Contribution lists activities not results; central object undefined |
| §2 Word-Product Paradigm | 2 | Reasonable table format; "?" in computational power is honest but incomplete |
| §3.1 Barrington's Theorem | 2 | Theorem statement correct; "key algebraic fact" paragraph informal without citing commutator-nesting precisely |
| §3.2 Barrington-Therien Table | 4 | Factual errors in two rows; presents nontrivial equivalences as simple definitions |
| §3.3 Connection to SMC-PGG | 3 | Speculative connection framed as established ("The classification tells us...") |
| §4.1 CPS Definition | 2 | Definition and theorem clearly stated; attribution needs verification |
| §4.2 CPS and SMC-PGG | 4 | Unproven containment stated as fact; missing security model; non-commutativity/non-solvability confusion |
| §4.3 NIMPC Spectrum | 4 | "Full (abelian)" is wrong; table implies known hierarchy where one is open |
| §5.1 Ishai-Kushilevitz | 3 | Construction sketch correct; security statement wrong |
| §5.2 Connection to SMC-PGG | 4 | Informal analogy; "the word IS the secret" undefined; speculative extension |
| §6 Landscape Map | 3 | Useful diagram; bidirectional arrow misleading; no legend |
| §7.1 Current: Secret Sharing | 2 | Accurate and appropriately scoped |
| §7.2 Barrington Extension | 3 | Steps 1-3 reasonable; omits key technical obstacles (private permutation selection, security argument) |
| §7.3 Krohn-Rhodes Extension | 4 | Inverted containment; "no one has developed this" is honest but the technical claims are wrong |
| §8 Dictionary Table | 3 | Several entries imprecise/wrong; trade-off paragraph is the clearest prose in the note |
| §9.1 Garbled Circuits vs Words | 3 | Degree comparison misleading; otherwise reasonable |
| §9.2 Group-based FHE | 3 | Incorrect A_5 attribution; GRAFHEN citation unverifiable |
| §9.3 Oblivious Automata | 2 | Accurate; applications list relevant |
| §9.4 PSM | 3 | Overgeneralizes word-product interpretation of PSM |
| §10 Open Directions | 3 | Directions 1-2 well-posed; 3-5 increasingly imprecise; Direction 5 technically wrong |
| §11 Summary | 4 | Repeats §1; states conjectures as facts; three-way correspondence too vague for a conclusion |
| §12 References | 3 | Ref [3] attribution suspicious; ref [12] unverifiable; ref [6] venue needs checking |

*(1 = publication-ready, 5 = informal notes / far from formal)*

## 5. Constructive Suggestions

### Critical

- **FIX-C1 (F4+D8) -- §4.2, §4.3 (restatement)**: Replace "non-commutativity" with "non-solvability" throughout NC^1 capability claims. Replace "abelian" with "pairwise commutativity" in the CPS table column.
  - *Confidence*: definite

- **FIX-C2 (F3+S10) -- §3.3, §11 (hypothesis-insertion)**: Insert an explicit "Construction Assumption" making NC^1 completeness of SMC-PGG conditional on exhibiting a polynomial-length monodromy-word encoding for each width-5 BP, and note that secure evaluation additionally requires a simulation argument.
  - *LaTeX sketch*:
    ```
    \begin{assumption}[BP Instantiation]
    For every width-5 BP $P$ computing $f \in \NC^1$, there exists a
    monodromy word $w_P \in S_5^{\poly(n)}$ whose product over any input
    $x$ equals the BP output permutation. SMC-PGG inherits NC^1-completeness
    only if this encoding is efficiently constructible and the simulator applies.
    \end{assumption}
    ```
  - *Confidence*: definite

- **FIX-C3 (F5+D5) -- §5.1 (proof-repair)**: Replace the marginal-uniformity claim with a simulation-based statement: there exists a simulator whose output distribution is statistically indistinguishable from the joint view of any semi-honest adversary, given only f(x).
  - *LaTeX sketch*:
    ```
    \begin{claim}[Security of Garbled Encoding]
    Given $f(x)$, the joint distribution of all garbled factors is
    statistically independent of $x$. Formally, there exists a simulator
    $\Sim$ such that $\Sim(f(x)) \approx_s \{R_{j-1} M_j(x) R_j^{-1}\}_j$.
    \end{claim}
    ```
  - *Confidence*: definite

- **FIX-C4 (F6+D4) -- §7.3 (restatement)**: Fix the inverted containment. Replace "extend beyond NC^1 to all regular language recognition" with "REG subset NC^1; monodromy words handle regular languages as a special case of NC^1, not an extension beyond it."
  - *Options*: (A) Delete §7.3 and fold correct observation into §3.2. (B) Rewrite: Krohn-Rhodes cascades recover all regular languages, which already lie within NC^1.
  - *Confidence*: definite

- **FIX-C5 (D10) -- before §3 (structural)**: Insert a self-contained definition of SMC-PGG (monodromy group G, representation rho, sheet set [N], word structure, endpoint readout) so all subsequent claims have a concrete referent.
  - *Confidence*: definite

- **FIX-C6 (D15) -- new subsection (structural)**: Add a "Security Model" subsection specifying adversary class (semi-honest vs. malicious), simulation paradigm (ideal/real), corruption threshold, and computational vs. statistical security before any security claim is stated.
  - *Confidence*: definite

### Major

- **FIX-M1 (F1) -- §2 table (restatement)**: Split the BP row into two: width-5/poly-length (NC^1 via S_5) and poly-width/poly-length (P via general matrix products), with explicit parameters.
  - *Confidence*: definite

- **FIX-M2 (F2) -- §3.2 table (restatement)**: Replace "symmetric functions only" with "modular counting functions (MOD-n for abelian groups of exponent n); symmetric functions arise only for the trivial monoid."
  - *Options*: (A) Annotate with footnote. (B) Add separate rows for abelian p-group (MOD_p) and trivial monoid.
  - *Confidence*: definite

- **FIX-M3 (S3) -- §3.2 table (hypothesis-insertion)**: Qualify: "An elementary abelian p-group (Z/pZ)^k recognizes exactly MOD_p; non-abelian groups of exponent p may recognize strictly more."
  - *Confidence*: definite

- **FIX-M4 (F7) -- §9.2 (restatement)**: Either cite Nuida's actual algebraic mechanism and remove the A_5 claim, or qualify: "motivated by non-solvability, though Nuida's construction uses [specific hardness assumption]."
  - *Options*: (A) Delete pending verification. (B) Replace with qualified statement.
  - *Confidence*: definite

- **FIX-M5 (D2+S5+S11) -- §4.2, §11 (hypothesis-insertion)**: Demote "CPS subset SMC-PGG" and "SMC-PGG generalizes CPS" to labeled conjectures with explicit proof obligations.
  - *Confidence*: definite

- **FIX-M6 (D11) -- first use (structural)**: Define RAAG: "A right-angled Artin group A(Gamma) has generators {v_i} indexed by vertices of Gamma, with relations v_i v_j = v_j v_i whenever {i,j} is an edge."
  - *Confidence*: definite

- **FIX-M7 (S9+D17) -- §10 (hypothesis-insertion)**: Add width-5 constraint explicitly. Fix Direction 5: NC^1 = width-5 BPs; the barrier to NC^2 is not width but the algebraic characterization of NC^2 is open.
  - *Confidence*: definite

- **FIX-M8 (S4) -- §4.1 (hypothesis-insertion)**: Qualify the CPS equivalence: holds for deterministic functions, perfect security, server-aided NIMPC model only.
  - *Confidence*: definite

- **FIX-M9 (D13) -- §9.2 (structural)**: Provide full GRAFHEN citation (authors, venue, verified arXiv/ePrint) or mark as "unpublished, citation pending verification."
  - *Confidence*: definite

- **FIX-M10 (D3) -- §3.2 (structural)**: Split into two tables: one mapping algebraic structures to complexity classes (Barrington-Therien), one mapping to security properties.
  - *Confidence*: definite

- **FIX-M11 (D14) -- §9.4 (hypothesis-insertion)**: Qualify: "When f is computed via a branching program, PSM admits a word-product structure; in general, PSM is not restricted to word-product computation."
  - *Confidence*: definite

### Minor

- **FIX-N1 (S1) -- §1 (restatement)**: Replace "words over S_5" with "sequences of input-dependent S_5 instructions."
  - *Confidence*: definite

- **FIX-N2 (S2) -- §3.1 (restatement)**: Insert "suitably chosen": "the commutator of two *suitably chosen* 5-cycles in A_5 is again a 5-cycle."
  - *Confidence*: definite

- **FIX-N3 (S6) -- §5.2 (remark-elimination)**: Either formalize the sheet/matrix analogy with a precise correspondence or remove it.
  - *Options*: (A) Formalize via leftover-hash-lemma style bound. (B) Remove and replace with concrete entropy argument.
  - *Confidence*: possible

- **FIX-N4 (S7) -- §8 (hypothesis-insertion)**: Qualify the commutativity-power trade-off as a conjecture, or state only the proven direction.
  - *Confidence*: possible

- **FIX-N5 (S8) -- §8 (notation)**: Replace "free group" with "free monoid" (if no inverses) or clarify RAAG vs. monodromy group distinction.
  - *Confidence*: definite

- **FIX-N6 (D1) -- §1 (structural)**: Rewrite contribution bullets as results ("We show/prove") or conjectures ("We conjecture").
  - *Confidence*: definite

- **FIX-N7 (D6) -- §4.1 (structural)**: Verify CPS definition attribution (Beimel et al. 2014 vs. Agarwal et al. 2019).
  - *Confidence*: possible

- **FIX-N8 (D7) -- §9.1 (restatement)**: Clarify that "degree-2" refers to Yao's garbled circuit protocol, not randomized encodings of circuits in general.
  - *Confidence*: possible

- **FIX-N9 (D9) -- §8 (restatement)**: Replace "symmetric functions (sums, thresholds)" with "modular counting functions."
  - *Confidence*: definite

- **FIX-N10 (D12) -- §6 (notation)**: Replace bidirectional arrow with labeled unidirectional arrows.
  - *Confidence*: possible

- **FIX-N11 (D16) -- §7.3, §10 (structural)**: Convert "Honest assessment" paragraphs to Remark/Open Problem labels, or collect in a Limitations section.
  - *Confidence*: definite

- **FIX-N12 (D18) -- §11 (structural)**: Rewrite summary to synthesize findings rather than repeat §1. State the precise conjecture and the Barrington extension as a formal proposal.
  - *Confidence*: definite

## 6. Summary Verdict

The note's reasoning has significant structural problems: 8 false claims and 11 suspicious claims across 12 sections. The most damaging cluster is the conflation of *non-commutativity* with *non-solvability* (which pervades §3.3, §4.2, §8), the inverted REG/NC^1 containment in §7.3, and the presentation of unproven conjectures ("CPS subset SMC-PGG", "any NC^1 function can be securely evaluated") as established results. The note also lacks self-containedness: SMC-PGG, RAAG, and the security model are never defined.

The landscape survey (§2, §6, §9) and the honest self-assessments are valuable, and the core observation -- that SMC-PGG's monodromy walk is a word-product computation analogous to Barrington BPs -- is sound and worth developing. However, the note requires substantial revision before the technical claims can be trusted: fix the 6 critical issues (define SMC-PGG, define security model, correct the solvability/commutativity distinction, fix the security statement, fix the containment inversion, and demote unproven claims to conjectures), then address the 11 major issues.

## 7. Fix Manifest

```yaml
fixes:
  - id: "FIX-C1"
    category: "restatement"
    severity: "critical"
    target: "§4.2 non-commutativity claim and §4.3 table"
    location: "non-commutativity is exactly what enables NC^1"
    description: "Conflates non-commutativity with non-solvability; what enables NC^1 is non-solvability"
    suggestions:
      - "Replace 'non-commutativity' with 'non-solvability' throughout"
      - "Replace 'Full (abelian)' in §4.3 table with 'All generator pairs commute (pairwise commutativity)'"

  - id: "FIX-C2"
    category: "hypothesis-insertion"
    severity: "critical"
    target: "§3.3 NC^1 completeness claim and §11 secure evaluation claim"
    location: "the word-product can compute any NC^1 function"
    description: "NC^1 completeness of SMC-PGG requires constructive proof not provided; secure evaluation conflated with expressibility"
    suggestions:
      - "Insert explicit Construction Assumption making NC^1 completeness conditional"
      - "Separate expressibility (Barrington) from security (requires simulation argument)"

  - id: "FIX-C3"
    category: "proof-repair"
    severity: "critical"
    target: "§5.1 security claim"
    location: "each individual garbled factor is uniformly random given only the product"
    description: "Wrong security statement; should be simulation-based joint indistinguishability"
    suggestions:
      - "Replace with simulation-based statement: exists simulator whose output is indistinguishable from joint view given f(x)"

  - id: "FIX-C4"
    category: "restatement"
    severity: "critical"
    target: "§7.3 containment claim"
    location: "extend SMC-PGG beyond NC^1 to all regular language recognition"
    description: "Inverted containment: REG subset NC^1, not the other way around"
    suggestions:
      - "Rewrite: regular languages are a special case of NC^1, not an extension beyond it"
      - "Delete §7.3 and fold correct observation into §3.2"

  - id: "FIX-C5"
    category: "structural"
    severity: "critical"
    target: "Missing SMC-PGG definition"
    location: "before §3 (new section needed)"
    description: "SMC-PGG is never defined; all downstream claims lack a concrete referent"
    suggestions:
      - "Insert definition: monodromy group G, representation rho, sheet set [N], word structure, endpoint readout"

  - id: "FIX-C6"
    category: "structural"
    severity: "critical"
    target: "Missing security model"
    location: "new subsection before any security claim"
    description: "No security model defined; security claims are vacuous without adversary class, simulation paradigm, corruption threshold"
    suggestions:
      - "Add Security Model subsection: semi-honest vs malicious, ideal/real paradigm, corruption threshold, computational vs statistical"

  - id: "FIX-M1"
    category: "restatement"
    severity: "major"
    target: "§2 table BP row"
    location: "Branching program | Matrix monoid GL_k(F)"
    description: "Underspecified; conflates width and length parameters"
    suggestions:
      - "Split into width-5/poly-length (NC^1) and poly-width/poly-length (P) rows"

  - id: "FIX-M2"
    category: "restatement"
    severity: "major"
    target: "§3.2 table commutative monoid row"
    location: "Commutative monoid | ACC^0 ∩ comm | Symmetric functions only"
    description: "Wrong; commutative monoids include Z/nZ recognizing MOD-n, not just symmetric functions"
    suggestions:
      - "Replace with 'modular counting functions (MOD-n for abelian groups of exponent n)'"
      - "Add separate rows for abelian p-group and trivial monoid"

  - id: "FIX-M3"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§3.2 table exponent-p row"
    location: "Finite group of exponent p | MOD_p"
    description: "Too broad; only elementary abelian p-groups give exactly MOD_p"
    suggestions:
      - "Restrict to elementary abelian p-groups (Z/pZ)^k"

  - id: "FIX-M4"
    category: "restatement"
    severity: "major"
    target: "§9.2 Nuida FHE claim"
    location: "The non-solvability of A_5 (same as Barrington) is essential"
    description: "Nuida's FHE uses different algebraic mechanisms, not A_5 non-solvability"
    suggestions:
      - "Delete the A_5 claim pending verification of Nuida's actual construction"
      - "Replace with qualified statement citing Nuida's specific mechanism"

  - id: "FIX-M5"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§4.2 and §11 CPS generalization claims"
    location: "CPS ⊂ SMC-PGG in algebraic structure"
    description: "Unproven containment stated as theorem; should be conjecture"
    suggestions:
      - "Demote to labeled Conjecture with explicit proof obligations"

  - id: "FIX-M6"
    category: "structural"
    severity: "major"
    target: "RAAG definition missing"
    location: "first use in §4.2"
    description: "RAAG appears in §4.2, §4.3, §8, §10 without definition"
    suggestions:
      - "Insert one-sentence definition at first use"

  - id: "FIX-M7"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§10 Direction 2 and Direction 5"
    location: "I = ∅ → NC^1 for non-solvable G"
    description: "Omits width-5 constraint; Direction 5 confuses bounded-width with polynomial-width"
    suggestions:
      - "Add width-5 constraint explicitly"
      - "Fix Direction 5: algebraic characterization of NC^2 via monoids is open"

  - id: "FIX-M8"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§4.1 NIMPC iff CPS"
    location: "A function f admits information-theoretically secure non-interactive MPC"
    description: "Equivalence holds only for deterministic functions, perfect security, server-aided model"
    suggestions:
      - "Add qualification specifying the model"

  - id: "FIX-M9"
    category: "structural"
    severity: "major"
    target: "§9.2 GRAFHEN citation"
    location: "GRAFHEN (2025)"
    description: "No author names; ePrint number unverifiable"
    suggestions:
      - "Provide full citation or mark as unpublished/pending verification"

  - id: "FIX-M10"
    category: "structural"
    severity: "major"
    target: "§3.2 table"
    location: "Barrington-Therien complexity classification table"
    description: "Conflates complexity classes with security properties in same column"
    suggestions:
      - "Split into separate complexity-class table and security-properties table"

  - id: "FIX-M11"
    category: "hypothesis-insertion"
    severity: "major"
    target: "§9.4 PSM characterization"
    location: "Each party's message is a 'letter'; the referee assembles the 'word'"
    description: "Word-product interpretation only valid for BP-structured functions"
    suggestions:
      - "Add qualifier: word-product structure applies when f has a BP representation"

  - id: "FIX-N1"
    category: "restatement"
    severity: "minor"
    target: "§1 BP description"
    location: "width-5 branching programs (= words over S_5)"
    description: "BPs are input-dependent instructions, not fixed words"
    suggestions:
      - "Replace 'words over S_5' with 'sequences of input-dependent S_5 instructions'"

  - id: "FIX-N2"
    category: "restatement"
    severity: "minor"
    target: "§3.1 commutator claim"
    location: "The commutator identity [α, β] = α^{-1}β^{-1}αβ, where α, β are 5-cycles, produces another 5-cycle"
    description: "Not true for arbitrary 5-cycles; needs 'suitably chosen'"
    suggestions:
      - "Insert 'suitably chosen' before '5-cycles'"

  - id: "FIX-N3"
    category: "remark-elimination"
    severity: "minor"
    target: "§5.2 sheet/matrix analogy"
    location: "The random sheet assignment acts like the random matrices R_i"
    description: "Unsubstantiated analogy"
    suggestions:
      - "Formalize with precise correspondence"
      - "Remove and replace with concrete argument"

  - id: "FIX-N4"
    category: "hypothesis-insertion"
    severity: "minor"
    target: "§8 trade-off claim"
    location: "commutativity enables parallelism and non-interaction, but reduces computational power"
    description: "Monotone trade-off asserted without proof"
    suggestions:
      - "Qualify as conjecture or cite proven direction only"

  - id: "FIX-N5"
    category: "notation"
    severity: "minor"
    target: "§8 free group terminology"
    location: "A fully non-commutative protocol (free group)"
    description: "Should be 'free monoid'; monodromy group is finite, not free"
    suggestions:
      - "Replace 'free group' with 'free monoid on the generator set'"

  - id: "FIX-N6"
    category: "structural"
    severity: "minor"
    target: "§1 contribution statement"
    location: "Contributions. We (1) survey"
    description: "Lists activities not results"
    suggestions:
      - "Rewrite as results or conjectures"

  - id: "FIX-N7"
    category: "structural"
    severity: "minor"
    target: "§4.1 CPS attribution"
    location: "Definition (Agarwal–Anand–Prabhakaran, EUROCRYPT 2019)"
    description: "May not be the original source; verify against Beimel et al. 2014"
    suggestions:
      - "Verify and correct attribution"

  - id: "FIX-N8"
    category: "restatement"
    severity: "minor"
    target: "§9.1 degree comparison"
    location: "degree-3 randomized encodings (vs. degree-2 for circuits)"
    description: "Degree-2 refers to Yao's protocol, not randomized encodings of circuits"
    suggestions:
      - "Clarify what degree-2 refers to"

  - id: "FIX-N9"
    category: "restatement"
    severity: "minor"
    target: "§8 abelian row"
    location: "Symmetric functions only (sums, thresholds)"
    description: "Should be modular counting functions"
    suggestions:
      - "Replace 'symmetric functions (sums, thresholds)' with 'modular counting functions'"

  - id: "FIX-N10"
    category: "notation"
    severity: "minor"
    target: "§6 landscape diagram"
    location: "Trace monoids M(Σ,I) ◄──────────→ SMC-PGG"
    description: "Bidirectional arrow suggests equivalence; relationship is one-directional"
    suggestions:
      - "Replace with labeled unidirectional arrows"

  - id: "FIX-N11"
    category: "structural"
    severity: "minor"
    target: "§7.3 and §10 honest assessment paragraphs"
    location: "Honest assessment: The single-round Barrington extension"
    description: "Stylistically inconsistent with technical body"
    suggestions:
      - "Convert to Remark/Open Problem labels or collect in Limitations section"

  - id: "FIX-N12"
    category: "structural"
    severity: "minor"
    target: "§11 Summary"
    location: "SMC-PGG's monodromy walk is a word-product computation"
    description: "Repeats §1 verbatim without synthesis"
    suggestions:
      - "Rewrite to synthesize findings; state precise conjecture; give formal Barrington extension proposal"
```
