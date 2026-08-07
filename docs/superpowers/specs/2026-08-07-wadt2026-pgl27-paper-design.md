# WADT 2026 full paper: revised design spec

Date: 2026-08-07. Status: approved design, pre-plan.

This document supersedes
`docs/superpowers/specs/2026-07-13-wadt2026-pgl27-paper-design.md`.
The earlier document remains as a historical record. This revision corrects
the mathematical claims, separates the exact and finite-step shuffle models,
narrows the LLM discussion to methodology, and defines the paper-only work
boundary.

## Deliverable and venue

The deliverable is one LNCS paper for the WADT 2026 refereed
post-proceedings. The submission deadline is 2026-09-17 and the notification
date is 2026-10-29. The paper extends the abstract accepted and presented on
2026-06-30 in Rennes. That abstract used den Boer's protocol as its main case
and proposed an S5 and Barrington compilation direction. The full paper keeps
the same algebraic thesis and replaces the main case with the later PGL(2,7)
development. The abstract, slides, and source diagrams are in
`~/Projects/aplas2024-poster/wadtSep17/`.

- Title: **Algebraic Specification of Card-Based Cryptographic Protocols in
  Rocq**.
- Default author form: Cheng-Hui Weng, Nagoya University, solo. The LaTeX
  front matter has an anonymized build switch until the chairs confirm the
  review policy.
- Funding information must be confirmed during drafting.
- The bibliography style is `splncs04.bst` unless the current venue package
  says otherwise.
- The source `WengEtAl2025` entry already contains Cheng-Hui Weng, Reynald
  Affeldt, Jacques Garrigue, and Takafumi Saikawa. Copy it without replacing
  the authors with the anonymous placeholder used in the accepted LaTeX.

The author will contact the chairs about the page rule. This design does not
reduce the planned technical content or adopt a lower page target. The same
message should also confirm how appendices count, whether the paper is
anonymous, which template version is required, which EasyChair track accepts
the full paper, and whether the post-proceedings paper may replace the
workshop abstract's den Boer case study with the PGL(2,7) results.

## Work boundary

This project is a paper-writing task. It does not authorize changes to the
formalization.

The paper task may:

- create and edit LaTeX, figures, bibliography data, artifact metadata, and
  disclosure text
- read existing Rocq source files and theorem statements
- inspect assumptions, dependency information, and repository history
- run read-only Rocq queries or isolated probes
- compare prose claims with committed theorems
- write a formalization request for another proving tool
- update the paper after a separately completed proof has been checked

The paper task must not:

- edit any `.v` file
- fill a proof, alter a theorem statement, or refactor the Rocq library
- expand the formalization merely to preserve an ambitious sentence
- present a requested but unfinished theorem as an established result

When prose exceeds the formal result, the first response is to narrow the
prose. A formalization request is appropriate only when the missing result is
necessary for the paper's approved core.

## Paper thesis and contributions

The paper presents a Rocq framework in which a card protocol is described by
a finite group, a permutation representation, and a shuffle law. The PGL(2,7)
instance is the main case study. Four sibling instances show which parts of
the development are reusable.

The paper makes three technical contributions.

1. It gives a common Rocq interface for the group action, shuffle law,
   reconstruction, participant views, and executed traces of card-based
   protocols.
2. It proves correctness, the exact recovery ramp, coalition view privacy,
   and executed-trace secrecy for the PGL(2,7) protocol under the exact
   uniform shuffle model.
3. It proves that a realistic 200-letter generator-word shuffle approaches
   the exact uniform law. One certificate establishes the law-level bound.
   Rocq then transfers that bound to each single-card marginal and to the
   product of any secret prior with the shuffle law.

The LLM-assisted workflow is not a research contribution. It is reported in
the methodology and AI-use disclosures so that the production process is
transparent.

## Two shuffle models and their proven relation

The paper uses two related models throughout.

### Exact uniform shuffle

The ideal law is the uniform distribution `U_G` over the PGL(2,7) shuffle
group. The exact view-independence and executed-trace secrecy theorems use this
law.

The primary exact execution law is `pgl27P`. It samples a uniform Boolean
secret, uses the fixed representative `orbit_encode`, and samples an
independent uniform element of the PGL(2,7) shuffle group. The main exact view
and trace claims use this law and this uniform secret prior.

The all-decks law `pgl27P_alldecks` also uses a uniform Boolean prior. It
samples a uniform valid deck from the selected secret class before applying an
independent uniform group element. Its view and trace results are robustness
results, not the definition of the primary execution model.

The shuffle-free deck model proves prior-generic view independence through
`pgl27_view_indep_deck_prior`. The current trace theorems for that model still
use the uniform Boolean prior. The paper states these prior and dealer choices
at every security result.

### Realistic finite-step shuffle

The executable law is the 200-fold generator-word law `mu^*200`. It samples a
uniform 200-letter word over the chosen symmetric generator set and evaluates
the word in the shuffle group. The alphabet has five letters. It consists of
three PGL(2,7) generators and the two additional inverses needed to make the
tuple symmetric. The certificate compares `5^200` words across 336 group
fibers.

### Established bridge

The theorem `pgl27_word_mixing` proves

```text
var_dist(mu^*200, U_G) <= 2^-40.
```

In this repository, `var_dist` is the unhalved L1 distance

```text
sum_x |P(x) - Q(x)|.
```

The paper must therefore state the result as L1 distance at most `2^-40`.
Under the common halved convention, the corresponding total variation bound
is at most `2^-41`.

The theorem `pgl27_endpoint_mixing` transfers the same L1 upper bound to every
single-card marginal. The theorem `pgl27_joint_mixing` transfers it to the
product of any secret prior with the shuffle law. Independence is built into
this product distribution. The theorem is not a statement about an executed
protocol.

### Missing bridge

The current development does not transport product-law proximity through the
interpreter to an approximate view-privacy or approximate executed-trace
secrecy theorem. The paper must not describe `2^-40` as a trace-secrecy bound.
It must also not describe `2^-40` as a coalition-privacy bound. Section 6 ends
by showing this missing arrow explicitly.

The relation between the models is therefore a main result of this paper at
the distribution level. A general security-level bridge belongs to future
work.

## Security and functionality scope

The paper states the following scope in the abstract, introduction, and model
section.

- The PGL(2,7) case is an empty-input, dealer-based sharing protocol.
- Adversaries are passive and honest-but-curious.
- Under `pgl27P`, a coalition of at most three players has exact view and trace
  privacy for a uniform Boolean secret, a fixed encoded representative, and a
  uniform PGL(2,7) shuffle.
- The verifier receives the endpoints and learns the secret by design.
- Post-reveal knowledge is outside the model.
- Active deviation and composition across executions are outside the model.
- The implemented decoder reads all eight endpoints.
- Seven revealed cards already determine the deck and its secret class.
- Six revealed cards never determine the class.
- Three or fewer revealed cards preserve exact privacy.
- One specific four-card coalition has positive leakage, which makes the
  privacy threshold three sharp. The development does not prove that every
  four-card coalition leaks, and it does not compute exact leakage for four
  through six reveals.

The recovery description uses the ramp parameters
`(t, r, n) = (3, 7, 8)`. The `ThresholdScheme` record has no recovery-threshold
field. For this instance, it packages the privacy cutoff and an eight-endpoint
decoder. The value `r = 7` comes from `pgl27_seven_reveal_class`, which proves
determination from seven reveals rather than implementing a seven-card
decoder.

## PGL(2,7) mathematical facts

The PGL case uses an orbit-class secret over the seventy four-element subsets
of the eight projective points. The theorem `orbit_class_split` proves that
twenty-eight subsets are equianharmonic. The theorem
`orbit_class_split_complement` proves that forty-two subsets are harmonic.
Every occurrence of the old `14+56` split must be replaced by `28+42`.

The main theorem chain includes:

- `pgl27_3transitive`
- `orbit_class_split` and `orbit_class_split_complement`
- `orbit_encodeK`
- `pgl27_run_recovers_class`
- `pgl27_seven_reveal_determines`
- `pgl27_seven_reveal_class`
- `pgl27_six_reveal_ambiguous`
- `pgl27_reveal_ambiguous`
- `pgl27_view_indep` and its coalition variants
- `pgl27_view_leakage_le`
- `pgl27_view_dep_k4` and `pgl27_view_leak_k4`
- `pgl27_view_indep_alldecks`
- `pgl27_view_indep_deck_prior`
- `pgl27_trace_secrecy`
- `pgl27_coalition_trace_secrecy`
- `pgl27_alldecks_trace_secrecy`
- `pgl27_alldecks_coalition_secrecy`
- `pgl27_deck_trace_secrecy`
- `pgl27_deck_coalition_secrecy`
- `pgl27_gen5_eq`
- `pgl27_card`
- `pgl27_word_mixing`
- `pgl27_endpoint_mixing`
- `pgl27_joint_mixing`

The paper cites the exact theorem used for each displayed claim. Rocq
identifiers remain in footnotes, theorem-index entries, or code listings.
Body prose uses mathematical names.

## Novelty policy

The novelty discussion is organized around four technical axes.

1. Formal verification of card-based cryptography
2. Group-parametric shuffle models
3. Machine-checked finite-step mixing bounds
4. Proof-assistant cryptography and trace security

The paper does not claim novelty for each axis separately. Prior work already
covers SAT-backed bounded verification, pen-and-paper permutation-group
models, and machine-checked random-walk results in other settings.

Until a repository-local novelty report is complete and can be reproduced,
the abstract and introduction use a descriptive claim:

> A Rocq framework that treats the shuffle group and shuffle law as
> first-class parameters, instantiated with exact coalition and trace privacy
> results and certified finite-step mixing bounds.

The accepted workshop abstract used "first formalization" wording. The
full-paper introduction is not drafted until an early full-text audit checks a
narrowed version of that claim. If the audit supports the claim, the full
paper preserves it with the verified scope. If the audit is inconclusive or
finds prior work, the full paper replaces it with the descriptive wording
above and states that the full paper sharpens the workshop abstract's scope.

The words "first", "first refereed", and equivalent priority wording require
the early audit and a fresh check near the submission date. Any approved
priority wording is limited to the verified combination, not an individual
axis.

The author's FORTE 2025 Rocq interpreter and trace-security work is a
foundation of the trace component. It is cited as prior work, not presented as
new in this paper.

## Repository layout

The paper lives in this repository under:

```text
pgg-smc/paper-wadt2026/
  main.tex
  sections/
    01-intro.tex
    02-model.tex
    03-framework.tex
    04-pgl27-construction.tex
    05-exact-security.tex
    06-finite-step-approximation.tex
    07-other-instances.tex
    08-methodology-artifact.tex
    09-related-work.tex
    10-conclusion.tex
  figures/
  artifact/
    THEOREM_INDEX.md
    CLAIM_MATRIX.md
    ASSUMPTIONS.md
  references.bib
  wadt2026-macros.sty
  Makefile
  .gitignore
```

The directory name is intentionally distinct from the existing
`pgg-smc/paper/` project. The paper plan does not move or reuse that directory.

The current official LNCS package supplies `llncs.cls` and
`splncs04.bst`. The project does not copy an older class file from the slide
repository unless the chairs confirm that version. Shared macros are copied
into the paper directory so that the build has no parent-directory path
dependency.

The default build should not require `minted` or `-shell-escape`. Rocq excerpts
use a production-safe listing mechanism unless the current Springer workflow
explicitly permits the existing setup.

## Section map

The author is handling the page-limit question separately. The allocations
below preserve the previous content budget and remain provisional until the
chairs reply.

| S | Content | Main sources | Planned pages |
|---|---|---|---:|
| 1 | Introduction. State the problem, the three contributions, the two shuffle models, and the security boundary. | Accepted abstract and verified literature | 2 |
| 2 | Protocol and security model. Define views, traces, coalitions, the exact law, the finite-step law, and the L1 convention. | `pgg_interface.v`, interpreter and session-type files | 2 |
| 3 | Framework and generic theorems. Present only the components used by the main proof chain. | Sharing framework, transitivity privacy, trace secrecy, weighted words | 2.5 |
| 4 | PGL(2,7) construction. Present the group action, orbit-class secret, the 28+42 split, and 3-transitivity. | `pgl27_group.v`, `pgl27_orbit.v` | 2 |
| 5 | Exact-shuffle correctness and security. Present the ramp, recovery, coalition privacy, and executed-trace secrecy under `U_G`. | PGL run, recovery, secrecy, and trace files | 3 |
| 6 | Finite-step approximation of the exact model. Present `mu^*200`, the L1 certificate, the endpoint and secret-prior product-law transfers, and the missing trace bridge. | `pgl27_mixing.v`, weighted-word framework | 2.5 |
| 7 | Other instances. Compare recovery, exact privacy, trace privacy, mixing, and trust-base coverage. Include Kim's in-kernel `L = 7` result and distinguish it from the assumed-certificate routes for S5 and S5xS5. | `instances/` | 1.5 |
| 8 | Methodology and artifact. Give reproduction data, the claim matrix, assumption reports, and AI-use methodology. | Git history, audit data, build metadata | 2 |
| 9 | Related work. Organize the discussion by the four novelty axes. | Full-text verified sources | 1.5 |
| 10 | Conclusion and future work. State the proven relation, the missing bridge, and the next research program. | Claim boundary and Section 6 | 1 |

The planned total is twenty pages before references and appendices. No
compression policy is chosen until the chairs answer the page question.

## Introduction plan

The introduction follows a problem-first order.

1. Card-based protocols realize information-theoretic computation with
   physical cards, while their security proofs are usually protocol-specific.
2. Existing mechanized work does not combine a reusable group-action model,
   executed-trace privacy, and a checked finite-step mixing certificate for a
   concrete card protocol.
3. A continuity paragraph explains that the workshop abstract illustrated
   the algebraic thesis with den Boer's protocol and S5. The PGL(2,7) case is
   the later concrete realization of that thesis with a complete exact
   security stack and a finite-step mixing certificate.
4. The paper introduces the framework and its five instances.
5. The PGL(2,7) case gives the exact-model correctness, ramp, and privacy
   results.
6. The finite-step result compares the executable 200-letter law with the
   exact uniform law.
7. The sibling-instance summary notes that Kim's biased five-card protocol
   already has an in-kernel `L = 7` finite-step bound. PGL is distinguished by
   attaching a larger non-abelian mixing certificate to the full exact
   security stack, not by being the development's only finite-step result.
8. The introduction states that approximate executed-trace secrecy remains
   unproved.
9. The final paragraph gives the paper organization.

The introduction contains no LLM priority claim. The methodology appears only
after the technical results.

## Framework coverage policy

The paper presents the following components fully because they carry the main
argument:

- `pgg_interface`
- `ThresholdScheme`, with the PGL-specific packaging limitation stated
- `transitivity_privacy`
- the piSMC runner layer
- `pgg_trace_secrecy`
- `pgg_weighted_words`

The paper gives only short context for:

- `MonodromyProfile`
- `SecurityWitness` and `SecurityExact`
- `ReconPlug`
- `pgg_collusion_bound`
- notation-only material from `pismc.v`

The paper does not credit the following material as part of its contribution:

- unused covering, genus, Klein, rigidity, and dropout packaging
- unused input-encoding and asymptotic-security records
- unused collusion headline theorems
- unused additive leakage machinery
- undeveloped algebraic-geometry recovery claims
- `pgl27_pgl2_order`, which has no consumer in the main proof chain

Section 8 discloses that `content_of` is duplicated in four instance files and
that the general mixing lemma is local to the PGL instance. It credits the
MathComp transitivity infrastructure and the standard library binary natural
number arithmetic as dependencies.

## Evidence and claim matrix

Every substantive claim belongs to one of four evidence classes.

| Evidence class | Required support |
|---|---|
| Kernel | Committed `Qed` theorem, source file, theorem name, and assumptions |
| Code or build | Reproducible command, fixed commit, and saved output or generated report |
| Literature | Full-text checked source with a verified citation locus |
| Limitation or disclosure | Explicit statement that the item is outside the model, unfinished, or not claimed |

The claim matrix records:

- the prose claim
- its model, either exact or finite-step
- its dealer law
- its secret prior
- its evidence class
- the exact source
- the permitted wording
- the relevant limitation

The matrix does not force every sentence to map to a kernel object. Repository
statistics use code or build evidence. Historical and novelty statements use
literature evidence. Model boundaries use explicit disclosures.

## Artifact and reproducibility requirements

The artifact statement includes:

- the exact git commit
- the Rocq, MathComp, infotheo, and system versions
- a single-threaded `make -j1` build command
- a theorem index for every displayed formal result
- a `Print Assumptions` summary
- the claim matrix
- the repository-local novelty report
- commands for regenerating statistics
- the source and method for effort accounting
- the status of any external certificate

The paper uses a paper-specific theorem index at
`pgg-smc/paper-wadt2026/artifact/THEOREM_INDEX.md`. It is generated from the
PGL instance, the four credited sibling instances, and the framework files
that support displayed results. It does not reuse
`pgg-smc/audit-inventory/THEOREM_INDEX.md`, because that index currently omits
PGL and includes unrelated developments. The paper plan must define the exact
roots before drafting Section 8. It must exclude the abelian, cyclic, monster,
oc, and star instances from paper statistics.

The paper distinguishes kernel-checked computation from an externally
generated certificate that is only checked or assumed by the development.
"Checked in Rocq" means checked by the kernel modulo the assumptions reported
for that exact theorem. For the PGL probability and mixing results, the
expected trust base includes the three classical `boolp` axioms. Group, orbit,
cardinality, and recovery results are expected to be closed under the global
context.

The assumption report is per credited theorem, not a tree-wide list. It must
identify which S5 and S5xS5 results depend on the Rayleigh, group-order, or
curve-realization assumptions. It must not imply that a credited result is
axiom-free until its own `Print Assumptions` output confirms that fact.
Conjectures and axioms in excluded framework demonstrations are listed
separately as excluded material. They are not attributed to unrelated paper
results.

The repository contains `security/pgg_schreier_test.v` with an `Admitted`
proof, but that file is outside `_CoqProject`. The artifact statement records
this fact so that a repository search is not mistaken for a build dependency.

For `pgl27_word_mixing`, the assumption report uses a small compile scratch
file with the project's `-R` flags and a `Print Assumptions` command. It does
not use `rocq_assumptions` through `rocq_query`, because that path timed out in
the audit. This scratch probe is read-only with respect to the formalization.

## Methodology and AI-use disclosure

Section 8 describes the workflow as:

> LLM-generated proof scripts and documentation drafts under human
> specification, review, and responsibility.

The human author owns the research questions, mathematical specification,
claim selection, acceptance decisions, citation verification, and final text.
The Rocq kernel checks accepted proof terms. The audit pipeline checks that
statements and prose remain aligned.

The paper does not use the phrases "agents as authors", "proof authorship",
or "first refereed development". LLM use is not listed in the contribution
paragraph.

The disclosure appears in Section 8 and in a separate AI-use statement placed
with the acknowledgements or other front or back matter required by the
current Springer policy. A separate Disclosure of Interests is included when
the venue template requires it.

## Formalization request workflow

The paper writer does not perform formalization work. If drafting exposes a
possible gap, the following decision process applies.

1. Compare the sentence with the exact theorem statement and assumptions.
2. Narrow or remove the sentence when the theorem proves less than the prose.
3. Use a read-only query or isolated probe when the statement, type, or
   dependency is unclear.
4. Create a formalization request only when the approved paper core cannot be
   stated accurately without a new or repaired result.
5. Exclude or downgrade the claim until another proving tool completes the
   request.
6. Check the returned theorem and assumptions before updating the paper.

Formalization requests live at:

```text
docs/superpowers/requests/YYYY-MM-DD-<topic>-formalization-request.md
```

Each request contains:

- the paper claim that needs support
- the current theorem and the exact shortfall
- the mathematical proposition to prove or repair
- a suggested Rocq statement
- the variables, hypotheses, relevant files, and related lemmas
- the required trust base and assumption policy
- acceptance criteria
- the paper locations to update after completion

The paper writer creates the request document only. The author gives it to a
separate proving tool. The paper writer does not open a proof task or edit the
formalization.

The missing approximate executed-trace bridge is already assigned to future
work. It does not trigger a formalization request for this paper.

## Figures and typesetting

The paper may reuse technical diagrams from the accepted presentation after
their labels and source files are checked. The preferred figures are:

- the group, representation, and shuffle-law pipeline
- the PGL orbit-class construction
- the exact-law and finite-step-law relation
- the recovery ramp
- the mixing convergence plot
- a compact cross-instance coverage table

Figures use vector PDF or TikZ when practical. Raster figures must remain
legible in print. Every figure is checked in color, grayscale, and at the final
column width. Labels use mathematical language rather than bare Rocq names.

Custom floats are avoided unless required by the current LNCS template.
The build must succeed without parent-directory assets and without manual file
copying.

## Voice and prose discipline

- The author uses personal "I" for research choices, responsibility, and
  credit.
- Reader-inclusive "we" is limited to mathematical constructions and proofs.
- LLM systems are tools, not authors.
- Theorem environments contain terse mathematical statements without status,
  motivation, or proof strategy.
- Body prose uses pen-and-paper concepts. Rocq identifiers appear in footnotes,
  listings, and the theorem index.
- Sentences stay short and direct.
- The paper avoids em dashes, semicolons, prose asides in parentheses, and
  unexplained abbreviations.
- Every drafted section receives a separate AI-ism and prose audit before it
  is accepted.

## FORTE prose baseline and AI-ism gate

The language baseline is the author's FORTE paper at
`~/Projects/aplas2024-poster/forteApr22/forteApr22.tex`. The WADT paper keeps
the same level of vocabulary and grammar. It may introduce new mathematical
terms required by the PGL development, but it does not raise the surrounding
language to a more ornate academic register.

The reference paper supplies these positive rules:

- Put the grammatical subject and main verb near the start of the sentence.
- Give one main idea to each sentence.
- Use direct verbs such as "define", "use", "prove", "show", "compare", and
  "compute".
- Introduce a technical term with a concrete explanation before relying on
  it.
- Lead into an equation or theorem with a plain sentence that states its
  purpose.
- Give each paragraph one job. Typical jobs are setting the problem, defining
  an object, stating a result, explaining evidence, or marking a limitation.
- Prefer a short sequence of connected sentences to one sentence with several
  nested clauses.
- Keep the exact mathematical term when a simpler substitute would change the
  claim. Simplify the grammar around the term instead.

The WADT paper follows the reference paper's language level rather than every
surface habit in that source. It uses the current name Rocq. It follows this
spec's solo-author voice policy. It also removes grammar errors, outdated
terminology, and inflated wording that may occur in the reference draft.

The AI-ism check is a mandatory detect-first gate. It runs after each section
draft and once over the complete paper. The check reports exact spans before
any prose is changed. It must flag:

- generic openings that could introduce any paper
- stock transitions such as "Moreover", "Furthermore", and "Consequently"
  when the logical relation is not needed
- claims of importance, novelty, robustness, or completeness that add no
  checked fact
- repeated three-part lists created for rhythm rather than content
- repeated restatement of the same result in nearby sentences
- excessive hedging and vague qualifiers
- nominalizations where a direct verb gives the same meaning
- sentences with several front-loaded or nested clauses
- repeated paragraph endings that merely announce significance
- repeated templates such as "This work", "This paper", or "It is worth
  noting"
- code identifiers in body prose
- unexplained technical terms
- em dashes, semicolons, and prose asides in parentheses

The audit fixes plain prose only. It does not rewrite mathematics, citations,
macro arguments, theorem statements, or `\coqin{}` content automatically.
Each accepted fix must preserve every claim, hedge, quantifier, citation, and
formula. A section is ready only when every finding is fixed or carries a
specific reason for keeping it.

## Citation and submission checks

Before submission, the paper must pass these checks:

1. Verify every citation against the full source text.
2. Verify the volume, year, pages, and publication metadata of the New
   Generation Computing version of Koch, Schrempp, and Kirsten against the
   publisher record. Then choose either that verified entry or the ASIACRYPT
   2019 entry and use it consistently.
3. Store the novelty report inside the repository with its query, date, source
   list, and verdicts.
4. Repeat the novelty search near submission because the LLM formalization and
   machine-checked cryptography literature changes quickly.
5. Recount files, lines, main theorems, agents, tokens, and audit statistics.
6. Verify every exact-model and finite-step-model label in the claim matrix.
7. Regenerate the assumption report at the fixed submission commit.
8. Run the per-section AI-ism gates, the final whole-paper AI-ism audit, the
   mathematical meaning audit, the citation audit, and the cross-reference
   audit. Compare the final prose with the FORTE language baseline.
9. Build from a clean checkout with the current official LNCS package.
10. Check vector output, grayscale legibility, minimum text size, bibliography,
    disclosures, and artifact links.
11. Confirm the anonymous status, appendix rule, template version, full-paper
    submission path, presenter eligibility, and page rule with the chairs.

No citation may ship from an abstract-only note or an inaccessible internal
wiki reference.

## Failure policy

- If a citation does not support a claim, narrow or remove the claim.
- If novelty evidence is incomplete, remove priority wording.
- If a Rocq theorem proves less than the draft says, change the draft first.
- If an essential theorem is absent, write a formalization request and exclude
  the dependent claim until the result returns.
- If a probe is inconclusive, do not state the inferred result as fact.
- If a venue rule is not public, record it as a submission dependency and ask
  the chairs.
- If the official template rejects a package or float, simplify the typesetting
  rather than preserve the old setup.
- If the paper becomes too dense after the chairs answer, make a new content
  decision. This spec does not preselect material to cut.

## Future work

The main future work is a separate two-model development. It will establish a
general theorem that transports finite-step shuffle convergence to approximate
view privacy and approximate executed-trace secrecy. That work can reorganize
the framework around two first-class models:

1. the exact uniform shuffle model
2. the realistic finite-step shuffle model

The desired theorem chain is:

```text
finite-step shuffle mixing
  -> secret-prior product-law proximity
  -> approximate view privacy
  -> approximate executed-trace secrecy
```

The future paper can then compare which instances support each arrow and which
security losses arise under measurable post-processing. This WADT paper proves
and explains the first two levels for PGL(2,7). It does not claim the final two
levels.

Other future directions remain secondary:

- completing the Barrington and NC1 compilation direction announced in the
  workshop abstract
- active security and compositional security
- quantitative leakage for four through six revealed cards
- algebraic-geometry recovery for feasible groups
- a quantum direction in one sentence only

## Out of scope

- Any change to a Rocq `.v` file
- A new approximate trace-secrecy theorem for this paper
- Repairing framework-wide zero-epsilon witness semantics
- Refactoring duplicated `content_of` definitions
- New algebraic-geometry code claims
- A proof-authorship or first-LLM-paper claim
- A full redesign around the two-model future-work program
- A page-budget reduction before the chairs answer

## Next step

After the author approves this written spec, invoke
`superpowers:writing-plans`. The plan covers the paper scaffold, source and
artifact inventory, section drafting order, citation verification, claim
matrix, LaTeX build, and final audits. The plan must not contain edits to the
formalization. Any necessary formal work is represented only by a separate
formalization request document for another proving tool.
