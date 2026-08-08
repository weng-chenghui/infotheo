# WADT 2026 Paper Framework Revision Design

Date: 2026-08-08

## Purpose

This revision removes material that describes the working process rather than
the research contribution. It also replaces the prose-heavy framework section
with a figure-led account of the architecture and a separate presentation of
the generic theorems. The related-work section will identify den Boer's
five-card trick as the first card-based cryptographic protocol.

The revision changes only the paper. It does not change the Rocq
formalization.

## Source Material

The paper source is:

- `pgg-smc/paper-wadt2026/main.tex`
- `pgg-smc/paper-wadt2026/references.bib`

The architecture figure comes from the frame titled `The specification: one
MonodromyProfile` in:

- `/Users/cheng-huiweng/Projects/aplas2024-poster/wadtSep17/slides.tex`

The figure will be adapted to the LNCS page width. Its record structure and
dependency arrows will be preserved. Beamer-specific formatting will not be
copied.

## Section Structure

The paper keeps one top-level section named `Framework and Generic Theorems`.
It will contain two clearly separated subsections:

1. `Framework Architecture`
2. `Generic Theorems`

This structure keeps the framework visible as a contribution without mixing
record architecture and mathematical results. The first subsection explains
what an instance supplies. The second subsection states what follows from
those components.

### Framework Architecture

The subsection contains four items in this order:

1. One short paragraph defines the boundary between the reusable framework and
   a protocol instance.
2. One TikZ figure presents the framework records and their dependencies.
3. One short paragraph explains how `PGGInterface`, `SecurityWitness`, and
   `ReconPlug` form the main profile.
4. One short paragraph places `SecurityExact`, `SecurityAsymptotic`,
   `ThresholdScheme`, and `InputEncoding` as supporting records.

The text will not describe every record field. It will not list proof-engine
details. It will explain only the role of each component in the paper's
framework.

The figure title is:

> Architecture of the group-parametric card-protocol framework.

The complete caption is:

> Architecture of the group-parametric card-protocol framework. Blue boxes
> denote the profile and its three component records. Green boxes denote
> supporting records. Arrows denote dependencies.

The caption contains only the figure name and the meaning of its visual styles.
It does not contain a takeaway, a contribution claim, or explanatory prose.

Blue boxes represent `MonodromyProfile` and its three direct components:
`PGGInterface`, `SecurityWitness`, and `ReconPlug`. Green boxes represent
`SecurityExact`, `SecurityAsymptotic`, `ThresholdScheme`, and `InputEncoding`.
Arrows point from a supporting or component record toward the record that uses
it.

### Transition to Generic Theorems

The subsection boundary must make the change of subject explicit. The
transition is:

> The records above specify one protocol instance. The next subsection turns
> from the architecture to the generic theorems derived from these records.

The paper has one author. This transition and the rest of the paper must not
use authorial `we` or `our`.

### Generic Theorems

The current prose account will be replaced by three formal statements. Each
statement will use a theorem or proposition environment. Its title will carry
a footnote with the Rocq file path and theorem name.

#### Generic coalition privacy

The statement says that a uniform shuffle from a group with a
`t`-transitive action makes the view of every coalition of size at most `t`
independent of the secret, under the distinct-card encoding condition used by
the formal theorem.

Formal source:

- `pgg-smc/reconstruct/transitivity_privacy.v`
- `ttrans_view_indep_gen`

The paper statement must preserve the hypotheses of the formal result. It must
not imply privacy for repeated cards, a nonuniform shuffle, or coalitions larger
than `t`.

#### Generic trace lifting

The statement says that view privacy yields equality between the conditional
entropy of the secret given the executed trace and the entropy of the secret.
It must state the trace-to-view correspondence required by the formal theorem,
including the cancellation condition. It must not replace those hypotheses
with the weaker sentence that the trace is merely a function of the view.

Formal source:

- `pgg-smc/security/pgg_trace_secrecy.v`
- `trace_secrecy_of_view`

#### Finite-distribution data processing

The statement says that for any map `f`, pushing two finite distributions
through `f` does not increase their unhalved L1 distance. This result provides
the generic link from a group-level distribution bound to an endpoint bound.

Formal source:

- `pgg-smc/security/pgg_collusion_bound.v`
- `var_dist_fdistmap`

Explanations of how the PGL instance uses these results belong after the formal
statements. The theorem bodies contain only mathematical claims. They do not
contain proof strategy, implementation status, motivation, or roadmap text.

## Removal of Methodology and Artifact Section

The complete `Methodology and Artifact` section will be removed. This includes:

- the fixed commit identifier
- operating-system and toolchain details
- the single-threaded build explanation
- theorem-index and claim-matrix production details
- the procedure for `Print Assumptions`
- the excluded test-file discussion
- the long account of the LLM-assisted workflow

Any roadmap sentence or cross-reference that names this section will be
updated. `Other Instances` will lead directly to `Related Work`.

The `Artifact availability` subsubsection at the end of the paper will also be
removed. A one-sentence footnote will be attached to the first mention of the
Rocq development in the introduction. It will say that the companion artifact
contains the source, theorem index, assumption report, and build instructions.
It will not repeat hardware data, workflow history, or release procedures.

The short AI-use statement remains under acknowledgements. It will use
single-author language and retain the author's responsibility for the final
claims, citations, and text.

## Related Work

The first paragraph of `Related Work` will begin with the historical origin of
the field. It will state that den Boer introduced the first card-based
cryptographic protocol with the five-card trick. It will then explain in one
short sentence that the protocol securely computes AND with five cards. The
claim will cite `denBoer1989`.

Before drafting, the priority claim and bibliographic metadata will be checked
against the original publication and a reliable historical source. The wording
must remain limited to the first card-based cryptographic protocol. It must not
claim priority over all forms of physical cryptography or secure computation.

The paragraph will then move to later reductions in card count and broader
function classes. The remaining related work will retain the current groups of
sources:

- bounded protocol search and model checking
- physical implementations of structured shuffles
- machine-checked probability and mixing results
- proof-assistant frameworks for cryptography

Repeated descriptions of the present paper will be shortened. The section will
compare the cited methods with the paper only where the distinction helps place
the contribution.

## Writing Rules

The revision follows the language level of the author's FORTE paper at:

- `/Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex`

The prose must satisfy these rules:

- Use short sentences and common grammatical forms.
- Keep technical terms only when they name a concept used by the paper.
- Use single-author voice. Do not use authorial `we` or `our`.
- Avoid AI-style throat-clearing, inflated claims, repeated summaries, and
  vague transitions.
- Do not use em dashes or semicolons.
- Keep theorem statements terse and mathematical.
- Place motivation, scope, and interpretation outside theorem blocks.
- Preserve every existing security qualification concerning the secret prior,
  dealer law, shuffle law, adversary model, and reveal boundary.

## Files and Change Boundary

The paper revision may edit:

- `pgg-smc/paper-wadt2026/main.tex`
- `pgg-smc/paper-wadt2026/references.bib` only if citation verification finds
  incorrect den Boer metadata

The revision must not edit any `.v` file. It must not submit a new
formalization request unless comparison with the three planned statements
reveals that the named formal sources do not support them. The current source
inspection found a direct formal source for all three statements, so no
formalization request is expected.

No unrelated paper sections will be rewritten. Small changes to the abstract,
introduction roadmap, section transitions, and conclusion are allowed only
when needed to keep the revised structure consistent.

## Verification

The revision is complete only after all of the following checks pass:

1. Rebuild the PDF with `latexmk` using a clean enough run to expose stale
   cross-references.
2. Check the log for undefined references, undefined citations, and overfull
   boxes.
3. Render and inspect the page containing the architecture figure. Confirm that
   every label, arrow, and color distinction is readable at normal page size.
4. Confirm that the caption contains only the figure name and the meanings of
   colors and arrows.
5. Confirm that each of the three new formal statements has a title footnote
   with the correct Rocq file path and theorem name.
6. Compare each paper statement with its formal source and confirm that all
   hypotheses and conclusions match.
7. Search the paper for stale references to `Methodology and Artifact`,
   `sec:method`, and the removed artifact subsubsection.
8. Search authorial prose for `we` and `our`. Ignore occurrences inside cited
   titles only.
9. Run the paper's AI-ism and plain-language checks. Review every hit instead of
   applying blind replacements.
10. Confirm that `Related Work` cites den Boer and limits the priority claim to
    the first card-based cryptographic protocol.
11. Read the full modified `main.tex` and inspect the rebuilt PDF before
    committing the paper change.

## Acceptance Criteria

The revision is accepted when:

- the methodology section is absent
- artifact information appears only as one introduction footnote
- the short AI-use acknowledgement remains
- the framework architecture is presented by the adapted slide figure and two
  short explanatory paragraphs
- the figure is named as the architecture of the group-parametric card-protocol
  framework
- the caption explains only the visual styles
- a subsection boundary and explicit transition separate architecture from
  generic theorems
- all three generic statements are formal blocks with source footnotes
- Related Work identifies den Boer within the agreed priority scope
- the prose uses simple single-author language
- the LaTeX build and visual checks pass
- no Rocq formalization file changes

## Out of Scope

This revision does not add a new protocol result, strengthen a security claim,
change the PGL construction, alter the exact and finite-step distinction, or
modify the formalization. It does not restore the detailed artifact narrative
elsewhere in the paper. Page-count reduction is not a design requirement for
this round.
