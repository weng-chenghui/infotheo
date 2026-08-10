# WADT 2026 piSMC and Structural Follow-up Design

Date: 2026-08-10

Status: for user review

Targets:

- `pgg-smc/paper-wadt2026/main.tex`
- `pgg-smc/paper-wadt2026/references.bib`

This revision changes only the paper. It does not change any Rocq file.

## Purpose

This revision makes four focused improvements.

1. It shows how the piSMC language models one card-protocol participant and
   how interpretation produces the traces used by the privacy theorems.
2. It moves the framework architecture figure to the start of the architecture
   account and keeps a clear boundary before the generic theorems.
3. It gives the PGL source map an academic role as a claim-to-proof map and
   makes the other-instances section match its title.
4. It places the paper against Shinagawa's unified model for card protocols
   while preserving den Boer's historical priority.

The revision also corrects the description of the five-card leakage figure
after the all-reveal theorem landed. The figure remains an example with card
rows and bit values. The theorem and its footnote continue to cover all fixed
reveal sets.

## Baseline and execution order

The five-card all-reveal work has already landed in these commits:

- `780668e4`: `leak_k3_gap`
- `a84c0095`: `leak_view_set`
- `1db52837`: paper claim and footnote

This design starts from that state. It preserves the new Rocq names, the
contribution bullet, the thirty-two-set footnote, and the three-card equality
sentence.

The all-reveal work was implemented before this design, as required. The
implementation plan for this design must inspect the current paper instead of
using line numbers from an older revision.

## Fixed section order

The top-level section order stays as follows.

1. Introduction
2. Protocol and Security Model
3. Framework and Generic Theorems
4. A First Instance: The Five-Card Family
5. The PGL Construction
6. Correctness, Recovery, and Uniform-Shuffle Privacy
7. Word-Shuffle Approximation of the Uniform-Shuffle Model
8. Other Instances and Trust Base
9. Related Work
10. Conclusion and Future Work

The five-card and PGL construction sections therefore precede both PGL
security analyses. The uniform-shuffle and finite-word sections remain
adjacent. No instance section may be inserted between them.

The final paragraph of the uniform-shuffle section must state that its results
use a uniform group element. The opening of the finite-word section must then
ask how a finite generator word approximates that ideal distribution. This
link presents the finite-word analysis as the realization of the preceding
uniform model.

## 1. Executable protocol model in piSMC

### Placement

Insert the piSMC example in `Protocol and Security Model`. Its exact position
is after the paragraph that defines the individual executed trace and the
coalition trace. It appears before the paragraph that introduces the primary
execution distribution.

This placement gives the reader the following order.

1. A coalition view is defined.
2. The interpreter and executed trace are introduced.
3. One actual process shows what the interpreter executes.
4. The security distributions and trace privacy are defined.

The example does not create a subsection. It does not restore the removed
methodology section.

### Exact listing

The paper uses the actual Rocq definition from
`pgg-smc/protocol/card_exchange_pismc.v`. It keeps the type signature and the
piSMC syntax.

```coq
Definition exchange_player (i : 'I_T)
    : sproc pgg_dtype data (player_idx i) :=
  \pi{ Receive<dealer_idx> #my_hand =>
     Receive<dealer_idx> $shuffle_idx =>
     Reveal<verifier_idx> &(nth ord0 my_hand shuffle_idx) ;
     Finish }.
```

The lead-in sentence carries one source footnote. The footnote names the file
and the three definitions `exchange_dealer`, `exchange_player`, and
`exchange_verifier`. The body listing shows only `exchange_player` because it
is the shortest process that displays the protocol's main information flow.

### Operational reading

One short paragraph explains the notation in plain language.

- `#` marks the dealt hand.
- `$` marks the public shuffle index.
- `&` marks the revealed card position.
- The player receives the hand and the index, selects one entry, reveals that
  entry to the verifier, and finishes.
- The interpreter records the received values in the player's trace.
- The verifier's `Observe` action receives the value sent by `Reveal`.

The paragraph ends by connecting the levels used by the paper:

```text
card-protocol action -> piSMC program -> interpreter trace -> trace theorem
```

The paper need not print this arrow chain as a display. It states the same
connection in one or two sentences.

### Scope limit

The example does not explain fuel, session-environment indices, the complete
DSL grammar, interpreter implementation, or all three programs. Those details
do not help the reader understand the paper's security model.

Section 3.1 retains only one backward reference to this example when it says
that the protocol-layout record supplies executable participant processes.
It does not introduce the interpreter a second time.

## 2. Five-card leakage figure after the all-reveal theorem

The TikZ figure keeps every existing card row, covered card, suit, and printed
bit value. These examples help the reader see the leakage ramp.

The body text distinguishes the theorem from the examples.

- The master theorem quantifies every one of the thirty-two fixed position
  sets.
- The figure shows selected representative reveal cases.
- The gapped three-card case has the same value as the drawn consecutive
  three-card case, so the figure does not need another row.
- Only the two-card value depends on whether the two positions are adjacent or
  at cyclic distance two.

The current master-theorem footnote stays. It continues to name
`leak_view_set`, `leak_k3_gap`, the six earlier anchor lemmas, and
`H_secret` in `five_card_leakage.v`.

The caption becomes:

> Mutual-information leakage for selected reveal cases. Blue card backs mark
> unrevealed positions.

The explanation that the decimal values evaluate proved closed forms stays in
body prose. The caption contains only the figure name and the meaning of the
blue card backs.

## 3. Framework architecture before the record listing

### Name and figure role

The figure is named the architecture of the group-parametric card-protocol
framework. It is not named the `MonodromyProfile` architecture.
`MonodromyProfile` is the central bundle, while the figure covers the main
records and the supporting records around it.

This design supersedes decision D8 of
`docs/superpowers/specs/2026-08-09-wadt2026-architecture-section-design.md`
only. That decision placed the architecture figure at the end of Section 3.1.
All other compatible decisions in that design remain in force.

### Block order

`Framework Architecture` uses this order.

1. A short opener introduces one profile and the bridge table.
2. The model-to-record bridge table appears.
3. The architecture figure appears.
4. One short paragraph explains the record dependencies shown by the figure.
5. The `MonodromyProfile` and derived-protocol listing appears.
6. The three proof obligations appear.
7. A short paragraph explains the derived protocol wiring.
8. The security-witness mechanism table appears.
9. One paragraph explains the optional committed-input encoding.
10. One sentence closes the framework account and introduces the next
    subsection.

The architecture figure therefore appears after `tab:bridge` and before the
record listing. The PDF must preserve this visual order. Source order alone is
not enough.

### Figure caption

The caption is:

> Architecture of the group-parametric card-protocol framework. Blue boxes
> are profile records, green boxes are supporting records, and arrows are
> dependencies.

The caption contains only the figure name and the meanings of colors and
arrows. The body paragraph explains the roles of the records.

### Framework and theorem boundary

The current subsection `Generic Theorems` remains. Every generic theorem
statement, formula, hypothesis, and formal-source footnote remains unchanged.

The last sentence of Section 3.1 is:

> This completes the framework description. The next subsection states the
> generic theorems.

This sentence and the subsection heading make the subject change explicit.
The architecture discussion does not continue after the heading.

## 4. PGL claim-to-proof map

### Placement and purpose

Move `tab:source-index` from the end of the current other-instances section to
the end of the finite-word section. It appears after Theorem B, its proof
summary, and the paragraph that limits the finite-word result to the fixed
representative dealer.

The lead-in explains its academic purpose:

> The PGL argument has four proof layers: construction, recovery, privacy, and
> finite-word transfer. Table X maps the mathematical claims used by Theorems
> A and B to the Rocq results that establish them.

The table is a claim-to-proof map. It is not an artifact inventory, a theorem
count, or a development report.

### Contents

The table remains specific to the PGL results. Its four groups stay:

- Construction
- Correctness and recovery
- Privacy
- Mixing and transfers

The five-card `leak_view_set` theorem does not enter this table because its
source is already given at the five-card claim. The table does not add file
statistics, implementation status, or proof-authoring information.

The caption becomes:

> Rocq sources for the PGL results.

Use `[H]` so the table remains before the next section. The existing `float`
package already supplies this placement. The implementation must inspect the
rendered page. If the table exceeds the text height, the implementation stops
and returns to the design rather than silently allowing it to cross the
section boundary.

## 5. Other instances and trust base

Rename the section to:

```latex
\section{Other Instances and Trust Base}\label{sec:instances}
```

The label stays unchanged. Existing references therefore remain valid.

The section contains:

- the five-instance comparison table
- the scope of each instance's proved results
- the global assumptions used by the development
- the separate Rayleigh premise used by the `S_5` and `S_5 x S_5` instances
- the fact that the PGL mixing proof does not use that Rayleigh premise
- the spectral summaries for `S_5` and `S_5 x S_5`

The section does not contain the PGL source table after the move. It also does
not contain methodology, artifact procedures, LLM workflow, theorem counts,
file counts, hardware details, or build history.

## 6. Related work

### Den Boer priority

Keep the current opening statement that den Boer introduced the first
card-based cryptographic protocol with the five-card trick. Keep the priority
claim limited to the first card-based cryptographic protocol. Do not broaden
it to physical cryptography, secure computation, group-based protocols, or all
card protocols.

The existing citations `denBoer1989` and `KochFUN2021` remain attached to the
historical statement.

### Shinagawa's unified protocol model

Add Shinagawa's 2021 paper before the current graph-automorphism discussion.
The new paragraph states two facts.

1. Shinagawa gives a unified protocol model in which a card-based protocol is
   specified by a deck and a set of operations.
2. The model covers binary cards, regular polygon cards, and dihedral cards.

The comparison then states the different framework boundaries.

- Shinagawa varies the card type and the allowed physical operations.
- This paper varies the finite group, its permutation action, the shuffle
  distribution, and the reconstruction map.
- This paper connects those parameters to executable traces and
  machine-checked privacy and mixing results.

The paragraph does not compare card counts or efficiency. It does not claim
that either framework replaces the other. It does not make an absence claim
about Shinagawa's security proofs or tool support.

The verified bibliography entry is:

```bibtex
@article{Shinagawa2021,
  author  = {Kazumasa Shinagawa},
  title   = {Card-based Cryptography with Dihedral Symmetry},
  journal = {New Generation Computing},
  volume  = {39},
  pages   = {41--71},
  year    = {2021},
  doi     = {10.1007/s00354-020-00117-9}
}
```

Metadata and the two model claims were checked against the published
open-access version of record. The stored research record is
`Shinagawa2021-dihedral-symmetry` in the personal research knowledge base.

The remaining related-work paragraphs keep their present roles:

- bounded protocol search and model checking
- graph and hypergraph automorphism shuffles
- closed shuffles and their applications
- machine-checked probability and mixing results
- proof-assistant frameworks for cryptography
- the FORTE interpreter and trace semantics

## Writing rules

The prose follows the language level of the author's FORTE paper:

- `/Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex`

Apply these rules while drafting, not only in a cleanup pass.

- Use short sentences and common grammatical forms.
- Keep one main idea per sentence.
- Keep technical terms only when they name a concept used by the paper.
- Use single-author voice. Do not use authorial `we` or `our`.
- Use `I` only for the author's choices or contributions.
- Use concepts in body prose and keep Rocq identifiers in listings,
  `\coqin{}` spans, tables, or source footnotes.
- Avoid throat-clearing, inflated significance, vague transitions, repeated
  summaries, compulsive three-part rhetoric, and unsupported hedges.
- Do not use em dashes or semicolons.
- Do not use `Moreover`, `Furthermore`, `Consequently`, `It is worth noting`,
  `delve`, `pivotal`, `crucial`, `groundbreaking`, `comprehensive`, `robust`, or
  `seamless` as automatic prose glue.
- Keep theorem statements terse and mathematical.
- Keep motivation, scope, proof status, and interpretation outside theorem
  blocks.
- Preserve every qualification about the secret prior, dealer distribution,
  shuffle distribution, adversary model, coalition size, and reveal boundary.
- Captions contain only the figure or table name and the meanings of visual
  styles when a style key is needed.

The AI-ism check is detect-first. Every match is read in context. The
implementation does not apply blind replacements inside math, macro arguments,
code listings, citations, or bibliography titles.

## Change boundary

Allowed edits:

- `pgg-smc/paper-wadt2026/main.tex`
- `pgg-smc/paper-wadt2026/references.bib`

Forbidden edits:

- every `.v` file
- the all-reveal design and implementation plan
- generated artifact reports
- unrelated paper sections

No formalization request is needed. Every Rocq object named by this design
already exists. The Shinagawa addition is a literature change only.

The abstract, theorem statements, PGL formulas, five-card theorem footnote,
and conclusion remain unchanged except for a label-based transition or
cross-reference that the table move strictly requires. Existing future-work
items remain.

## Verification

The implementation is complete only after all checks below pass.

1. Confirm the top-level section order with `rg` and confirm that the
   uniform-shuffle and finite-word sections are adjacent.
2. Confirm that the exact `exchange_player` listing matches
   `card_exchange_pismc.v` token for token, apart from LaTeX listing
   delimiters.
3. Confirm that the piSMC source footnote names the correct path and the three
   process definitions.
4. Confirm that the five-card figure retains all six card rows and all printed
   bit values.
5. Confirm that the five-card body distinguishes all thirty-two sets from the
   selected cases drawn in the figure.
6. Confirm that `leak_view_set`, `leak_k3_gap`, the existing anchor names, and
   `H_secret` remain in the five-card source footnote.
7. Confirm in the PDF that the bridge table, architecture figure, record
   listing, and generic-theorem heading occur in that order.
8. Confirm that every generic theorem statement and formalization footnote is
   unchanged.
9. Confirm in the PDF that the PGL claim-to-proof table appears before
   `Other Instances and Trust Base` and fits within the text area.
10. Confirm that the source table still contains all four groups and every
    current PGL Rocq name.
11. Confirm that the other-instances section contains the instance table,
    trust base, and the `S_5` and `S_5 x S_5` summaries.
12. Confirm that `references.bib` contains one `Shinagawa2021` entry with the
    verified DOI and metadata.
13. Confirm that Related Work preserves the limited den Boer priority claim
    and compares the two frameworks only by their parameters and outputs.
14. Run the AI-ism scan over changed prose. Review each match by hand:

    ```sh
    rg -n -i '\b(we|our)\b|—|;|Moreover|Furthermore|Consequently|It is worth noting|delve|pivotal|crucial|groundbreaking|comprehensive|robust|seamless' main.tex
    ```

15. Build from `pgg-smc/paper-wadt2026/`:

    ```sh
    latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
    ```

16. Check `main.log` for undefined references, undefined citations, multiply
    defined labels, errors, and overfull boxes.
17. Render and inspect the pages containing the piSMC listing, the five-card
    figure, the architecture figure, the PGL source table, and Related Work.
18. Read the complete modified `main.tex` before committing. Compare every
    changed claim and hedge with the old text and the source named by this
    design.

## Acceptance criteria

The revision is accepted when all of the following statements hold.

- The paper shows one real piSMC program and explains how it yields an
  executed trace.
- The five-card figure remains a useful visual example without claiming to
  display all thirty-two sets.
- The architecture figure appears near the start of Section 3.1 and is named
  for the full framework.
- The start of `Generic Theorems` is unmistakable and the theorem statements
  are unchanged.
- The uniform and finite-word PGL analyses remain adjacent and explicitly
  connected.
- The PGL source table is motivated as a claim-to-proof map and appears with
  the PGL analysis.
- Section 8 contains only other instances and the trust base described above.
- Related Work includes den Boer's limited priority claim and a verified,
  fair comparison with Shinagawa 2021.
- The prose matches the simple language level of the FORTE paper and passes a
  detect-first AI-ism review.
- The PDF builds and the five inspected areas are readable.
- No Rocq file changes.
