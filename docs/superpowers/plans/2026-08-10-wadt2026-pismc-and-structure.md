# WADT 2026 piSMC and Structure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Revise the WADT 2026 paper so that it shows one executable piSMC process, explains record packing without printing the abstract record, keeps the two PGL shuffle analyses adjacent, moves the PGL claim map to the PGL argument, and adds the verified Shinagawa 2021 comparison.

**Architecture:** This is a paper-only revision. Four sequential tasks edit the model, framework, PGL structure, and related work. Each task rebuilds the PDF and commits an independently reviewable state. A final task rereads the source, compares protected theorem text, runs the prose checks, and inspects rendered pages.

**Tech Stack:** LNCS LaTeX, BibTeX with `splncs04`, TikZ, `listings`, `latexmk`, Poppler rendering, ripgrep, and read-only Rocq source inspection.

## Global Constraints

- Authoritative design: `docs/superpowers/specs/2026-08-10-wadt2026-pismc-and-structure-design.md` at or after commit `57065c5b`.
- Modify only `pgg-smc/paper-wadt2026/main.tex` and `pgg-smc/paper-wadt2026/references.bib`.
- Do not modify any `.v` file. Do not create a formalization request.
- Preserve unrelated worktree changes. Stage only the files named by the current task.
- Use `apply_patch` for source edits. Do not rewrite `main.tex` wholesale.
- Use content anchors and labels. Old line numbers are not authoritative.
- Preserve every generic theorem statement, formula, hypothesis, label, and formal-source footnote.
- Preserve the landed five-card theorem names and their full source footnote.
- Keep all six five-card example rows and their printed bit values.
- Hide the abstract `Record MonodromyProfile` declaration and its derived wiring code.
- Keep the concrete `five_card_profile` listing and its source footnote.
- Keep the uniform-shuffle and finite-word sections adjacent.
- Use single-author voice. Do not add authorial `we` or `our`.
- Follow the language level of `/Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex`.
- Use short sentences and common grammar. Keep one main idea per sentence.
- Do not add em dashes or prose semicolons.
- Apply the AI-ism scan detect-first. Review hits in context.
- Captions contain only the name and any needed visual-style key.
- Page count is not a constraint. Readability and section structure are constraints.
- Baseline build on 2026-08-10: `latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex` exits 0 and produces 22 pages.
- Baseline has one existing `Overfull \hbox`, 37.19664pt in the recovery-ramp caption. Do not add another overfull warning.
- Do not stage generated LaTeX files.

## File Map

- `pgg-smc/paper-wadt2026/main.tex`: all changed prose, listings, figures, tables, headings, labels, and citations.
- `pgg-smc/paper-wadt2026/references.bib`: the new verified `Shinagawa2021` entry.
- `pgg-smc/protocol/card_exchange_pismc.v`: read-only source of the exact player process.
- `pgg-smc/instances/denboer1989/five_card_leakage.v`: read-only source of the landed leakage results.

---

### Task 1: Show the executable player and qualify the five-card examples

**Files:**

- Modify: `pgg-smc/paper-wadt2026/main.tex`, Sections 2 and 4
- Read: `pgg-smc/protocol/card_exchange_pismc.v`, `exchange_player`

**Interfaces:**

- Consumes: the executed-trace paragraph, `fig:fivecard-leakage`, and the landed all-reveal footnote.
- Produces: one exact piSMC listing, one operational explanation, and an honest distinction between the all-set theorem and selected drawn cases.

- [ ] **Step 1: Verify the current paper lacks the piSMC example**

Run:

```sh
test "$(rg -c -F 'Definition exchange_player' pgg-smc/paper-wadt2026/main.tex || true)" -eq 1
```

Expected: FAIL because the count is 0.

Run:

```sh
rg -n -F 'quantifies every reveal pattern' pgg-smc/paper-wadt2026/main.tex
rg -n -F 'one machine-checked value per reveal pattern' pgg-smc/paper-wadt2026/main.tex
```

Expected: both current overstatements are present.

- [ ] **Step 2: Insert the exact player process after the executed-trace paragraph**

Use `apply_patch`. Insert the following before `The primary execution distribution`:

```latex
The following player process makes this execution model
concrete.\footnote{Formalized in
\path{pgg-smc/protocol/card_exchange_pismc.v} as
\coqin{exchange\_dealer}, \coqin{exchange\_player}, and
\coqin{exchange\_verifier}.}

\begin{lstlisting}
Definition exchange_player (i : 'I_T)
    : sproc pgg_dtype data (player_idx i) :=
  \pi{ Receive<dealer_idx> #my_hand =>
     Receive<dealer_idx> $shuffle_idx =>
     Reveal<verifier_idx> &(nth ord0 my_hand shuffle_idx) ;
     Finish }.
\end{lstlisting}

In the listing, \coqin{\#} marks a dealt hand, \coqin{\$} marks the
public shuffle index, and \coqin{\&} marks a card position. The player
receives the hand and the index, selects one entry, and reveals it to the
verifier. The verifier's observation receives this entry. The interpreter
records both received values in the player's trace. The trace-privacy
theorem therefore concerns the execution of this process, not only a static
distribution of cards.
```

Do not add a subsection or another process listing.

- [ ] **Step 3: Separate the all-set theorem from the selected examples**

Replace the lead sentence before the existing master-theorem footnote with:

```latex
The master theorem quantifies every fixed reveal set exactly.
```

Keep the footnote unchanged. After it, add:

```latex
Figure~\ref{fig:fivecard-leakage} shows selected cases.
```

Keep every TikZ node and bit label. Replace the caption with:

```latex
\caption{Mutual-information leakage for selected reveal cases. Blue card
backs mark unrevealed positions.}
```

Replace the sentence after the figure with:

```latex
Every three-card reveal leaks the same
$\tfrac65-\tfrac{9}{20}\log 3$ bits. The figure draws the consecutive
case, and the gapped case has the same value. Only the two-card value
depends on the pattern's shape.
```

- [ ] **Step 4: Verify the listing and protected evidence**

Run:

```sh
rg -n -A7 -F 'Definition exchange_player' pgg-smc/paper-wadt2026/main.tex
sed -n '239,245p' pgg-smc/protocol/card_exchange_pismc.v
rg -n -F 'leak\_view\_set' pgg-smc/paper-wadt2026/main.tex
rg -n -F 'leak\_k3\_gap' pgg-smc/paper-wadt2026/main.tex
rg -n -F 'H\_secret' pgg-smc/paper-wadt2026/main.tex
test "$(rg -c -F 'quantifies every reveal pattern' pgg-smc/paper-wadt2026/main.tex || true)" -eq 0
test "$(rg -c -F 'one machine-checked value per reveal pattern' pgg-smc/paper-wadt2026/main.tex || true)" -eq 0
```

Expected: the listing matches the Rocq source, the evidence names remain, and both negative tests pass.

- [ ] **Step 5: Build and commit Task 1**

Run from `pgg-smc/paper-wadt2026/`:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
grep -E 'LaTeX Warning:.*(undefined|multiply)|Citation.*undefined|Reference.*undefined' main.log
grep -c 'Overfull \\hbox' main.log
```

Expected: build exit 0, no undefined warnings, and overfull count 1.

Then run from the repository root:

```sh
git diff --check -- pgg-smc/paper-wadt2026/main.tex
git diff -- pgg-smc/paper-wadt2026/main.tex
git add -- pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git commit -m "paper: connect piSMC execution to traces"
```

---

### Task 2: Lead with the architecture and explain record packing in prose

**Files:**

- Modify: `pgg-smc/paper-wadt2026/main.tex`, Section 3.1 only
- Preserve: the complete `Generic Theorems` subsection

**Interfaces:**

- Consumes: `tab:bridge`, `fig:framework-architecture`, the obligation list, `tab:witness-mechanism`, and the later `five_card_profile` listing.
- Produces: a figure-led architecture account with no abstract record listing, two short record-packing paragraphs, a forward reference to the concrete profile, and a clear theorem boundary.

- [ ] **Step 1: Verify the abstract record is currently printed**

Run:

```sh
rg -n -F 'Record MonodromyProfile' pgg-smc/paper-wadt2026/main.tex
rg -n -F '\subsection{Generic Theorems}' pgg-smc/paper-wadt2026/main.tex
```

Expected: both are present. The current `HEAD` is the protected-text baseline for this task.

- [ ] **Step 2: Move the architecture figure after the bridge table**

Use `apply_patch` to move the full environment labeled `fig:framework-architecture` immediately after the table labeled `tab:bridge`. Change both the bridge table and architecture figure placements to `[H]` so their rendered order matches their source order. Keep every table cell, TikZ node, and arrow. Set the figure caption to:

```latex
\caption{Architecture of the group-parametric card-protocol framework.
Blue boxes are profile records, green boxes are supporting records, and
arrows are dependencies.}
```

- [ ] **Step 3: Remove the abstract listing and add the prose account**

Delete the block from `The central record and its derived protocol follow` through its `\end{lstlisting}`. This removes the listing-only source footnote.

After the moved figure, insert:

```latex
The profile packs the group action and its generators, the secret type, the
protocol layout, the shuffle-security evidence, and the reconstruction
component. The layout supplies the participant processes. The security
evidence supplies an endpoint bound. The reconstruction component supplies
the threshold scheme and decoder.

Packing these choices in one profile keeps the participants, verifier,
recovery map, privacy threshold, and shuffle bound tied to the same
instance. Each instance discharges the three obligations below once. Later
definitions can then use the packed components without repeating them.
```

- [ ] **Step 4: Shorten the prose around the preserved anchors**

Keep the obligation list. Change its lead-in to `A profile has three proof obligations.` Delete the long paragraph beginning `Once the record is filled`.

Replace the interpreter and reconstruction paragraph with:

```latex
The layout supplies the executable processes described in
Section~\ref{sec:model}. The group action and shuffle distribution fix the
dealing rule and endpoint bound. The reconstruction component chooses the
decoder, so profiles over the same group can use different reconstruction
schemes.
```

Replace the witness-table lead-in with:

```latex
The security witness can carry exact evidence, asymptotic evidence, or
both. Table~\ref{tab:witness-mechanism} shows the combinations used by the
five instances in this paper.
```

Keep the witness table and committed-input paragraph. After that paragraph, add:

```latex
Section~\ref{sec:fivecard} gives a concrete packing example in the
definition of the five-card profile.
```

Remove the old late copy of the architecture figure.

- [ ] **Step 5: Add the explicit theorem boundary and compare protected text**

Immediately before `\subsection{Generic Theorems}`, insert:

```latex
This completes the framework description. The next subsection states the
generic theorems.
```

Run before committing:

```sh
diff -u \
  <(git show HEAD:pgg-smc/paper-wadt2026/main.tex | sed -n '/\\subsection{Generic Theorems}/,/\\section{A First Instance: The Five-Card Family}/p') \
  <(sed -n '/\\subsection{Generic Theorems}/,/\\section{A First Instance: The Five-Card Family}/p' pgg-smc/paper-wadt2026/main.tex)
```

Expected: no diff.

- [ ] **Step 6: Verify, build, inspect, and commit Task 2**

Run:

```sh
test "$(rg -c -F 'Record MonodromyProfile' pgg-smc/paper-wadt2026/main.tex || true)" -eq 0
test "$(rg -c -F 'Definition five_card_profile' pgg-smc/paper-wadt2026/main.tex)" -eq 1
bridge_line=$(rg -n -F '\label{tab:bridge}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
figure_line=$(rg -n -F '\label{fig:framework-architecture}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
theorem_line=$(rg -n -F '\subsection{Generic Theorems}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
test "$bridge_line" -lt "$figure_line"
test "$figure_line" -lt "$theorem_line"
```

Build from the paper directory:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
grep -E 'LaTeX Warning:.*(undefined|multiply)|Citation.*undefined|Reference.*undefined' main.log
grep -c 'Overfull \\hbox' main.log
```

Expected: build exit 0, no undefined warnings, and one overfull warning. Render with:

```sh
paper_render_dir=$(mktemp -d)
pdftoppm -png -r 144 main.pdf "$paper_render_dir/page"
```

Inspect the framework page with the local image viewer. Confirm the visual order and that no record listing remains.

Then commit from the repository root:

```sh
git diff --check -- pgg-smc/paper-wadt2026/main.tex
git add -- pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git commit -m "paper: lead framework section with architecture"
```

---

### Task 3: Keep the shuffle regimes adjacent and move the PGL claim map

**Files:**

- Modify: `pgg-smc/paper-wadt2026/main.tex`, the ends of Sections 6 and 7, plus the Section 8 heading

**Interfaces:**

- Consumes: Theorems A and B, `tab:source-index`, `tab:instances`, and label `sec:instances`.
- Produces: an explicit ideal-to-finite transition, a PGL-local claim map, and a Section 8 whose title matches its contents.

- [ ] **Step 1: Verify the source table currently follows the other-instances heading**

Run:

```sh
section_line=$(rg -n -F '\section{Other Instances}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
source_line=$(rg -n -F '\label{tab:source-index}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
test "$source_line" -lt "$section_line"
```

Expected: FAIL because the source table is currently inside Section 8.

- [ ] **Step 2: Strengthen the transition from the exact shuffle to finite words**

Immediately before the finite-word section heading, add:

```latex
Theorem A uses a uniform group element. The next section replaces this
ideal shuffle with a finite generator word and bounds the resulting error.
```

Keep the finite-word opening paragraph. Do not insert another section between the two shuffle sections.

- [ ] **Step 3: Move the source table to the end of the finite-word section**

Use `apply_patch` to move the full table labeled `tab:source-index`. Place it after the paragraph that limits word-shuffle privacy to the fixed representative dealer and before Section 8. In that paragraph, keep the sentence that points to the trust base and delete the sentence that already describes the table's mixing-transfer group. The new lead-in below replaces that description.

Insert this lead-in immediately before it:

```latex
The PGL argument has four proof layers: construction, recovery, privacy,
and finite-word transfer. Table~\ref{tab:source-index} maps the
mathematical claims used by Theorems A and B to the \Rocq{} results that
establish them.
```

Change the table placement to `[H]`. Change its caption to:

```latex
\caption{Rocq sources for the $\PG$ results.}
```

Keep all four group headings, every table row, every Rocq name, and the label unchanged.

- [ ] **Step 4: Rename Section 8 without changing its remaining content**

Replace its heading with:

```latex
\section{Other Instances and Trust Base}\label{sec:instances}
```

Keep the instance table, global assumptions, and the two spectral summaries. Do not add methodology or artifact prose.

- [ ] **Step 5: Verify source order, contents, and section adjacency**

Run:

```sh
rg -n '^\\section\{' pgg-smc/paper-wadt2026/main.tex
test "$(rg -c -F '\section{Other Instances and Trust Base}\label{sec:instances}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F '\label{tab:source-index}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
source_line=$(rg -n -F '\label{tab:source-index}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
section_line=$(rg -n -F '\section{Other Instances and Trust Base}' pgg-smc/paper-wadt2026/main.tex | cut -d: -f1)
test "$source_line" -lt "$section_line"
rg -n -F '\emph{Construction}' pgg-smc/paper-wadt2026/main.tex
rg -n -F '\emph{Correctness and recovery}' pgg-smc/paper-wadt2026/main.tex
rg -n -F '\emph{Privacy}' pgg-smc/paper-wadt2026/main.tex
rg -n -F '\emph{Mixing and transfers}' pgg-smc/paper-wadt2026/main.tex
```

Expected: all tests pass. The two shuffle headings are consecutive top-level headings. All four table groups remain.

- [ ] **Step 6: Build, inspect the section boundary, and commit Task 3**

Build from the paper directory:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
grep -E 'LaTeX Warning:.*(undefined|multiply)|Citation.*undefined|Reference.*undefined' main.log
grep -c 'Overfull \\hbox' main.log
```

Expected: build exit 0, no undefined warnings, and one overfull warning. If the `[H]` source table exceeds the text height or crosses the Section 8 heading, stop and report the rendered failure. Do not choose another placement without a design update.

Render with `pdftoppm` and inspect the source table plus the next page. Confirm that the table is readable and belongs visually to the finite-word section.

Commit from the repository root:

```sh
git diff --check -- pgg-smc/paper-wadt2026/main.tex
git add -- pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git commit -m "paper: place PGL claim map with security results"
```

---

### Task 4: Add the verified Shinagawa framework comparison

**Files:**

- Modify: `pgg-smc/paper-wadt2026/main.tex`, Related Work only
- Modify: `pgg-smc/paper-wadt2026/references.bib`

**Interfaces:**

- Consumes: DOI `10.1007/s00354-020-00117-9`, the current den Boer priority sentence, and the existing related-work groups.
- Produces: one `Shinagawa2021` entry and a comparison of the two framework boundaries.

- [ ] **Step 1: Verify the citation key is absent and the priority sentence is present**

Run:

```sh
test "$(rg -c -F '@article{Shinagawa2021,' pgg-smc/paper-wadt2026/references.bib || true)" -eq 1
```

Expected: FAIL because the entry is absent.

Run:

```sh
rg -n -F 'Den Boer introduced the first card-based cryptographic protocol' pgg-smc/paper-wadt2026/main.tex
```

Expected: one match. Preserve it and its citations.

- [ ] **Step 2: Add the verified bibliography entry**

Use `apply_patch` to add this near the other Shinagawa entries:

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

- [ ] **Step 3: Add the model comparison and remove duplicated self-description**

Insert this paragraph after the bounded-model-checking paragraph and before the graph-automorphism paragraph:

```latex
Shinagawa gives a unified model in which a card protocol is specified by a
deck and a set of operations~\cite{Shinagawa2021}. The model covers binary
cards, regular polygon cards, and dihedral cards. It varies the card type
and the allowed physical operations. The framework in this paper instead
varies the finite group, its permutation action, the shuffle distribution,
and the reconstruction map. It connects these parameters to executable
traces and machine-checked privacy and mixing results.
```

In the following graph-automorphism paragraph, delete the two duplicated sentences beginning `The framework in this paper takes the finite group` and ending `sharing and execution semantics.` Keep the graph and hypergraph citations, the closed-shuffle citation, and the compiler citation.

- [ ] **Step 4: Verify metadata, priority scope, and comparison scope**

Run:

```sh
test "$(rg -c -F '@article{Shinagawa2021,' pgg-smc/paper-wadt2026/references.bib)" -eq 1
test "$(rg -c -F 'doi     = {10.1007/s00354-020-00117-9}' pgg-smc/paper-wadt2026/references.bib)" -eq 1
test "$(rg -c -F '\cite{Shinagawa2021}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
rg -n -F 'first card-based cryptographic protocol' pgg-smc/paper-wadt2026/main.tex
rg -n -i 'Shinagawa.*(fewer cards|more efficient|no security|not formal|lacks|replaces)|replaces.*Shinagawa' pgg-smc/paper-wadt2026/main.tex
```

Expected: the first four checks pass. The negative-scope scan prints nothing.

- [ ] **Step 5: Build and commit Task 4**

Build from the paper directory:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
grep -E 'LaTeX Warning:.*(undefined|multiply)|Citation.*undefined|Reference.*undefined' main.log
grep -E 'Warning--I didn.t find|Warning--empty' main.blg
grep -c 'Overfull \\hbox' main.log
```

Expected: build exit 0, both warning scans print nothing, and the overfull count remains 1. Read the compiled Related Work page and the bibliography entry.

Commit:

```sh
git diff --check -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git add -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git diff --cached --check
git commit -m "paper: compare the framework with Shinagawa 2021"
```

---

### Task 5: Run the whole-paper prose, source, and rendered-layout audit

**Files:**

- Inspect: `pgg-smc/paper-wadt2026/main.tex`
- Inspect: `pgg-smc/paper-wadt2026/references.bib`
- Inspect: `pgg-smc/paper-wadt2026/main.pdf`
- Modify only for an in-scope finding

**Interfaces:**

- Consumes: the four committed paper tasks.
- Produces: a clean final build, protected-theorem comparison, manual AI-ism review, and rendered confirmation of all changed areas.

- [ ] **Step 1: Confirm structure and protected labels**

Run:

```sh
rg -n '^\\section\{|^\\subsection\{' pgg-smc/paper-wadt2026/main.tex
test "$(rg -c -F '\label{sec:instances}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F '\label{tab:source-index}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F '\label{fig:framework-architecture}' pgg-smc/paper-wadt2026/main.tex)" -eq 1
```

Expected: the section listing matches the design and all tests pass.

- [ ] **Step 2: Prove the generic theorem subsection is unchanged**

Run:

```sh
framework_commit=$(git log -1 --format=%H --grep='paper: lead framework section with architecture')
test -n "$framework_commit"
diff -u \
  <(git show "${framework_commit}^":pgg-smc/paper-wadt2026/main.tex | sed -n '/\\subsection{Generic Theorems}/,/\\section{A First Instance: The Five-Card Family}/p') \
  <(sed -n '/\\subsection{Generic Theorems}/,/\\section{A First Instance: The Five-Card Family}/p' pgg-smc/paper-wadt2026/main.tex)
```

Expected: no diff.

- [ ] **Step 3: Run the detect-first prose scan**

Run:

```sh
rg -n -i '\b(we|our)\b|—|;|Moreover|Furthermore|Consequently|It is worth noting|delve|pivotal|crucial|groundbreaking|comprehensive|robust|seamless' pgg-smc/paper-wadt2026/main.tex
```

Review every hit. The semicolon in the exact piSMC listing is code and remains. Bibliography titles are exempt. Plain authorial prose must contain no authorial `we`, `our`, em dash, or semicolon.

Read the changed blocks:

```sh
rg -n -A12 -B4 'exchange_player|selected reveal cases|framework description|four proof layers|Shinagawa gives a unified model' pgg-smc/paper-wadt2026/main.tex
```

- [ ] **Step 4: Run source and citation integrity checks**

Run:

```sh
test "$(rg -c -F 'Definition exchange_player' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F 'Record MonodromyProfile' pgg-smc/paper-wadt2026/main.tex || true)" -eq 0
test "$(rg -c -F 'Definition five_card_profile' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F 'leak\_view\_set' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F 'leak\_k3\_gap' pgg-smc/paper-wadt2026/main.tex)" -eq 1
test "$(rg -c -F '@article{Shinagawa2021,' pgg-smc/paper-wadt2026/references.bib)" -eq 1
```

Expected: all tests pass.

- [ ] **Step 5: Rebuild and compare warnings**

Run from the paper directory:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
grep -E 'LaTeX Warning:.*(undefined|multiply)|Citation.*undefined|Reference.*undefined' main.log
grep -E 'Warning--I didn.t find|Warning--empty' main.blg
grep -c 'Overfull \\hbox' main.log
```

Expected: build exit 0, no undefined or BibTeX warnings, and exactly one pre-existing overfull warning.

- [ ] **Step 6: Render and inspect all changed areas**

Run:

```sh
paper_render_dir=$(mktemp -d)
pdftoppm -png -r 144 main.pdf "$paper_render_dir/page"
pdfinfo main.pdf | rg '^Pages:'
```

Use the local image viewer to inspect the pages containing:

1. the piSMC listing
2. the five-card rows and bit values
3. the architecture figure and the start of Generic Theorems
4. the PGL claim map and Section 8 boundary
5. the Shinagawa paragraph and bibliography entry

Confirm that every object fits, captions are short, all card rows remain, the architecture figure precedes its prose, and the source table stays before Section 8.

- [ ] **Step 7: Read the complete source and resolve only in-scope findings**

Run:

```sh
sed -n '1,360p' pgg-smc/paper-wadt2026/main.tex
sed -n '361,720p' pgg-smc/paper-wadt2026/main.tex
sed -n '721,1080p' pgg-smc/paper-wadt2026/main.tex
sed -n '1081,1500p' pgg-smc/paper-wadt2026/main.tex
```

Check each changed claim, hedge, citation, and transition. If a correction is needed, use `apply_patch`, rerun Steps 3 through 6, and commit:

```sh
git add -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git diff --cached --check
git commit -m "paper: finish WADT structural follow-up"
```

If no correction is needed, do not create an empty commit.

- [ ] **Step 8: Confirm the final handoff**

Run:

```sh
git status --short
git log -5 --oneline
```

Expected: the two paper sources have no uncommitted changes from this plan. Generated files remain unstaged. Unrelated user-owned changes remain untouched.
