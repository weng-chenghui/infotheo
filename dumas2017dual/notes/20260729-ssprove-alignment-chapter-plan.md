# SSProve-Alignment Chapter Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.
>
> Spec: `dumas2017dual/notes/20260729-ssprove-alignment-chapter.md` (commit 9803379b).
> Branch: `20260729-0028-reduction-form-security`.

**Goal:** One new blueprint chapter recording, in a six-row table, how the
reduction-form statement discipline follows the SSProve case studies.

**Architecture:** New `src/ssprove_alignment.tex` input from `security.tex`
after the overview chapter; one new label `ch:derivation_overview` in
`content.tex`; a two-sentence forward-reference paragraph in the overview
chapter. Verification is the blueprint build plus HTML table check plus
coverage gate; no `.v` file changes.

**Tech Stack:** plasTeX 3.1 blueprint (`make_blueprint.sh`), `check_coverage.py`.

---

### Task 1: The chapter file and its three anchor edits

**Files:**
- Create: `dumas2017dual/blueprint/src/ssprove_alignment.tex`
- Modify: `dumas2017dual/blueprint/src/security.tex` (after the overview
  chapter's last paragraph, before `\part{Foundations}`)
- Modify: `dumas2017dual/blueprint/src/content.tex` (after
  `\chapter{Overview of the derivation}`)

- [ ] **Step 1.1:** Create `dumas2017dual/blueprint/src/ssprove_alignment.tex`
  with exactly the chapter content from the spec's "Chapter content (draft,
  post-audit)" section — the `\chapter{Alignment with the \ssprove{} case
  studies}` block: label `ch:ssprove_alignment`, one opening paragraph (4
  sentences), the `\begin{center}\begin{tabular}{p{0.30\linewidth}p{0.30\linewidth}p{0.32\linewidth}}`
  six-row table with `\hline` separators, and the closing two-part paragraph
  (Parameters gloss; trust-base sentence referencing
  `Chapter~\ref{ch:derivation_overview}` and the allowlist note path). Copy
  the LaTeX verbatim from the spec.
- [ ] **Step 1.2:** In `content.tex`, add the label line directly after the
  chapter heading:

```latex
\chapter{Overview of the derivation}
\label{ch:derivation_overview}
```

- [ ] **Step 1.3:** In `security.tex`, between the overview chapter's final
  paragraph (ending "...the SSProve ciphertext game from the one protocol
  program.") and `\part{Foundations}`, insert:

```latex
Both computational legs above state their bounds as advantages of explicit
reductions. Chapter~\ref{ch:ssprove_alignment} records how this statement
discipline follows the \ssprove{} case studies.

\input{ssprove_alignment}
```

### Task 2: Verify and commit

- [ ] **Step 2.1:** Build the blueprint:

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/blueprint
bash make_blueprint.sh; echo "BP_EXIT=$?"
```

Expected: `BP_EXIT=0`.
- [ ] **Step 2.2:** Verify the table rendered and the labels resolved:

```bash
grep -l "<table" web/*.html | head -3
grep -rl "prf_epsilon" web/*.html | head -3
grep -in "undefined" plastex.log 2>/dev/null | head -5   # or the build's log file
```

Expected: at least one HTML file matches both greps; no undefined-reference
lines mentioning `ch:ssprove_alignment`, `ch:derivation_overview`. If the
table did NOT render, fall back to the spec's `itemize` form (same six rows,
one `\item` per correspondence) and re-run from Step 2.1.
- [ ] **Step 2.3:** Coverage gate:

```bash
python3 dumas2017dual/blueprint/check_coverage.py
```

Expected: `OK` with counts unchanged from HEAD (`code=376 blueprint=108
excl=268`).
- [ ] **Step 2.4:** Paragraph-length check: every prose paragraph in the new
  chapter and the forward-reference is at most 4 sentences (count manually;
  the opening paragraph has 4, the closing paragraph has 4 including the
  colon-extended first sentence — if any paragraph exceeds 4, apply the
  spec's list-conversion rule before committing).
- [ ] **Step 2.5:** Commit (prose-only change):

```bash
git add dumas2017dual/blueprint/src/ssprove_alignment.tex \
  dumas2017dual/blueprint/src/security.tex \
  dumas2017dual/blueprint/src/content.tex
ROCQ_AUDIT_BYPASS=1 git commit -m "blueprint: SSProve-alignment chapter"
```

---

## Self-review notes

- Spec coverage: deliverable file + both anchor edits = Task 1; all four
  verification bullets = Task 2; fallback (itemize) = Step 2.2; style gate =
  Step 2.4. Naming-audit items are name choices already fixed in the spec.
- The chapter LaTeX itself lives once, in the spec, and Step 1.1 copies it
  verbatim — the spec is in-repo at a pinned commit, so this is a reference
  to committed content, not a placeholder.
