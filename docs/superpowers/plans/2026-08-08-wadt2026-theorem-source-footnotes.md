# WADT 2026 Theorem Source Footnotes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Audit all nine paper theorem blocks and add title footnotes that name every verified direct Rocq counterpart and its repository-relative source path.

**Architecture:** A read-only mapping pass first compares each rendered theorem body with declarations in `pgg-smc/instances/pgl27/`. The paper writer then adds a footnote mark to each mapped theorem title and places the matching footnote text immediately inside that theorem environment. The parent agent independently checks the mappings, rebuilds the PDF, and visually verifies every theorem page.

**Tech Stack:** LaTeX with `llncs`, `hyperref`/`url` path formatting, Rocq source inspection with `rg`, `latexmk`, and Poppler rendering.

## Global Constraints

- Modify only `pgg-smc/paper-wadt2026/main.tex` during implementation.
- Do not edit any `.v` file or create a formalization request.
- Use repository-relative `.v` paths and exact Rocq declaration names.
- List direct formal counterparts only. Do not list proof dependencies or helper lemmas.
- A theorem with no direct counterpart receives no fabricated footnote and must be reported in chat.
- Keep all existing source-index tables.
- The same paper-writing subagent owns all changes to `main.tex`, as required by the user.
- The parent agent performs the final source and PDF verification without editing `main.tex`.

---

### Task 1: Audit the nine paper theorem blocks

**Files:**
- Read: `pgg-smc/paper-wadt2026/main.tex`
- Read: `pgg-smc/instances/pgl27/*.v`
- Do not modify files.

**Interfaces:**
- Consumes: the nine rendered `theorem` environments in `main.tex`.
- Produces: one mapping row per theorem with title, direct `.v` path or paths, exact declaration names, and a short claim-to-declaration justification. An unmapped theorem is marked `NO_DIRECT_COUNTERPART`.

- [ ] **Step 1: Enumerate the paper theorem blocks**

Run:

```bash
rg -n '\\begin\{theorem\}' pgg-smc/paper-wadt2026/main.tex
```

Expected: exactly nine matches with these titles: Orbit encoder, Orbit split, Three-transitivity, Executed correctness, Recovery ramp, Exact privacy for the fixed dealer, All-decks exact privacy, Shuffle-free deck privacy, and Finite-step shuffle bound.

- [ ] **Step 2: Locate candidate formal declarations**

Run focused searches in `pgg-smc/instances/pgl27/` for the claims in each theorem body. Candidate names must be opened at their declarations. Comments and theorem-index tables are search aids, not sufficient evidence.

```bash
rg -n '^(Lemma|Theorem|Fact|Corollary|Proposition|Definition) (orbit_encode|orbit_class_split|pgl27_3transitive|pgl27_run_recovers_class|pgl27_seven_reveal|pgl27_reveal_ambiguous|pgl27_view_|pgl27_.*trace.*secrecy|pgl27_word_mixing)' pgg-smc/instances/pgl27 --glob '*.v'
```

- [ ] **Step 3: Compare every paper claim with the formal statement**

For each candidate, read its complete declaration and premises. Include it only if it directly states one or more claims rendered inside the paper theorem. Record multiple declarations when the paper block is a conjunction of formal results.

- [ ] **Step 4: Return the mapping to the paper writer and parent**

The mapping must state explicitly whether all nine theorem blocks have direct formal counterparts. Do not edit or commit any file in this task.

---

### Task 2: Add verified source footnotes to theorem titles

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

**Interfaces:**
- Consumes: Task 1's verified theorem-to-source mapping.
- Produces: one source footnote for every mapped theorem block and no footnote for an unmapped block.

- [ ] **Step 1: Record the pre-edit structural counts**

Run:

```bash
rg -c '\\begin\{theorem\}' pgg-smc/paper-wadt2026/main.tex
rg -c 'Formalized in \\path' pgg-smc/paper-wadt2026/main.tex || true
```

Expected before the edit: nine theorem environments and zero theorem-source footnotes.

- [ ] **Step 2: Add the first theorem-title footnote and compile it**

Use a title mark and immediate text so the title is visibly footnoted without placing a fragile `\footnote` command in the optional theorem title:

```tex
\begin{theorem}[Orbit encoder\footnotemark]
\footnotetext{Formalized in
\path{pgg-smc/instances/pgl27/pgl27_orbit.v} as
\coqin{orbit\_encode\_deck} and \coqin{orbit\_encodeK}.}
```

These two declarations directly state validity and class recovery. Run:

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Expected: exit 0 and a visible footnote mark in the theorem title.

- [ ] **Step 3: Add footnotes to every other mapped theorem**

For one source file, use:

```tex
\footnotetext{Formalized in \path{repo/relative/file.v} as
\coqin{name\_one} and \coqin{name\_two}.}
```

For multiple files, use separate plain sentences in the same footnote. Keep paths repository-relative. Escape underscores in `\coqin{}` names. Do not add a footnote to a theorem marked `NO_DIRECT_COUNTERPART`.

- [ ] **Step 4: Check structural coverage and source validity**

Run:

```bash
rg -n '\\begin\{theorem\}' pgg-smc/paper-wadt2026/main.tex
rg -n 'Formalized in \\path' pgg-smc/paper-wadt2026/main.tex
```

Count the mapped theorem blocks and confirm the second count matches it. For every path and declaration in a footnote, confirm that the file exists and the declaration header occurs in that file.

- [ ] **Step 5: Run the paper checks**

Run:

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
git diff --check -- main.tex
```

Expected: build exit 0 and no matches from the warning or whitespace scans.

- [ ] **Step 6: Commit the paper edit**

```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m 'wadt2026: link theorem titles to Rocq sources'
```

---

### Task 3: Parent verification and completion report

**Files:**
- Read: `pgg-smc/paper-wadt2026/main.tex`
- Read: every `.v` path cited by a new theorem footnote.
- Inspect: `pgg-smc/paper-wadt2026/main.pdf`
- Do not modify `main.tex` or any `.v` file.

**Interfaces:**
- Consumes: the committed Task 2 paper and Task 1 mapping.
- Produces: an evidence-backed final report that lists unmapped theorem blocks or states that all nine have verified direct counterparts.

- [ ] **Step 1: Re-read all nine theorem blocks and their footnotes**

Check title, rendered mathematical claims, path, and each declaration name together. Reopen every cited formal declaration and confirm the footnote covers the paper statement without adding unsupported strength.

- [ ] **Step 2: Verify scope and counts**

Run:

```bash
rg -c '\\begin\{theorem\}' pgg-smc/paper-wadt2026/main.tex
rg -c 'Formalized in \\path' pgg-smc/paper-wadt2026/main.tex
git diff --name-only beefec6..HEAD
```

Expected: nine theorem environments. The footnote count equals the number of mapped blocks. The implementation diff contains `pgg-smc/paper-wadt2026/main.tex` and no `.v` file.

- [ ] **Step 3: Force-rebuild and scan the final log**

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
```

Expected: build exit 0, thirteen or more pages, and no matches.

- [ ] **Step 4: Render and visually inspect every theorem page**

Render with Poppler. Check footnote numbering, line wrapping, margins, theorem-title marks, and separation between adjacent footnotes. The source footnotes must be legible and must not create clipping or overlaps.

- [ ] **Step 5: Report completion**

State the implementation commit, build result, page count, and mapping coverage. List every theorem with no direct formal counterpart. If the list is empty, state that all nine paper theorem blocks have verified Rocq counterparts.
