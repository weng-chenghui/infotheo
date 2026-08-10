# WADT Round 3 Signposting Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Raise `pgg-smc/paper-wadt2026/main.tex` signposting from 13 hits (17.4/10k) to 30 hits (~39.7/10k) via the audit-amended edits S1-S16 + B1 of spec `2026-08-10-wadt-round3-signposting-design.md`.

**Architecture:** Two edit commits in document order (model/intro/framework, then instances/mixing), each compile-checked and count-checked, followed by the full acceptance run against the five-peer panel.

**Tech Stack:** Edit tool on main.tex; `fact_density.py` / `count_connectives.py` / `per_section.py` from `~/.claude/skills/baseline-transition-analysis/scripts/`; `latexmk -pdf`.

All OLD/NEW strings below are the audit-amended spec versions and are matched
modulo line wrapping; the executor re-indents NEW text to the surrounding file
context (audit N18). No abstract line may change.

---

### Task 1: Model, Introduction, and Framework edits (S16, B1, S1, S2, S3a, S3b, S4, S5)

**Files:** Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 1.1 S16** (L146-147, Introduction footnote): `, called variation distance in the formal development,` → `, which is called variation distance in the formal development,`
- [ ] **Step 1.2 B1** (L93): `the security results in the ideal model and then` → `the security results in the uniform-shuffle model of Section~\ref{sec:model} and then`
- [ ] **Step 1.3 S3a** (L136): `one profile at bias $\varepsilon$: executed-run correctness` → `one profile at bias $\varepsilon$, in the sense of Section~\ref{sec:framework}: executed-run correctness`
- [ ] **Step 1.4 S2** (L207-208): `The resulting record is the executed trace $T_i$, and $T_C=(T_i)_{i\in C}$ is the coalition trace.` → `The resulting record is called the executed trace $T_i$, and $T_C=(T_i)_{i\in C}$ is called the coalition trace.`
- [ ] **Step 1.5 S1** (L259-260): `A second model describes the dealer performing the shuffle as a sequence of physical cuts. I call this the word-shuffle model.` → `The model described so far applies one uniform group element, and I call it the uniform-shuffle model. A second model describes the dealer performing the shuffle as a sequence of physical cuts. I call this the word-shuffle model.`
- [ ] **Step 1.6 S3b** (L414): `Packing these components in one profile keeps the participants, verifier,` → `I call a filled \coqin{MonodromyProfile} a profile. Packing these components in one profile keeps the participants, verifier,`
- [ ] **Step 1.7 S4** (L436): `The security witness can carry exact evidence, asymptotic evidence, or both.` → `The record that carries the shuffle distribution and its endpoint bound is called the security witness. It can carry exact evidence, asymptotic evidence, or both.`
- [ ] **Step 1.8 S5** (L465-467): `With an \coqin{InputEncoding}, a commit prologue collects the players' inputs and assembles the dealt deck from them, so the same flow evaluates a function of committed inputs.` → `With an \coqin{InputEncoding}, the flow gains a phase that I call the commit prologue. It collects the players' inputs and assembles the dealt deck from them, so the same flow evaluates a function of committed inputs.`
- [ ] **Step 1.9 Verify count.** Run the SIGNPOST count via `count_connectives.load` + `fact_density.SIGNPOST` on main.tex. Expected: 20 hits (13 + 7).
- [ ] **Step 1.10 Compile.** `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` in the paper dir. Expected: exit 0, 24 pages, no new warnings.
- [ ] **Step 1.11 Commit.** `git add pgg-smc/paper-wadt2026/main.tex && git commit -m "paper: counted term introductions in model, intro, and framework"`

### Task 2: Five-Card, Exact, Mixing, and Instances edits (S6-S15)

**Files:** Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 2.1 S6** (L602-603): `The dealing distribution is the biased cut of Kim and \c{C}etinkaya` + newline + `\begin{equation}` → `The dealing distribution is the biased cut of Kim and \c{C}etinkaya, and I write $w_\varepsilon$ for it:` + newline + `\begin{equation}`
- [ ] **Step 2.2 S7** (L614): `The master theorem gives the exact leakage` → `What I call the master theorem gives the exact leakage`
- [ ] **Step 2.3 S8a** (L617-618 footnote): `and the cap \coqin{H\_secret} in` → `and the secret's own entropy \coqin{H\_secret} in`
- [ ] **Step 2.4 S8b** (L623-624): `$2-\tfrac34\log 3\approx 0.811$. The decimals are` → `$2-\tfrac34\log 3\approx 0.811$, which I call the cap. The decimals are`
- [ ] **Step 2.5 S9+S10** (L944-947): `The privacy threshold $t$ is the largest coalition size with perfect privacy, the recovery threshold $r$ is the least number of revealed positions that always determines the secret class,` → `The privacy threshold $t$ is defined as the largest coalition size with perfect privacy, the recovery threshold $r$ is defined as the least number of revealed positions that always determines the secret class,`
- [ ] **Step 2.6 S11** (L1055-1057): `no later shuffle. For this shuffle-free deck distribution, view independence holds for every Boolean secret prior.` → `no later shuffle. I call the resulting distribution the shuffle-free deck distribution, and view independence holds under it for every Boolean secret prior.`
- [ ] **Step 2.7 S12** (L1138): `Equation~\ref{eq:pgl-mixing} is one checked certificate.` → `Equation~\ref{eq:pgl-mixing} is one checked certificate, which I call the mixing certificate.`
- [ ] **Step 2.8 S13** (L1145-1146): `The first transfer maps each permutation to the endpoint of one fixed card.` → `The first transfer, which I call the endpoint transfer, maps each permutation to the endpoint of one fixed card.`
- [ ] **Step 2.9 S14** (L1199-1200, Theorem B): `writing $V_C(s,g)$ for the coalition view at dealt secret $s$ and shuffle $g$,` → `where the coalition view at dealt secret $s$ and shuffle $g$ is denoted $V_C(s,g)$,`
- [ ] **Step 2.10 S15** (L1349): `The probability, view, and trace results use three classical principles` → `The checker and the axioms that a result's verification rests on are called its trust base. The probability, view, and trace results use three classical principles`
- [ ] **Step 2.11 Verify count.** SIGNPOST count on main.tex. Expected: 30 hits.
- [ ] **Step 2.12 Compile.** Same latexmk command. Expected: exit 0, 24 pages, no new warnings.
- [ ] **Step 2.13 Commit.** `git commit -m "paper: counted term introductions in instances and mixing"`

### Task 3: Acceptance run and report

- [ ] **Step 3.1 Panel run.** `fact_density.py` on main.tex + the five peer PDFs in `~/.claude/research-kb/pdfs/`. Gates: signpost/10k >= 38.0, hits >= 29, moves/10k >= 60.0.
- [ ] **Step 3.2 Per-section.** Per-section SIGNPOST rates; every touched section >= 18.0/10k; Related Work and Conclusion exactly 0. Abstract diff-clean.
- [ ] **Step 3.3 Round-2 gate re-check.** `count_connectives.py` family totals still satisfy round-2 thresholds (TOTAL >= 60/10k); `per_section.py` shows no section below the round-2 floor 24.6/10k.
- [ ] **Step 3.4 Memory update.** Append the round-3 record to `project_wadt_transition_fixes_landed.md`.
- [ ] **Step 3.5 Report in Zh-TW** with the spec's eight disclosures, the Before/After table (13 -> 30 hits, 17.4 -> ~39.7/10k), the audit verdict summary (F1-F8 applied), and the panel position (above KochSchKir21/KochWalzer17, at Iwamoto level, Shinagawa-style papers remain far above by design).
