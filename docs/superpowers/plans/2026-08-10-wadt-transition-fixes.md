# WADT Transition Fixes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the 22 audit-amended prose edits of
`docs/superpowers/specs/2026-08-10-wadt-transition-fixes-design.md` on
`pgg-smc/paper-wadt2026/main.tex` in three commits, then re-run the
baseline-transition-analysis check as the acceptance gate.

**Architecture:** Pure prose edits to one LaTeX file, applied as
exact-string replacements (never line-range replacements), grouped into
three mechanism commits: structure and motivation (E1-E6, E22),
signposting and grounding (E7-E17, E19, E20; E18 is cut), numeric worked
example (E21). Every commit recompiles; acceptance is measured by the
skill scripts plus two committed instruments.

**Tech Stack:** LaTeX (llncs), latexmk, python3 measurement scripts at
`~/.claude/skills/baseline-transition-analysis/scripts/` and
`docs/superpowers/specs/tools/`.

**Base revision:** `e39751e1` for `main.tex` (spec line numbers refer to
it). The OLD strings below are authoritative; if an OLD string does not
match, STOP and re-locate by content, never by line number.

**Voice rules for all inserted text:** "I" for authorial acts, impersonal
"Let ... be" for the E21 example, no "we", no em-dashes, no semicolons,
no parenthetical asides, "distribution" never "law", no new
abbreviations.

---

### Task 1: Preconditions and before-measurements

**Files:**
- Read: `pgg-smc/paper-wadt2026/main.tex`
- No modifications.

- [ ] **Step 1: Verify the working tree and revision**

Run: `git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg status --short -- pgg-smc/paper-wadt2026/main.tex && git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg log --oneline -1 -- pgg-smc/paper-wadt2026/main.tex`
Expected: no modification lines for main.tex; last paper commit `e39751e1`.

- [ ] **Step 2: Record before-values from all instruments**

Run (from repo root):
```bash
python3 ~/.claude/skills/baseline-transition-analysis/scripts/count_connectives.py \
  ~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf \
  pgg-smc/paper-wadt2026/main.tex --labels Shinagawa,WADT
python3 docs/superpowers/specs/tools/wadt_per_section.py
python3 docs/superpowers/specs/tools/wadt_signpost_neutral.py \
  pgg-smc/paper-wadt2026/main.tex=WADT
```
Expected: WADT 6720 words, TOTAL 10 std events (14.9/10k by the skill
script, 14.7 by the per-section instrument), Section 3 std 0, Section 7
all/10k 11.9, neutral signposting 4 events (6.0/10k). These are the
"Before" gate values; if they differ, STOP and reconcile before editing.

- [ ] **Step 3: Verify the paper compiles cleanly before any edit**

Run: `cd pgg-smc/paper-wadt2026 && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && pdfinfo main.pdf | grep Pages`
Expected: exit 0, `Pages: 21`.

---

### Task 2: Commit 1 — structure and motivation (E1-E6, E22)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

Apply each edit with the Edit tool using EXACTLY these old/new strings
(newlines included as shown).

- [ ] **Step 1: E1 — Section 3 opener (spec lines 304-309)**

OLD:
```
An instance is specified by filling one record. The record type
\coqin{MonodromyProfile} has five fields, and they carry the data of
Equation~\ref{eq:model-data} into the executable protocol: the group with
its action and generators, the secret type, the layout of a run, the
shuffle-security bound, and the decoder. Here $R$ is the real closed field
of Equation~\ref{eq:model-data}, not a protocol datum.
```
NEW:
```
Every instance in this paper supplies the same kinds of data: a group
with its action and generators, a secret type, the layout of a run, a
shuffle-security bound, and a decoder. In order to reuse one executable
protocol across instances, the framework therefore gathers these five
choices into one record, the record type \coqin{MonodromyProfile}, while
the generic theorems of this section take their hypotheses directly. The
record carries the data of Equation~\ref{eq:model-data} into the
executable protocol. Here $R$ is the real closed field of
Equation~\ref{eq:model-data}, not a protocol datum.
```

- [ ] **Step 2: E2 — delete the third field-list enumeration (405-409) and fix the antecedent (411)**

OLD (delete, including the trailing blank line):
```
The profile packs the group action and its generators, the secret type, the
protocol layout, the shuffle-security evidence, and the reconstruction
component. The layout supplies the participant processes. The security
evidence supplies an endpoint bound. The reconstruction component supplies
the threshold scheme and decoder.

```
NEW: (empty string)

Then OLD:
```
Packing these choices in one profile keeps
```
NEW:
```
Packing these components in one profile keeps
```

- [ ] **Step 3: E3 — merge orphan sentence, compress caveats (914-919)**

OLD:
```
The implemented decoder reads all eight endpoints.

The witness coalition makes the privacy cutoff three sharp. It
does not classify all four-position coalitions. The development also proves
monotonicity of mutual information under inclusion, but it does not compute
the leakage for all reveal sets of sizes four through six.
```
NEW:
```
The implemented decoder reads all eight endpoints. The witness coalition
makes the privacy cutoff three sharp. Although the development proves
monotonicity of mutual information under inclusion, it neither classifies
all four-position coalitions nor computes the leakage for every reveal set
of sizes four through six.
```

- [ ] **Step 4: E4 — compress the transfer caveats (1087-1090)**

OLD:
```
Equation~\ref{eq:product-transfer} compares two distributions on a secret
and a shuffle. It is not an execution distribution. Equations~\ref{eq:endpoint-transfer}
and~\ref{eq:product-transfer} transfer the one certificate in
Equation~\ref{eq:pgl-mixing}. They are not separate mixing certificates.
```
NEW:
```
Equations~\ref{eq:endpoint-transfer} and~\ref{eq:product-transfer}
transfer the one certificate of Equation~\ref{eq:pgl-mixing} to two
further sample spaces. Neither is a separate mixing certificate, and
Equation~\ref{eq:product-transfer} still compares a prior with a shuffle
distribution rather than a distribution over executed runs.
```

- [ ] **Step 5: E5 — motivational roadmap (156-162)**

OLD:
```
Section~\ref{sec:framework} presents the framework
components used by the proofs. Section~\ref{sec:fivecard} instantiates them
on the five-card family as a first worked example.
Sections~\ref{sec:pgl} and~\ref{sec:exact}
give the $\PG$ construction and its uniform-shuffle results, ending in
Theorem A. Section~\ref{sec:mixing} proves the word-shuffle results, ending
in Theorem B.
```
NEW:
```
Section~\ref{sec:framework} presents the framework components used by
the proofs. Section~\ref{sec:fivecard} instantiates them on the five-card
family, where the deck is small enough for direct case analysis.
Sections~\ref{sec:pgl} and~\ref{sec:exact} construct the $\PG$ instance,
where deck enumeration no longer suffices and three-transitivity carries
the privacy proofs, ending in Theorem A. Because a physical dealer repeats
cuts rather than sampling one uniform group element,
Section~\ref{sec:mixing} proves the word-shuffle results, ending in
Theorem B.
```

- [ ] **Step 6: E6 — claim-map pointer (833)**

OLD:
```
Table~\ref{tab:source-index} indexes the formal sources for this section.
```
NEW:
```
Table~\ref{tab:source-index} at the end of Section~\ref{sec:mixing}
indexes the formal sources for this section and the two that follow.
```

- [ ] **Step 7: E22 — action-direction convention sentence (195)**

OLD:
```
of a sampled shuffle $g$ produces the arrangement $\rho(g)D$. Player $i$
```
NEW:
```
of a sampled shuffle $g$ produces the arrangement $\rho(g)D$. Position $i$
of the shuffled arrangement holds the card that $D$ places at position
$\rho(g)(i)$. Player $i$
```

- [ ] **Step 8: Verify no stale text remains**

Run: `grep -c "The profile packs the group action" pgg-smc/paper-wadt2026/main.tex; grep -c "as a first worked example" pgg-smc/paper-wadt2026/main.tex; grep -c "Packing these components" pgg-smc/paper-wadt2026/main.tex`
Expected: `0`, `0`, `1` (grep exits 1 on zero matches; that is the pass condition for the first two).

- [ ] **Step 9: Recompile**

Run: `cd pgg-smc/paper-wadt2026 && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && pdfinfo main.pdf | grep Pages`
Expected: exit 0; pages 21 (float drift acceptable, note the number).

- [ ] **Step 10: Commit**

```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: motivate the framework record and repair locator prose

E1 need-before-machinery opener for Section 3, E2 field-list dedup,
E3 caveat merge with the quantifier preserved, E4 transfer-caveat
rewrite, E5 motivational roadmap, E6 claim-map pointer, E22 explicit
action-direction convention. Spec:
docs/superpowers/specs/2026-08-10-wadt-transition-fixes-design.md"
```

---

### Task 3: E9 attribution check (before Commit 2)

**Files:**
- Read: `~/.claude/research-kb/index.jsonl`, KB slice for Kim and
  Cetinkaya 2025, `pgg-smc/paper-wadt2026/references.bib`

- [ ] **Step 1: Search the knowledge base and bibliography for the term**

Run: `grep -iF 'biased cut' ~/.claude/research-kb/slices/*.md pgg-smc/paper-wadt2026/references.bib pgg-smc/instances/kim2025/*.v | head -20`

- [ ] **Step 2: Decide the E9 wording**

Decision rule: if any hit shows Kim and Cetinkaya (or their paper's
title/abstract) using "biased cut" as their own term, E9 becomes:
OLD `The dealing distribution is the biased cut`
NEW `The dealing distribution is the biased cut of Kim and \c{C}etinkaya`
Otherwise E9 stays as specified:
NEW `The dealing distribution is what I call the biased cut`
Record which branch was taken for the final report. The neutral
signposting gate survives either branch (spec projection).

---

### Task 4: Commit 2 — signposting and grounding (E7-E17, E19, E20)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 1: E7 — name the word distribution at first use (90)**

OLD:
```
and the repeated cuts follow a word distribution over
```
NEW:
```
and the repeated cuts follow what I call a word distribution over
```

- [ ] **Step 2: E8 — connect the convolution to the name (191-192)**

OLD:
```
The convolution $\mu^{*L}$ is the distribution of the
group element obtained by evaluating $L$ independent letters.
```
NEW:
```
I write $\mu^{*L}$ for the word distribution at length $L$: the
distribution of the group element obtained by evaluating $L$ independent
letters.
```

- [ ] **Step 3: E10 — name the word-shuffle model (254-255)**

OLD:
```
The word-shuffle model describes the dealer performing the shuffle as a
sequence of physical cuts. It replaces $U_G$ by $\mu^{*L}$.
```
NEW:
```
A second model describes the dealer performing the shuffle as a
sequence of physical cuts. I call this the word-shuffle model. It
replaces $U_G$ by $\mu^{*L}$.
```

- [ ] **Step 4: E11 — name the fixed representative dealer (233-234)**

OLD:
```
then applies an independent uniform shuffle. This fixed-representative
dealer is the dealer of the headline theorems. An all-decks dealer instead
```
NEW:
```
then applies an independent uniform shuffle. I call this the fixed
representative dealer, and it is the dealer of the headline theorems. An
all-decks dealer instead
```

- [ ] **Step 5: E9 — name the biased cut (597), wording from Task 3**

OLD:
```
The dealing distribution is the biased cut
```
NEW (default branch):
```
The dealing distribution is what I call the biased cut
```

- [ ] **Step 6: E12 — name the orbit class at first use (708-709)**

OLD:
```
shuffle distribution draws uniform generator letters, and the decoder reads
the orbit class.
```
NEW:
```
shuffle distribution draws uniform generator letters, and the decoder
reads what I call the orbit class.
```

- [ ] **Step 7: E13 — name the recovery ramp (875)**

OLD:
```
class, and $n$ is the number of card positions.
```
NEW:
```
class, and $n$ is the number of card positions. I call the triple
$(t,r,n)$ the recovery ramp.
```

- [ ] **Step 8: E16 — base-triple example (827)**

OLD:
```
The kernel checks the resulting finite table.
```
NEW:
```
The kernel checks the resulting finite table. For example, the base
triple is $(0,1,2)$, and the table stores for every other ordered triple
of distinct points one generator word that carries $(0,1,2)$ to it.
```

- [ ] **Step 9: E15 — witness-slot example (435)**

OLD:
```
five instances in this paper.
```
NEW:
```
five instances in this paper. For example, the den Boer row fills only
the exact slot, since one uniform cut already gives the exact endpoint
distribution.
```

- [ ] **Step 10: E19 — symmetric-alphabet reason (1026-1027)**

OLD:
```
The resulting tuple is symmetric and generates the same group
as the original three generators.
```
NEW:
```
The alphabet includes the two inverse letters because the fiber
computation below steps backward through a letter's inverse and must stay
inside the alphabet. The symmetric tuple still generates the same group
as the original three generators, so the fiber count concerns the same
$336$ elements.
```

- [ ] **Step 11: E14 — name the fiber (1031-1033)**

OLD:
```
The proof partitions these words into $336$ fibers, one for each group
element. A computation over binary naturals records the size of every
fiber.
```
NEW:
```
The proof partitions these words by evaluated group element. I call the
set of words that evaluate to $g$ the fiber of $g$, and there are $336$
fibers. A computation over binary naturals records the size of every
fiber.
```

- [ ] **Step 12: E20 — endpoint-transfer motivation (1052)**

OLD:
```
The first transfer maps each permutation to the endpoint of one fixed card.
```
NEW:
```
A coalition observes card endpoints rather than group elements. The
certificate therefore moves from the group to the endpoints first. The
first transfer maps each permutation to the endpoint of one fixed card.
```

- [ ] **Step 13: E17 — cross-instance example (1206-1207)**

OLD:
```
across all five. Perfect privacy in the table refers
```
NEW:
```
across all five. For example, the trace-lifting theorem of
Section~\ref{sec:framework} is consumed verbatim by all five instances,
while each instance supplies its own endpoint bound. Perfect privacy in
the table refers
```

- [ ] **Step 14: Verify the signposting count**

Run: `python3 docs/superpowers/specs/tools/wadt_signpost_neutral.py pgg-smc/paper-wadt2026/main.tex=WADT`
Expected: 11 or 12 events (4 before + 7 or 8 new I-forms depending on the
E9 branch), at least 15 per 10k.

- [ ] **Step 15: Recompile**

Run: `cd pgg-smc/paper-wadt2026 && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && pdfinfo main.pdf | grep Pages`
Expected: exit 0; note pages.

- [ ] **Step 16: Commit**

```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: signpost coined terms and ground claims with examples

E7/E8 word distribution, E9 biased cut, E10 word-shuffle model, E11
fixed representative dealer, E12 orbit class, E13 recovery ramp, E14
fiber; E15/E16/E17 for-example grounding; E19 symmetric-alphabet
reason; E20 endpoint-transfer motivation. E18 cut per audit A12."
```

---

### Task 5: Commit 3 — numeric worked example (E21)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 1: E21 — insert the example after the fixed-dealer proposition (943-945)**

OLD:
```
\end{proposition}

Two further dealers act as robustness checks on the fixed representative.
```
NEW:
```
\end{proposition}

\begin{example}\label{ex:coalition-view}
Let the dealt secret be $s=0$, so the dealt arrangement is $D_0$, and let
the shuffle be the translation $x\mapsto x+1$, which fixes the point
$\infty$ at position seven. Each position then shows the card that $D_0$
places one position later, and the coalition $\{0,1,2\}$ sees the card
values $(1,2,3)$. At $s=1$ the same shuffle would show $(1,2,4)$. By
Lemma~\ref{thm:three-transitive} some shuffle instead sends the
coalition's three positions to the positions $1$, $2$, and $4$ of $D_1$,
which hold the values $1$, $2$, and $3$. A coalition of three cards
therefore never separates the two secrets, and the proposition above makes
this uniformity exact.
\end{example}

Two further dealers act as robustness checks on the fixed representative.
```

Values were source-verified by the Opus audit (seat $i$ observes
$D(\rho(g)(i))$, `tr_tbl = [1;2;3;4;5;6;0;7]`, $D_1$ = `[0;1;2;4;3;5;6;7]`).
Do NOT add any `\spnewtheorem{example}` declaration; llncs predefines it.

- [ ] **Step 2: Recompile and check the example renders**

Run: `cd pgg-smc/paper-wadt2026 && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && grep -c "Example" main.aux; pdfinfo main.pdf | grep Pages`
Expected: exit 0; at least one Example aux entry; note final page count.

- [ ] **Step 3: Commit**

```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: worked coalition-view example for the PGL instance

One run at s=0 under the translation shuffle, the (1,2,3) coalition
view, the s=1 contrast (1,2,4), and the three-transitivity repair.
Values verified against pgl27_orbit.v and card_exchange_pismc.v."
```

---

### Task 6: Inserted-prose style audit

**Files:**
- Read: `pgg-smc/paper-wadt2026/main.tex` (the diff `e39751e1..HEAD`)

- [ ] **Step 1: Mechanical checks on the full diff**

Run:
```bash
git diff e39751e1..HEAD -- pgg-smc/paper-wadt2026/main.tex | grep '^+' | grep -nE '—|;' | grep -v ';}' | grep -vE '^\+\+\+'
git diff e39751e1..HEAD -- pgg-smc/paper-wadt2026/main.tex | grep '^+' | grep -inE '\blaw\b|\bwe (call|define|write|denote)\b'
```
Expected: no matches from either command (LaTeX `\;` and code contexts
excluded by inspection if they appear).

- [ ] **Step 2: Jargon table check**

The jargon table for the inserted text (rule: rate H/M/L, plain rewrite
for every H). Verify each row still matches the landed text:

| Term in inserted text | Rating | Treatment |
|---|---|---|
| shuffle-security bound | M | existing record-role name, glossed by Table 1 |
| dealer layout | L | plain |
| direct case analysis | L | plain |
| deck enumeration | M | matches the paper's existing register (line 699) |
| word distribution | L after E7/E8 | signposted at first use |
| biased cut | L after E9 | signposted |
| word-shuffle model | L after E10 | signposted |
| fixed representative dealer | L after E11 | signposted |
| orbit class | L after E12 | signposted |
| recovery ramp | L after E13 | signposted |
| fiber | L after E14 | signposted |
| base triple | L | defined in context by E16 |
| trace-lifting theorem | M | names an existing Section 3 theorem |
| endpoint | M | established term from Sections 2-3 |

No H-rated terms: no rewrites required. If landing changed any wording,
re-rate the changed row; any H requires a plain rewrite before Task 7.

---

### Task 7: Acceptance re-run (the same skill check)

**Files:**
- No modifications. Instruments only.

- [ ] **Step 1: Census and control panel (same baseline, same peers)**

Run:
```bash
python3 ~/.claude/skills/baseline-transition-analysis/scripts/count_connectives.py \
  ~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf \
  pgg-smc/paper-wadt2026/main.tex --labels Shinagawa,WADT
python3 ~/.claude/skills/baseline-transition-analysis/scripts/control_panel.py \
  --target pgg-smc/paper-wadt2026/main.tex \
  --baseline ~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf \
  ~/.claude/research-kb/pdfs/Iwamoto2024-itsec.pdf \
  ~/.claude/research-kb/pdfs/2205.04774_shinagawa_miyamoto_automorphism_shuffles.pdf \
  ~/.claude/research-kb/pdfs/KochSchremppKirsten2021-cardcrypto-formal-verification.pdf \
  ~/.claude/research-kb/pdfs/koch-walzer-2017-423-actively-secure-cardbased.pdf
python3 ~/.claude/skills/baseline-transition-analysis/scripts/fact_density.py \
  ~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf=Shinagawa21 \
  pgg-smc/paper-wadt2026/main.tex=WADT
```

- [ ] **Step 2: Committed instruments**

Run:
```bash
python3 docs/superpowers/specs/tools/wadt_per_section.py
python3 docs/superpowers/specs/tools/wadt_signpost_neutral.py \
  pgg-smc/paper-wadt2026/main.tex=WADT \
  ~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf=Shinagawa21 \
  ~/.claude/research-kb/pdfs/Iwamoto2024-itsec.pdf=Iwamoto24 \
  ~/.claude/research-kb/pdfs/2205.04774_shinagawa_miyamoto_automorphism_shuffles.pdf=ShinMiya22 \
  ~/.claude/research-kb/pdfs/KochSchremppKirsten2021-cardcrypto-formal-verification.pdf=KochSK21 \
  ~/.claude/research-kb/pdfs/koch-walzer-2017-423-actively-secure-cardbased.pdf=KochWalzer17
```

- [ ] **Step 3: Check every gate**

| Gate | Before | Target | Where measured |
|------|-------:|-------:|----------------|
| std census TOTAL per 10k | 14.9 | >= 30 | count_connectives |
| instance family per 10k | 1.5 | >= 5.5 | count_connectives |
| worked Example blocks | 0 | >= 1 | count_connectives |
| adversative (std) events | 0 | >= 1 | count_connectives |
| reason events | 4 | >= 6 | count_connectives |
| inference events | 5 | >= 7 | count_connectives |
| neutral signposting per 10k | 6.0 | >= 14 | wadt_signpost_neutral |
| Section 3 std moves | 0 | >= 3 | wadt_per_section |
| Section 7 all per 10k | 11.9 | >= 25 | wadt_per_section |
| compile | 21 pp clean | clean, pages reported | latexmk |

Any failed gate: diagnose which edit was expected to supply the missing
events (spec "Projection basis"), fix wording within the spec's voice
rules, recompile, amend nothing silently: land the fix as a follow-up
commit, then re-run this task.

- [ ] **Step 4: Report in chat (Zh-TW), Phase C shape**

The report must include: the census table, the control-panel verdict, the
density and per-section tables, gate pass/fail, the final page count, the
E9 branch taken, and the two disclosures: reason/inference gates were
lowered to 6/7 with one-event margins (spec Decision 7), and the std
TOTAL remains below the 46.5 peer floor by design (spec "Honest
expectation"). State what a future round would need for band entry.

---

## Self-review notes

- Spec coverage: E1-E17, E19-E22 all appear (E18 is cut by spec Decision
  6; no task implements it). Verification protocol steps 1-4 map to
  Tasks 1, 3, 6, 7. Jargon table required by spec step 3 is embedded in
  Task 6.
- OLD strings were transcribed from the `e39751e1` file content read this
  session, with original line breaks.
- Type consistency: not applicable (prose only); term consistency checked
  in Task 6's jargon table.
