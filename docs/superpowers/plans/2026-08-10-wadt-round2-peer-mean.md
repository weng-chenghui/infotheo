# WADT Round 2 Peer-Mean Density Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the 20 audit-amended edits R1-R20 from `docs/superpowers/specs/2026-08-10-wadt-round2-peer-mean-design.md` on `pgg-smc/paper-wadt2026/main.tex`, raising the v2 census from 26 moves (37.2/10k) to 50 moves (~68/10k), then re-run the baseline-transition-analysis v2 full panel as the acceptance gate.

**Architecture:** Three commits on branch `pgg-smc`, each followed by a clean `latexmk` compile and a census checkpoint: (1) worked examples and the PGL generator card figure, (2) abstract + conclusion + related work, (3) scattered connectives + full acceptance. All edits are exact-string replacements in one file; OLD strings below are character-exact including line breaks, verified against the working tree at `235aae65`.

**Tech Stack:** LaTeX (llncs), latexmk, `~/.claude/skills/baseline-transition-analysis/scripts/` v2 instruments (count_connectives.py, per_section.py, fact_density.py, control_panel.py).

**Panel files (acceptance):**
- Baseline: `~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf`
- Peers: `~/.claude/research-kb/pdfs/Iwamoto2024-itsec.pdf`, `~/.claude/research-kb/pdfs/2205.04774_shinagawa_miyamoto_automorphism_shuffles.pdf`, `~/.claude/research-kb/pdfs/KochSchremppKirsten2021-cardcrypto-formal-verification.pdf`, `~/.claude/research-kb/pdfs/koch-walzer-2017-423-actively-secure-cardbased.pdf`

**Conventions:** No em-dashes, no semicolons, no prose parentheses, I-voice, "distribution" never "law", gloss/aside families must stay at zero. Commits touch only `main.tex` (no `.v` files), so the rocq-audit pre-commit gate passes trivially. Never use `git commit --amend` (blocked by hook); follow-up commits only.

---

### Task 1: Worked examples and PGL generator figure (R6, R7, R8)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 4 line ~677, Section 5 line ~767)

- [ ] **Step 1.1: R6, five-card shape example.** Exact-string edit:

OLD:
```
Only the two-card value
depends on the pattern's shape.

\begin{proposition}
```

NEW:
```
Only the two-card value
depends on the pattern's shape.

\begin{example}\label{ex:fivecard-shape}
Let the reveal expose two of the five positions. Two adjacent positions
reveal $0.154$ bits about the conjunction, and two positions at cyclic
distance two reveal $0.119$ bits. Both decimals evaluate proven closed
forms, for instance the adjacent value is
$\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log 7$. The shape stops
mattering at three revealed cards, because the closed form there depends
only on how many cards the reveal exposes.
\end{example}

\begin{proposition}
```

- [ ] **Step 1.2: R7, generator figure with lead-in.** Exact-string edit:

OLD:
```
  \label{eq:pgl-order}
\end{equation}

Each valid arrangement contains eight distinct cards.
```

NEW:
```
  \label{eq:pgl-order}
\end{equation}

Three fractional linear maps generate this action. They are the
translation $z\mapsto z+1$, the scaling $z\mapsto 3z$, and the inversion
$z\mapsto -1/z$.\footnote{The rows of Figure~\ref{fig:pgl-generators} are
the permutation tables of the three maps, identified with them by
\coqin{tr\_moebius}, \coqin{sc\_moebius}, and \coqin{inv\_moebius} in
\path{pgg-smc/instances/pgl27/pgl27_group.v}.}
Figure~\ref{fig:pgl-generators} shows each map as a rearrangement of the
row of eight cards, one card per projective point. The executable shuffle
of Section~\ref{sec:mixing} draws its letters from these three maps and
from two inverses.

\begin{figure}[H]
  \centering
  % Drawn at true document font sizes; the picture is never scaled.
  \begin{tikzpicture}[every node/.style={font=\small},
      card/.style={draw,minimum width=7mm,minimum height=9mm,inner sep=1pt}]
    \foreach \p in {0,...,7}
      \node[gray] at (\p*0.85,0.85) {\p};
    \node at (-2.1,0) {$z\mapsto z$};
    \foreach \p/\c in {0/0,1/1,2/2,3/3,4/4,5/5,6/6,7/\infty}
      \node[card] at (\p*0.85,0) {$\c$};
    \node at (-2.1,-1.2) {$z\mapsto z+1$};
    \foreach \p/\c in {0/1,1/2,2/3,3/4,4/5,5/6,6/0,7/\infty}
      \node[card] at (\p*0.85,-1.2) {$\c$};
    \node at (-2.1,-2.4) {$z\mapsto 3z$};
    \foreach \p/\c in {0/0,1/3,2/6,3/2,4/5,5/1,6/4,7/\infty}
      \node[card] at (\p*0.85,-2.4) {$\c$};
    \node at (-2.1,-3.6) {$z\mapsto -1/z$};
    \foreach \p/\c in {0/\infty,1/6,2/3,3/2,4/5,5/4,6/1,7/0}
      \node[card] at (\p*0.85,-3.6) {$\c$};
  \end{tikzpicture}
  \caption{The three generating maps acting on the row that places card
  $z$ at position $z$. Gray labels are card positions. Position $i$ shows
  the image point $g(i)$, the observation convention of
  Section~\ref{sec:model}, with the point at infinity carried by position
  seven. Figure~\ref{fig:encoding} draws the same row as the encoded
  arrangement $D_0$ and writes its eighth card as the value $7$. The
  order $336$ equals the number $8\cdot 7\cdot 6$ of ordered triples of
  distinct points, so Lemma~\ref{thm:three-transitive} leaves exactly one
  group element for each ordered destination.}
  \label{fig:pgl-generators}
\end{figure}

\begin{example}\label{ex:pgl-letters}
Let the deck be the identity assignment with card $z$ at position $z$.
The translation map turns the row $(0,1,2,3,4,5,6,\infty)$ into
$(1,2,3,4,5,6,0,\infty)$ because position $i$ shows the image $g(i)$.
The scaling map fixes $0$ and $\infty$ and moves the six remaining
points in one six-cycle. The inversion map is an involution. It
exchanges $0$ with $\infty$, $1$ with $6$, $2$ with $3$, and $4$ with
$5$. Words in the three maps reach every one of the $336$ group
elements. Lemma~\ref{thm:three-transitive} below gives one such word for
every ordered triple of distinct points, for example a word that carries
$(0,1,2)$ to $(2,0,1)$.
\end{example}

Each valid arrangement contains eight distinct cards.
```

(R8 is the example block inside this same edit.)

- [ ] **Step 1.3: Compile.** Run in `pgg-smc/paper-wadt2026/`: `latexmk -pdf main.tex`. Expected: exit 0, no new warnings beyond the pre-existing single Overfull, `fig:pgl-generators` renders before `fig:encoding`.

- [ ] **Step 1.4: Census checkpoint.** Run `python3 ~/.claude/skills/baseline-transition-analysis/scripts/count_connectives.py pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/main.tex --labels W,W`. Expected: TOTAL 32 moves (was 26; +2 example blocks, +2 reason, +1 instance, +1 for example), worked-example row 3, gloss 0, aside 0.

- [ ] **Step 1.5: Commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: pgl generator card figure and two worked examples"
```

### Task 2: Abstract, Conclusion, Related Work (R1-R5, R9-R13)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (abstract ~56, conclusion ~1360-1374, related work ~1306-1350; line numbers shift +55 after Task 1)

- [ ] **Step 2.1: R1 (abstract, reason).**

OLD:
```
For a finite implementation, I analyze a uniform word of length 200
over five generator letters.
```
NEW:
```
Because no single physical move samples a uniform group element, I
analyze a finite implementation that draws a uniform word of length 200
over five generator letters.
```

- [ ] **Step 2.2: R2 (abstract, inference).**

OLD:
```
Transport theorems then
bound approximate coalition-view and executed-trace privacy by $2^{-39}$
under the word distribution.
```
NEW:
```
Transport theorems therefore bound approximate coalition-view and
executed-trace privacy by $2^{-39}$ under the word distribution.
```

- [ ] **Step 2.3: R3 (conclusion, inference).**

OLD:
```
distributions stated in Section~\ref{sec:model}. The verifier learns the
secret.

For a finite shuffle implementation
```
NEW:
```
distributions stated in Section~\ref{sec:model}. The verifier learns the
secret. Theorem~\ref{thm:generic-privacy} consumes only the
three-transitive action, the fixed encoding into decks of distinct
cards, and the uniform group distribution, and it therefore transfers to
any instance that supplies these three inputs.

For a finite shuffle implementation
```

- [ ] **Step 2.4: R4 (conclusion, inference).**

OLD:
```
prior, and approximate coalition-view and executed-trace bounds at
$2^{-39}$.
```
NEW:
```
prior, and approximate coalition-view and executed-trace bounds at
$2^{-39}$. The word-shuffle model hence replaces the ideal uniform
shuffle at a quantified and machine-checked cost.
```

- [ ] **Step 2.5: R5 (conclusion, purpose).**

OLD:
```
The entropy
form of approximate privacy needs a quantitative continuity modulus for the
binary entropy function near one half.
```
NEW:
```
The entropy form of approximate privacy needs a quantitative continuity
modulus for the binary entropy function near one half in order to
convert the $L_1$ bound into a conditional-entropy bound.
```

- [ ] **Step 2.6: R9 (related work, although).**

OLD:
```
Later protocols reduced the
number of cards and supported other functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.
```
NEW:
```
Although the security is already perfect against passive participants,
later protocols reduced the number of cards and supported other
functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.
```

- [ ] **Step 2.7: R10 (related work, however).**

OLD:
```
The present development proves reusable
group-action, execution, privacy, and mixing lemmas in \Rocq{}.
```
NEW:
```
The present development, however, proves reusable group-action,
execution, privacy, and mixing lemmas in \Rocq{}.
```

- [ ] **Step 2.8: R11 (related work, although).**

OLD:
```
It varies the card type
and the allowed physical operations. The framework in this paper instead
varies the finite group, its permutation action, the shuffle distribution,
and the reconstruction map.
```
NEW:
```
Although Shinagawa's model varies the card type and the allowed physical
operations, the framework in this paper varies the finite group, its
permutation action, the shuffle distribution, and the reconstruction
map.
```

- [ ] **Step 2.9: R12 (related work, however).**

OLD:
```
The PGL proof uses another
route.
```
NEW:
```
The PGL proof, however, uses another route.
```

- [ ] **Step 2.10: R13 (related work, however + therefore).**

OLD:
```
The present work uses the MathComp and infotheo libraries for finite
algebra, probability, independence, and entropy~\cite{MathComp,InfoTheo}.
```
NEW:
```
The present work, however, states information-theoretic bounds rather
than game-based reductions, and it therefore uses the MathComp and
infotheo libraries for finite algebra, probability, independence, and
entropy~\cite{MathComp,InfoTheo}.
```

- [ ] **Step 2.11: Compile.** `latexmk -pdf main.tex`. Expected: exit 0, clean.

- [ ] **Step 2.12: Census checkpoint.** Same self-panel command as Step 1.4. Expected: TOTAL 43 (+2 abstract, +3 conclusion, +6 related work), adversative 6, gloss 0, aside 0. Also `per_section.py`: preamble+abstract std 2, Conclusion std 3, Related Work std 7.

- [ ] **Step 2.13: Commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: motivate abstract, conclusion, and related work"
```

### Task 3: Scattered connectives (R14-R20) + acceptance

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (intro ~93, model ~178 and ~271, five-card ~610 and ~689, mixing ~1055, instances ~1297; numbers pre-Task-1)

- [ ] **Step 3.1: R14 (introduction, orientation).**

OLD:
```
The paper proves
the security results in the ideal model and then proves that the word
distribution approximates it.
```
NEW:
```
In this paper I prove the security results in the ideal model and then
prove that the word distribution approximates it.
```

- [ ] **Step 3.2: R15 (model, reason).**

OLD:
```
Security rests on the shuffle alone. A player sees one card, and a
coalition sees the cards at its positions.
```
NEW:
```
Security rests on the shuffle alone, because the dealer's encoding of
the secret is fixed and the shuffle carries all the randomness. A player
sees one card, and a coalition sees the cards at its positions.
```

- [ ] **Step 3.3: R16 (model, inference).**

OLD:
```
The dealer
process takes a list of alternative cuts and deals one hand per cut, so a
word enters the execution only through its evaluated group
element.
```
NEW:
```
The dealer process takes a list of alternative cuts and deals one hand
per cut. A word hence enters the execution only through its evaluated
group element.
```

- [ ] **Step 3.4: R17 (five-card, inference).**

OLD:
```
At bias zero the witness bound collapses to zero for any positive word
length, which is the precise sense in which the unbiased member is den
Boer's protocol.
```
If this string mismatches on wrapping, re-read lines 605-615 and match the
actual wrapping; the sentence is unique. NEW:
```
At bias zero the witness bound collapses to zero for any positive word
length. The unbiased member is therefore den Boer's protocol in
precisely this sense.
```
(The `\footnote{\coqin{five\_card\_eps0\_eq0} ...}` stays attached
immediately after the final period.)

- [ ] **Step 3.5: R18 (five-card, reason).**

OLD:
```
The two members share one executed program, so correctness transfers
verbatim.
```
NEW:
```
Because the two members share one executed program, correctness
transfers verbatim.
```

- [ ] **Step 3.6: R19 (mixing, instance).**

OLD:
```
At $L=200$, the sample space contains $5^{200}$ words.
```
NEW:
```
For instance, at the Theorem B length $L=200$ the sample space contains
$5^{200}$ words.
```

- [ ] **Step 3.7: R20 (instances, reason).**

OLD:
```
A card never changes piles, so its distance from the
uniform distribution on all ten positions cannot converge to zero.
```
NEW:
```
Because a card never changes piles, its distance from the uniform
distribution on all ten positions cannot converge to zero.
```

- [ ] **Step 3.8: Compile.** `latexmk -pdf main.tex`. Expected: exit 0. Note final page count (audit projects 24).

- [ ] **Step 3.9: Full acceptance run.** Commands and gates:

```bash
S=~/.claude/skills/baseline-transition-analysis/scripts
T=pgg-smc/paper-wadt2026/main.tex
B=~/.claude/research-kb/pdfs/Shinagawa2021-dihedral-symmetry.pdf
python3 $S/count_connectives.py $B $T --labels Shinagawa,WADT
python3 $S/per_section.py $T --ext
python3 $S/control_panel.py --target $T --baseline $B \
  ~/.claude/research-kb/pdfs/Iwamoto2024-itsec.pdf \
  ~/.claude/research-kb/pdfs/2205.04774_shinagawa_miyamoto_automorphism_shuffles.pdf \
  ~/.claude/research-kb/pdfs/KochSchremppKirsten2021-cardcrypto-formal-verification.pdf \
  ~/.claude/research-kb/pdfs/koch-walzer-2017-423-actively-secure-cardbased.pdf
python3 $S/fact_density.py $B $T=WADT \
  ~/.claude/research-kb/pdfs/Iwamoto2024-itsec.pdf
```

Gates (from spec): TOTAL >= 60/10k (expect ~50 moves / ~7338 words = 68.1);
example blocks >= 3; adversative >= 5 (expect 6); gloss = 0; aside = 0;
Abstract std >= 2 (expect exactly 2); Conclusion std >= 3 (expect exactly
3); five-card section std >= 3 (expect 6); every section >= 24.6/10k
(expect lowest ~43.8); clean compile. If any gate fails, fix within the
counted-vocabulary constraint (spec table) and re-run; do not touch gloss
or aside vocabulary to close a gap.

- [ ] **Step 3.10: Commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex
git commit -m "paper: scattered counted connectives for peer-band density"
```

- [ ] **Step 3.11: Report.** Report in Zh-TW with the honesty disclosures
required by the spec's gate table: page growth 21 to 24; 8 of 24 moves are
relabelings of existing constructions and the `--ext` supplement falls 15
to 11; Abstract and Conclusion gates at zero margin; R5 is deliberate new
content; R1, R11, R13 accept the simplicity-rule deviation. State the
panel verdict honestly (peer mean 71.9, floor 49.2, target now ~68).
