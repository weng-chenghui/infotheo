# WADT Round 2: Peer-Mean Transition Density Design

**Date:** 2026-08-10
**Target:** `pgg-smc/paper-wadt2026/main.tex` at commit `5ad9246b` (21 pages, 7047 words by `count_connectives.py` v2)
**Instrument:** `baseline-transition-analysis` v2 (case-insensitive families, I-voice signposting, `per_section.py`). All numbers in this spec are v2 numbers. Never compare against round-1 (v1) numbers.
**Predecessor:** `2026-08-10-wadt-transition-fixes-design.md` (round 1, landed as commits `906e2146..5ad9246b`).

## Goal

Raise the paper's motivational-move density from 26 moves (37.2/10k) into the
peer-mean band (peer mean 71.9/10k, band floor 49.2/10k) by adding 24 counted
moves across six streams, including a new card-glyph figure that shows the
three PGL(2,7) generators acting on a row of eight cards. Projected result:
50 moves at roughly 7330 words, about 68/10k.

## Decisions (user-approved 2026-08-10)

| # | Decision | Choice |
|---|---|---|
| D1 | Quantitative target | Pull toward peer mean (~60-65/10k as gate floor; projection lands ~68) |
| D2 | Page budget | No page limit |
| D3 | Content scope | Abstract, Conclusion, new worked examples, Related Work adversatives, scattered connectives |
| D4 | gloss / aside families | Both stay at zero. The spec forbids introducing "roughly speaking / informally / intuitively" and "I note / I observe / I remark" |
| D5 | Method | Quota-per-section exact-string edits (approach A) |
| D6 | Card-glyph explainer | New figure + example showing the three generators on cards, in Section 5 after Equation `eq:pgl-order`. This replaces the earlier idea of a Kim/word-shuffle worked example, since the Kim material already has card rows and leakage-bit figures |
| D7 | Flow | Spec → Opus adversarial audit → amended spec → user review → writing-plans → execute in 3 commits → re-run baseline-transition-analysis full panel as acceptance |

## Counted vocabulary (v2 families)

Every planned move below must literally match one of these regexes, or it
does not count. The plan writer and the auditor check each edit against them.

| Family | v2 regex |
|---|---|
| orientation | `(?i:\bin this (?:section\|paper\|article\|chapter))\b` |
| purpose | `(?i:\b(?:in order to\|so that (?:we\|i)\|so as to))\b` |
| reason | `(?i:\b(?:because\|since))\b` |
| inference | `(?i:\b(?:thus\|therefore\|hence))\b` |
| instance | `(?i:\bfor (?:example\|instance))\b` |
| worked example | `(\bExample\s+\d\|\\begin\{example\})` |
| adversative | `(?i:\b(?:although\|however))\b` |
| gloss (FORBIDDEN) | `(?i:\b(?:roughly speaking\|informally\|intuitively))\b` |
| aside (FORBIDDEN) | `\b(?:[Ww]e\|I) (?:note\|can observe\|observe\|sometimes\|remark)\b` |

Warnings baked into the edits: ", so" and "instead / in contrast / whereas /
unlike" count only in the `--ext` supplement, never in std. `so that the ...`
does not count (only "so that we/I"). TikZ bodies are stripped by the census,
so figures contribute moves only through captions and surrounding prose.

## Quota table (projected)

| Stream | Edits | New moves | Families |
|---|---|---|---|
| A: Abstract | R1, R2 | +2 | reason, inference |
| B: Conclusion | R3, R4, R5 | +3 | inference x2, purpose |
| C: Five-card example | R6 | +3 | example block, instance, reason |
| D: PGL glyph figure + example | R7, R8 | +3 | example block, reason, instance |
| E: Related Work | R9-R13 | +6 | although x2, however x3, therefore |
| F: Scattered | R14-R20 | +7 | orientation, reason x3, inference x2, instance |
| **Total** | 20 edits | **+24** | 26 → 50 moves, ~68/10k |

## Edit inventory

Anchors are line numbers at commit `5ad9246b`. All edits are exact-string;
the implementation plan repeats each with full OLD/NEW context.

### Stream A: Abstract

**R1 (reason).**
OLD: `For a finite implementation, I analyze a uniform word of length 200
over five generator letters.`
NEW: `Because no single physical move samples a uniform group element, I
analyze a finite implementation that draws a uniform word of length 200 over
five generator letters.`

**R2 (inference).**
OLD: `Transport theorems then bound approximate coalition-view and
executed-trace privacy by $2^{-39}$ under the word distribution.`
NEW: `Transport theorems therefore bound approximate coalition-view and
executed-trace privacy by $2^{-39}$ under the word distribution.`

### Stream B: Conclusion

**R3 (inference).** Insert after `...and the dealer distributions stated in
Section~\ref{sec:model}. The verifier learns the secret.` (end of first
paragraph, line ~1364):
`The coalition bound rests on the three-transitive action alone, and the
generic privacy theorem therefore transfers to any instance that proves the
same transitivity.`
Grounding: `thm:generic-privacy` consumed at $t=3$ via
`thm:three-transitive` (paper lines 836-839).

**R4 (inference).** Insert after `...and approximate coalition-view and
executed-trace bounds at $2^{-39}$.` (line ~1370):
`The word-shuffle model hence replaces the ideal uniform shuffle at a
quantified and machine-checked cost.`

**R5 (purpose).**
OLD: `The entropy form of approximate privacy needs a quantitative
continuity modulus for the binary entropy function near one half.`
NEW: `The entropy form of approximate privacy needs a quantitative
continuity modulus for the binary entropy function near one half in order to
convert the $L_1$ bound into a conditional-entropy bound.`

### Stream C: Five-card worked example

**R6.** Insert after `Only the two-card value depends on the pattern's
shape.` (line 677):

```latex
\begin{example}\label{ex:fivecard-shape}
Let the reveal expose two of the five positions. Two adjacent positions
determine the conjunction to $0.154$ bits. Two positions at cyclic
distance two determine it to $0.119$ bits. The decimals evaluate the
proven closed forms, for instance the adjacent value is
$\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log 7$. One more revealed
card erases the difference, because every three-card reveal leaks the
same amount.
\end{example}
```

Grounding: `leak_k2_adj`, `leak_k2_dist2`, `leak_k3`, `leak_k3_gap` in
`pgg-smc/instances/denboer1989/five_card_leakage.v`; decimals 0.154 / 0.119
already appear in `fig:fivecard-leakage`; the closed form is quoted verbatim
from the existing footnote (paper line 621). Audit must confirm adjacent
maps to `leak_k2_adj` and cyclic-distance-two to `leak_k2_dist2`, and that
rotation invariance (`fc_sigma` equivariance) justifies the position-free
phrasing.

### Stream D: PGL card-glyph figure and example

**R7 (lead-in + figure).** Insert after Equation `eq:pgl-order` paragraph
(line 767), before `Each valid arrangement contains eight distinct cards.`:

Lead-in prose:
`The three generator letters make this action concrete on the cards
themselves. Figure~\ref{fig:pgl-generators} shows each letter as a
rearrangement of the row of eight cards, one card per projective point.`

```latex
\begin{figure}[H]
  \centering
  \begin{tikzpicture}[every node/.style={font=\small},
      card/.style={draw,minimum width=7mm,minimum height=9mm,inner sep=1pt}]
    \foreach \p in {0,...,7}
      \node[gray] at (\p*0.85,0.85) {\p};
    \node at (-2.1,0) {deck $D$};
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
  \caption{The three generator letters acting on the identity deck. Gray
  labels are card positions. Position $i$ shows the image point $g(i)$,
  the observation convention of Section~\ref{sec:model}, and the rows are
  the kernel tables \coqin{tr\_tbl}, \coqin{sc\_tbl}, and \coqin{inv\_tbl},
  which encode $\infty$ as the value $7$. The order $336=8\cdot 7\cdot 6$
  matches one group element for each ordered destination of three chosen
  points.}
  \label{fig:pgl-generators}
\end{figure}
```

Grounding, all in `pgg-smc/instances/pgl27/pgl27_group.v` lines 51-53:
`tr_tbl = [1;2;3;4;5;6;0;7]`, `sc_tbl = [0;3;6;2;5;1;4;7]`,
`inv_tbl = [7;6;3;2;5;4;1;0]`. Direction convention: paper Section 2 lines
197-199 state position $i$ of the shuffled arrangement holds the card that
$D$ places at position $\rho(g)(i)$; with the identity deck this shows
$g(i)$, which is the table entry, so the rows transcribe the tables
verbatim (with entry 7 printed as $\infty$). The caption's final sentence
asserts sharp 3-transitivity via $336=8\cdot7\cdot6$; the kernel proves the
order and existence (`pgl27_3transitive`), sharpness is the classical
count. Audit rules on the wording.

**R8 (example).** Insert after the figure:

```latex
\begin{example}\label{ex:pgl-letters}
Let the deck be the identity assignment with card $z$ at position $z$.
The translation letter turns the row $(0,1,2,3,4,5,6,\infty)$ into
$(1,2,3,4,5,6,0,\infty)$ because position $i$ shows the image $g(i)$.
The scaling letter fixes $0$ and $\infty$ and moves the six remaining
points in one six-cycle. The inversion letter exchanges $0$ and $\infty$.
Words in the three letters reach all $336$ group elements, for example
the table behind Lemma~\ref{thm:three-transitive} stores for every
ordered triple of distinct points one word that carries $(0,1,2)$ to it.
\end{example}
```

Grounding: six-cycle of $z\mapsto 3z$ on $\mathbb{F}_7^\times$ is
$(1\,3\,2\,6\,4\,5)$ since 3 is a primitive root mod 7 (audit re-derives
from `sc_tbl`). The base-triple table claim restates existing paper text
(lines 832-835). `Lemma~\ref{thm:three-transitive}` is a forward reference
from Section 5's opening half; acceptable in LaTeX, audit judges whether
the prose needs a "below" cue.

### Stream E: Related Work

**R9 (although).**
OLD: `Later protocols reduced the
number of cards and supported other functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.`
(the Related Work occurrence, line 1306; the Introduction has a similar
sentence that stays untouched)
NEW: `Although the security is already perfect, later protocols reduced the
number of cards and supported other
functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.`

**R10 (however).**
OLD: `The present development proves reusable
group-action, execution, privacy, and mixing lemmas in \Rocq{}.`
NEW: `The present development, however, proves reusable group-action,
execution, privacy, and mixing lemmas in \Rocq{}.`

**R11 (although).**
OLD: `It varies the card type
and the allowed physical operations. The framework in this paper instead
varies the finite group, its permutation action, the shuffle distribution,
and the reconstruction map.`
NEW: `Although Shinagawa's model varies the card type and the allowed
physical operations, the framework in this paper varies the finite group,
its permutation action, the shuffle distribution, and the reconstruction
map.`
Note: the existing `in this paper` orientation move is preserved.

**R12 (however).**
OLD: `The PGL proof uses another
route.`
NEW: `The PGL proof, however, uses another route.`

**R13 (however + therefore).**
OLD: `The present work uses the MathComp and infotheo libraries for finite
algebra, probability, independence, and entropy~\cite{MathComp,InfoTheo}.`
NEW: `The present work, however, needs finite group actions and entropy
rather than a full cryptographic program logic, and it therefore uses the
MathComp and infotheo libraries for finite algebra, probability,
independence, and entropy~\cite{MathComp,InfoTheo}.`
Claim check for audit: the development uses no game-hopping or
probabilistic program logic; its imports are MathComp finite algebra plus
infotheo entropy and the FORTE interpreter.

### Stream F: Scattered connectives

**R14 (orientation, Introduction).**
OLD: `The group parameters pay for this connection.`
NEW: `In this paper, the group parameters pay for this connection.`

**R15 (reason, Section 2).**
OLD: `Security rests on the shuffle alone. A player sees one card, and a
coalition sees the cards at its positions.`
NEW: `Security rests on the shuffle alone, because a player sees one card
and a coalition sees the cards at its positions.`

**R16 (inference, Section 2).**
OLD: `The dealer
process takes a list of alternative cuts and deals one hand per cut, so a
word enters the execution only through its evaluated group
element.`
NEW: `The dealer process takes a list of alternative cuts and deals one
hand per cut. A word hence enters the execution only through its evaluated
group element.`

**R17 (inference, Section 4).**
OLD: `At bias zero the witness bound
collapses to zero for any positive word length, which is the precise sense
in which the unbiased member is den Boer's protocol.`
NEW: `At bias zero the witness bound collapses to zero for any positive
word length. Hence the unbiased member is den Boer's protocol in a precise
sense.`

**R18 (reason, Section 4).**
OLD: `The two members share one executed program, so correctness transfers
verbatim.`
NEW: `Because the two members share one executed program, correctness
transfers verbatim.`

**R19 (instance, Section 7).**
OLD: `At $L=200$, the sample space contains $5^{200}$ words.`
NEW: `For example, at $L=200$ the sample space contains $5^{200}$ words.`

**R20 (reason, Section 8).**
OLD: `A card never changes piles, so its distance from the
uniform distribution on all ten positions cannot converge to zero.`
NEW: `Because a card never changes piles, its distance from the uniform
distribution on all ten positions cannot converge to zero.`

## Register constraints (all edits)

- No em-dashes, no semicolons, no parenthetical asides.
- Authorial voice is "I", never mathematical "we". Examples use the
  impersonal "Let ... be" register.
- "distribution", never "law". No abbreviations in prose.
- gloss and aside families stay at zero (D4).
- New TikZ is drawn at true document font sizes and never scaled.
- Rewritten sentences must be simpler than their originals with meaning
  preserved exactly (claims, hedges, quantifiers, citations).

## Acceptance gates (v2 instrument, full panel re-run)

| Gate | Threshold | Source |
|---|---|---|
| TOTAL | >= 60 moves/10k | `count_connectives.py` target column |
| Worked-example blocks | >= 3 | family row |
| adversative | >= 5 | family row |
| gloss, aside | = 0 each | family row (D4) |
| Abstract std | >= 2 | `per_section.py` |
| Conclusion std | >= 3 | `per_section.py` |
| Section 4 (five-card) std | >= 3 | `per_section.py` |
| Every section std/10k | >= 24.6 (half the band floor) | `per_section.py` |
| Compile | clean `latexmk`, no new warnings, page count unconstrained | build log |
| Content fidelity | no claim, hedge, quantifier, or citation changed; all example values verified against the named Rocq sources | Opus audit + plan review |
| Panel verdict | reported with peer mean 71.9 / floor 49.2 context; disclosed honestly whether the paper enters the band | `control_panel.py` |

Verification input sources: `pgl27_group.v` (generator tables),
`pgl27_orbit.v` (orbit sizes), `five_card_leakage.v` (closed forms),
`pgl27_mixing.v` (word-length and fiber facts), paper at `5ad9246b`.

## Execution shape (for writing-plans)

Three commits: (1) Stream C + D (figures and examples, the technically
audited content), (2) Streams A + B + E (abstract, conclusion, related
work), (3) Stream F (scattered) + acceptance re-run + report. Compile after
each commit with `latexmk` and check the census delta against the quota
table.
