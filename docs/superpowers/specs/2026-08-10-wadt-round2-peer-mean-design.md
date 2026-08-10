# WADT Round 2: Peer-Mean Transition Density Design

**Date:** 2026-08-10
**Target:** `pgg-smc/paper-wadt2026/main.tex` at commit `5ad9246b` (21 pages, 7047 words by `count_connectives.py` v2)
**Instrument:** `baseline-transition-analysis` v2 (case-insensitive families, I-voice signposting, `per_section.py`). All numbers in this spec are v2 numbers. Never compare against round-1 (v1) numbers.
**Predecessor:** `2026-08-10-wadt-transition-fixes-design.md` (round 1, landed as commits `906e2146..5ad9246b`).

## Goal

Raise the paper's motivational-move density from 26 moves (37.2/10k) into the
peer-mean band (peer mean 71.9/10k, band floor 49.2/10k) by adding 24 counted
moves across six streams, including a new card-glyph figure that shows the
three PGL(2,7) generators acting on a row of eight cards. Audit-verified
projection (the auditor built the edited paper and ran the instruments):
50 moves at 7338 words, 68.1/10k; page count grows 21 to 24; the `--ext`
supplement falls 15 to 11 because four uncounted constructions are
converted to counted vocabulary. Eight of the 24 moves are relabelings of
existing constructions (R2, R10, R11, R12, R16, R17, R18, R20); the
acceptance report must disclose this split honestly.

Audit: `2026-08-10-wadt-round2-audit.md` (Opus, findings A1-A22). This spec
incorporates every BLOCKER and AMEND resolution; the audit-resolution table
at the end records each disposition.

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
does not count (only "so that we/I"). Whole `figure` environments, captions
included, are stripped by both instruments (audit A10), so figures
contribute nothing to the census, neither moves nor words; caption edits
are census-free. Every counted move must live in body prose.

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
`Theorem~\ref{thm:generic-privacy} consumes only the three-transitive
action, the fixed encoding into decks of distinct cards, and the uniform
group distribution, and it therefore transfers to any instance that
supplies these three inputs.`
Grounding (audit A1): `thm:generic-privacy` (paper 491-502) =
`ttrans_view_indep_gen` in `pgg-smc/reconstruct/transitivity_privacy.v`
(Hypothesis Htrans line 528, HG line 531, encode line 532, uniform
shuffle in the statement). The wording names all three inputs; the earlier
"transitivity alone" draft contradicted the preceding hypotheses sentence
and was rejected.

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
reveal $0.154$ bits about the conjunction, and two positions at cyclic
distance two reveal $0.119$ bits. Both decimals evaluate proven closed
forms, for instance the adjacent value is
$\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log 7$. The shape stops
mattering at three revealed cards, because the closed form there depends
only on how many cards the reveal exposes.
\end{example}
```

Grounding (audit A9, A13, verified clean): `leak_k2_adj` is
`I(Secret; ViewA [0;1])` (`five_card_leakage.v:317`), numerically
0.154370; `leak_k2_dist2` is 0.118717; "reveal X bits about" is the
faithful mutual-information reading. The final clause is exactly `leakE3`
(`five_card_leakage.v:832`), whose closed form is cardinality-only. The
`adjacent` classifier is cyclic distance one and `leak_view_set`
(line 1049) covers all 32 subsets, so the position-free phrasing is
justified. This wording avoids restating paper lines 624-625 and 674-677.

### Stream D: PGL card-glyph figure and example

**R7 (lead-in + figure).** Insert after Equation `eq:pgl-order` paragraph
(line 767), before `Each valid arrangement contains eight distinct cards.`:

Lead-in prose (audit A2: introduces the maps before naming letters, and
reconciles with the abstract's five letters):
`Three fractional linear maps generate this action. They are the
translation $z\mapsto z+1$, the scaling $z\mapsto 3z$, and the inversion
$z\mapsto -1/z$.\footnote{The rows of Figure~\ref{fig:pgl-generators} are
the permutation tables of the three maps, identified with them by
\coqin{tr\_moebius}, \coqin{sc\_moebius}, and \coqin{inv\_moebius} in
\path{pgg-smc/instances/pgl27/pgl27_group.v}.}
Figure~\ref{fig:pgl-generators} shows each map as a rearrangement of the
row of eight cards, one card per projective point. The executable shuffle
of Section~\ref{sec:mixing} draws its letters from these three maps and
from two inverses.`

```latex
\begin{figure}[H]
  \centering
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
```

Grounding (audit A4, A11, A12, A22, verified clean): tables
`tr_tbl = [1;2;3;4;5;6;0;7]`, `sc_tbl = [0;3;6;2;5;1;4;7]`,
`inv_tbl = [7;6;3;2;5;4;1;0]` (`pgl27_group.v:51-53`); all 24 transformed
values audit-re-derived from the Moebius maps over $\mathbb{F}_7$.
Direction "position $i$ shows $g(i)$" is exact for this row
(`transitivity_privacy.v:541`, `pgg_rho` is the inclusion). The top row is
map-labelled `$z\mapsto z$`, avoiding the symbol $D$ (which Section 2
reserves for the dealt arrangement) and cross-referencing fig:encoding's
$D_0$, which prints the eighth card as 7. Kernel-name attribution lives in
the lead-in footnote using the exported lemmas `tr_moebius`,
`sc_moebius`, `inv_moebius` (not the file-local tables), keeping captions
`\coqin`-free per the paper's convention. The sharpness sentence shows its
counting step: order 336 (`pgl27_card`, `pgl27_mixing.v:474`) equals the
number of ordered triples, so existence (`pgl27_3transitive`) leaves
exactly one element each. Captions are census-stripped, so none of this
affects the quota.

**R8 (example).** Insert after the figure:

```latex
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
```

Grounding (audit A6, A14, verified clean): six-cycle of $z\mapsto 3z$ on
$\mathbb{F}_7^\times$ is $(1\,3\,2\,6\,4\,5)$; the inversion's full swap
structure (0-$\infty$, 1-6, 2-3, 4-5) is stated so the prose matches the
drawn row. The last two sentences add the "below" cue and no longer
duplicate paper lines 832-835 or `ex:coalition-view`. Vocabulary uses
"map" throughout, matching the R7 lead-in, and "letter" stays reserved
for the Section 7 alphabet. Counted moves: example block, because, for
example.

### Stream E: Related Work

**R9 (although).**
OLD: `Later protocols reduced the
number of cards and supported other functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.`
(the Related Work occurrence, line 1306; the Introduction has a similar
sentence that stays untouched)
NEW: `Although the security is already perfect against passive
participants, later protocols reduced the number of cards and supported
other functions~\cite{MizukiSone2009,MizukiSone2012,KochWalzerHartel2015}.`
(Audit A8: the passivity qualifier from the antecedent sentence is kept.)

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
NEW: `The present work, however, states information-theoretic bounds
rather than game-based reductions, and it therefore uses the MathComp and
infotheo libraries for finite algebra, probability, independence, and
entropy~\cite{MathComp,InfoTheo}.`
(Audit A7: "program logic" mislabeled CryptHOL and contradicted the FORTE
interpreter credit two sentences later; the honest contrast axis is
information-theoretic bounds versus game-based reductions.)

### Stream F: Scattered connectives

**R14 (orientation, Introduction).**
OLD: `The paper proves
the security results in the ideal model and then proves that the word
distribution approximates it.`
NEW: `In this paper I prove the security results in the ideal model and
then prove that the word distribution approximates it.`
(Audit A15: this target replaces the earlier filler candidate and also
fixes a third-person voice slip in an I-voice paper.)

**R15 (reason, Section 2).**
OLD: `Security rests on the shuffle alone. A player sees one card, and a
coalition sees the cards at its positions.`
NEW: `Security rests on the shuffle alone, because the dealer's encoding
of the secret is fixed and the shuffle carries all the randomness. A
player sees one card, and a coalition sees the cards at its positions.`
(Audit A3: the earlier draft attributed security to view size, which is
not the reason; the fixed public representative is, per paper 772-773.)

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
word length. The unbiased member is therefore den Boer's protocol in
precisely this sense.`
(Audit A5: keeps the definite hedge "precisely this sense" and does not
present the identification as derived from the bound.)

**R18 (reason, Section 4).**
OLD: `The two members share one executed program, so correctness transfers
verbatim.`
NEW: `Because the two members share one executed program, correctness
transfers verbatim.`

**R19 (instance, Section 7).**
OLD: `At $L=200$, the sample space contains $5^{200}$ words.`
NEW: `For instance, at the Theorem B length $L=200$ the sample space
contains $5^{200}$ words.`
(Audit A21: signals that 200 is the canonical Theorem B length, not an
arbitrary illustration.)

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
| Honesty disclosures | report must state: page growth 21 to 24 (A16); 8 of 24 moves are relabelings of existing constructions and `--ext` falls 15 to 11 (A17); Abstract and Conclusion gates sit at zero margin (A18); R5's purpose clause is deliberate new content (A19); R1, R11, R13 accept the simplicity-rule deviation because the added clause is the motivational move (A20) | this spec |

Verification input sources: `pgl27_group.v` (generator tables),
`pgl27_orbit.v` (orbit sizes), `five_card_leakage.v` (closed forms),
`pgl27_mixing.v` (word-length and fiber facts), paper at `5ad9246b`.

## Execution shape (for writing-plans)

Three commits: (1) Stream C + D (figures and examples, the technically
audited content), (2) Streams A + B + E (abstract, conclusion, related
work), (3) Stream F (scattered) + acceptance re-run + report. Compile after
each commit with `latexmk` and check the census delta against the quota
table.

## Audit-resolution table

Opus audit `2026-08-10-wadt-round2-audit.md`, findings A1-A22, all
resolved in this revision:

| Finding | Severity | Resolution |
|---|---|---|
| A1 | BLOCKER | R3 rewritten to name all three theorem inputs |
| A2 | BLOCKER | R7 lead-in introduces the three maps explicitly and reconciles with the five-letter alphabet |
| A3 | BLOCKER | R15 reason corrected to the fixed encoding; original second sentence kept |
| A4 | AMEND | Top row relabelled `$z\mapsto z$`; caption cross-references fig:encoding's $D_0$ and the value-7 convention |
| A5 | AMEND | R17 keeps "precisely this sense", inference marker moved to "therefore" |
| A6 | AMEND | R8 ending rewritten: "below" cue added, duplication with lines 832-835 removed |
| A7 | AMEND | R13 contrast axis changed to information-theoretic bounds vs game-based reductions |
| A8 | AMEND | R9 keeps "against passive participants" |
| A9 | AMEND | R6 says "reveal X bits about the conjunction" |
| A10 | AMEND | Census note corrected: figures (captions included) are fully stripped |
| A11 | AMEND | Kernel attribution moved to a lead-in footnote citing `tr_moebius`/`sc_moebius`/`inv_moebius` |
| A12 | AMEND | Sharpness caption shows the counting step |
| A13 | AMEND | R6 rewritten non-repetitively; final clause grounded in `leakE3` |
| A14 | NOTE | R8 states the involution's full swap structure |
| A15 | NOTE | R14 retargeted to the third-person voice slip |
| A16 | NOTE | Page growth 21 to 24 recorded in Goal and disclosure gate |
| A17 | NOTE | Relabeling split and ext drop recorded in Goal and disclosure gate |
| A18 | NOTE | Zero-margin gates recorded; A1 fix keeps "therefore" |
| A19 | NOTE | R5 recorded as deliberate content addition |
| A20 | NOTE | Accepted deviation recorded in disclosure gate |
| A21 | NOTE | R19 names the Theorem B length |
| A22 | NOTE | Captions stay `\coqin`-free; attribution in footnote |
