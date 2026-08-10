# WADT Round 3: Signposting to the Iwamoto Level (Design Spec)

Target file: `pgg-smc/paper-wadt2026/main.tex` at revision `ae47ca79`.
Instrument: baseline-transition-analysis v2, `fact_density.py` SIGNPOST regex.
All line numbers below refer to revision `ae47ca79`.

## Decisions

| ID | Decision |
|----|----------|
| D1 | Target level: Iwamoto band. Signposting rises from 17.4/10k (13 hits) to >= 38/10k (>= 29 hits). Peer context: KochSchKir21 18.1, KochWalzer17 22.8, Iwamoto24 38.3, ShinMiya22 117.3, Shinagawa21 181.1, peer mean 75.5. |
| D2 | Edit style: mixed. Retrofit existing sentences into counted forms where a bare introduction already exists; add a short new introduction sentence only where an object genuinely arrives unannounced. |
| D3 | Inventory method: term-inventory-driven (approach A). Every edit anchors to a verified first-use point of a real recurring term or symbol. No quota-filling. |
| D4 | Sections that introduce no objects stay at zero: Related Work and Conclusion keep 0 signposts, disclosed as honest zeros. |
| D5 | Acceptance is the Before/After table verified by an adversarial Opus audit (charter below) plus a full `fact_density.py` re-run. |
| D6 | The abstract is untouched. Its connective gates (std 2) from round 2 have zero margin. |
| D7 | Counted vocabulary is exactly the v2 SIGNPOST regex. Relevant facts: `figure`/`tabular`/`tikzpicture`/`lstlisting`/`verbatim`/`algorithmic` environments are stripped INCLUDING captions; footnotes are NOT stripped and do count; theorem-class environments count. |

## Instrument definition (verbatim from fact_density.py v2)

```
(?x)\b(
   (?:[Ww]e|I)\s+(define|write|denote|call|set|say\s+that|put)
 | what\s+(?:we|I)\s+call
 | is\s+defined\s+(as|by) | are\s+defined\s+(as|by)
 | is\s+called | are\s+called
 | is\s+denoted | denoted\s+by
 | [Dd]efinition\s+\d
 | [Ll]et\s+\$?[A-Za-z\\][^.]{0,30}?\s+be\s+(a|an|the)\s
)\b
```

## Edit inventory S1-S16 (17 new hits: S2 carries two)

Every OLD string is verbatim from revision `ae47ca79` (whitespace may wrap
differently in the file; the executor matches modulo line breaks). Register
constraints for every NEW string: I-voice, no em-dash, no semicolon, no prose
parentheses, "distribution" never "law", no new abbreviations, existing counted
connectives in touched sentences are preserved.

### S1. Term: uniform-shuffle model (sec:model, L259-260). Form: I call. +1

The word-shuffle model gets "I call this the word-shuffle model" at L260; its
sibling model is never named, and its first use at L272 is bare.

OLD:
```
A second model describes the dealer performing the shuffle as a
sequence of physical cuts. I call this the word-shuffle model.
```
NEW:
```
The model described so far applies one uniform group element, and I call
it the uniform-shuffle model. A second model describes the dealer
performing the shuffle as a sequence of physical cuts. I call this the
word-shuffle model.
```

### S2. Terms: executed trace, coalition trace (sec:model, L207-208). Form: is called, twice. +2

OLD:
```
The resulting record is the
executed trace $T_i$, and $T_C=(T_i)_{i\in C}$ is the coalition trace.
```
NEW:
```
The resulting record is called the
executed trace $T_i$, and $T_C=(T_i)_{i\in C}$ is called the coalition trace.
```

### S3. Term: profile (sec:framework, L414). Form: I call. +1

First standalone body-prose use of "profile" is L414 (earlier occurrences are
in the stripped table and figure). The term recurs at L433, L438, L535, L588.

OLD:
```
Packing these components in one profile keeps the participants, verifier,
```
NEW:
```
I call a filled record a profile. Packing these components in one
profile keeps the participants, verifier,
```

### S4. Term: security witness (sec:framework, L436). Form: is called. +1

First body-prose use is L436 (the table caption occurrence is stripped).

OLD:
```
The security witness can carry exact evidence, asymptotic evidence, or
both.
```
NEW:
```
The record that holds the shuffle-security evidence is called the
security witness. It can carry exact evidence, asymptotic evidence, or
both.
```

### S5. Term: commit prologue (sec:framework, L465). Form: I call. +1

First use is L465; "the prologue" recurs at L471-472.

OLD:
```
With an \coqin{InputEncoding}, a commit prologue collects the players'
inputs and assembles the dealt deck from them, so the same flow evaluates
a function of committed inputs.
```
NEW:
```
With an \coqin{InputEncoding}, the flow gains a phase that I call the
commit prologue. It collects the players' inputs and assembles the dealt
deck from them, so the same flow evaluates a function of committed
inputs.
```

### S6. Symbol: $w_\varepsilon$ (sec:fivecard, L602-603). Form: I write. +1

The symbol first appears inside the display without introduction and recurs
at L693 as $w_{1/100}$.

OLD:
```
The dealing distribution is the biased cut of Kim and \c{C}etinkaya
\begin{equation}
```
NEW:
```
The dealing distribution is the biased cut of Kim and \c{C}etinkaya,
and I write $w_\varepsilon$ for it:
\begin{equation}
```

### S7. Term: master theorem (sec:fivecard, L614). Form: what I call. +1

The paper's own coinage for `leak_view_set`, used bare at its only prose site.

OLD:
```
The master theorem gives the exact leakage for every fixed reveal set.
```
NEW:
```
What I call the master theorem gives the exact leakage for every fixed
reveal set.
```

### S8. Term: the cap (sec:fivecard, L623-624 plus footnote sub-edit at L617). Form: I call. +1

The term appears in the leakage figure labels (stripped) and in the L614
footnote before its body use. Sub-edit (a) removes the footnote gloss so the
body sentence owns the first use; sub-edit (b) introduces the term.

Sub-edit (a), footnote at L617-618, OLD:
```
\coqin{leak\_k3\_gap}, \coqin{leak\_k4}, \coqin{leak\_k5}, and the cap
\coqin{H\_secret} in
```
NEW:
```
\coqin{leak\_k3\_gap}, \coqin{leak\_k4}, \coqin{leak\_k5}, and
\coqin{H\_secret} in
```

Sub-edit (b), body at L623-624, OLD:
```
threshold, and the ramp climbs to the secret's own entropy
$2-\tfrac34\log 3\approx 0.811$. The decimals are evaluations of the
proven closed forms.
```
NEW:
```
threshold, and the ramp climbs to the secret's own entropy
$2-\tfrac34\log 3\approx 0.811$, which I call the cap. The decimals are
evaluations of the proven closed forms.
```

### S9 + S10. Terms: privacy threshold $t$, recovery threshold $r$ (sec:exact, L944-947). Form: is defined as, twice. +2

These clauses are definitions already; the retrofit makes them counted
definitional forms. The closing "I call the triple" sentence is untouched.

OLD:
```
Three parameters summarize the instance. The privacy threshold $t$ is the
largest coalition size with perfect privacy, the recovery threshold $r$ is
the least number of revealed positions that always determines the secret
class, and $n$ is the number of card positions.
```
NEW:
```
Three parameters summarize the instance. The privacy threshold $t$ is
defined as the largest coalition size with perfect privacy, the recovery
threshold $r$ is defined as the least number of revealed positions that
always determines the secret class, and $n$ is the number of card
positions.
```

### S11. Term: shuffle-free deck distribution (sec:exact, L1055-1057). Form: I call. +1

First use is L1056; the term recurs at L1230, L1274 (table, stripped), L1446.

OLD:
```
A third dealer samples a uniform valid deck in the chosen class and applies
no later shuffle. For this shuffle-free deck distribution, view independence holds for
every Boolean secret prior.
```
NEW:
```
A third dealer samples a uniform valid deck in the chosen class and applies
no later shuffle. I call this the shuffle-free deck distribution. For it,
view independence holds for
every Boolean secret prior.
```

### S12. Term: mixing certificate (sec:mixing, L1138). Form: I call. +1

The term appears in the stripped fig:models caption and at L1183 in body
prose; the introduction precedes the body use.

OLD:
```
Equation~\ref{eq:pgl-mixing} is one checked certificate.
```
NEW:
```
Equation~\ref{eq:pgl-mixing} is one checked certificate, which I call
the mixing certificate.
```

### S13. Term: endpoint transfer (sec:mixing, L1145-1146). Form: I call. +1

The lowercase prose term does not exist yet; the edit ties the prose to the
Lemma~\ref{lem:endpoint-transfer} title "Endpoint transfer".

OLD:
```
The
first transfer maps each permutation to the endpoint of one fixed card.
```
NEW:
```
The
first transfer, which I call the endpoint transfer, maps each
permutation to the endpoint of one fixed card.
```

### S14. Symbol: $V_C(s,g)$ in Theorem B (sec:mixing, L1199-1200). Form: I write. +1

Zero-meaning-change retrofit of a participle into a counted main clause.

OLD:
```
$\lvert C\rvert\leq3$, and all secrets $s,s'\in\{0,1\}$, writing $V_C(s,g)$
for the coalition view at dealt secret $s$ and shuffle $g$,
```
NEW:
```
$\lvert C\rvert\leq3$, and all secrets $s,s'\in\{0,1\}$, where I write
$V_C(s,g)$ for the coalition view at dealt secret $s$ and shuffle $g$,
```

### S15. Term: trust base (sec:instances, L1349). Form: is called. +1

Earlier occurrences at L163, L1098, L1231 are forward pointers of the form
"the trust base ... is stated in Section~8"; the section that states it never
introduces the term.

OLD:
```
The probability, view, and trace results use three classical principles
from the MathComp probability stack: propositional extensionality,
```
NEW:
```
The set of assumptions that a result's verification rests on is called
its trust base. The probability, view, and trace results use three
classical principles
from the MathComp probability stack: propositional extensionality,
```

### S16. Term: variation distance (Introduction footnote, L146-147). Form: is called. +1

Footnotes are not stripped by the census and count.

OLD:
```
$\lVert P-Q\rVert_1=\sum_x\lvert P(x)-Q(x)\rvert$, called variation
distance in the formal development, with maximum value 2.
```
NEW:
```
$\lVert P-Q\rVert_1=\sum_x\lvert P(x)-Q(x)\rvert$, which is called variation
distance in the formal development, with maximum value 2.
```

## Bonus edit B1 (non-counted, term consistency)

Introduction L93 uses "the ideal model", an orphan term appearing exactly once
in the paper. It becomes "the uniform-shuffle model", matching the term S1
introduces and the Section 7 title. This is a forward use of a term introduced
in Section 2, disclosed below.

OLD:
```
small cut alphabet yields a finite implementable shuffle. In this paper I prove the security results in the ideal model and then
```
NEW:
```
small cut alphabet yields a finite implementable shuffle. In this paper I prove the security results in the uniform-shuffle model and then
```

## Projected numbers

13 + 17 = 30 hits at roughly 7550 words gives 39.7/10k. Per-section
projection: model 6, intro 2, framework 4, fivecard 4, pgl 3 (untouched),
exact 5, mixing 4, instances 1, abstract 1 (untouched), related 0,
conclusion 0. Every touched section lands at or above 25/10k; the floor gate
is 18/10k. Word growth about +100 dilutes connective moves from 67.1/10k to
about 66.2/10k, above the 60 floor.

## Acceptance gates

| Gate | Threshold |
|------|-----------|
| signpost/10k (fact_density) | >= 38.0 |
| total SIGNPOST hits | >= 29 |
| moves/10k (count_connectives families) | >= 60.0 |
| per-section signpost rate, every touched section | >= 18.0/10k |
| Related Work and Conclusion signposts | exactly 0, disclosed |
| abstract untouched | diff shows no abstract change |
| Opus audit | all 16 edits pass or pass after amendment |
| latexmk | clean compile, no new warnings |

## Adversarial Opus audit charter

For each edit S1-S16 the auditor must attack five ways:

1. **Regex evidence.** Apply the edit to a scratch copy, run the census strip
   (`count_connectives.load`), and show the SIGNPOST match count rises by
   exactly the claimed amount, with the match landing in surviving text (not
   in a stripped environment). Also confirm the OLD string contains no match.
2. **First-use honesty.** Grep the whole paper for the term or symbol.
   Confirm the introduction site is the first body-prose use, or that every
   earlier occurrence is a stripped environment, a lemma title, or a
   disclosed forward pointer (trust base: L163, L1098, L1231; uniform-shuffle
   model after B1: L93; the cap: none after sub-edit a).
3. **Meaning preservation.** Compare OLD and NEW claim by claim: every
   quantifier, hedge, citation, and formula must survive. S14 and S16 must be
   meaning-identical; S1, S3, S4, S5, S11, S12, S13, S15 add only a naming
   sentence or clause; S6, S7, S8b, S9, S10 rephrase a definition without
   changing it.
4. **Register.** I-voice only, no em-dashes, no semicolons, no prose
   parentheses, "distribution" never "law", no abbreviations, and no existing
   counted connective family word deleted from a touched sentence.
5. **Decoration detection.** Judge whether the named object is genuinely
   introduced at that point and used afterwards. An introduction whose term
   never recurs, or that names something the reader never needs again, fails.

Aggregate checks: rebuild the fully edited paper in a scratch directory, run
`fact_density.py` and `count_connectives.py` against the panel, verify the
projected numbers table, and compile with latexmk. Report findings as
numbered blockers, amendments, and notes.

## Disclosures carried to the final report

1. Forward-pointer terms: "trust base" and (after B1) "uniform-shuffle model"
   are used as forward references before their introduction sections; both
   pointers name the section that introduces them.
2. S2, S9+S10 each place two counted forms in one sentence, a deliberate
   parallel-definition style.
3. 14 of 17 new hits are retrofits of existing introductions into counted
   forms; S3, S5 (partially), and S15 are new sentences.
4. Related Work and Conclusion remain at zero signposts by design (D4).
5. The word growth dilutes round 2's moves/10k from 67.1 to about 66;
   the round 2 gates all still hold.
