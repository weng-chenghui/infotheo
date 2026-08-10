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
| D7 | Counted vocabulary is exactly the v2 SIGNPOST regex. Relevant facts: `figure` environments are stripped INCLUDING their captions; `tabular`/`tikzpicture`/`lstlisting`/`verbatim`/`algorithmic` bodies are stripped but TABLE CAPTIONS SURVIVE (audit N9); footnotes are NOT stripped and do count; theorem-class environments count. |
| D8 | Audit-driven amendment (2026-08-10): S3, S4, S8a, S11, S14, S15, B1 replaced per audit findings F1-F8; resolution table at the end of this file. |

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

### S3. Term: profile (sec:framework, L414; plus forward pointer at L136). Form: I call. +1

Audit F1: "profile" is already used in surviving body prose at Introduction
L136 ("one profile at bias $\varepsilon$", renders page 2), so the L414
introduction needs a forward pointer there. Audit F2: "a filled record" is
over-general; a profile is specifically a filled `MonodromyProfile`.

Sub-edit (a), forward pointer at L136, OLD:
```
one profile at bias $\varepsilon$: executed-run correctness of the
```
NEW:
```
one profile at bias $\varepsilon$, in the sense of
Section~\ref{sec:framework}: executed-run correctness of the
```

Sub-edit (b), introduction at L414, OLD:
```
Packing these components in one profile keeps the participants, verifier,
```
NEW:
```
I call a filled \coqin{MonodromyProfile} a profile. Packing these
components in one profile keeps the participants, verifier,
```

### S4. Term: security witness (sec:framework, L436). Form: is called. +1

First body-prose use is L436. The tab:witness-mechanism caption also uses
the term but sits at L458, after this site (table captions survive the
strip, audit N9). Gloss per audit F3: the record carries the shuffle
distribution `sw_rho_dist` and the endpoint bound, not the evidence itself.

OLD:
```
The security witness can carry exact evidence, asymptotic evidence, or
both.
```
NEW:
```
The record that carries the shuffle distribution and its endpoint bound is
called the security witness. It can carry exact evidence, asymptotic
evidence, or both.
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

Sub-edit (a), footnote at L617-618 (audit F4: keep a gloss because
`H_secret` is the entropy ceiling, not a leakage value; in the compiled PDF
the body introduction precedes this footnote in reading order), OLD:
```
\coqin{leak\_k3\_gap}, \coqin{leak\_k4}, \coqin{leak\_k5}, and the cap
\coqin{H\_secret} in
```
NEW:
```
\coqin{leak\_k3\_gap}, \coqin{leak\_k4}, \coqin{leak\_k5}, and the secret's
own entropy \coqin{H\_secret} in
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
NEW (audit F5: "the resulting distribution" fixes the dealer-as-antecedent
slip and the clause order):
```
A third dealer samples a uniform valid deck in the chosen class and applies
no later shuffle. I call the resulting distribution the shuffle-free deck
distribution, and view independence holds under it for
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

### S14. Symbol: $V_C(s,g)$ in Theorem B (sec:mixing, L1199-1200). Form: is denoted. +1

Zero-meaning-change retrofit of a participle into a counted clause. Audit
F6: no theorem-class environment in the paper contains an authorial
pronoun, so the counted form must be voice-neutral.

OLD:
```
$\lvert C\rvert\leq3$, and all secrets $s,s'\in\{0,1\}$, writing $V_C(s,g)$
for the coalition view at dealt secret $s$ and shuffle $g$,
```
NEW:
```
$\lvert C\rvert\leq3$, and all secrets $s,s'\in\{0,1\}$, where the coalition
view at dealt secret $s$ and shuffle $g$ is denoted $V_C(s,g)$,
```

### S15. Term: trust base (sec:instances, L1349). Form: are called. +1

Earlier occurrences at L163, L1098, L1231 are forward pointers of the form
"the trust base ... is stated in Section~8"; the section that states it never
introduces the term. Audit F7: the paper's trust-base column lists the Rocq
kernel, which is trusted software, not an assumption, so the definition must
cover the checker as well as the axioms.

OLD:
```
The probability, view, and trace results use three classical principles
from the MathComp probability stack: propositional extensionality,
```
NEW:
```
The checker and the axioms that a result's verification rests on are called
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

Introduction L93 uses "the ideal model", a bigram appearing exactly once in
the paper (the wider "ideal" vocabulary survives at L88, L1102, L1226,
L1441, disclosed below). It becomes "the uniform-shuffle model of
Section~\ref{sec:model}", matching the term S1 introduces; audit F8
requires the section reference so the forward use names its introducing
section, like the trust-base pointers.

OLD:
```
small cut alphabet yields a finite implementable shuffle. In this paper I prove the security results in the ideal model and then
```
NEW:
```
small cut alphabet yields a finite implementable shuffle. In this paper I prove the security results in the uniform-shuffle model of Section~\ref{sec:model} and then
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

1. Forward-pointer terms: "trust base" (L163, L1098, L1231), "profile"
   (L136 after S3a), and "uniform-shuffle model" (L93 after B1) are used
   before their introduction sections; every pointer names the section that
   introduces the term.
2. S2, S9+S10 each place two counted forms in one sentence, a deliberate
   parallel-definition style.
3. 14 of 17 new hits are retrofits of existing introductions into counted
   forms; S3b, S5 (partially), and S15 are new sentences.
4. Related Work and Conclusion remain at zero signposts by design (D4).
5. The word growth dilutes round 2's moves/10k from 67.1 to about 66;
   the round 2 gates all still hold.
6. Census exemptions are not reader exemptions (audit N11): "mixing
   certificate" appears in the stripped fig:models caption (page 5) before
   its S12 introduction; "executed trace" (abstract L48, intro L83) and
   "coalition trace" (Theorem B informal, L119) precede the S2 naming.
7. "master theorem" recurs nowhere after its introduction sentence and
   footnote (audit N13); kept as an honest coinage that disambiguates from
   the divide-and-conquer Master theorem.
8. S13 names the first transfer while the second transfer stays unnamed in
   prose (audit N16).

## Audit resolution table

| Finding | Severity | Resolution |
|---------|----------|------------|
| F1 profile used at L136 before L414 | BLOCKER | S3a forward pointer added at L136 |
| F2 "filled record" over-general | AMEND | S3b names `MonodromyProfile` |
| F3 witness gloss wrong | AMEND | S4 gloss: carries shuffle distribution and endpoint bound |
| F4 S8a deleted load-bearing gloss | AMEND | footnote keeps "the secret's own entropy" gloss |
| F5 dealer-as-antecedent, term never recurs | AMEND | S11 "the resulting distribution" + merged clause |
| F6 authorial pronoun in Theorem B | AMEND | S14 voice-neutral "is denoted" |
| F7 trust base excludes the kernel | AMEND | S15 "the checker and the axioms" |
| F8 B1 pointer named no section | AMEND | B1 adds "of Section~\ref{sec:model}" |
| N9 table captions survive strip | NOTE | D7 corrected; S4 justification fixed |
| N11 caption precedes S12 intro | NOTE | disclosure 6 |
| N12 trace terms precede S2 naming | NOTE | disclosure 6 |
| N13 master theorem no downstream use | NOTE | disclosure 7 |
| N14 privacy threshold bare at L415 | NOTE | accepted, list mention |
| N15 designator/class-noun tension | NOTE | accepted |
| N16 second transfer unnamed | NOTE | disclosure 8 |
| N17 two senses of "record" | NOTE | mitigated by F2 naming the Rocq record |
| N18 indentation drift | NOTE | executor re-indents to file context |
