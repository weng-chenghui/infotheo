# WADT paper transition fixes: design (audit-amended)

Date: 2026-08-10
Target: `pgg-smc/paper-wadt2026/main.tex`, base revision `e39751e1` (21 pages).
Origin: baseline-transition-analysis run of 2026-08-10 against Shinagawa 2021
(dihedral symmetry) with a four-peer negative-control panel (Iwamoto 2024,
Shinagawa-Miyamoto 2022, Koch-Schrempp-Kirsten 2021, Koch-Walzer 2017).
Verdict: target 14.9 motivational moves per 10k words, below every peer
(lowest peer 46.5). Eight ranked fixes were reported in chat; this design
lands all eight.

Audit: an Opus adversarial audit
(`2026-08-10-wadt-transition-fixes-audit.md`) reviewed revision `8325785d`
of this spec and found 4 blockers and 13 further findings. This revision
resolves all of them; the disposition table is at the end.

## Decisions (user-confirmed unless marked)

1. Fix 4 (numeric worked example) is IN scope. Page growth is allowed.
2. Edits are applied in place, following this paper's existing commit
   practice.
3. Execution by the main session, three commits grouped by mechanism, with
   a jargon/prose self-audit; example values were source-verified by the
   audit (A1).
4. Voice: authorial signposting and motivation prose uses "I", never
   mathematical "we". Existing "I define / I prove" sentences untouched.
   Scope clarification after audit (A17): the numeric example E21 is a
   mathematical statement and uses the impersonal "Let ... be" register,
   with no "I" and no "we". PENDING USER CONFIRMATION.
5. After all changes land, the SAME skill check is re-run (same baseline,
   same panel) as the acceptance gate, supplemented by the two committed
   instruments in `tools/` (audit A10).
6. E18 is CUT as measurement stuffing (audit A12) and E12 is moved to the
   term's first use (A11). Projected gates remain reachable without them.
7. The reason and inference gates are lowered by one event each (to >=6
   and >=7) so every truth-driven rewording keeps at least one event of
   margin (audit A9). The re-run report discloses this.

## Honest expectation

Projected std census total is roughly 31-33 per 10k words, still below the
peer floor of 46.5. Band entry is not this round's goal and the re-run
report must say so.

## Edit table

All edits are exact-string replacements or anchored insertions (audit A5).
Line numbers refer to `e39751e1` and are locators only; the OLD string is
authoritative. LaTeX line wrapping inside OLD/NEW strings is immaterial.

### Commit 1: structure and motivation (E1-E6, E22)

**E1** (Section 3 opener, lines 304-310; audit A4, A15). REPLACE:

> An instance is specified by filling one record. The record type
> \coqin{MonodromyProfile} has five fields, and they carry the data of
> Equation~\ref{eq:model-data} into the executable protocol: the group with
> its action and generators, the secret type, the layout of a run, the
> shuffle-security bound, and the decoder. Here $R$ is the real closed field
> of Equation~\ref{eq:model-data}, not a protocol datum.

WITH:

> Every instance in this paper supplies the same kinds of data: a group
> with its action and generators, a secret type, the layout of a run, a
> shuffle-security bound, and a decoder. In order to reuse one executable
> protocol across instances, the framework therefore gathers these five
> choices into one record, the record type \coqin{MonodromyProfile}, while
> the generic theorems of this section take their hypotheses directly. The
> record carries the data of Equation~\ref{eq:model-data} into the
> executable protocol. Here $R$ is the real closed field of
> Equation~\ref{eq:model-data}, not a protocol datum.

**E2** (lines 405-409 and 411; audit A15). DELETE the paragraph:

> The profile packs the group action and its generators, the secret type,
> the protocol layout, the shuffle-security evidence, and the
> reconstruction component. The layout supplies the participant processes.
> The security evidence supplies an endpoint bound. The reconstruction
> component supplies the threshold scheme and decoder.

and in the next paragraph REPLACE "Packing these choices in one profile
keeps" WITH "Packing these components in one profile keeps".

**E3** (lines 914-919; audit A8). REPLACE:

> The implemented decoder reads all eight endpoints.
>
> The witness coalition makes the privacy cutoff three sharp. It
> does not classify all four-position coalitions. The development also
> proves monotonicity of mutual information under inclusion, but it does
> not compute the leakage for all reveal sets of sizes four through six.

WITH (one paragraph):

> The implemented decoder reads all eight endpoints. The witness coalition
> makes the privacy cutoff three sharp. Although the development proves
> monotonicity of mutual information under inclusion, it neither
> classifies all four-position coalitions nor computes the leakage for
> every reveal set of sizes four through six.

**E4** (lines 1087-1090; audit A14). REPLACE:

> Equation~\ref{eq:product-transfer} compares two distributions on a secret
> and a shuffle. It is not an execution distribution.
> Equations~\ref{eq:endpoint-transfer} and~\ref{eq:product-transfer}
> transfer the one certificate in Equation~\ref{eq:pgl-mixing}. They are
> not separate mixing certificates.

WITH:

> Equations~\ref{eq:endpoint-transfer} and~\ref{eq:product-transfer}
> transfer the one certificate of Equation~\ref{eq:pgl-mixing} to two
> further sample spaces. Neither is a separate mixing certificate, and
> Equation~\ref{eq:product-transfer} still compares a prior with a shuffle
> distribution rather than a distribution over executed runs.

**E5** (roadmap, lines 156-162; audit A2). REPLACE:

> Section~\ref{sec:framework} presents the framework components used by
> the proofs. Section~\ref{sec:fivecard} instantiates them on the
> five-card family as a first worked example. Sections~\ref{sec:pgl}
> and~\ref{sec:exact} give the $\PG$ construction and its uniform-shuffle
> results, ending in Theorem A. Section~\ref{sec:mixing} proves the
> word-shuffle results, ending in Theorem B.

WITH:

> Section~\ref{sec:framework} presents the framework components used by
> the proofs. Section~\ref{sec:fivecard} instantiates them on the
> five-card family, where the deck is small enough for direct case
> analysis. Sections~\ref{sec:pgl} and~\ref{sec:exact} construct the $\PG$
> instance, where deck enumeration no longer suffices and
> three-transitivity carries the privacy proofs, ending in Theorem A.
> Because a physical dealer repeats cuts rather than sampling one uniform
> group element, Section~\ref{sec:mixing} proves the word-shuffle results,
> ending in Theorem B.

**E6** (line 833; audit-verified clean). REPLACE:

> Table~\ref{tab:source-index} indexes the formal sources for this section.

WITH:

> Table~\ref{tab:source-index} at the end of Section~\ref{sec:mixing}
> indexes the formal sources for this section and the two that follow.

**E22** (new, after line 195; audit A1 latent hazard). AFTER the sentence
"The action of a sampled shuffle $g$ produces the arrangement $\rho(g)D$."
INSERT:

> Position $i$ of the shuffled arrangement holds the card that $D$ places
> at position $\rho(g)(i)$.

### Commit 2: signposting and grounding (E7-E17, E19, E20; E18 cut)

**E7** (lines 89-91). REPLACE "follow a word distribution" WITH "follow
what I call a word distribution".

**E8** (lines 191-192). REPLACE:

> The convolution $\mu^{*L}$ is the distribution of the group element
> obtained by evaluating $L$ independent letters.

WITH:

> I write $\mu^{*L}$ for the word distribution at length $L$: the
> distribution of the group element obtained by evaluating $L$ independent
> letters.

**E9** (line 597). REPLACE "The dealing distribution is the biased cut"
WITH "The dealing distribution is what I call the biased cut".
VERIFY attribution first: if Kim and Cetinkaya's paper already uses the
term "biased cut" (check the research-kb slice and `references.bib`
context), instead use "The dealing distribution is the biased cut of Kim
and \c{C}etinkaya" and drop "what I call".

**E10** (lines 254-255; audit A5 garden path). REPLACE:

> The word-shuffle model describes the dealer performing the shuffle as a
> sequence of physical cuts. It replaces $U_G$ by $\mu^{*L}$.

WITH:

> A second model describes the dealer performing the shuffle as a sequence
> of physical cuts. I call this the word-shuffle model. It replaces $U_G$
> by $\mu^{*L}$.

**E11** (lines 233-234; audit A3). REPLACE:

> It then applies an independent uniform shuffle. This fixed-representative
> dealer is the dealer of the headline theorems.

WITH:

> It then applies an independent uniform shuffle. I call this the fixed
> representative dealer, and it is the dealer of the headline theorems.

The following sentences ("An all-decks dealer instead ... uniform Boolean
prior.") are preserved verbatim.

**E12** (moved to first use, lines 708-709; audit A11, A12). REPLACE
"and the decoder reads the orbit class" WITH "and the decoder reads what I
call the orbit class". No insertion at line 766.

**E13** (after line 875). AFTER "...and $n$ is the number of card
positions." INSERT:

> I call the triple $(t,r,n)$ the recovery ramp.

**E14** (lines 1030-1032). REPLACE:

> The proof partitions these words into $336$ fibers, one for each group
> element. A computation over binary naturals records the size of every
> fiber.

WITH:

> The proof partitions these words by evaluated group element. I call the
> set of words that evaluate to $g$ the fiber of $g$, and there are $336$
> fibers. A computation over binary naturals records the size of every
> fiber.

The final-check sentence ("The final arithmetic check ...") is preserved.

**E15** (after line 435). AFTER "...the five instances in this paper."
INSERT:

> For example, the den Boer row fills only the exact slot, since one
> uniform cut already gives the exact endpoint distribution.

Mechanism verified by the audit (`five_card_eps0_eq0`,
`five_card_family.v:180-183`). The echo of `main.tex:690`, 255 lines away
in another section, is accepted (audit A13).

**E16** (after line 827; audit A6). AFTER "The kernel checks the resulting
finite table." INSERT:

> For example, the base triple is $(0,1,2)$, and the table stores for
> every other ordered triple of distinct points one generator word that
> carries $(0,1,2)$ to it.

Base triple source-verified (`pgl27_group.v:205-213`). No concrete table
entry is quoted because the table is never materialized outside
`vm_compute`.

**E17** (after line 1208; audit-verified clean, fallback removed). INSERT:

> For example, the trace-lifting theorem of Section~\ref{sec:framework} is
> consumed verbatim by all five instances, while each instance supplies
> its own endpoint bound.

**E18**: CUT (audit A12; true but informationally empty).

**E19** (lines 1026-1027; audit A7). REPLACE:

> The resulting tuple is symmetric and generates the same group as the
> original three generators.

WITH:

> The alphabet includes the two inverse letters because the fiber
> computation below steps backward through a letter's inverse and must
> stay inside the alphabet. The symmetric tuple still generates the same
> group as the original three generators, so the fiber count concerns the
> same $336$ elements.

Reason grounded in `inv_letter` (`pgl27_mixing.v:150,596,634-660`);
same-group claim grounded in `pgl27_gen5_eq` (`pgl27_mixing.v:454-456`).

**E20** (before line 1052). BEFORE "The first transfer maps each
permutation to the endpoint of one fixed card." INSERT:

> A coalition observes card endpoints rather than group elements. The
> certificate therefore moves from the group to the endpoints first.

### Commit 3: numeric worked example (E21; audit A1, A16)

After the fixed-dealer perfect-privacy proposition (its `\end{proposition}`
near line 943, before "Two further dealers act as robustness checks"),
INSERT:

```latex
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
```

All values audit-verified against the formal convention: seat $i$ observes
`content(rho g (starts i))`, that is $D(\rho(g)(i))$; $D_0$ is the
identity tuple; translation is `tr_tbl = [1;2;3;4;5;6;0;7]`; $D_1$ holds
values $1,2,3$ at positions $1,2,4$. The llncs class predefines the
numbered `example` environment and labelling it is safe; do NOT add a
`\spnewtheorem` fallback, which would error (audit A16).

## Verification protocol

1. After each commit: `latexmk` recompile must be clean. Watch the `[H]`
   float fit around page 9 (Figure 4); net word change before it is about
   +40. Report final page count.
2. Remaining truth check: E9 attribution ("biased cut" in Kim and
   Cetinkaya) before commit 2. E16, E17, E19, E21 were source-verified by
   the audit; re-verify only if the paper or sources change under this
   design.
3. Inserted-prose style audit: no em-dash, no semicolon, no parenthetical
   asides, "distribution" never "law", no new abbreviations, "I" voice for
   authorial prose, impersonal register for E21. The implementation plan
   includes a jargon table (H/M/L plus plain rewrite) for the inserted
   text.
4. Final acceptance: re-run the full skill check at the landed revision:
   `count_connectives.py` (baseline Shinagawa 2021 PDF), `control_panel.py`
   (same four peers), `fact_density.py`, plus the two committed
   instruments `tools/wadt_per_section.py` and
   `tools/wadt_signpost_neutral.py` (the latter over all six panel
   papers). Report the full Phase C shape in chat, including the
   disclosure of Decision 7 and the honest expectation above.

### Acceptance gates

| Gate | Instrument | Before | Target | Projected |
|------|-----------|-------:|-------:|----------:|
| std census TOTAL per 10k | count_connectives.py | 14.9 | >= 30 | ~31.6 |
| instance family per 10k | count_connectives.py | 1.5 | >= 5.5 | ~5.8 |
| worked Example blocks | count_connectives.py | 0 | >= 1 | 1 |
| adversative (std) events | count_connectives.py | 0 | >= 1 | 1 |
| reason events | count_connectives.py | 4 | >= 6 | 7 |
| inference events | count_connectives.py | 5 | >= 7 | 8 |
| neutral signposting per 10k | tools/wadt_signpost_neutral.py | 6.0 | >= 14 | ~17 |
| Section 3 std moves | tools/wadt_per_section.py | 0 | >= 3 | 4 |
| Section 7 all per 10k | tools/wadt_per_section.py | 11.9 | >= 25 | ~45 |
| compile | latexmk | clean, 21 pp | clean, pages reported | - |

Projection basis: +12 std events (purpose 1, reason 3, inference 3,
instance 3, example 1, adversative 1) at roughly 6960 words, +8 I-form
signposting events. The neutral signposting gate survives even if E9 falls
to the attribution check (12 -> 11 events, 15.8 per 10k).

## Audit resolution

| Finding | Disposition |
|---------|-------------|
| A1 (E21 wrong values/direction) | Adopted corrected example; E22 added |
| A2 (E5 enumeration inverted) | E5 rewritten per sources |
| A3 (E11 range destroys all-decks dealer) | Exact-string edit; unhyphenated |
| A4 (E1 false universal) | Restated over instances, five data, bound |
| A5 (line-range splices) | All edits now exact-string or anchored |
| A6 (E16 no table entry) | Restated around base triple (0,1,2) |
| A7 (E19 unrecorded reason) | Fiber-closure reason adopted |
| A8 (E3 dropped quantifier) | "every" restored, sentence split |
| A9 (zero gate margin) | reason/inference gates lowered to 6/7, disclosed |
| A10 (missing instruments) | tools/ scripts committed; before-values re-measured |
| A11/A12 (E12 placement, E18 filler) | E12 moved to line 708; E18 cut |
| A13 (E15 echo) | Accepted, noted |
| A14 (E4 "idealized") | Reworded |
| A15 (antecedents) | "these components"; "one record" repetition removed |
| A16 (spnewtheorem fallback errors) | Fallback struck; llncs example used |
| A17 (E21 register, E9 attribution) | Register decision 4 clarified (pending user); E9 verify step |

## Risks and rollback

- Float placement may shift pages; recompile per commit.
- E9 may lose its "what I call" to the attribution check; gates already
  carry the margin.
- `.tex`-only commits do not trigger the rocq-audit Stage 2 gate; no
  bypass is needed.
- Rollback is per-commit `git revert`.
