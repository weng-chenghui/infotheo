# WADT paper transition fixes: design

Date: 2026-08-10
Target: `pgg-smc/paper-wadt2026/main.tex`, base revision `e39751e1` (21 pages).
Origin: baseline-transition-analysis run of 2026-08-10 against Shinagawa 2021
(dihedral symmetry) with a four-peer negative-control panel (Iwamoto 2024,
Shinagawa-Miyamoto 2022, Koch-Schrempp-Kirsten 2021, Koch-Walzer 2017).
Verdict: target 14.9 motivational moves per 10k words, below every peer
(lowest peer 46.5). Eight ranked fixes were reported in chat; this design
lands all eight.

## Decisions (user-confirmed)

1. Fix 4 (numeric worked example) is IN scope. Page growth is allowed.
2. Edits are applied in place, following this paper's existing commit
   practice. No additive-draft mode.
3. Execution is by the main session (Approach A), three commits grouped by
   mechanism, with a jargon/prose self-audit and source-checked example
   values. No subagent drafting.
4. Voice: all inserted prose uses "I", never mathematical "we". Existing
   "I define / I prove" sentences are untouched.
5. After all changes land, the SAME skill check is re-run (same baseline,
   same panel, same scripts) as the acceptance gate.

## Honest expectation

The fixes close the named mechanism gaps (signposting, instance markers,
section-level zeros, missing why-sentences). Projected std census total is
roughly 33 per 10k words. That is still below the peer floor of 46.5. Band
entry is not this round's goal and the re-run report must say so.

## Edit table

Line numbers refer to `e39751e1`. Inserted text is final unless marked
"verify against source".

### Commit 1: structure and motivation (fixes 1, 6, 7, 8)

| ID | Location | Action |
|----|----------|--------|
| E1 | before line 304 | Insert Section 3 opener: "Every security proof in this paper consumes the same kinds of data: a group action, a shuffle distribution, a dealer layout, and a decoder. In order to reuse the proofs across protocols, the framework therefore gathers these data into one record." |
| E2 | lines 405-409 | Delete the paragraph "The profile packs ... threshold scheme and decoder." (third enumeration of the field list). |
| E3 | lines 914-919 | Replace orphan sentence plus caveat pile with: "The implemented decoder reads all eight endpoints, and the witness coalition makes the privacy cutoff three sharp. Although the development proves monotonicity of mutual information under inclusion, it neither classifies all four-position coalitions nor computes the leakage for reveal sets of sizes four through six." |
| E4 | lines 1087-1090 | Replace double-negation cluster with: "Equations~\ref{eq:endpoint-transfer} and~\ref{eq:product-transfer} transfer the one certificate of Equation~\ref{eq:pgl-mixing} to two further sample spaces. Neither is a separate mixing certificate, and Equation~\ref{eq:product-transfer} still compares idealized distributions rather than an execution distribution." |
| E5 | lines 156-162 | Roadmap rewrite: "Section~\ref{sec:framework} presents the framework components used by the proofs. Section~\ref{sec:fivecard} instantiates them on the five-card family, where kernel enumeration still discharges every obligation. Sections~\ref{sec:pgl} and~\ref{sec:exact} construct the $\PG$ instance, where enumeration fails and three-transitivity carries the privacy proofs, ending in Theorem A. Because a physical dealer repeats cuts rather than sampling one uniform group element, Section~\ref{sec:mixing} proves the word-shuffle results, ending in Theorem B." (Remaining roadmap sentences unchanged.) |
| E6 | line 833 | Replace with: "Table~\ref{tab:source-index} at the end of Section~\ref{sec:mixing} indexes the formal sources for this section and the two that follow." |

### Commit 2: signposting and grounding (fixes 2, 3, 5)

| ID | Location | Action |
|----|----------|--------|
| E7 | lines 89-91 | "...follow what I call a word distribution over the generators of the group." |
| E8 | line 191 | "The convolution $\mu^{*L}$ is the word distribution at length $L$: the distribution of the group element obtained by evaluating $L$ independent letters." |
| E9 | line 597 | "The dealing distribution is what I call the biased cut" |
| E10 | line 254 | "I call the model in which the dealer performs the shuffle as a sequence of physical cuts the word-shuffle model." |
| E11 | lines 234-236 | "I call this dealer the fixed-representative dealer. It is the dealer of the headline theorems." |
| E12 | after line 766 | "I call this orbit datum the orbit class." |
| E13 | after line 875 | "I call the triple $(t,r,n)$ the recovery ramp." |
| E14 | lines 1031-1033 | "The proof partitions these words by evaluated group element. I call the set of words that evaluate to $g$ the fiber of $g$, and there are $336$ fibers." |
| E15 | after line 435 | "For example, the den Boer row fills only the exact slot, since one uniform cut already gives the exact endpoint distribution." |
| E16 | after line 831 | "For example, the enumerated table sends the base triple to the triple $(1,3,5)$ by one generator word." VERIFY against `pgg-smc/instances/pgl27/pgl27_group.v`: use the actual base triple and an actual table entry. |
| E17 | after line 1208 | "For example, the trace-lifting theorem of Section~\ref{sec:framework} is consumed verbatim by all five instances, while each instance supplies its own endpoint bound." VERIFY by grep that all five instances go through `trace_secrecy_of_view`. Fallback: if an instance uses another route, name the actual consumer count ("by the den Boer, Kim, ... instances") instead of "all five". |
| E18 | after E14 | "For example, the fiber of the identity contains every word whose letters multiply to the identity element." |
| E19 | lines 1026-1027 | Replace closing sentence with: "The inverse letters are included because a dealer can repeat each cut in either direction. The symmetric tuple still generates the same group as the original three generators, so the fiber count below concerns the same $336$ elements." VERIFY rationale against `pgl27_mixing.v` comments; if the recorded reason differs, restate it faithfully. |
| E20 | before line 1052 | "A coalition observes card endpoints rather than group elements. The certificate therefore moves from the group to the endpoints first." |

### Commit 3: numeric worked example (fix 4)

E21: after the fixed-dealer perfect-privacy proposition (line 943), add a
numbered `example` environment (llncs predefines one; if absent, declare via
`\spnewtheorem`):

> Deal the secret $s=0$, so the dealt arrangement is $D_0$, and let the
> shuffle be the translation $x\mapsto x+1$, which fixes the point $\infty$.
> Each card moves one position forward, and the coalition $\{0,1,2\}$ sees
> the card values $(6,0,1)$. The same observation arises at $s=1$: by
> Lemma~\ref{thm:three-transitive} some shuffle sends the three positions of
> $D_1$ holding the values $6$, $0$, and $1$ to the coalition's positions. A
> coalition of three cards therefore never separates the two secrets, and
> the proposition above makes this uniformity exact.

VERIFY before landing: the values $(6,0,1)$ assume the convention
$(\rho(g)D)(i) = D(g^{-1}i)$. Check the actual action direction in
`pgl27_run.v` / `pgl27_orbit.v` (rocq-mcp if needed). If the composition
runs the other way, the values become $(1,2,3)$. Position 7 is the
projective point $\infty$.

## Verification protocol

1. After each commit: `latexmk` recompile must be clean. Watch the
   `[H]` float fit around page 9 (Figure 4). Report final page count.
2. Truth checks (inputs named): E16 against `pgl27_group.v`, E17 against a
   repo-wide grep for `trace_secrecy_of_view` consumers, E21 against
   `pgl27_run.v`/`pgl27_orbit.v` action direction.
3. Inserted-prose style audit: no em-dash, no semicolon, no parenthetical
   asides, "distribution" never "law", no new abbreviations, "I" voice.
   Inserted text totals more than 200 words, so the implementation plan
   includes a jargon table (H/M/L plus plain rewrite) for it.
4. Final acceptance: re-run the full skill check at the landed revision:
   `count_connectives.py` (baseline Shinagawa 2021 PDF), `control_panel.py`
   (same four peers), `fact_density.py`, the per-section script, plus an
   I/we-neutral signposting variant applied to ALL six panel papers (peers
   use "we", so the extension cannot flatter the target).

### Acceptance gates

| Gate | Before | Target |
|------|-------:|-------:|
| std census TOTAL per 10k | 14.9 | >= 30 |
| instance family per 10k | 1.5 | >= 5.5 |
| worked Example blocks | 0 | >= 1 |
| adversative (std) events | 0 | >= 1 |
| neutral signposting per 10k | ~4.5 | >= 14 |
| Section 3 std moves | 0 | >= 3 |
| Section 7 extended rate per 10k | 11.9 | >= 25 |
| reason events | 4 | >= 7 |
| inference events | 5 | >= 8 |
| compile | clean, 21 pp | clean, pages reported |

No-regression side conditions: reason and inference event counts must not
drop below their before values at intermediate commits.

## Risks and rollback

- Example values depend on the action-direction convention (recorded as a
  load-bearing unknown in project memory). The example does not land until
  the source check resolves it.
- llncs `example` environment may clash with the existing `\spnewtheorem`
  preamble; fall back to a fresh `\spnewtheorem` name.
- Float placement may shift pages; recompile per commit.
- `.tex`-only commits do not trigger the rocq-audit Stage 2 gate; no bypass
  is needed.
- Rollback is per-commit `git revert`.
