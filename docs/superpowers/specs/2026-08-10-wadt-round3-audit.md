# Opus Audit Report: WADT Round 3 Signposting Spec (2026-08-10)

Adversarial audit of `2026-08-10-wadt-round3-signposting-design.md` at spec
commit `0644d731` against `main.tex` at `ae47ca79`. The auditor applied every
edit in a scratch directory, ran the v2 census scripts per edit and in
aggregate, compiled before and after with latexmk, grepped every term's full
occurrence set, and checked the naming sentences against the Rocq sources.

## Per-edit verdicts

S1 PASS. S2 PASS (N12). S3 BLOCKER (F1) + AMEND (F2). S4 AMEND (F3).
S5 PASS. S6 PASS. S7 PASS (N13). S8a AMEND (F4). S8b PASS. S9 PASS (N14).
S10 PASS. S11 AMEND (F5). S12 PASS (N15). S13 PASS (N16). S14 AMEND (F6).
S15 AMEND (F7). S16 PASS. B1 AMEND (F8).

All 17 OLD strings unique modulo whitespace; all deltas match the spec; all
new matches land in surviving text; no OLD string double-counts.

## Findings

**F1 BLOCKER.** "profile" is used in surviving body prose at L136
(Introduction, itemize, renders page 2): "one profile at bias
$\varepsilon$". S3's introduction at L414 renders page 7, so the reader
meets the term undisclosed five pages early. Fix: forward pointer at L136
plus the F2 amendment.

**F2 AMEND.** "I call a filled record a profile" is over-general:
`PGGInterface`, `SecurityWitness`, `ReconPlug`, `InputEncoding`,
`ThresholdScheme` are all records whose filling is not a profile. A profile
is a filled `MonodromyProfile` (`pgg_monodromy_profile.v:49`).

**F3 AMEND.** S4's gloss "the record that holds the shuffle-security
evidence" misdescribes `SecurityWitness` (`algebraic_rigidity.v:147`): it
carries the shuffle distribution `sw_rho_dist` and the endpoint bound, which
are protocol data; fig:framework-architecture draws the evidence as a
separate supporting box. Replacement: "carries the shuffle distribution and
its endpoint bound".

**F4 AMEND.** S8a deletes the load-bearing gloss on `H_secret` (entropy
ceiling, not a leakage value) and buys nothing: in the compiled PDF the S8b
body sentence precedes footnote 11 in reading order. Replacement keeps a
gloss: "the secret's own entropy \coqin{H\_secret}".

**F5 AMEND.** S11's "I call this" has "A third dealer" as antecedent, naming
a dealer as a distribution, and the exact phrase never recurs (downstream
says "shuffle-free dealers"). Replacement: "I call the resulting
distribution the shuffle-free deck distribution, and view independence
holds under it for every Boolean secret prior."

**F6 AMEND.** No theorem-class environment in the paper contains an
authorial pronoun; S14 would put the first "I" inside Theorem B. Voice-
neutral counted replacement: "where the coalition view at dealt secret $s$
and shuffle $g$ is denoted $V_C(s,g)$".

**F7 AMEND.** S15's "set of assumptions" excludes the Rocq kernel, which
the paper's own trust-base column lists ("kernel, boolp") and L1356
describes as checking software. Replacement: "The checker and the axioms
that a result's verification rests on are called its trust base."

**F8 AMEND.** B1 leaves L93's "uniform-shuffle model" with no section
reference, making the spec's "both pointers name the section" disclosure
false; and "ideal" vocabulary survives at L88, L1102, L1226, L1441, so the
orphan-term claim holds only for the exact bigram. Replacement adds "of
Section~\ref{sec:model}".

## Notes

**N9.** D7 is wrong about table captions: `table` is not in the stripped
env list, so table captions survive (verified for tab:bridge,
tab:witness-mechanism, tab:instances); only the `tabular` body is stripped.
S4's "(the table caption occurrence is stripped)" justification is false but
the verdict is unaffected (that caption is at L458, after L436).

**N10.** Footnote survival and figure-caption stripping confirmed.

**N11.** "mixing certificate" appears in the stripped fig:models caption
(renders ~page 5) long before S12's introduction (L1138); a census
exemption is not a reader exemption. Disclose.

**N12.** "executed trace" (L48 abstract, L83 intro) and "coalition trace"
(L119 Theorem B informal) precede the S2 naming at L208. Pre-existing;
disclose rather than claim clean first use.

**N13.** "master theorem" never recurs after L614 (weakest edit on the
decoration test; honest coinage, kept).

**N14.** "privacy threshold" used bare at L415 before S9's definition
(pre-existing, list mention).

**N15.** S12 designator vs L1183 class-noun tension; harmless.

**N16.** S13 names the first transfer but the second transfer (L1163) stays
unnamed despite its lemma title.

**N17.** "record" carries two defined senses after S2+S3; the F2 amendment
(naming `MonodromyProfile`) removes most of the collision.

**N18.** Executor must re-indent NEW blocks to the surrounding file
indentation (notably S16 inside an itemize item).

## Aggregate verification

WADT before: 7453 words, 13 hits, 17.4/10k, moves 67.1. After all edits:
7553 words, 30 hits, 39.7/10k, moves 66.2. Projections reproduce exactly.
Gates: signpost 39.7 >= 38 PASS; hits 30 >= 29 PASS; moves 66.2 >= 60 PASS;
minimum touched section 23.7/10k (Introduction) >= 18 PASS; Related Work and
Conclusion 0 and 0 PASS; abstract byte-identical PASS. Compile: both builds
exit 0, 24 pages, warning multiset identical modulo line numbers.

Landing recommendation: S1, S2, S5, S6, S7, S8b, S9, S10, S12, S13, S16 as
written; S4, S8a, S11, S14, S15, B1 with the F3-F8 replacements; S3 with the
F1 forward pointer plus the F2 replacement.
