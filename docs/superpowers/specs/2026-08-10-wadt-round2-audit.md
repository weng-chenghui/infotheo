# Opus Audit Report: WADT Round 2 Spec (2026-08-10)

Adversarial audit of `2026-08-10-wadt-round2-peer-mean-design.md` at spec
commit `e970ab53`. The auditor built the fully-edited paper in a scratch
directory, ran the v2 census scripts on it, compiled with `latexmk`, and
re-derived every Rocq-grounded number from source. Findings A1-A22 below;
resolutions are recorded in the amended spec's audit-resolution table.

## Findings

**A1. BLOCKER.** R3 contradicts the sentence it is inserted after and
overclaims `thm:generic-privacy` (paper 491-502): the theorem needs a
t-transitive action, distinct-card encoding, uniform shuffle, and
|C| <= t (`transitivity_privacy.v:528-622`), not transitivity alone.
"Rests on the three-transitive action alone" denies the preceding
hypotheses sentence and is false under the word distribution.

**A2. BLOCKER.** R7's lead-in "the three generator letters" has no
antecedent at line 767 and collides with "five generator letters"
(abstract line 57, line 116); the three generators are first named in
Section 7 (1045-1047).

**A3. BLOCKER.** R15's stated reason is not the reason: security rests on
the shuffle because the encoding is a fixed public representative
(paper 772-773), not because views are small.

**A4. AMEND.** Figure top row "deck $D$" clashes with $D$ = dealt
arrangement (196-199) and duplicates fig:encoding's $D_0$ row, which
prints the eighth card as 7 while the new figure prints infinity; the two
figures land on facing pages.

**A5. AMEND.** R17 demotes "the precise sense" to "a precise sense" and
claims the identification follows from the bound; the collapse is
evidence, not derivation.

**A6. AMEND.** R8's last sentence near-verbatim duplicates paper 832-835
and consumes the same `for example`; forward reference lacks a "below"
cue; the translation sentence also overlaps ex:coalition-view (954-966).

**A7. AMEND.** R13's "full cryptographic program logic" mislabels
CryptHOL and contradicts the FORTE-interpreter credit two sentences later
(`card_exchange_pismc.v:7` imports the interpreter). Honest axis:
information-theoretic bounds vs game-based reductions.

**A8. AMEND.** R9 drops "against passive participants" from a
perfect-security claim.

**A9. AMEND.** "determine the conjunction to X bits" misreads mutual
information (`leak_k2_adj : I(Secret; ViewA [0;1]) = ...`,
`five_card_leakage.v:317`); say "reveal X bits about the conjunction".

**A10. AMEND.** Spec's census note is wrong: whole `figure` environments
including captions are stripped (`count_connectives.py:76`, the `figure*`
pattern's `*` quantifies the letter `e`). Captions contribute nothing,
neither moves nor words.

**A11. AMEND.** Caption attributes rows to `Local Definition` tables
(`pgl27_group.v:51-53`) invisible outside the file; the exported names
are `tr_moebius`, `sc_moebius`, `inv_moebius` (lines 136/144/152).

**A12. AMEND.** Sharpness sentence should show its one counting step:
order 336 (`pgl27_card`, `pgl27_mixing.v:474`) equals the number of
ordered triples, so existence leaves exactly one element each.

**A13. AMEND.** R6 restates four nearby sentences (674-677, 624-625).
Non-repetitive replacement keeps all three counted moves; final clause is
exactly `leakE3` (`five_card_leakage.v:832`), cardinality-only.

**A14. NOTE.** Inversion is an involution with four swaps
(0-inf, 1-6, 2-3, 4-5); naming only one invites reader confusion.

**A15. NOTE.** R14 is filler; better target four lines later also fixes a
third-person voice slip ("The paper proves..." at 93-95).

**A16. NOTE.** Page count grows 21 to 24 (one page Section 5, two float
slack). Permitted by D2 but must be reported.

**A17. NOTE.** Eight of 24 moves are relabelings of existing
constructions (R2, R10, R11, R12, R16, R17, R18, R20); `--ext` falls
15 to 11. The acceptance report must disclose this.

**A18. NOTE.** Abstract (=2) and Conclusion (=3) gates have zero margin;
the A1 fix must keep an inference-family word.

**A19. NOTE.** R5's purpose clause is new content, not a
meaning-preserving rewrite; record as deliberate.

**A20. NOTE.** R1, R11, R13 are heavier than their originals, against the
spec's simplicity constraint; accepted deviation, the added clause IS the
motivational move.

**A21. NOTE.** R19 calls L=200 an example, but 200 is Theorem B's length;
advisory.

**A22. NOTE.** R7 caption would be the paper's first with `\coqin`; all
eleven existing captions keep kernel names in footnotes or body.

## Verified clean

All 24 transformed-row card values and the identity row match the kernel
tables and independent re-derivation from z+1, 3z, -1/z over F_7 with
infinity encoded as 7. Direction convention "position i shows g(i)" is
exact (`transitivity_privacy.v:541`, `pgl27_secrecy.v:72`,
`pgl27_word_privacy.v:122`, `pgl27_recovery.v:117`,
`pgg_interface.v:455`; `pgg_rho` is the inclusion). Six-cycle of 3z is
(1 3 2 6 4 5). Numerics: adjacent 0.154370, distance-two 0.118717,
three-card 0.486767, cap 0.811278; `leak_k3` = `leak_k3_gap`; `leakE3`
generalizes. Shape-only phrasing justified by the `adjacent` classifier
and `leak_view_set` (all 32 subsets). All twenty OLD strings unique
modulo wrapping. Census arithmetic: 26 to 50 moves at 7338 words =
68.1/10k; example blocks 3, adversative 6, gloss 0, aside 0, Abstract 2,
Conclusion 3, five-card 6, lowest section 43.8 vs 24.6 floor. Compile
clean, float order holds (generator figure page 12, encoding figure page
13). No forbidden punctuation, voice, or vocabulary in inserted prose.
