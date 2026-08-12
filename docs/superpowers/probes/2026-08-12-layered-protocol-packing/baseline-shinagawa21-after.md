# Baseline: pgg-smc measured against Shinagawa 2021 (AFTER)

Measured 2026-08-12 at HEAD `b4a163d0`, after the layered-protocol-packing
implementation, by re-running the frozen METRIC procedures of
`baseline-shinagawa21-before.md` verbatim.

## AFTER scorecard

| # | BEFORE | AFTER | Evidence (abbreviated; full evidence in the run log) |
|---|---|---|---|
| V1 | 1 | 1 | SecurityWitness gone from the instance-defining path (grep 0 hits); the metric grep returns 4 record hits instead of 5, but the remaining constituents still span protocol/ + reconstruct/ |
| V2 | 1 | 1 | manifest/pgg_analysis_manifest.v is one current machine-checked table (dated at HEAD, 89 type-pinned Check lines) but covers 3 of 5 in-scope instances (5 rows: 2 pgl27 + 3 five-card/den Boer; s5/s5x5 = 0 hits) — the H2 rows close this |
| V3 | 1 | 1 | per-dir prefix counts byte-identical to BEFORE; new role files only in the two featured dirs |
| V4 | 1 | 1 | denboer_indep / kim_indep / pgl27_view_indep still three spellings; FiveCardKim_protocol_correct still in denboer1989/; facades add a second uniform alias layer (14 shared names) but security aliases still diverge |
| V5 | 0 | 1 | (a) FIXED: MonodromyProfile has 4 fields, no R, no mp_security (proof obligations still ride via mp_plug — R-free, not proof-free); (b) unchanged: pgg_uc_security.v in protocol/, demo/test files in security/, witness records in reconstruct/ |
| V6 | 0 | 0 | no README/scope note in pgg-smc/; _CoqProject retired-instance census still exactly 14 lines |
| V7 | 1 | 1 | pgg_monodromy_profile.v header now names the four current fillers; pgg_interface.v and algebraic_rigidity.v example pointers still stale; two files have no pointers |
| V8 | 0 | 2 | 4 Require Export files (was 0); PGL story = 1 file (pgl27_analysis.v, 42 aliases), five-card story = 1 file (five_card_analysis.v, 47 aliases, absorbing the cross-dir den Boer part), both = the manifest; client: 1 Require, 48 resolving Checks |

## TOTAL: 8 / 16 (BEFORE 5 / 16, delta +3)

The request's stages moved exactly the virtues they targeted: stage A moved
V5, stage H1 moved V8 (0 to 2, the largest single gap closed). The
remaining distance has a mapped route: H2 facades for s5/s5x5 complete V2's
table; a scope README plus retired-instance build cleanup (a user decision,
out of this request's scope) closes V6; framework-header example-pointer
refresh closes V7; view/correctness name unification across instances
closes V4. V5's second point requires directory hygiene (moving
pgg_uc_security.v, the demo/test files, and the witness records) — a
mechanical follow-up, also outside this request.
