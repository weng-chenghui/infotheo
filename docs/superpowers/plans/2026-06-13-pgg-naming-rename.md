# PGG-SMC Naming Rename Plan

> **For agentic workers:** a mechanical identifier-rename refactor, gated by recompilation. **Deferred: execute AFTER the blueprint is written** (the blueprint uses the *target* names as display labels, so it is not blocked on this). Status: PLANNED, not executed.

**Goal:** Apply the 34 naming-audit-approved renames (high-confidence list + `ie_fun→ie_output` + `pgg_hidden_invariant_perm→pgg_recon_monodromy_correct`; `ReconPlug` kept). Semantics unchanged; `Print Assumptions` of every headline theorem must be identical before and after.

**Method:** word-bounded replace per identifier (`grep -rlw` to find files, then per-file replace of the exact token), recompile the affected subtree with `make -j1`, never blind-`sed` the short names. Gate each unit on a clean build.

---

## Pre-flight (once, before any rename)

- [ ] For every NEW name in the table, `grep -rnw '<new>' pgg-smc --include='*.v'` must return nothing (no clash). Special watch: `perm_repr` (may exist in mathcomp `mxrepresentation`), `proj_share`, `s5_genus0_pgl_bound` (must not already exist alongside `s5_genus0_pgl_crypto`).
- [ ] Record the baseline: `Print Assumptions` for `den_boer_run_output`, `den_boer_input_private`, `s5_wired_gap_impossible`(→new), `s5x5_protocol_correct`, `recon_from_layout_output`. Re-check identical at the end.

## Unit A — `reconstruct/s5_nogo.v` (file-local batch, 17 renames)

Every occurrence is inside `s5_nogo.v`; `e0` and `rG` are KEPT. The `Pr` rename is **scoped to this file only** — `Pr` in `security/`, `protocol/`, `lib/` is the probability `Pr[·]` and must not be touched.

| old | new | occ |
|---|---|---|
| `rGV` | `rG_secret` | 13 |
| `rGVfun` | `secret_action` | 8 |
| `rGVfun_repr` | `secret_action_repr` | 2 |
| `rGV_Pr_comm` | `secret_proj_comm` | 2 |
| `Dmx` | `diff_basis_mx` | 12 |
| `prep` | `perm_repr` | 3 |
| `Pr` | `proj_share` | (s5_nogo.v only) |
| `Pr_rank` | `proj_share_rank` | 2 |
| `e0_Pr` | `e0_proj_share` | 2 |
| `dvec_act` | `diff_actE` | 4 |
| `nonconst_dvec_in` | `nonconst_diff_in` | 5 |
| `all_dvec_in` | `all_diff_in` | 5 |
| `rank4_of_dvec` | `rank4_of_diff` | 3 |
| `W_module` | `proj_mxmodule` | 5 |
| `W_rank_pred` | `mxrank_proj_pred` | 6 |
| `s5_gate_rejects` | `s5_gap_window_infeasible` | 1 |
| `s5_wired_gap_impossible` | `s5_gap_infeasible` | 1 |

- [ ] Apply all 17 within `s5_nogo.v`. Order the `Pr` token replace carefully: replace `Pr_rank`/`e0_Pr`/`rGV_Pr_comm` first (compound), then standalone `Pr` `\b`-bounded.
- [ ] `make -j1 pgg-smc/reconstruct/s5_nogo.vo` clean.
- [ ] `grep -lw '<new>' downstream` — confirm no other file references the renamed s5_nogo internals (the map showed none do).

## Unit B — cross-file renames (word-bounded, project-wide per identifier)

| old | new | files (occ) |
|---|---|---|
| `pgg_hidden_invariant_perm` | `pgg_recon_monodromy_correct` | cover_genus0, covering_scheme, pgg_covering_correctness, pgg_protocol_landscape, algebraic_rigidity, pgg_sharing_framework, rigidity_s5x5_instance, den_boer_run, den_boer_profile (14) |
| `ie_fun` | `ie_output` | input_encoding (8) |
| `kim_slev` | `kim_lambda2` | five_card_family, five_card_kim, den_boer_profile (29) |
| `fc_kim_wsc` | `fc_kim_schreier_cert` | five_card_kim (4) |
| `FiveCardKim_HT` | `FiveCardKim_Teq` | den_boer_run, den_boer_profile (13) |
| `s5_rayleigh_Qsq_R` | `s5_rayleigh_Q2_R` | s5_mixing, s5x5_mixing (8) |
| `s5_lazy_rayleigh_Qsq_R` | `s5_lazy_rayleigh_Q2_R` | s5x5_mixing (4) |
| `R_s5` | `M_s5` | curve_realisation, rigidity_s5_instance (35) — **check `R_s5_brings`: rename to `M_s5_brings` for consistency** |
| `R_s5x5` | `M_s5x5` | rigidity_s5x5_instance, pgg_s5x5 (55) |
| `run_k_den_boer` | `den_boer_run_k` | den_boer_profile (2) |
| `s5x5_preserves_pile1_proved` | `s5x5_pile1_stab` | s5x5_pile, rigidity_s5x5_instance (2) |
| `ar_tradeoff` | `ar_genus_gap_dichotomy` | pgg_protocol_landscape, pgg_landscape_demo, algebraic_rigidity, rigidity_s5x5_instance (7) |
| `ar_search_gap_tradeoff` | `ar_search_gap_dichotomy` | algebraic_rigidity (2) |
| `leak_k2_d2` | `leak_k2_dist2` | five_card_leakage (3) |
| `den_boer_decode_commit` | `den_boer_decodeK` | den_boer_run (2) |
| `fcI_correct` | `fcI_reconK` | five_card_program, five_card_scheme_I5 (6) |
| `s5_genus0_pgl_crypto` | `s5_genus0_pgl_bound` | rigidity_s5_instance (4) |

- [ ] Do one identifier at a time, in this order (definition file last is fine since it is a pure rename): for each, `grep -rlw '<old>' pgg-smc --include='*.v'` → replace the `\b`-bounded token in each → `make -j1` the highest-level dependent `.vo` (which pulls the subtree).
- [ ] `R_s5`/`R_s5x5`: verify `\b`-boundedness does not catch each other or `R_s5_brings` unintentionally; decide `R_s5_brings`→`M_s5_brings` and apply together.
- [ ] `ar_tradeoff`: `\b`-bounded so it will NOT catch `ar_search_gap_tradeoff`, `s5_tradeoff`, `s5x5_tradeoff` — confirm by diff.

## Out of scope (do NOT rename)

- `channels_dual` (Boolean-vs-Prop naming flaw) — lives in upstream `infotheo/smc/smc_session_types.v`, not pgg-smc.
- `pgl_bound` (the name overstates: body is Klein's `maxn (2N) 60`, not `|PGL|`). Flagged for a SEPARATE decision; high blast-radius, file comment defends it. Not in this plan.
- `e0`, `rG`, `endpoint(s)`, `ts_valid`, `achievable`, `search_space`, `exchange_dealer/player/verifier`, the genus ladder, the records, proper-noun lemmas — audited KEEP.

## Final verification

- [ ] `make -j1` full build green (or rebuild the touched subtree from clean `.vo`).
- [ ] `grep -rnw '<old>'` for every old name returns nothing (except the deliberately-kept probability `Pr` in non-s5_nogo files).
- [ ] `Print Assumptions` parity vs the pre-flight baseline — identical axiom sets, no new axioms.
- [ ] Update the blueprint `\rocq{}` targets to the new names (they were displayed under the new labels already; only the link anchors change).
