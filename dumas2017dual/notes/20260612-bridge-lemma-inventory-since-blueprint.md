# 2026-06-12 — Bridge lemma inventory (since the blueprint), diagram vs dependencies

Inventory of every name the SSProve↔Infotheo bridge diagrams relate to, split
into what the diagrams show versus the dependencies they do not, scoped to what
was created in this round of the bridge formalization.

**Cutoff: 2026-06-10**, when the bridge blueprint
`dumas2017dual/blueprint/src/it_bound_bridge.tex` was created (commit `5648f6c`).
Everything in `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v` dates from this
round. The three diagrams are `fig:dsdp:merge` (the bridge derivation map),
`fig:dsdp:two-channels`, and `fig:dsdp:guessing-experiment` in
`aplas2024-poster/thesis/chapters/dsdp.tex`.

## A. Shown in the diagram(s) — created since the blueprint

**Merge figure** (`dsdp_security_indcpa_fiber.v` unless noted):
- `guessing_experiment`, `guess_resolve_eq`, `guess_joint_code`
- `guess_success_sdistr_eq_fdist` (connector), `guess_joint_fdist` +
  `guess_joint_fdist_marginal` (marginal)
- `guess_sample_fdist`, `guess_cinde_V2` (realization), `run_heap_agree_predictor`
  (frame)
- `guess_fdist_success_le`, `guess_sdistr_success_le`, `guess_V2_cond_le`
  (per-fiber bound (b))
- `guess_advantage_eq`, `guess_advantage_le`, `dsdp_alice_secrecy_leak_S` (final)
- `cinde_diagonal_bound` — `lib/extra_proba.v` (06-12)
- `Pr_dsdp_sol_uniform_ring`, `dsdp_fiber_card_ring` — `dsdp_entropy.v`
  (route-F, 06-11)
- `dsdp_advantage_derived_leak_S` — `dsdp_indcpa_security.v` (06-10)

**Two-channels figure** adds: `id_s_get` (`dsdp_game_code.v`, 06-10),
`real_game_leak_S` / `zero_game_leak_S` (`dsdp_indcpa_security.v`, 06-10).

**Guessing-experiment figure** adds: `guessing_challenger`, `predictor_guesser`.

**Referenced in the diagrams but PRE-dating the blueprint** (reused
infrastructure, outside this window): `gen_cPr_uniform_fiber`
(`entropy_fiber/entropy_fiber_zpq.v`, 2026-03-01), `dsdp_entropy_ring` section
(`dsdp_entropy.v`, 2026-05-14), `id_game_run` / `id_v2_get`
(`dsdp_game_code.v`, 2026-05-15).

## B. Dependencies created this round, NOT shown in the diagram

All in `dsdp_security_indcpa_fiber.v` unless noted.

**fdist <-> SDistr bridge:** `sdistr_to_fdist`, `sdistr_to_fdistE`,
`Pr_sdistr_to_fdist`, `dmargin_comp`, `dlet_dmargin_eq`, `Pr_fst_map`,
`Pr_fdistmap_pre`, `fdistmap_bij_unif`, `mean1_eq1`, `fin_to_plain`

**heap-frame / footprint:** `Pr_fst_agree_locs`, `Pr_fst_closed`,
`Pr_fst_put_invariant`, `eq_in_dlet`, `dlet_const_unit`, `dmargin_fst_const`,
`Pr_code_preserves`

**challenger linking / oracle resolution:** `id_guess`, `guesser_export`,
`guess_pair_challenger`, `guess_op`, `guess_resolved`, `resolve_predictor_valid`,
`guess_resolved_par`, `resolve_game_run`, `resolve_game_sget`,
`resolve_game_v2get`, `guess_resolved_oracles`, `guess_sdistr_success`,
`guess_fdist_success`

**denotation of the leaked output S:** `drun_sample_msg`, `drun_sample_renc`,
`drun_put`, `drun_put_output`, `drun_let`, `drun_enc_hop`, `drun_ret`, `gc_eq`,
`denote_output_termE`, `denote_run_distrE`; `dsdp_output`, `alice_resultE`
(`dsdp_program.v`, 06-11); `denote_game_leak_S`, `denote_game_leak_S_raw`,
`denote_game_leak_S_valid` (`dsdp_game_code.v`, 06-11)

**the capturing run (rich carrier):** `denote_run_caps_fst`,
`denote_run_caps_valid`, `denote_run_caps_preserves`, `drc_sample_msg`,
`drc_sample_renc`, `drc_put`, `drc_let`, `drc_hop`, `drc_putout`,
`guess_resolved_caps`, `guess_full_code`, `guess_full_proj_code`,
`guess_triple_proj_code`, `guess_inner`, `guess_triple_peel`

**the kernel crux (the hard reflection):** `view_marginal_indep`,
`guess_run_cells`, `guess_inner_v2v3_det`, `guess_inner_kernel_form`,
`guess_inner_out`, `Dview`, `Kguess`, `guess_inner_kernel_z`, `guess_triple_pr`

**random variables + determinism:** `guess_rv`, `V1`, `V2`, `V3`, `U1`, `U2`,
`U3`, `ir1_rv`, `ir2_rv`, `Sout`, `Zcond`, `guess_S_determined`,
`de_val_nth_pushS`, `de_val_nth_push0`, `de_val_nth_pushrand`, `as_plain_Gplain`,
`dhe_var`, `guess_inputs_indep`, `cpr_eq_drop_indep`

**entropy-side (1/m residual):** `cardpp`, `Htail2_abs`, `guess_VarRV_uniform`,
`guess_VarRV_cond_uniform`, `guess_V2_cond_Sout`; `dsdp_fiber_ring`
(`dsdp_entropy.v`)

**composition / final assembly:** `real_game`, `guess_sdistr_success_real`,
`guess_reduction`, `guess_reduction_valid`, `real_game_valid`, `game_valid`

## Scope notes

- `Definition`/`Let` nodes are counted where the diagram names them (e.g.
  `guess_sample_fdist`, `guessing_experiment`), since they are diagram boxes even
  if not "lemmas."
- If "the diagram" means only the merge figure, then `id_s_get`,
  `guessing_challenger`, `predictor_guesser`, and the two `*_leak_S` games move
  from A into "shown only in the side figures."
