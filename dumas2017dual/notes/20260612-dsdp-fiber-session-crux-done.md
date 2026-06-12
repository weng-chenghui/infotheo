# 2026-06-12 — fiber item-1 crux + item-8 final theorem DONE; only `guess_cinde_V2` remains

Branch `itp2026-dumas2017dual`, file
`dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v` (compiles green, ~35s;
the slow step is the `dmargin_comp` over the giant predictor term in
`guess_inner_kernel_form`, accepted).

## Committed this session

- `6890e66` — `denote_run_caps_valid` (rich run valid over `protocol_state`,
  structural induction reusing `denote_run_valid` at the put_output/drun leaf)
  + `denote_run_caps_preserves` (run heaps agree with the start heap off the two
  protocol cells, proved by induction; `Pr_code_preserves` applies on the plain
  `drun` leaf where the value type `cipher_list` is a genuine choice_type, but
  NOT on the rich run whose value type is a mathcomp product — that mismatch is
  why the generic frame `apply` times out) + `run_heap_agree_predictor`.
- `4cc1bfc` — **THE CRUX**: `guess_inner_kernel_form` + `guess_inner_out`.
  `guess_inner_kernel_form a b`: the guess marginal of `guess_inner a b` =
  `dlet (fun cl => dmargin (msg_to_fin \o fst) (Pr_code (resolve (pack predictor)
  (id_guess,...) (cl, chmsg_of_msg (dsdp_output _ (msg a)(msg b)))) emptym))
  (dmargin fst (Pr_code (drun (push (msg b)(push (msg a) seed)) gci) emptym))`.
  Proof path (all FAST except the final `dmargin_comp`, which is the accepted
  perf wall): `-Pr_fst_map` to a code projection; peel the run with
  `Pr_code_bind`+`dfst_dlet_commut`; `HBASE` identifies the drun cipher-marginal
  with the run's via `denote_run_caps_fst`; new helper `dlet_dmargin_eq` reindexes
  `dlet g (dmargin f mu) = dlet (g\o f) mu` keeping `dmargin` folded; `eq_in_dlet`
  over the run support; `s_get` collapsed by `guess_run_cells` (HS); the discarded
  `V_2` read is lossless (`Hinner`); heap dropped via `Pr_fst_agree_locs` +
  `run_heap_agree_predictor`; final `transitivity` through `dmargin fst` +
  `dmargin_comp`. `guess_inner_out`: equal `dsdp_output` => equal guess marginals
  (kernels coincide by equal `chmsg`, bases coincide by `view_marginal_indep`).
- `2c3245a` — **item 8 / final theorem**: `guess_sdistr_success_real`,
  `guess_reduction` (= `guessing_challenger ∘ par (pack predictor) (ID ...)`,
  `guess_reduction_valid` via `valid_par`/`valid_link_weak`/
  `valid_package_inject_locations`), `real_game_valid`/`game_valid`
  (`denote_game_leak_S_valid`), `guess_advantage_eq` (`Advantage_par` slides the
  fixed predictor out of the `par`; `rewrite -Hpar /AdvantageE`),
  `guess_advantage_le` (`eapply dsdp_advantage_derived_leak_S`, NOT `apply:` —
  the latter delta-unfolds raw_package bodies), and the theorem
  `dsdp_alice_secrecy_leak_S : guess_sdistr_success_real <= card_msg^-1 +
  2*epsilon_cpa`. `Print Assumptions`: only classical axioms + the IND-CPA
  assumption `enc_ind_cpa_real_or_zero` + the upstream `realsum` admit; no custom
  axioms. `Hcinde` is still THREADED (the cinde below).

## Remaining: `guess_cinde_V2` (discharges the threaded `Hcinde`), then inline

`guess_sample_fdist |= guess_rv _|_ V2 | Sout`, via `cinde_RV_factor`
(`extra_proba.v:529`: needs `forall x y z, Pr[[%X,Y,Z]=(x,y,z)] = f y z * g z x`,
X=`guess_rv`, Y=`V2`, Z=`Sout`).

Kernel-z route (no canonical-fiber choice needed):
- `Dview := dmargin fst (Pr_code (drun (push (Gplain 0)(push (Gplain 0) seed)) gci)
  emptym)` (view marginal at the 0,0 secrets; 0 : plain AHE exists).
- `Kguess z := dlet (fun cl => dmargin (msg_to_fin \o fst) (Pr_code (resolve
  (pack predictor) (id_guess,...) (cl, chmsg_of_msg z)) emptym)) Dview`.
- Lemma `guess_inner_kernel_z a b : dmargin (.1.1) (Pr_fst (guess_inner a b)) =
  Kguess (dsdp_output w_v1 w_u1 w_u2 w_u3 (msg_of_idx a)(msg_of_idx b))`. Proof:
  `rewrite guess_inner_kernel_form; congr (dlet _ _); exact: (view_marginal_indep
  (msg_of_idx a)(msg_of_idx b) 0 0 emptym)`. (Short, confident.)
- Bridge (the hard part): `pfwd1 [%guess_rv,V2,Sout] (x,y,z) = f y z * g z x`, with
  `g z x := (dmargin fin_to_plain (Kguess z)) x` and `f y z := (#|plain AHE|^-1)^2 *
  #{b : dsdp_output _ y (msg_of_idx b) = z}` (the V3-fiber count, V2=y).
  Math: by `guess_triple_peel` the finite (guess_M,V2_M,V3_M) law is
  `a←unif;;b←unif;; PROJ3(guess_inner a b)`; by `guess_inner_v2v3_det` V2_M,V3_M are
  the constants `msg_to_fin(chmsg(msg a))`, `msg_to_fin(chmsg(msg b))`, so V2=msg a,
  V3=msg b (via `chmsg_of_msgK`,`msg_to_finK`), and `msg_of_idx` bijective
  (`Hmsg_bij`) pins a=idx y. Sout = `dsdp_output _ (msg a)(msg b)`. Fiber-sum the
  Sout=z over b; on the fiber `guess_inner_out` => guess marginal = `Kguess z`
  (constant in b). The fdist↔code bridge mirrors `guess_VarRV_uniform`
  (`dist_of_RV` = `fdistmap PROJ guess_sample_fdist` = `sdistr_to_fdist` of the
  projected code, then `Pr_fst_map`); the Sout marginalisation uses that
  `[%guess_rv,V2,Sout]` is the deterministic image of `[%guess_rv,V2,V3]` under
  `(g,v2,v3) ↦ (g,v2, dsdp_output _ v2 v3)`, so its pfwd1 is the V3-fiber sum.

Then inline (item 3/5): drop the `Hcinde` binder from `guess_fdist_success_le`,
`guess_sdistr_success_le`, and `dsdp_alice_secrecy_leak_S`, discharging it with
`guess_cinde_V2`.

Scaffolding probe that compiles (item-8 dev): `dumas2017dual/dsdp/.scratch/probe_item8b.v`.
