# DSDP output-channel (1/m) — derived implementation plan (A1)

Date: 2026-06-10. Branch: itp2026-dumas2017dual.
Spec: `blueprint/src/it_bound_bridge.tex` (Part II, chs 9–11). Each blue node
carries `% to create:` and `% proof:` comments — that file IS the per-node spec.

## Decision (A1, approved)

Derive the scalar-product output `S` faithfully: continue the corrupted-view
walk across Alice's decrypt-receive (which already exists in `palice_sym`,
consumed by her last `Recv_dec`, `dsdp_symbolic.v:142,148`). Retire the
hand-written `ref/dsdp_security_indcpa.v` strand. Build the absolute-Pr guessing
layer + the Infotheo connector on the DERIVED endpoint game.

## Grounding (verified signatures)

- `alice_obs` (`dsdp_game_symbolic.v:108`): ctors `AO_sample_val/_rnd`, `AO_put`,
  `AO_recv_hop p secret result`, `AO_combine result expr`, `AO_leak names`.
- `count_obs_hops` (`:120`): catch-all `_ :: rest => count_obs_hops rest`, stops
  at `AO_leak`. A NEW non-hop ctor needs NO change here.
- `walk_obs` (`:219`): at `Recv`, matches `symbolic_get_cipher r` =
  `Some (HE_enc party (HE_var secret) _)` → `AO_recv_hop`; ELSE `[::]` (halt).
  The decrypt result `HE_var 50` is not an `HE_enc`, so it currently halts.
- `lower_obs` (`:155`): per-ctor arm → `game_code`; `AO_put`→`GC_put`,
  `AO_recv_hop`→`GC_enc_hop`, `AO_combine`→`GC_let`, `AO_leak`→`GC_ret`.
- `game_iface` (`dsdp_game_code.v:233`): exports `id_game_run : unit→ciphers`,
  `id_v2_get : unit→msg`. `V_2_cell` (`:221`) `option t_msg`, written in
  `denote_run` by the `GC_put` arm, read by `id_v2_get`. `cipher_list` (`:204`)
  is the `GC_ret` type — KEEP it; the generic 2eps theorem is over it.
- The derived chain (`dsdp_game_code/symbolic/indcpa_security`) does NOT Require
  `ref/dsdp_security_indcpa.v`. Only `ref/dsdp_security_indcpa_{concrete,pismc}.v`
  do (plus `_clone` shadows, off the build).

## Expose-S mechanism (keeps GC_ret = cipher_list)

Add `S_output_cell : Location` + `id_s_get` oracle (parallel to `V_2_cell` /
`id_v2_get`). `id_game_run` computes `S = u1*v1 + u2*v2 + u3*v3` from the sampled
scalars (and Alice's constant inputs) and `#put`s it to `S_output_cell`;
`id_s_get` reads it. The write needs ONE put-to-S statement in `denote_run`:
prefer generalizing `GC_put` to carry a target cell id, else add `GC_put_output`
— rocq-prover picks the minimal-ripple option. Either way `S` adds NO hop, so
`count_hops` adequacy and the generic hybrid bound `advantage_le` re-prove
mechanically (one extra/threaded case, recurses; not a hop site).

## Atomic tasks (each verified via rocq_check + committed; rocq audit hook skipped)

1. `dsdp_game_code.v`: expose-S machinery (`S_output_cell`, `id_s_get`, widen
   `game_iface`, the put-to-S statement), update `count_hops`, `denote_run`,
   `zero_hop_prefix`/`all_real`/`all_zero`, `hop_sites`; re-prove the generic
   hybrid bound for the extended `game_code`. Verify `advantage_le` holds.
2. `dsdp_game_symbolic.v`: `AO_recv_output` ctor; `walk_obs` decrypt arm; 3-elt
   response stream; `lower_obs` arm → put-to-S; new trace lemma
   `obs_of_procs_dsdp_leak_S`; re-prove `count_hops_*` adequacy + a faithfulness
   lemma. Verify the 2-hop count is preserved.
3. `dsdp_indcpa_security.v`: `real_game_leak_S`, `zero_game_leak_S`,
   `dsdp_advantage_derived_leak_S` (2eps for the S-games, S cancels).
4. `dsdp_security_indcpa_fiber.v` (new): `predictor_guesser`,
   `guessing_challenger`, `guessing_experiment` on the derived S-game;
   `dsdp_guess_fdist`; the connector `Pr_guess_enc_zero_leak_S_eqE`
   (reflection, ~30–80 lines, one induction over the sample list).
5. fiber file: identities `dsdp_guess_V2_uniform`,
   `dsdp_guess_VarRV_indep_inputs`, `dsdp_guess_S_determined`,
   `dsdp_guess_indep_V2_given_S`; `Pr_guess_fiber_le_invm` (instantiate
   `dsdp_entropy` at `P`).
6. fiber file: `Pr_guess_enc_zero_leak_S_le_invm` (connector ∘ fiber);
   `dsdp_alice_secrecy_leak_S` (triangle: 1/m + 2eps).
7. Retire: delete `ref/dsdp_security_indcpa.v` +
   `ref/dsdp_security_indcpa_{concrete,pismc}.v`; drop from `_CoqProject`;
   green build.

## Risk points (would-be plan defects, watch for)

- Connector (task 4): if the opaque predictor's `dlet` does not factor through
  `P`'s sample tuple cleanly. Mitigation: predictor draws are extra coordinates
  of `P`; total-probability keeps it abstract.
- Fiber instantiation (task 5): constructing the fdist `P` from the SSProve
  game samples and discharging `dsdp_entropy`'s uniform/independence hypotheses.
  This is the research-grade step.

## Naming audit

After the code lands, one naming-audit agent over the cumulative `git diff` vs
MathComp/SSProve style; add a `(* reason *)` ONLY where a deviation is genuinely
necessary. New identifiers: `AO_recv_output`, `S_output_cell`, `id_s_get`,
`real_game_leak_S`, `zero_game_leak_S`, `dsdp_advantage_derived_leak_S`,
`predictor_guesser`, `guessing_challenger`, `guessing_experiment`,
`dsdp_guess_fdist`, `Pr_guess_enc_zero_leak_S_eqE`, `dsdp_guess_V2_uniform`,
`dsdp_guess_VarRV_indep_inputs`, `dsdp_guess_S_determined`,
`dsdp_guess_indep_V2_given_S`, `Pr_guess_fiber_le_invm`,
`Pr_guess_enc_zero_leak_S_le_invm`, `dsdp_alice_secrecy_leak_S`,
`obs_of_procs_dsdp_leak_S`.
