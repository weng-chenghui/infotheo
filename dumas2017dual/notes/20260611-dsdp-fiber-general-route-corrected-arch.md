# DSDP fiber leg — corrected architecture (general / footprint route)

Supersedes the Task 10–12 design in `20260611-dsdp-fiber-bound-implementation-plan.md`.
Reason: the predictor is an **arbitrary SSProve package** (`predictor_guesser :=
package [interface] guesser_export`), hence possibly randomized, so `guess` is
**not** a deterministic function of `(view, S)`. `cinde_RV_comp` (deterministic
composition) does not apply. The lemma that does is `cinde_RV_factor`
(committed, `extra_proba.v`): `guess ⊥ V2 | Z` from a joint-law factorization
`Pr[guess,V2,Z] = f(V2,Z)·g(Z,guess)` with the guess-kernel `g` depending only
on `Z`.

Both crux lemmas are proven and committed:
- `cinde_RV_factor` (`extra_proba.v`, commit 9cf83be) — the math core
  (`/tmp/feas_layer1.v` was the feasibility proof).
- `Pr_fst_put_invariant` (fiber file, near `Pr_fst_agree_locs`) — the footprint
  bridge: the predictor's value-marginal is invariant under the V2-cell value
  (`/tmp/feas_layer2.v` was the feasibility proof).

## Conditioning variable

`Z := [% ir1, ir2, S]` where `ir1, ir2 : 'I_card_renc` are the two hop
encryption-randomness samples (they determine `view`, the all-zero cipher list)
and `S` is the leaked output. The protocol inputs `V1 U1 U2 U3` are **constants**
(seeded weights) → use `const_RV P (weight)` when instantiating the entropy
lemma; they need not be carrier coordinates (conditioning on a constant is
trivial, and the fiber given constants reduces to the fiber given `S`).

## Rich carrier and fdist (Task 10)

`guess_full_code : raw_code (Mfin*Mfin*Mfin*Mfin*'I_card_renc*'I_card_renc)`
returning `(guess, V2, V3, S, ir1, ir2)` (guess/V2/V3/S via `msg_to_fin ∘
chmsg_of_msg`; ir1,ir2 captured by a `denote_run_full` that also returns the hop
randomness). Then:
- `guess_full_lossless` hypothesis (mirrors `guess_lossless`).
- `guess_sample_fdist := sdistr_to_fdist guess_full_lossless`.
- Projection RVs `guess V2 V3 S : {RV _ -> plain AHE}` (via `fin_to_plain`),
  `ir1 ir2 : {RV _ -> 'I_card_renc}`; inputs as `const_RV`.
- `guess_S_determined : S = (fun t => dsdp_output v1 u1 u2 u3 (V2 t) (V3 t))`
  proved via `denote_output_termE` + `gc_eq` (NOT definitional — S is the
  physical projection; this is the meaningful constraint, avoiding the vacuity
  of the first agent attempt).
- `guess_joint_fdist = fdistmap (proj to (guess,V2)) guess_sample_fdist`
  (marginal link, so the connector's diagonal over `guess_joint_fdist` reduces
  to the rich fdist).

## The factorization (Task 11, crux)

`guess_sample_factor : Pr[ [% guess, V2, Z] = (m, v, z) ] = f(v,z)·g(z,m)`.
Derivation: the experiment binds (sample v2,v3,ir1,ir2; put v2; build view from
ir1,ir2; put S; read s; guess ← predictor(view,s); read v2; ret). Via
`Pr_code_bind` the joint law is a `dlet` chain; the predictor's contribution is
a kernel that, by `Pr_fst_put_invariant` (`predictor_locs_disj`), does not read
the V2 cell → `g(z,m)` independent of `v`. `view` is a function of `(ir1,ir2) ⊆
Z`, so `g` depends only on `Z`. (The agent already proved comparable bind
manipulations: `denote_run_full_fst`, `guess_full_marginal`.)

Then `guess_cinde_V2 : guess ⊥ V2 | Z := cinde_RV_factor guess_sample_factor`.

## Uniform side (Task 11/12)

- `guess_VarRV_uniform : `p_[%V2,V3] = fdist_uniform` (the two secrets are
  independent uniform samples; `Hmsg_bij : bijective msg_of_idx` makes them
  uniform on `plain AHE`).
- `guess_VarRV_indep_inputs : [%V1,U1,U2,U3] _|_ [%V2,V3]` — trivial (inputs
  const).
- `view_rand_cinde_V2 : [%ir1,ir2] ⊥ V2 | S` (hop randomness fresh, ⊥ V2) — to
  lift "V2 uniform | S" to "V2 uniform | Z".

## Fiber + diagonal (Task 12)

Instantiate `Pr_dsdp_sol_uniform_ring` at `R := plain AHE` with the projection
RVs + const inputs + `injective (·u3)` + `Hmsg_bij`, giving V2 uniform on the
fiber given S, hence given Z. Then
`Pr[guess=V2] = Σ_z Pr[Z=z]·Σ_m Pr[guess=m|Z=z]·Pr[V2=m|Z=z]
             = Σ_z Pr[Z=z]·(1/#|plain AHE|) = 1/#|plain AHE| = 1/card_msg`
(`Hmsg_bij`), via `guess_cinde_V2` + uniformity. Reduce to `guess_joint_fdist`'s
diagonal by the marginal link → `guess_fdist_success_le`.

## Composition (Tasks 13–15) — unchanged from the plan

`guess_sdistr_success_le` (connector `guess_success_sdistr_eq_fdist`),
`guess_advantage_le` (the 2·epsilon_cpa leg, `eapply
dsdp_advantage_derived_leak_S`), `dsdp_alice_secrecy_leak_S` (triangle).

## New identifiers (audited, mathcomp-style)

`cinde_RV_factor`, `marg_out_Y/X`, `marg_Z_X` (extra_proba, committed);
`Pr_fst_put_invariant` (fiber, committed); `guess_full_code`,
`guess_full_lossless`, `guess_sample_fdist`, `guess_sample_factor`,
`fin_to_plain`, `S_cell`, `guess_S_determined`, `guess_joint_fdist_marginal`,
`guess_VarRV_uniform`, `guess_VarRV_indep_inputs`, `guess_cinde_V2`,
`view_rand_cinde_V2`, `guess_fdist_success_le`, `guess_sdistr_success_le`,
`guess_advantage_le`, `dsdp_alice_secrecy_leak_S`.
