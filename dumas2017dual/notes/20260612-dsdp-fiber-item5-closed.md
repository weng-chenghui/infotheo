# DSDP fiber leg — item 5 CLOSED (Z := Sout); items 1, 6, 7+8 remain

Continuation of `20260612-dsdp-fiber-item2-done.md`. Branch
`itp2026-dumas2017dual`. Commits `9773ce8`, `babd795`, `d3a051c`.

## Architecture decision: Z := Sout (NOT Zcond = [%ir1,ir2,Sout])

The `cinde_diagonal_bound` conditioning variable is now **`Sout`**, not the
earlier `Zcond = [% ir1_rv, ir2_rv, Sout]`. Reason: the all-zero view's
let-combine `HE_emul (HE_epow (HE_var 1) (HE_var 7)) (HE_enc 1 (HE_var 3) 1)`
encrypts `HE_var 3 = sample 3 = mask r2` (a fresh `card_msg` sample, NOT a
secret — de Bruijn at the let: slot0=hop2cipher, 1=hop1cipher, 2..5 = the four
`card_msg` samples [v2,v3 at put_output indices 7,6; masks r2,r3], 6+ = seed
weights; so `HE_var 7` at the let is a seeded WEIGHT, `HE_var 3` is mask r2).
So the view depends on the masks r2,r3 (V2-independent) regardless of Z. Pinning
the hop randomness ir1,ir2 in Z therefore buys nothing for item 1's reflection
(it must marginalize V2-independent randomness either way). Z := Sout keeps
item 5 reflection-free. **No plan defect**: item 1's statement is TRUE (the
zero-game view is V2/V3-free given the run randomness; secrets live inside
ciphertexts = zeroed, weights live in exponents = public/seeded).

`Zcond`, `ir1_rv`, `ir2_rv` are now UNUSED — remove at cleanup (aggressive).

## Done this session (committed, Qed, no admits)

- **`guess_VarRV_cond_uniform`** (item 5a, `9773ce8`): the fiber-file instance of
  `Pr_dsdp_sol_uniform_ring` (R := plain AHE : finComNzRingType). Discharges
  constraint_holds_r (ring), VarRV_uniform_r (item 2 via `fdist_uniformE`
  proof-irrelevance bridge `fdist_uniform cardpp = fdist_uniform card_RR_pair`),
  VarRV_indep_inputs_r (guess_inputs_indep). Apply needs explicit implicits:
  `apply: (@Pr_dsdp_sol_uniform_ring _ (plain AHE) _ guess_sample_fdist V1 V2 V3 U1 U2 U3 Sout)`.
  Gives `Pr[(V2,V3)=(v2,v3) | [%V1,U1,U2,U3,Sout]=(...)] = 1/#|plain AHE|`.

- **`cpr_eq_drop_indep`** (general, `babd795`): a conditioning coordinate
  independent of the numerator pair drops out:
  `Pr[W=w]!=0 -> P |= W _|_ [%X,Y] -> Pr[X=a|[%W,Y]=(w,y)] = Pr[X=a|Y=y]`.
  Proof: `cpr_eqE`, `pfwd1_pairCA`, factor by `inde_RV` (W⊥[%X,Y]) + `inde_RV_comp idfun snd` (W⊥Y), cancel via `invfM mulrACA (mulfV Hw) mul1r`.
  GOTCHA: needs `proba_scope` open for `{RV _ -> _}` — so it lives INSIDE the
  section (after `Local Open Scope proba_scope`), not with the pre-section
  helpers. Candidate for upstream to extra_proba. Used twice: drop the const
  inputs (item 5) and (future) the hops lift.

- **`guess_V2_cond_Sout`** (`babd795`): `Pr[Sout=s]!=0 -> Pr[V2=a|Sout=s] = 1/#|plain AHE|`.
  Construct v3* = g(s - w_u1 w_v1 - w_u2 a) (g = inverse of (.w_u3), `inj_card_bij`),
  fiber membership, event equality `{V2=a,Sout=s}={[%V2,V3]=(a,v3*)}` (boolean,
  via `(Sout t==s)=(V3 t==v3star)` from `inj_eq (addrI _)`+`inj_eq Hinj`), drop
  the const inputs via `cpr_eq_drop_indep` (W:=[%V1,U1,U2,U3]; Pr[const=cval]=1
  via `Pr_setT`; const indep via `inde_const_RV`; Pr[cond]=Pr[Sout=s] via
  pfwd1E+setP), then `guess_VarRV_cond_uniform`.
  GOTCHA: `Set Implicit Arguments` made the lemma's `s` IMPLICIT (inferred from
  `Pr[Sout=s]!=0`); call as `guess_V2_cond_Sout a Hinj Hn0` (a explicit, s/Hinj/Hs).
  GOTCHA: the `@cpr_eq_drop_indep _ _ guess_sample_fdist _ _ _ X Y W a y w H1 H2`
  full-explicit form is needed (the value binders a,y got auto-renamed by A,Y
  type-name clash; positional/named both misfire).

- **`guess_V2_cond_le`** (item 5 CLOSED, `d3a051c`): `injective(.w_u3) ->
  forall a s, Pr[V2=a|Sout=s] <= card_msg^-1`. Card bridge `#|plain AHE|=card_msg`
  via `bij_eq_card Hmsg_bij` + `card_ord`. cPr=0 case: `cpr_eqE H0 invr0 mulr0
  invr_ge0 ler0n`. nonzero: `guess_V2_cond_Sout a Hinj Hn0` + Hcard + lexx.
  **This is exactly the 2nd hypothesis of `cinde_diagonal_bound` (Y:=V2, Z:=Sout,
  m:=card_msg).**

## Done this session (continued) — items 6, 7 given Hcinde

The cinde `guess_rv _|_ V2 | Sout` (item 1) is threaded as an EXPLICIT hypothesis
`Hcinde` through items 6, 7 (and will be through item 8). These are committable
real lemmas (no admit) that isolate item 1 to the single obligation "discharge
Hcinde". When item 1 lands, inline `guess_cinde_V2` for `Hcinde`.

- **`Pr_fdistmap_pre`** (general, `f7aee67`): `Pr (fdistmap g p) E = Pr p (g@^-1 E)`,
  via `partition_big g (mem E)` + `fdistmapE` + `andb_idl`.
- **`guess_fdist_success_le`** (item 6, `f7aee67`): `Hcinde -> injective(.w_u3) ->
  guess_fdist_success <= card_msg^-1`. `le_trans` to `cinde_diagonal_bound Hcinde
  (fun a c => @guess_V2_cond_le a c Hinj)`, then `guess_joint_fdist_marginal` +
  `Pr_fdistmap_pre` + `subset_Pr` (diagonal {Mfin coords eq} ⊆ {guess_rv = V2}).
- **`guess_sdistr_success_le`** (item 7, `cfe91a4`): `Hcinde -> injective ->
  guess_sdistr_success <= card_msg^-1`. `rewrite guess_success_sdistr_eq_fdist;
  exact: guess_fdist_success_le`.

Full `coqc` of the fiber file: exit 0 (gold-standard verified, .vo rebuilt).

### Name audit (instruction #2)
This session's identifiers are MathComp-clean snake_case
(`guess_VarRV_cond_uniform`, `cpr_eq_drop_indep`, `guess_V2_cond_Sout`,
`guess_V2_cond_le`, `Pr_fdistmap_pre`, `guess_fdist_success_le`,
`guess_sdistr_success_le`). Minor: `Pr_fdistmap_pre` `pre` could be `preim`.
PRIOR-session item-2 names still flagged for a dedicated rename pass (touching
committed item-2 code, deferred): `cardpp` -> `card_plain_pair`, `Htail2_abs`
(`_abs` strips meaning + H-prefix on a top-level lemma) -> a `Pr_code_*` name.

## Remaining

### Item 1 (CRUX) — `guess_cinde_V2 : guess_sample_fdist |= guess_rv _|_ V2 | Sout`
THE remaining reflection. Confirmed TRUE; the entry point and decomposition are
pinned down below. ~item-2 scale or harder (item 2 took 1h+; this is harder
because the predictor coordinate is KEPT, not discarded).

ENTRY (verified in session): `apply: cinde_RV_factor` reduces to
`forall x y z, pfwd1 [%guess_rv,V2,Sout] (x,y,z) = ?f y z * ?g z x`. With the
"obvious" f:=`pfwd1 [%V2,Sout]`, g:=`Pr[guess_rv=·|Sout=·]` the goal becomes
`pfwd1 [%guess_rv,V2,Sout](x,y,z) = pfwd1 [%V2,Sout](y,z) * Pr[guess_rv=x|Sout=z]`
which is circular (= the cinde via chain rule). MUST use CODE-DERIVED f,g: f =
the secret-sampling mass for (V2=y, Sout=z); g = the predictor-kernel mass for
guess=x given view-from-fresh-randomness and S=z. The factorization then holds
because in `guess_full_code` the secret samples and the view/predictor samples are
DISTINCT, independent draws (the product law), and the predictor reads the secrets
only through s=output(V2,V3).

WHY item 2's machinery doesn't transfer directly: item 2's `Hbody` (fiber file
~line 1016) reflects `gv ← guess_full_code ;; ret (proj gv)` but DISCARDS guess
and s (they don't appear in its `ret`), so they collapse by losslessness. Item 1
KEEPS the guess coordinate, so it cannot collapse the predictor.

DECOMPOSITION (the plan):
1. 3-coord reflection (adapt `Hbody`/`guess_full_proj_code`): reflect
   `gv ← guess_full_code ;; ret (gv.1.1.1.1.1, gv.1.1.1.1.2, gv.1.1.1.2)` (= the
   (guess_M, V2_M, V3_M) coords) to `vt ← denote_run_caps 11 8 9 10 7 6 [::] seed gc
   ;; s ← denote_s_get_body ;; guess ← resolve (pack predictor) … (vt.1.1, s) ;;
   v2 ← denote_v2_get_body ;; ret (msg_to_fin guess, msg_to_fin v2, vt.1.2.1.2)`.
   [%guess_rv,V2,Sout] is a function of these 3 coords (Sout = output `o [%V2,V3]).
2. KEY sub-lemma `view_indep_secrets`: the run's view (vt.1.1, the cipher list) is
   a function of the V2/V3-INDEPENDENT randomness only (hop randomness, masks
   r2,r3 = samples 3,4, encryption randomness, seed weights), NOT of the secret
   samples v2,v3 (= samples 1,2). Decisive de Bruijn fact (already traced): the
   GC_ret outputs `[:: HE_var 1; HE_var 0; HE_var 3; HE_var 2]` = the two let-
   combines + two hop ciphers; the combines are `(hopcipher=enc 0)^seedweight *
   HE_enc(mask)`, referencing masks/seed/hop-rand, never v2,v3. Reflect
   `denote_run_caps` peeling the 4 GC_sample card_msg with `drc_sample_msg`,
   showing the view component is constant in the first two (v2,v3) sample binders.
   This is the load-bearing run reflection (the new hard work).
3. Predictor kernel V2-independence: `guess` given (view, s) is
   `Pr_fst (resolve (pack predictor) … (view, s))`, invariant under the V2 cell
   (committed `Pr_fst_put_invariant`/`Pr_fst_agree_locs` + `predictor_locs_disj`;
   `resolve_predictor_valid` gives the ValidCode). So the kernel depends on
   (view, s), and via (2) view ⊥ secrets, so the guess law depends on the secrets
   only through s.
4. s_read = output: the S cell content read by `denote_s_get_body` is
   `chmsg_of_msg (dsdp_output …)` = the Sout value (committed `denote_output_termE`
   + the run's `GC_put_output`). So conditioning on Sout fixes the predictor's s
   input.
5. Assemble the product law (Pr_code_bind / dlet factoring of the independent
   secret-sample and view+predictor pieces) into the f·g factorization; supply to
   `cinde_RV_factor`.

Once proven, INLINE `guess_cinde_V2` for the `Hcinde` hypothesis in
`guess_fdist_success_le` / `guess_sdistr_success_le` (move it before item 6, drop
the `Hcinde` binder).

Items 6, 7 DONE (given Hcinde) — see "Done this session (continued)" above.

### Item 8 — real-vs-zero composition + final theorem (SUBSTANTIAL SSProve)
The current `Section dsdp_guess_distribution` fixes `Let game := zero_game_leak_S
…`, so `guess_sdistr_success` is the ZERO-game success. The final theorem needs the
REAL-game success. Plan (a NEW section, or generalize the section over `game` /
parameterize the real and zero instantiations):
1. `guess_sdistr_success_real := distr.mu (pkg_advantage.Pr (guessing_experiment
   predictor (real_game_leak_S …))) true` (parallel to `guess_sdistr_success`).
2. `guess_advantage_eq`: `\`| guess_sdistr_success_real - guess_sdistr_success_zero |
   = AdvantageE (real_game_leak_S …) (zero_game_leak_S …) (guessing_challenger ∘ predictor)`.
   Re-associate `guessing_experiment predictor game = (guessing_challenger ∘ predictor)
   ∘ game` (committed `guess_resolved_par`/link lemmas), unfold `AdvantageE`/`pkg_advantage.Pr`.
3. `guess_advantage_le`: package `guessing_challenger ∘ predictor` as a
   `dsdp_indcpa_adversary` (ValidPackage on `game_iface_leak_S` → `A_export`;
   `A_disj_state`/`A_disj_ore`/`A_disj_oze` from `predictor_locs_disj` + challenger
   locs); then vanilla `eapply dsdp_advantage_derived_leak_S` (NOT `apply:`,
   feedback_ssprove_apply_vs_eapply) => `<= 2*epsilon_cpa`.
4. Final `dsdp_alice_secrecy_leak_S (Hcinde) (Hinj : injective(.w_u3)) :
   guess_sdistr_success_real <= card_msg^-1 + 2*epsilon_cpa`. Triangle
   `real <= zero + |real-zero|`, then `guess_sdistr_success_le` (item 7) +
   `guess_advantage_le`. Inline item 1 for Hcinde once proven; final `Print Assumptions`
   (expect only epsilon_cpa/enc_ind_cpa_real_or_zero/guess_lossless + std axioms +
   the pre-existing realsum interchange_psum).

## Owed (deferred, lower priority)
- rocq:golf on guess_VarRV_uniform (item 2).
- MathComp name audit of committed item-2 ids (cardpp, Htail2_abs, mass_dlet,
  dlet_const_unit, dmargin_fst_const). Htail2_abs (`_abs` strips meaning, H-prefix
  on a top-level lemma) and cardpp (cryptic) are the flagged ones.

## Workflow notes (this session)
- Light-preamble session for general lemmas needs `From mathcomp Require Import reals.`
  for `realType` and `FDist.t Rr U` (not `Rr.-fdist U`; `.-fdist` needs fdist_scope).
- `congr (Pr _ _)` shelves a goal under the strict selector; `Unshelve.` refocuses;
  benign for Qed.
- rocq_start can serve a STALE cached prefix; `force_restart:true` after edits.
- A lemma before the section that uses `{RV}` silently FAILS (proba_scope closed)
  and the MCP SKIPS it (then "not found" downstream); put RV-using helpers in-section.
