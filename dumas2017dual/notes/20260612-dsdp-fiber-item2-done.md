# DSDP fiber leg — item 2 (guess_VarRV_uniform) CLOSED; items 1, 5, 6, 7+8 remain

Continuation of `20260611-dsdp-fiber-progress-items3-4-done.md`.
Branch `itp2026-dumas2017dual`. Commit `c8ce728`.

## Done this session (committed, Qed, no new axioms)

**Item 2 — `guess_VarRV_uniform : \`p_[%V2,V3] = fdist_uniform cardpp`** (commit
`c8ce728`, fiber file). The single isolated admit that defeated 4 agent runs +
the prior session is closed. Axiom footprint = standard classical axioms +
`realsum.__admitted__interchange_psum`, the latter PRE-EXISTING in the chain
(`Pr_fst_map`, `guess_success_sdistr_eq_fdist` already pull it via SSProve's
nominal-Pr layer / mathcomp-analysis admitted Tonelli). No NEW axioms introduced.

### The Hcore reflection (what closed the admit)
After peeling the two secret samples x0,x1, the goal is
`dmargin fst (Pr_code INNER emptym) = dunit (msg_of_idx x0, msg_of_idx x1)`.
Two new local distr helpers (placed near `eq_in_dlet`):
- `dlet_const_unit : psum(mu D)=1 -> dlet (fun=>dunit v) D = dunit v` (via
  `distr.dletC` + `distr.pr_predT`).
- `dmargin_fst_const : (forall p ∈ supp D, p.1 = v) -> dmargin fst D
  = dlet (fun=>dunit v) D` (via `eq_in_dlet`).
Then split into (I) constant-value and (II) mass:

(I) **const value** — every support point of `Pr_code INNER emptym` has value
`(msg_of_idx x0, msg_of_idx x1)`.  `Pr_code_bind` + `distr.dinsupp_dlet` exposes
a run point `y`; `Hrun` (run-support, proved by peeling the run with `drc_*`
lemmas + `dinsupp_dlet`/`Pr_code_put`, then `distr.in_dunit` at GC_ret) gives the
captured v3 = msg_of_idx x1 and heap V_2 = Some (chmsg_of_msg (msg_of_idx x0));
the s_get/predictor/v2_get tail collapses via `Htail2_abs` (apply: in a
transitivity, NOT rewrite — rewrite hits "type classes inference fails").

(II) **mass = 1** — the predictor mass averages to 1, so equals 1 on full support.
- `mass_dlet` (FINITE U): `psum(mu(dlet f mu0)) = psum(fun x => psum(mu(f x)) *
  mu mu0 x)` proved via `distr.dletE` + `psum_fin` + `psum_bigop` (the proven
  finite-sum/psum swap) — NOT `distr.pr_dlet`, which is deprecated and relies on
  the admitted interchange.
- `HbodyEq : (x ← two_idx_code ;; INNERf x.1 x.2) = (gv ← guess_full_code ;;
  ret (proj gv))`.  Reassociate `bind (sampler ...) k` (NOT `bind (bind ...) k`,
  so `bind_assoc` does not apply) with a one-line `sba` helper (refl) + peel each
  secret with `drc_sample_msg` AFTER introducing the prior sample var via
  `f_equal; boolp.funext` (drc's run env depends on the bound var, so ssr cannot
  instantiate it under the binder otherwise).  `cbn [bind]` is FORBIDDEN: it
  unfolds bind to `bindrFree` and breaks `bind_cong`/`bind_assoc`.
- `HmeanD`: `under eq_psum do rewrite -Hpd` (value-marginal mass = code mass),
  `-mass_dlet`, then `Pr_fst_bind` with the `ValidCode emptym two_idx_code`
  (`ssprove_valid`) supplied EXPLICITLY (rewrite alone fails typeclass inference),
  then `HbodyEq` and `Hproj_lossless`.
- `mean1_eq1` (committed helper) with D = `Pr_fst two_idx_code`, bounds from
  `ge0_psum`/`distr.le1_mu`; membership `p ∈ dinsupp (Pr_fst two_idx_code)` via
  `Pr_fst_sample` + `distr.dlet_dinsupp`, the uniform-support fact
  `x ∈ dinsupp (projT2 (uniform card_msg))` = `mu = UniformDistrLemmas.r =
  1/#|·| ≠ 0` (`distr.in_dinsupp`+`distr.mkdistrE`+`card_ord`+`invr_eq0`+
  `pnatr_eq0`+`-lt0n`+Hcard0), and the dunit diagonal at GC_ret.

### Reusable gotchas (now memory-worthy)
- giant `game_code` terms: closing-paren count differs by 1 between a
  `Pr_code (denote_run_caps …) emptym` wrapper and a bare `vt ← denote_run_caps …`.
- `Htail2_abs` / `Pr_fst_bind`: supply hyps as explicit args, never bare rewrite.
- finite bind-mass via `psum_bigop`, never `pr_dlet` (admitted).

## Remaining (undrafted — the section ends after guess_VarRV_uniform)

### Item 5 — `Pr[V2 = a | Zcond = c] <= card_msg^-1`  (UNBLOCKED by item 2)
Instantiate `Pr_dsdp_sol_uniform_ring` (dsdp_entropy.v, ring-generic, R := plain
AHE as finComNzRingType) with the projection RVs + const inputs.  Discharge hyps:
guess_VarRV_uniform (VarRV uniform), guess_inputs_indep (inputs ⊥ secrets),
guess_S_determined (constraint), injective(·w_u3).  Gives
`Pr[(V2,V3)=(v2,v3)|inputs,S]=1/#R`.  Then (a) marginalize V3 (u3 invertible
=> v3 determined by v2) => `Pr[V2=a|inputs,S]=1/#R`; (b) inputs const => condition
only on S; (c) lift S → Zcond via `[%ir1,ir2] ⊥ V2 | S`; (d) #R = card_msg (Hmsg_bij).

### Item 1 (CRUX) — `guess_cinde_V2 : guess_sample_fdist |= guess_rv _|_ V2 | Zcond`
Via committed `cinde_RV_factor`; predictor kernel K(view(z.ir), z.S)(guess),
V2-cell-independent by `Pr_fst_put_invariant` (predictor_locs_disj).  A
similar/harder predictor-kernel reflection to item 2.  Fallback: a lower-level
kernel V2-cell-independence lemma instead of the full cinde.

### Item 6 — `guess_fdist_success_le : injective(·w_u3) -> guess_fdist_success <= card_msg^-1`
`guess_joint_fdist_marginal` (committed) => subset {guess_Mfin=V2_Mfin} ⊆
{guess_rv=V2}; then `cinde_diagonal_bound` (item 4, committed) with item 1 + item 5.

### Item 7+8 — composition / final
Item 7: `rewrite guess_success_sdistr_eq_fdist` then item 6.
Item 8: `guess_advantage_le` via vanilla `eapply dsdp_advantage_derived_leak_S`;
triangle => `dsdp_alice_secrecy_leak_S <= card_msg^-1 + 2*epsilon_cpa`.  Final
`Print Assumptions`.
