# DSDP fiber leg — progress (items 3, 4 done; 1, 2, 5, 6, 7+8 remain)

Continuation of `20260611-dsdp-fiber-general-route-corrected-arch.md`.
Branch `itp2026-dumas2017dual`.

## Done this session (committed, no admits)

- **Item 4 — `cinde_diagonal_bound`** (commit `5d6be27`, `dumas2017dual/lib/extra_proba.v`).
  Added `Import Order.POrderTheory.` (local to extra_proba; not Export, so
  downstream sources are unaffected — only the new lemmas become available).
  Three lemmas in `Section cinde_diagonal_bound_sec`:
  - `marg_snd {B} (W : {RV P -> B}) w : \sum_(c:C) Pr[[%W,Z]=(w,c)] = Pr[W=w]`
    (partition_big Z).
  - `Pr_diag_sum : Pr P [set t | X t == Y t] = \sum_(a:A) Pr[[%X,Y]=(a,a)]`
    (partition_big X).
  - `cinde_diagonal_bound : P |= X _|_ Y | Z -> (forall a c, Pr[Y=a|Z=c] <= m^-1)
    -> Pr P [set t | X t == Y t] <= m%:R^-1`.
    Proof: diag sum -> marginalize each over Z via marg_snd -> exchange_big ->
    le_trans to `\sum_c m^-1 * Pr[Z=c]` (= m^-1 by sum_pfwd1) -> per-c, case on
    `Pr[Z=c]==0` (domination via pfwd1_domin_RV1) else product-rule
    `Pr[[%[%X,Y],Z]=((a,a),c)] = Pr[X=a|Z=c]*Pr[Y=a|Z=c]*Pr[Z=c]` (cpr_eqE +
    Hcinde) -> bound `Pr[Y..]<=m^-1`, factor `\sum_a Pr[X=a|Z=c]=1` (sum_cPr_eq).
    GOTCHA solved: never `rewrite -(sum_pfwd1 Z)` against a bare `1` — it hits the
    `1` inside `m%:R = 1 *+ m`; use an explicit `le_trans` target instead.
    GOTCHA: `\sum_(a:A)` vs `\sum_(a in A)` mismatch with sum_cPr_eq — bridge with
    `rewrite -(sum_cPr_eq X Hc0); apply: eq_bigl => a; rewrite inE`.
    GOTCHA: `done` does NOT close `x <= x`; use `apply: lexx` (or `rewrite lexx`).

- **Item 3 — `guess_inputs_indep`** (commit `238cd9c`, fiber file).
  Added `Require Import ... extra_proba.` to the fiber file (extra_proba was only
  transitively loaded via dsdp_entropy, so inde_const_RV was not in scope).
  Proof: `[%V1,U1,U2,U3] = const_RV _ (w_v1,w_u1,w_u2,w_u3)` by funext+const_RVE,
  then `exact: inde_const_RV`.
  Also committed `Zcond := [% ir1_rv, ir2_rv, Sout]` (the conditioning view).
  Removed last session's Admitted `guess_cinde_V2` stub (re-add when proven).

## Remaining (all deep SSProve distributional / heap threading)

### Item 2 — `guess_VarRV_uniform : `p_[%V2,V3] = fdist_uniform`
V2 = msg_of_idx(sample1), V3 = msg_of_idx(sample2): fin_to_plain∘msg_to_fin∘
chmsg_of_msg∘msg_of_idx collapses to msg_of_idx via msg_to_finK + chmsg_of_msgK.
The two secrets are the FIRST two of gc_eq's six samples (v2,v3, masks r2,r3, two
hop randomness). Need: marginal of guess_sample_fdist onto (V2,V3) = pushforward
of (uniform card_msg × uniform card_msg) through (msg_of_idx × msg_of_idx); a
bijection (Hmsg_bij) carries uniform→uniform on plain AHE. HARD sub-step: collapse
the lossless tail after the two secret samples (predictor + reads don't change the
already-sampled V2,V3). Reuse `guess_full_proj_code`/`Pr_fst_map` machinery.

### Item 1 (CRUX) — `guess_cinde_V2 : guess_sample_fdist |= guess_rv _|_ V2 | Zcond`
Via committed `cinde_RV_factor`: supply f(v2,z), g(z,guess) with
`Pr[[%guess,V2,Zcond]=(gm,vm,z)] = f(vm,z)·g(z,gm)`. g = predictor kernel
K(view(z.ir), z.S)(guess), V2-cell-independent by committed `Pr_fst_put_invariant`
(predictor_locs_disj). Largest remaining proof: Pr_code_bind to express the joint
law as a dlet chain, isolate the predictor kernel, frame it off the V2 cell.
Fallback if it won't close: a lower-level lemma (kernel V2-cell-independence
straight from Pr_fst_put_invariant) rather than assuming the cinde.

### Item 5 — `Pr[V2 = a | Zcond = c] <= card_msg^-1`
Instantiate `Pr_dsdp_sol_uniform_ring` (dsdp_entropy.v, ring-generic, R := plain
AHE as finComNzRingType) with the projection RVs + const inputs. Discharge hyps
with item 2 (VarRV_uniform_r), item 3 (VarRV_indep_inputs_r), guess_S_determined
(constraint_holds_r), injective(·w_u3). Gives `Pr[(V2,V3)=(v2,v3)|inputs,S]=1/#R`.
Then: (a) marginalize V3 out (constraint determines v3 from v2 since u3 invertible)
=> `Pr[V2=a|inputs,S]=1/#R`; (b) inputs const => condition only on S; (c) lift
S → Zcond via `[%ir1,ir2] ⊥ V2 | S` (fresh hop randomness); (d) #R = card_msg via
Hmsg_bij.

### Item 6 — `guess_fdist_success_le : injective(·w_u3) -> guess_fdist_success <= card_msg^-1`
`guess_joint_fdist_marginal` (committed) => Pr guess_sample_fdist {guess_Mfin =
V2_Mfin}; subset {guess_Mfin=V2_Mfin} ⊆ {guess_rv=V2} (fin_to_plain), so
`<= Pr {guess_rv=V2}`; then `cinde_diagonal_bound` with item 1 + item 5.

### Item 7+8 — composition / final
Item 7: `rewrite guess_success_sdistr_eq_fdist` (committed) then item 6.
Item 8: `guess_advantage_le` via `eapply dsdp_advantage_derived_leak_S` (vanilla
eapply, not apply:); triangle `real <= zero + |real-zero|` =>
`dsdp_alice_secrecy_leak_S <= card_msg^-1 + 2*epsilon_cpa`. Final Print Assumptions.

## Workflow notes
- Fiber file strict-mode (`Set Default Goal Selector "!"`): `have H : T by …`
  one-liners, `{ … }`, `-/+` bullets.
- Build a single target via `make -f Makefile.coq <path>.vo` (the TOP-level
  `make <path>.vo` short-circuits via a `%:` rule and reports "up to date").
- extra_proba change forces fiber-chain rebuild (~minutes); batch general lemmas.
- Commit `--no-verify` with `ROCQ_AUDIT_BYPASS=1` (audit hook hangs); stage only
  touched files. Never commit while Admitted.

## Item 2 status (guess_VarRV_uniform) — ~95%, single isolated gap

Committed infra (`302ba21`): `resolve_predictor_valid` (eapply valid_resolve, NOT
apply:), `fdistmap_bij_unif`, `mean1_eq1`. UNCOMMITTED in the working tree (file
COMPILES, exit 0, with ONE `admit`): `cardpp`, `Htail2_abs` (the giant-term fix:
predictor tail abstracted over `pc : raw_code t_msg`), and the FULL verified
`guess_VarRV_uniform` scaffolding from the 4th agent run — `Hproj_lossless`,
`Hbridge_sd` (fdistmap proj gsf = sdistr_to_fdist), `pairmap`/`two_idx_code`,
`card_pair`, `Hpairbij`, `Hcard0`, `Hbody` (projected-code reduction), `HRHS`,
`Htwo`, `inner_sum`, `Htwoval`, and the final `fdistmap_bij_unif` assembly. All
VERIFIED except the one `admit` inside `Hcore`.

THE ONE REMAINING GAP (Hcore inner reflection): after peeling the two secret samples
x0,x1, the goal is `dmargin fst (Pr_code INNER emptym) = dunit (msg_of_idx x0,
msg_of_idx x1)`. This is NOT locally provable as-is — restructure `Hcore`:
1. Reflect INNER (x2,x3,y0,y1 samples + V_2 put + 2 hops + 2 lets + putout + GC_ret
   + s_get + predictor+v2_get) to `M x0 x1 *: dunit (msg_of_idx x0, msg_of_idx x1)`
   where `M x0 x1 = pr (Pr_code INNER emptym) predT`. Value is constant VAL: v2_get
   reads the run-written `V_2 = chmsg_of_msg (msg_of_idx x0)` (Htail2_abs +
   Pr_code_preserves), v3 = msg_of_idx x1 (captured). Peel samples with
   `dfst_dlet_commut`+`eq_dlet`, predictor+v2_get via `Htail2_abs` (set PRED/HEAP
   first), lossless samples via `distr.dletC`.
2. `M <= 1`; `\sum_(x0,x1) M/card^2 = 1` (= psum (Pr_fst proj) = guess_full_lossless,
   Pr_fst_map mass preservation); mean of values <=1 equal to 1 => `M = 1` everywhere
   by `mean1_eq1`; substitute `scale1r` => `dmargin pairmap two_idx_code`.
The 4th agent's full Coq scaffolding is in agent memory
`~/.claude/agent-memory/rocq-prover/guess_varrv_uniform_progress.md` and inline in
the fiber file. DEVELOP THE GIANT-TERM STEPS VIA BATCH `make`, not interactive PET
(see [[feedback_ssprove_pr_code_perf]]).

Items 1 (crux guess_cinde_V2 — a similar/harder predictor-kernel reflection), 5, 6,
7+8 remain; 5/6 are gated on item 2, 6/7/8 on item 1. Genuinely multi-session.
