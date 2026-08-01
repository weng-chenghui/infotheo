# smc/security_models Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. Rocq proving inside a task is delegated to the rocq-prover agent per the repo's merged-flow playbook.

**Goal:** Land the audited smc/security_models formalization: FinStoch toolkit, statistical distance with max-advantage, the privacy kernel and party structure, the B+ rev-2 entropy characterization (iff under H0/H1/H2), T-relative unpredictability, the 'F_3 examples, and the SPP bridge.

**Architecture:** Two-layer design per the spec (`smc/notes/20260731-security-models-formalization-design.md`): an abstract privacy kernel carried by `R.-fdist` over finTypes, an n-party dffun layer instantiating it; every permanent statement is copied verbatim from a compiled probe in `smc/security_models/.scratch/` (paths cited per task) or drafted here and probed first.

**Tech Stack:** Rocq + MathComp 2 + local infotheo fork; build `coqc -R . infotheo` with `/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc`; project `make` for rebuild closures.

**Standing rules (apply to every task):**
- Compile check: `/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo <file>` from repo root, exit 0.
- Axiom check: `Print Assumptions` on each new named lemma — nothing beyond the boolp trio (`propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description`).
- Statement comments: every Definition/Lemma/Theorem in a permanent file carries a terse mathematical comment (chapter-label cross-reference where one exists). Probe files stay comment-light and are never edited by these tasks.
- Names: snake_case; the naming-audit resolutions of spec §4 are binding (`dist_of_RV_bind`, `perfect_privacy_centropyP`, Module namespacing for instance families, `Naming:` notes on `statdist_test_le`/`statdist_test_max`, `*_testP`, `stoch_comp_dirac_fdistmap`).
- Commits: one task = one commit, through the audit gate WITHOUT bypass (these are permanent files). Golf happens in the two sweep tasks (R12), bodies only.
- `_CoqProject`: each new file is added in the same task that creates it, in dependency order (security_models block after `probability/`+`information_theory/`; `spp_bridge.v` after the `du2002/` block).

---

### Task R1: Upstream the probability-layer lemmas into `probability/proba.v`

**Files:**
- Modify: `probability/proba.v` (append near `fdist_proj13_RV3`, line ~955, and near `cinde_RV`, line ~2302)
- Modify: `dumas2017dual/lib/extra_proba.v` (delete the moved lemmas)

- [ ] **Step 1: Move, verbatim,** `fdist_proj23_RV3` (`extra_proba.v:239`), `marg_out_Y`/`marg_out_X`/`marg_Z_X` (`extra_proba.v:494/516` block), `cinde_RV_factor` (`extra_proba.v:529`) into `proba.v`; add `pfwd1_pair_det` verbatim from `smc/security_models/.scratch/probe_entropy_link_mini.v:69-80`. Add statement comments.
- [ ] **Step 2: Add the NEW CI-recoding lemma** (audit F3; conditioner-nesting bridge), statement:

```coq
(* Conditional independence is invariant under an injective recoding of the
   conditioning random variable. *)
Lemma cinde_RV_recode (U : finType) (P : R.-fdist U)
    (A B C C' : finType) (X : {RV P -> A}) (Y : {RV P -> B})
    (Z : {RV P -> C}) (phi : C -> C') :
  injective phi ->
  P |= X _|_ Y | Z -> P |= X _|_ Y | (phi \o Z).
```

Proof route: unfold `cinde_RV`; on `c'` in the image of `phi` the conditioning events coincide; off the image both sides vanish by `pfwd1_domin_RV1`-style dominance. If the route needs the converse direction too, add it as `cinde_RV_recodeW` with the same hypothesis set and record the addition in the spec sync (Task R13).
- [ ] **Step 3: Delete the moved lemmas from `extra_proba.v`**, keep everything else; re-point its internal uses.
- [ ] **Step 4: Rebuild the closure**: `make -j8` (proba.v is upstream of most of the tree; expect a long rebuild, exit 0).
- [ ] **Step 5: Axiom check** on the six moved/new lemmas.
- [ ] **Step 6: Commit** `git commit -m "proba: upstream the CI factorization toolkit from the dsdp case-study lib"`.

### Task R2: Upstream the entropy-layer lemmas and the log lemma

**Files:**
- Modify: `information_theory/entropy.v` (after the `cond_mutual_info` section, ~line 1086; add `Require Import graphoid` — legal, graphoid precedes entropy in `_CoqProject`)
- Modify: `lib/realType_ln.v` (append `logr_eq1`)
- Modify: `dumas2017dual/lib/extra_entropy.v`, `dumas2017dual/lib/extra_algebra.v` (delete moved lemmas; extra_entropy.v had ZERO outside clients — naming audit F12)

- [ ] **Step 1:** Move `cinde_cond_mutual_info0` (`extra_entropy.v:73`) and `cinde_centropy_eq` (`extra_entropy.v:126`) into `entropy.v`; move `logr_eq1` (`extra_algebra.v:37`) into `realType_ln.v`. Statement comments.
- [ ] **Step 2:** Rebuild closure (`make -j8`), axiom check, gate commit `"entropy, realType_ln: upstream the CI-to-centropy link and logr_eq1"`.

### Task R3: `smc/security_models/finstoch.v`

**Files:**
- Create: `smc/security_models/finstoch.v`
- Modify: `_CoqProject` (add after the `information_theory/` block)
- Source (verbatim): `.scratch/probe_finstoch_kernel.v`, `Section stoch` — `stoch`, `dirac`, `stoch_comp`, `stoch_compA`, `stoch_comp_idl`, `stoch_comp_idr`, `dirac_comp`, `stoch_comp_dirac_fdistmap`, `eq_fdistmap`, `fdistmap_cst`, `fdistmap_cst_eq`, `tensor_fdist1`, `tensor`, `tensorE`.

- [ ] **Step 1:** Create the file: probe code verbatim; add the file header table, statement comments (chapter labels: def:smc:stochastic-map, def:smc:dirac, def:smc:finstoch, prop:smc:finstoch-laws, prop:smc:transport-commutes, def:smc:tensor), the `Naming:` note on `stoch_comp_dirac_fdistmap` (spec §4 table), and a comment on `dirac` warning about mathcomp-analysis measure-theory `dirac` (no collision in this import closure).
- [ ] **Step 2:** Compile, axiom check.
- [ ] **Step 3:** Gate commit `"security models: finstoch toolkit (stochastic maps, dirac, tensor)"`.

### Task R4: `smc/security_models/statdist.v`

**Files:**
- Create: `smc/security_models/statdist.v`; Modify: `_CoqProject`
- Source (verbatim): `.scratch/probe_statdist_maxadv.v` — all 12 lemmas + 4 local helpers.

- [ ] **Step 1:** Create with these DELTAS from the probe (each recorded in the spec):
  - `Variable B : finType` (explicit; NOT the probe's `Context {B}` — naming-audit F13, the one verbatim-copy deviation).
  - `Require Import variation_dist.` and add, right after the `statdist` definition:

```coq
(* statdist is half of variation_dist's total-variation sum. *)
Lemma statdist_var_dist p q : statdist p q = 2%:R^-1 * var_dist p q.
Proof. by []. Qed.
```

  and derive `statdist_sym` from `symmetric_var_dist`, `statdist_ge0` from `pos_var_dist` where the rewrite is one line (else keep the probe proofs).
  - Add the two headline supports (audit F5/F6 of the naming audit; consumed by privacy_kernel):

```coq
(* The advantage of a fixed tester is nonnegative. *)
Lemma adv_ge0 (D : tester) p q : 0 <= adv D p q.
Proof. exact: normr_ge0. Qed.

(* The advantage of a fixed tester satisfies the triangle inequality. *)
Lemma adv_triangle (D : tester) p q r : adv D p q <= adv D p r + adv D r q.
Proof. exact: ler_distD. Qed.
```

  - `Naming:` note covering the `statdist_test_le`/`statdist_test_max` pair and `_testP` style (spec §4 table).
- [ ] **Step 2:** Compile, axiom check, gate commit `"security models: statistical distance, testers, max-advantage, class advantage"`.

### Task R5: `smc/security_models/privacy_kernel.v`

**Files:**
- Create: `smc/security_models/privacy_kernel.v`; Modify: `_CoqProject`
- Source (verbatim): `.scratch/probe_finstoch_kernel.v` `Section kernel` (draw, view_law, view_lawE, f_a, allow, allowE, simulator, sim_view, perfect_privacy, insecurity, real_route_f, ideal_route_f) and `.scratch/probe_kernel_decomposition.v` headlines (perfect_privacy_testP, eps_privacy_testP, hybrid_bound) with the section Hypotheses REPLACED by the Task-R4 lemmas — shape agreement compiled in `.scratch/audit_nam_cross_section.v` Check B.

- [ ] **Step 1:** Create the file; add the missing second ideal route (soundness-audit F8 of the first audit round):

```coq
(* eq:smc:ideal-route-f, first equality: the input-projection route through
   the pair space also computes the function. *)
Lemma ideal_route_projx_f (x : X) :
  fdistmap (fun xy : X * Yfull => f xy.1) (tensor (fdist1 x) (F x))
  = fdist1 (f x).
Proof. (* tensor_fdist1 + fdistmap_comp, as in real_route_f *) Qed.
```

  Rename the probe's vacuity section into `Module identity_protocol` with unprefixed members (naming-audit F5): `Module identity_protocol. ... End identity_protocol.` carrying `F_compat`, `run_correct`, `perfect_privacy_holds`.
  `eps_privacy_testP` keeps its `0 <= eps` side condition (IT-audit-adjacent soundness F5 of round 1; spec §3 row).
- [ ] **Step 2:** Compile, axiom check, gate commit `"security models: privacy kernel (triangle, insecurity, test characterizations, hybrid bound)"`.

### Task R6: `smc/security_models/party_structure.v`

**Files:**
- Create: `smc/security_models/party_structure.v`; Modify: `_CoqProject`
- Source (verbatim): `.scratch/probe_party_dffun.v` — the `Section party` content and the concrete section.

- [ ] **Step 1:** Create with DELTAS:
  - Drop the probe's local `kernel_data` record mirror. Instead `Require Import privacy_kernel` and demonstrate the instantiation by section application (construction choice locked HERE: the kernel stays a Section, no record; reason: the record added nothing but an elaboration check, and section application is the mathcomp idiom):

```coq
(* The n-party observation diagram instantiates the privacy kernel:
   the kernel's view law at the party data. *)
Definition party_view_law (x : x_all) : R.-fdist view_space :=
  privacy_kernel.view_law P_Omega (view (A:=A)) x.
```

  (exact argument plumbing fixed by `Check @privacy_kernel.view_law` at implementation time; the discharged signature technique is recorded in the probe P1 report).
  - Concrete section becomes `Module three_party_identity` with unprefixed members (rename `c_*` — naming-audit F5).
- [ ] **Step 2:** Compile, axiom check, gate commit `"security models: n-party observation diagram and its kernel instantiation"`.

### Task R7: Probe, then land `smc/security_models/entropy_link.v` (B+ rev 2)

**Files:**
- Create: `.scratch/probe_entropy_iff.v` (probe FIRST; kept, comment-light, compiled zero-Admitted)
- Create: `smc/security_models/entropy_link.v`; Modify: `_CoqProject`
- Source: `.scratch/probe_entropy_link_mini.v` (pfwd1_view_input route, triangle_cinde via `cinde_RV_factor`), upstreamed lemmas of R1/R2, spec §3 of the thesis-side B+ spec (H0/H1/H2, full-support mu).

- [ ] **Step 1: Write the probe** `probe_entropy_iff.v` with the section context and the four target statements below; delegate to rocq-prover until zero Admitted; mutation-check the H0 and full-support hypotheses (drop each; expect failure or exhibit the audit counterexamples as the refutation reference):

```coq
Section entropy_iff_probe.
Context {R : realType}.
Variables X Yfull Y Xa Ya Xh Yh Bv Omega : finType.
Variables (proj_xa : X -> Xa) (proj_xh : X -> Xh).
Variables (proj_ya : Yfull -> Ya) (proj_yh : Yfull -> Yh).
Variables (f : X -> Y) (agg : Yfull -> Y).
Variable F : X -> R.-fdist Yfull.
Variable P_Omega : R.-fdist Omega.
Variables (view_at : X * Omega -> Bv) (run : X * Omega -> Yfull).
Variable out_adv : Bv -> Ya.
Hypothesis readoff : forall e, out_adv (view_at e) = proj_ya (run e).
Variable mu : R.-fdist X.
Hypothesis mu_full : forall x, mu x != 0.
Let d : R.-fdist (X * Omega)%type := (mu `x P_Omega)%fdist.
Let view_rv : {RV d -> Bv} := view_at.
Let input_rv : {RV d -> X} := fst.
Let ya_rv : {RV d -> Ya} := fun e => proj_ya (run e).
Let yh_rv : {RV d -> Yh} := fun e => proj_yh (run e).
Let xa_rv : {RV d -> Xa} := proj_xa \o fst.
Let xh_rv : {RV d -> Xh} := proj_xh \o fst.

(* H0: per-input delivery-law correctness. *)
Definition delivery_law_ok :=
  forall x, fdistmap (fun w => run (x, w)) P_Omega = F x.
(* H1 support-restricted consistency + triangle, kernel-shaped. *)
Definition consistent (Sim : Xa * Ya -> R.-fdist Bv) :=
  forall a y, `Pr[ [% xa_rv, ya_rv] = (a, y) ] != 0 ->
  fdistmap out_adv (Sim (a, y)) = fdist1 y.
Definition triangle (Sim : Xa * Ya -> R.-fdist Bv) :=
  forall x, fdistmap (fun w => view_at (x, w)) P_Omega
            = (fdistmap (fun yl => (proj_xa x, proj_ya yl)) (F x)) >>= Sim.
(* H2, zero-mass-robust product form (audit F5). *)
Definition output_independent :=
  d |= view_rv _|_ yh_rv | [% input_rv, ya_rv].

(* Target 1 (C3): the mixture-conditioning selection lemma. *)
Lemma triangle_cond_component Sim :
  delivery_law_ok -> consistent Sim -> triangle Sim ->
  forall x y, `Pr[ [% input_rv, ya_rv] = (x, y) ] != 0 ->
  forall v, `Pr[ view_rv = v | [% input_rv, ya_rv] = (x, y) ]
            = Sim (proj_xa x, y) v.
(* Target 2 (C4 forward): H1 + H2 => the pair CI. *)
Lemma triangle_cinde_pair Sim :
  consistent Sim -> triangle Sim -> output_independent ->
  d |= view_rv _|_ [% xh_rv, yh_rv] | [% xa_rv, ya_rv].
(* Target 3 (C4b converse): under H0 + full support. *)
Lemma centropy_to_sim :
  delivery_law_ok ->
  `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
    = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ) ->
  exists Sim, [/\ consistent Sim, triangle Sim & output_independent].
(* Target 4: the iff packaging. *)
Lemma perfect_privacy_centropy_iff :
  delivery_law_ok ->
  ((exists Sim, [/\ consistent Sim, triangle Sim & output_independent])
   <-> `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
       = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] )).
End entropy_iff_probe.
```

Spelling adjustments the prover needs (scopes, `{RV}` coercions, conditioner recoding via `cinde_RV_recode`) are ALLOWED and each is recorded as a probe finding for Task R13.
- [ ] **Step 2:** Commit the probe (bypass, scratch-evidence rationale) `"security models: probe the entropy-characterization iff (H0/H1/H2)"`.
- [ ] **Step 3: Land `entropy_link.v`**: probe code verbatim; headline names per spec — `perfect_privacy_centropyP` (Target 4), `perfect_privacy_centropy_eq` (Target 2 + `cinde_centropy_eq` application), `triangle_centropy_eq` intermediate; corollaries:

```coq
(* Real-deterministic delivery discharges the output-independence condition. *)
Lemma output_independent_det (g : X -> Yh) :
  (forall e : X * Omega, proj_yh (run e) = g e.1) -> output_independent.
(* Output-determined delivery discharges the condition. *)
Lemma output_independent_determined (g : X -> Ya -> Yh) :
  (forall e : X * Omega, proj_yh (run e) = g e.1 (proj_ya (run e))) ->
  output_independent.
```

- [ ] **Step 4:** Compile, axiom check, gate commit `"security models: entropy characterization (iff under delivery-law, consistency, output independence)"`.

### Task R8: Probe, then land `smc/security_models/unpredictability.v`

**Files:**
- Create: `.scratch/probe_unp_composition.v`, then `smc/security_models/unpredictability.v`; Modify: `_CoqProject`

- [ ] **Step 1: Probe** the composition shape with the hypotheses the spec (§3 unpredictability + IT-audit F10 of the B+ spec) fixed: secret map `sec : X -> Sec`; `predictor := {ffun Bv -> Sec}`; per-predictor success under the joint prior; induced testers `[ffun b => pred_map b == s]` for each `s`, hypothesis that they lie in `T` for both compared laws; conclusion chain:

```coq
Definition pred_success (pi : predictor) : R :=
  Pr d [set e | pi (view_at e) == sec e.1].
Lemma pred_success_le (pi : predictor) (T : {set tester Bv})
    (e_total p_ideal : R) :
  (forall s, [ffun b => pi b == s] \in T) ->
  (forall x, class_adv T (view_law x) (sim_view Sim x) <= e_total) ->
  ideal_guess <= p_ideal ->
  pred_success pi <= p_ideal + e_total.
Lemma unp_entropy_ge (pi : predictor) ... :
  0 < p_ideal + e_total ->
  - log (pred_success pi) >= - log (p_ideal + e_total).
```

(`ideal_guess` := the best success achievable from the allowed information alone; exact form fixed by the probe; the positivity side condition is mandatory — `ler_log` is `Num.pos`-domained.)
- [ ] **Step 2:** Probe commit (bypass), then land the permanent file with statement comments, compile, axiom check, gate commit `"security models: T-relative unpredictability composition"`.

### Task R9: `smc/security_models/examples_f3.v`

**Files:**
- Create: `smc/security_models/examples_f3.v`; Modify: `_CoqProject`
- Source (verbatim): `.scratch/probe_examples_f3.v` — card_F3, unif3, mask_chan(+E), biased3(+0/1/2), leaks, statdist computation `biased_uniform_eps` (= 6^-1), dirac_shiftE, tensor_dirac_l, draw_add_mask, log probes.

- [ ] **Step 1:** Create; add the three-verdict toy as `Module masking_verdicts` instantiating the kernel at `X := 'F_3`, `Yfull := Y := 'I_1`, `Bv := 'F_3`, `Omega := 'F_3`, `view_at := fun e => e.1 + e.2`:
  - uniform `P_Omega` => `perfect_privacy (fun _ => unif3)`;
  - `P_Omega := biased3` => `eps_privacy (fun _ => unif3) 6%:R^-1` (by `view_lawE`, `mask_chanE`, `biased_uniform_eps`);
  - `Omega := 'I_1` (no mask) => `insecurity` witness at inputs `0`,`1`.
  Map cells labeled "'F_3 analogue" of the chapter's 'F_29 instance.
- [ ] **Step 2:** Compile, axiom check, gate commit `"security models: F3 mask examples and the three-verdict toy"`.

### Task R10: `smc/security_models/spp_bridge.v`

**Files:**
- Create: `smc/security_models/spp_bridge.v`; Modify: `_CoqProject` (AFTER the du2002 block)
- Source: `.scratch/probe_spp_bridge_shape.v` (`cond_law_to_bind`, renamed), `du2002/spp_simulator.v` (`bob_view_cond_sim_xy:215`, `bob_simulator:66`).

- [ ] **Step 1:** Rebuild the du2002 chain first (stale `.vo`, naming-audit F16): `make du2002/spp_simulator.vo` (or `make -j8`), exit 0.
- [ ] **Step 2:** Create the file: `dist_of_RV_bind` (probe code verbatim under the audited name), then the bridge theorem

```coq
(* The SPP corrupted-Bob view law factors through Bob's allowed
   information via the mechanized simulator: nu = Sim o allow in RV form. *)
Theorem spp_bob_factorization :
  `p_ BobView = `p_ [% x2, y2] >>= (fun ay => bob_simulator ay.1 ay.2).
Proof. (* dist_of_RV_bind + bob_view_cond_sim_xy *) Qed.
```

  plus the H0-instance lemma for SPP (spec C8) if `spp_proof.v`'s share-law lemmas suffice (`bob_pads_law` route); otherwise record it as a remaining obligation in Task R13's spec sync — do NOT claim it silently.
- [ ] **Step 3:** Compile, axiom check, gate commit `"security models: SPP corrupted-Bob bridge (dist_of_RV_bind, factorization)"`.

### Task R11: Structure-map extension (thesis repo, untracked note)

**Files:**
- Modify: `phd-thesis/docs/notes/20260731-2237-security-models-pre-game-structure-map.md` (UNTRACKED by that repo's whitelist gitignore — edit in place, no commit; flag to the user if they want it force-added)

- [ ] **Step 1:** Append the game-section and examples-section block tables (chapter lines 1776-2571, same format) and add the "Rocq artifact" column on ALL rows: existing artifacts named directly (`bob_ext_ok`, `fdist`, `centropy_RV`, ...), new rows using the identifiers of Tasks R3-R10, prose-only rows get a dash; add rows for the B+ items (condition, consistency, theorem+corollaries, matrix example, corrected BK/Lindell sentences).

### Task R12: Golf sweeps + whole-file audit

- [ ] **Step 1:** `/rocq:golf` over the eight permanent files, PROOF BODIES ONLY; re-verify axioms after each file (`mcp__rocq-mcp__rocq_assumptions` or check_axioms.sh).
- [ ] **Step 2:** Whole-file audit (`audit-file.sh` per repo memory — gate Stage 1 is diff-scoped, so run the whole-file pass here).
- [ ] **Step 3:** Gate commit `"security models: golf proof bodies"` (one commit per batch if large).

### Task R13: Spec sync (the user-ordered post-plan update)

- [ ] **Step 1:** Update `smc/notes/20260731-security-models-formalization-design.md`: add a "Plan" pointer to this file; record every probe finding and allowed spelling adjustment from R7/R8; resolve the R10 H0-instance outcome; mark construction choices locked here (kernel = Section, party instantiation by section application, `Module` names `identity_protocol`/`three_party_identity`/`masking_verdicts`).
- [ ] **Step 2:** Update the thesis-side spec's §5-§6 rows correspondingly (C3/C4b probed; C8 outcome).
- [ ] **Step 3:** Commit both specs (md-only, no bypass needed).

**Task order:** R1 → R2 → R3 → R4 → R5 → R6 → R7 → R8 → R9 → R10 → R11 → R12 → R13. R3-R4 are independent of each other; everything else is ordered by `Require` dependencies.
