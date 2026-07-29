# DSDP infotheo-leg Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. Rocq adaptation: the TDD analogue is
> state-lemma-then-prove; a task is done only when its lemmas are `Qed` (no
> `Admitted`/`Abort`) and the file compiles; commit only then.

**Goal:** One SSProve-free file
`dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v` proving the
three corrupted-Alice headlines (guess bound, unpredictability, simulator
closeness) in infotheo, per the audited spec
`dumas2017dual/notes/20260729-dsdp-infotheo-leg-design.md`.

**Architecture:** Explicit product sample space (all uniformity/independence
theorems); reduction-form epsilons (`indcpa_fdist_epsilon` of explicit hop
reductions); one RV-level resampling lemma powers both hop equalities; the
IT zero-endpoint reuses `Pr_dsdp_sol_uniform_ring` + a graphoid
weak-union conditional-independence chain. Probe-verified code
(`<session scratchpad>/probe_infotheo_leg.v`) is copied verbatim where noted.

**Tech Stack:** Rocq 9.0.0 via `/Users/cheng-huiweng/Projects/coq/_opam`,
mathcomp 2.x, infotheo (this repo, `-R . infotheo`), HB.

**Compile command** (used by every task; macOS, no `timeout`):

```bash
/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc \
  -R /Users/cheng-huiweng/Projects/coq/infotheo-itp infotheo \
  -w -notation-overridden -w -ambiguous-paths \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-incompatible-format \
  dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v
```

(rocq MCP `rocq_compile_file` on the same path is equivalent and preferred
for error positions. All prerequisite `.vo`s are already built.)

---

### Task 1: Scaffold — file, imports, section parameters

**Files:**
- Create: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v`
- Modify: `_CoqProject` (add the new path after
  `dumas2017dual/dsdp/counting/dsdp_entropy.v`)

- [ ] **Step 1: Create the file** with exactly this content (imports are the
  probe's proven-working header minus the unused ones; `(**md ... *)` table
  filled in Task 12):

```coq
(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, infotheo axis                              *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_infotheo_secrecy.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variable pkey_of_party : party_id -> pub_key AHE.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).

End dsdp_alice_infotheo_secrecy.
```

- [ ] **Step 2: Add to `_CoqProject`**: insert the line
  `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v`
  directly after `dumas2017dual/dsdp/counting/dsdp_entropy.v`.

- [ ] **Step 3: Compile** with the command above. Expected: exit 0.

- [ ] **Step 4: Commit**
  `git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v _CoqProject && git commit -m "dsdp infotheo leg: scaffold"`

### Task 2: fdist glue toolkit

**Files:** Modify the new file — add a `Section fdist_glue` BEFORE
`Section dsdp_alice_infotheo_secrecy` (it is protocol-independent).

- [ ] **Step 1: Copy the four probe glue lemmas verbatim** from
  `<session scratchpad>/probe_infotheo_leg.v` lines 115-158
  (`probe_fdist_prod_bindE`, `probe_fdistmap_bind`, `probe_Pr_fdistmap_bool`,
  `probe_fdist_prod2`, with their exact proof bodies), renamed by dropping
  the `probe_` prefix: `fdist_prod_bindE`, `fdistmap_bind`,
  `Pr_fdistmap_bool`, `fdist_prod2`. Keep the `Context {R : realType}.`
  section header.

- [ ] **Step 2: Add the two layout lemmas** (new, not probed — small):

```coq
(* A uniform distribution over a product is the product of uniforms. *)
Lemma fdist_uniform_prod (T1 T2 : finType) (n1 n2 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1)
    (c12 : #|(T1 * T2)%type : finType| = (n1.+1 * n2.+1)%N.-1.+1) :
  fdist_uniform (R:=R) c12 = fdist_uniform c1 `x fdist_uniform c2.
Proof.
apply/fdist_ext => -[a b]; rewrite fdist_prodE !fdist_uniformE.
(* both sides are (n1.+1 * n2.+1)%:R^-1; close with natrM invfM *)
Admitted. (* iterate to Qed before committing *)

(* The pushforward of a uniform along a bijection is uniform. *)
Lemma fdistmap_bij_uniform (T1 T2 : finType) (n : nat)
    (c1 : #|T1| = n.+1) (c2 : #|T2| = n.+1) (g : T1 -> T2) :
  bijective g ->
  fdistmap g (fdist_uniform (R:=R) c1) = fdist_uniform c2.
Proof.
case=> h ghK hgK; apply/fdist_ext => b.
rewrite fdistmapE fdist_uniformE (big_pred1 (h b)); last first.
  by move=> a; rewrite !inE /=; apply/eqP/eqP => [<-|->].
by rewrite fdist_uniformE c1 c2.
Qed.
```

  The `Admitted` markers are placeholders for THIS plan document only — the
  step is not done until both are `Qed` (expect ~5 lines each; use
  `rocq_step_multi` batteries with `natrM`, `invfM`, `mulr_natl`).

- [ ] **Step 3: Compile.** Expected: exit 0, no `Admitted` remaining
  (grep the file: `grep -c Admitted` must print 0).

- [ ] **Step 4: Commit**
  `git commit -am "dsdp infotheo leg: fdist glue toolkit"`

### Task 3: Sample space, coordinate RVs, views

**Files:** Modify the new file, inside `Section
dsdp_alice_infotheo_secrecy` after the hypotheses.

- [ ] **Step 1: Cardinality `Let`s and the sample space:**

```coq
Let card_plain_gt0 : (0 < #|plain AHE|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.
Let card_plain : #|plain AHE| = #|plain AHE|.-1.+1.
Proof. by rewrite prednK. Qed.
Let card_plain_pair :
  #|((plain AHE * plain AHE)%type : finType)|
    = (#|plain AHE| * #|plain AHE|)%N.-1.+1.
Proof. by rewrite card_prod prednK // muln_gt0 card_plain_gt0. Qed.
Let card_renc_pair :
  #|((Renc * Renc)%type : finType)|
    = (index_renc.+1 * index_renc.+1)%N.-1.+1.
Proof. by rewrite card_prod card_renc. Qed.

Definition dsdp_alice_sampleT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * (Renc * Renc))%type.

Definition alice_sample_fdist : R.-fdist dsdp_alice_sampleT :=
  ((fdist_uniform card_plain_pair `x fdist_uniform card_plain_pair)
     `x fdist_uniform card_renc_pair) `x fdist_uniform card_renc_pair.
```

- [ ] **Step 2: Coordinate projections** (left-assoc nesting
  `(((vv * masks) * rho) * ra)`):

```coq
Definition V2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.1.
Definition V3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.2.
Definition R2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.1.
Definition R3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.2.
Definition Rho2 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.1.
Definition Rho3 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.2.
Definition RA1 : {RV alice_sample_fdist -> Renc} := fun t => t.2.1.
Definition RA2 : {RV alice_sample_fdist -> Renc} := fun t => t.2.2.
```

- [ ] **Step 3: Derived RVs and the indexed view family** (`uncurry` per
  probe C2; `if`-selection per spec section 3):

```coq
Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3) `o [% V2, V3].

Definition hop0_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Bob) (if (0 < i)%N then 0 else V2 t)
         (rand_of_renc (Rho2 t))).
Definition hop1_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Charlie) (if (1 < i)%N then 0 else V3 t)
         (rand_of_renc (Rho3 t))).

Definition dsdp_alice_viewT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * t_cipher * t_cipher)%type.

Definition AliceView_zero_prefix (i : nat) :
    {RV alice_sample_fdist -> dsdp_alice_viewT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, hop0_cipher i, hop1_cipher i].

Notation AliceView := (AliceView_zero_prefix 0).
Notation AliceView_all_zero := (AliceView_zero_prefix 2).

Definition E_bob_v2 := hop0_cipher 0.
Definition E_charlie_v3 := hop1_cipher 0.
```

- [ ] **Step 4: Compile; commit**
  `git commit -am "dsdp infotheo leg: sample space and views"`

### Task 4: Adversary record and epsilons

**Files:** Modify the new file (same section).

- [ ] **Step 1: Copy the probe P3 record/success/epsilon code**
  (`probe_infotheo_leg.v:236-260`) with these renames and instantiations:
  `probe_mini_adversary -> indcpa_fdist_adversary`, `Pl -> plain AHE`,
  `C -> t_cipher`, `probe_enc_fdist -> enc_fdist` now taking the public key:

```coq
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist t_cipher :=
  fdistmap (fun r => chcipher_of_cipher (enc pk v (rand_of_renc r)))
           (fdist_uniform card_renc).

Record indcpa_fdist_adversary := {
  adv_context : finType ;
  adv_choose : R.-fdist adv_context ;
  adv_plain : adv_context -> plain AHE ;
  adv_decide : adv_context -> t_cipher -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

Definition indcpa_fdist_success_real (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk (adv_plain adv c))))
     [set true].
Definition indcpa_fdist_success_zero (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk 0)))
     [set true].
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.
```

- [ ] **Step 2: Compile; commit**
  `git commit -am "dsdp infotheo leg: fdist-axis IND-CPA adversary and epsilon"`

### Task 5: RV-level resampling lemma and per-hop product laws

**Files:** Modify the new file.

- [ ] **Step 1: State and prove `enc_slot_resampleE`** — the RV-level
  generalization of probe `probe_enc_slot_resampleE_ctx`
  (`probe_infotheo_leg.v:212-229`): the probe pinned `P = unif `x unif`,
  here the product-law is a PREMISE so the lemma applies at any coordinate
  layout:

```coq
Lemma enc_slot_resampleE (ctxT : finType) (Q : R.-fdist ctxT)
    (Ctx : {RV alice_sample_fdist -> ctxT})
    (Rho : {RV alice_sample_fdist -> Renc})
    (k : ctxT -> Renc -> t_cipher) :
  `p_ [% Ctx, Rho] = Q `x fdist_uniform card_renc ->
  `p_ [% Ctx, (fun t => k (Ctx t) (Rho t))
        : {RV alice_sample_fdist -> t_cipher}]
    = Q `X (fun a => fdistmap (k a) (fdist_uniform card_renc)).
Proof.
move=> Hprod.
have -> : [% Ctx, (fun t => k (Ctx t) (Rho t))
             : {RV alice_sample_fdist -> t_cipher}]
          = (fun p : ctxT * Renc => (p.1, k p.1 p.2)) `o [% Ctx, Rho].
  exact/boolp.funext.
rewrite /dist_of_RV fdistmap_comp -/(dist_of_RV _) Hprod.
(* now literally the probe computation: fdist_prod_bindE both sides,
   fdistmap_bind, fdist_prod1, congr + funext + fdistmap_comp *)
Admitted. (* iterate to Qed; probe body probe_infotheo_leg.v:215-223 is the
             template with [in LHS]/P replaced by the Hprod rewrite *)
```

- [ ] **Step 2: Per-hop context RVs and product-law premises.** Contexts:

```coq
Definition hop0_ctxT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * Renc)%type.
Definition Hop0Ctx : {RV alice_sample_fdist -> hop0_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.2).   (* vv, masks, ra, rho3 *)

Definition hop1_ctxT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * t_cipher)%type.
Definition Hop1Ctx : {RV alice_sample_fdist -> hop1_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, hop0_cipher 1 t).
```

  (Hop 1's context carries the ZEROED hop-0 cipher sample, spec section 4 /
  audit F5: it is a function of `Rho2`, disjoint from `Rho3`.)

  Product-law lemmas to prove, both via `fdistmap_bij_uniform` +
  `fdist_uniform_prod` (hop 0: `[% Hop0Ctx, Rho2]` is a bijective
  repackaging of the identity, so its law is uniform, which factors) and,
  for hop 1, `enc_slot_resampleE`-free reasoning: `[% Hop1Ctx, Rho3]` is
  `(g `o [% Hop0CtxNoRho3-part...])` — concretely prove:

```coq
Lemma hop0_ctx_prod :
  `p_ [% Hop0Ctx, Rho2]
    = (`p_ Hop0Ctx) `x fdist_uniform card_renc.
Lemma hop1_ctx_prod :
  `p_ [% Hop1Ctx, Rho3]
    = (`p_ Hop1Ctx) `x fdist_uniform card_renc.
```

  Strategy hop 0: `[% Hop0Ctx, Rho2]` is a coordinate bijection of the full
  tuple; `alice_sample_fdist` equals `fdist_uniform` over `dsdp_alice_sampleT`
  (prove `alice_sample_fdistE` first via `fdist_uniform_prod` three times);
  so the pair law is uniform over `hop0_ctxT * Renc`, which
  `fdist_uniform_prod` splits; `p_ Hop0Ctx` is then uniform by
  `fdistmap_bij_uniform`... falling out of the same computation. Strategy
  hop 1: `[% Hop1Ctx, Rho3] = (fun p => ((p.1.1, p.1.2, p.1.3,
  cipher-of p.1.4...), p.2)) `o [% Hop0Ctx-like-pair]` — push the cipher map
  through with `fdistmap` lemmas and `inde`-style block reasoning; the
  cipher slot is a function of `(V2-block, Rho2)` while `Rho3` is a disjoint
  coordinate. If direct computation stalls, fall back to proving
  independence `alice_sample_fdist |= [% Hop1Ctx] _|_ Rho3` via
  `inde_RV_comp` from block independence and conclude with
  `inde_dist_of_RV2` + the `Rho3` marginal (probe pattern
  `probe_dist_Rho`/`probe_inde_Ctx_Slot`, `probe_infotheo_leg.v:183-193`).

- [ ] **Step 3: Compile (0 Admitted); commit**
  `git commit -am "dsdp infotheo leg: resampling lemma and hop product laws"`

### Task 6: Hop reductions and hop equalities

**Files:** Modify the new file.

- [ ] **Step 1: Distinguisher-facing joint and reductions.** Input-aware
  distinguisher type `D : plain AHE * plain AHE * dsdp_alice_viewT -> bool`.
  Assembly functions (each hop rebuilds `(v2, v3, view)` from
  `(context, challenge cipher)`):

```coq
Definition hop0_assemble (c : hop0_ctxT) (ch : t_cipher) :
    plain AHE * plain AHE * dsdp_alice_viewT :=
  let: (vv, masks, ra, rho3) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2, ch,
    chcipher_of_cipher
      (enc (pkey_of_party Charlie) vv.2 (rand_of_renc rho3)))).

Definition hop1_assemble (c : hop1_ctxT) (ch : t_cipher) :
    plain AHE * plain AHE * dsdp_alice_viewT :=
  let: (vv, masks, ra, c2zero) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2, c2zero, ch)).

Definition hop0_reduction
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_context := hop0_ctxT ;
     adv_choose := `p_ Hop0Ctx ;
     adv_plain := fun c => c.1.1.1 ;          (* v2 of the vv block *)
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.
Definition hop1_reduction
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_context := hop1_ctxT ;
     adv_choose := `p_ Hop1Ctx ;
     adv_plain := fun c => c.1.1.2 ;          (* v3 *)
     adv_decide := fun c ch => D (hop1_assemble c ch) |}.
```

  (`Sout` is recomputed inside the assemblies from the context's `vv` block
  — audit F5's joint requirement, satisfied by construction. NOTE for the
  implementer: check the exact `let:`-pattern syntax against the nested
  pair type; plain `.1`/`.2` projections are the fallback.)

- [ ] **Step 2: Arm equalities and the hop equalities**, following the probe
  P3 proofs verbatim in structure (`probe_hop_real_armE` /
  `probe_hop_zero_armE` / `probe_hop_advantageE`,
  `probe_infotheo_leg.v:275-305`; substitute `enc_slot_resampleE hop0_ctx_prod`
  for the probe's pinned-product resample lemma, and note the joint here is
  `[% V2, V3, AliceView_zero_prefix i]` re-expressed as
  `(fun p => ...assemble...) `o [% Hop?Ctx, slot]` first — prove that
  re-expression by `boolp.funext` as a preliminary `have ->`):

```coq
Lemma hop0_advantageE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 0]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D).

Lemma hop1_advantageE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceView_zero_prefix 2]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
```

- [ ] **Step 3: Compile (0 Admitted); commit**
  `git commit -am "dsdp infotheo leg: hop reductions and advantage equalities"`

### Task 7: IT leg — zero endpoint

**Files:** Modify the new file.

- [ ] **Step 1: Fiber-lemma premises.** Constant-input RVs
  `V1c := const_RV alice_sample_fdist w_v1` (likewise `U1c U2c U3c`), then
  copy the probe P4 application (`probe_infotheo_leg.v:313-348`) with
  `P := alice_sample_fdist` and `S := Sout`; premises:
  - constraint: `by move=> t; rewrite /dsdp_constraint_ring /Sout
    /dsdp_output !const_RVE /=; ring.` (template
    `dsdp_guess_fiber.v:1430-1432`);
  - `var_uniform : `p_ [% V2, V3] = fdist_uniform card_plain_pair`: the
    `[%V2,V3]` block is the first coordinate chain — via
    `alice_sample_fdistE`/`fdist_prod1` chain (`fdist_prod1` three times);
    then close the fiber lemma's own equation with
    `congr fdist_uniform; exact: eq_irrelevance` (probe C7);
  - `var_indep : alice_sample_fdist |= [% V1c, U1c, U2c, U3c] _|_ [% V2, V3]`:
    constants are independent of everything — search
    `Search inde_RV const_RV` / `Search "inde" "const"`; if absent, prove the
    two-line pointwise lemma `inde_RV_const : P |= const_RV P k _|_ X` and
    lift with `inde_RV_comp`.

- [ ] **Step 2: `V2 | Sout` conditional bound.** Adapt
  `guess_V2_cond_Sout` (`dsdp_guess_fiber.v:1443-1490`) and
  `guess_V2_cond_le` (`:1493-1503`) with `guess_sample_fdist ->
  alice_sample_fdist` and our premise names (this is the ~250-line P-swap
  region; copy the proof bodies and repair name-by-name with
  `rocq_compile_file` errors as the guide):

```coq
Lemma alice_V2_cond_Sout (a s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ V2 = a | Sout = s ] = #|plain AHE|%:R^-1.
Lemma alice_V2_cond_le (a s : plain AHE) :
  `Pr[ V2 = a | Sout = s ] <= #|plain AHE|%:R^-1.
```

  (`w_u3_inj` is a section hypothesis here, so it is not a premise of the
  statements. The `_le` form's zero-mass branch is
  `by rewrite cpr_eqE H0 invr0 mulr0 invr_ge0 ler0n`.)

- [ ] **Step 3: `Sout_uniform`** (spec F9):

```coq
Lemma Sout_uniform : `p_ Sout = fdist_uniform card_plain.
```

  Strategy: for fixed `v2`, `v3 |-> dsdp_output ... v2 v3` is a bijection
  (`w_u3_inj` + `inj_card_bij` as in `dsdp_guess_fiber.v` around `:1450`);
  `p_ Sout` at `s` is the sum over `v2` of `Pr[[%V2,V3] = (v2, g_inv v2 s)]
  = 1/m^2` each, `m` terms. Sum with `big_pred1`-style reindexing.

- [ ] **Step 4: Spectator conditional independence + endpoint.** The
  spectator is everything the view carries besides `Sout`:

```coq
Definition AliceSpectator :
    {RV alice_sample_fdist ->
       ((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)%type}
  := [% [% R2, R3], [% RA1, RA2], hop0_cipher 2, hop1_cipher 2].

Lemma alice_spectator_cinde :
  alice_sample_fdist |= AliceSpectator _|_ V2 | Sout.
```

  Strategy (simpler than the SSProve axis's kernel proof): `AliceSpectator`
  is a function of coordinates disjoint from the `vv` block, so
  `AliceSpectator _|_ [% V2, V3]` (block independence, probe
  `prod_dist_inde_RV` pattern); `Sout` is a function of `[% V2, V3]`
  (`inde_RV_comp` gives `AliceSpectator _|_ [% V2, Sout]`); conclude by
  graphoid weak union (`Search cinde weak_union` in `graphoid`; the law is
  `X _|_ [% Y, Z] -> X _|_ Y | Z`). Then copy the probe P5 chain
  (`probe_guess_all_zero_le_invm`, `probe_infotheo_leg.v:368-373`) —
  noting `AliceView_all_zero` is a deterministic repackaging of
  `[% AliceSpectator, Sout]` (prove the repackaging equality by
  `boolp.funext`, then `cinde_RV_comp` absorbs the repackaging exactly as
  in the probe):

```coq
Lemma guess_all_zero_le_invm (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView_all_zero) t == V2 t]
    <= #|plain AHE|%:R^-1.
```

- [ ] **Step 5: Compile (0 Admitted); commit**
  `git commit -am "dsdp infotheo leg: zero-endpoint fiber chain"`

### Task 8: Headline (i) — guess bound

**Files:** Modify the new file.

- [ ] **Step 1:**

```coq
Definition distinguisher_of_guess (g : dsdp_alice_viewT -> plain AHE) :
    plain AHE * plain AHE * dsdp_alice_viewT -> bool :=
  fun x => g x.2 == x.1.1.

Theorem dsdp_alice_guess_fdist_V2_real_le
    (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess g)).
```

  Proof plan: `Pr ... [set t | ...]` at prefix `i` equals
  `Pr (`p_ [% V2, V3, AliceView_zero_prefix i]) [set x |
  distinguisher_of_guess g x]` (event repackaging, `Pr_fdistmap_bool` /
  preimage lemma + `boolp.funext`); then two triangle steps
  `ler_distD`-style (`|a - c| <= |a - b| + |b - c|`, mathcomp
  `ler_dist_add`) rewritten by `hop0_advantageE`/`hop1_advantageE`, endpoint
  by `guess_all_zero_le_invm`. Chain:
  `Pr_real <= Pr_allzero + |Pr_real - Pr_mid| + |Pr_mid - Pr_allzero|`
  via `ler_normD`-family; keep the epsilon terms in the stated order.

- [ ] **Step 2: Compile; commit**
  `git commit -am "dsdp infotheo leg: guess-bound headline"`

### Task 9: Headline (ii) — unpredictability

**Files:** Modify the new file.

- [ ] **Step 1:** With `eps0 g`/`eps1 g` denoting the two epsilon terms of
  Task 8 (`Let`s to keep the statement short):

```coq
Theorem dsdp_alice_unpredictability_fdist_ge
    (g : dsdp_alice_viewT -> plain AHE)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (g `o AliceView) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
  <= - log (Pr alice_sample_fdist
              [set t | (g `o AliceView) t == V2 t]).
```

  Proof plan (~20 lines, template `dsdp_main.v:861` region): from Task 8,
  `success <= (1 + m*(eps0+eps1))/m` (exact identity
  `m^-1 + e = (1 + m*e)/m` by `field`-style rewriting with
  `#|plain AHE|%:R != 0`); apply `ler_log`-family monotonicity
  (`realType_ln`: search `Search log ler`; `log` is monotone on positives,
  `Hpos` + positivity of the bound discharge the domain side conditions);
  then `log (x/y) = log x - log y` (`logM`/`logV` lemmas) rearranged.

- [ ] **Step 2: Compile; commit**
  `git commit -am "dsdp infotheo leg: unpredictability headline"`

### Task 10: Simulator, factorizations, headline (iii)

**Files:** Modify the new file.

- [ ] **Step 1: Simulator distribution** (slot layout = `dsdp_alice_viewT`
  nesting; `bob_simulator` product style, `du2002/spp_simulator.v:66`):

```coq
Definition dsdp_alice_simulator (s : plain AHE) :
    R.-fdist dsdp_alice_viewT :=
  (((fdist_uniform card_plain_pair `x fdist_uniform card_renc_pair)
      `x fdist1 s)
     `x enc_fdist (pkey_of_party Bob) 0)
    `x enc_fdist (pkey_of_party Charlie) 0.
```

  (Check associativity against `dsdp_alice_viewT = ((pp * rr * plain)
  * t_cipher * t_cipher)`; adjust the ``x`` nesting to match exactly — the
  type checker is the judge. Masks and `RA` coordinates are uniform in both
  worlds.)

- [ ] **Step 2: Factorizations:**

```coq
Lemma dsdp_alice_view_cond_sim (v : dsdp_alice_viewT) (v2 v3 : plain AHE) :
  `Pr[ [% V2, V3] = (v2, v3) ] != 0 ->
  `Pr[ AliceView_all_zero = v | [% V2, V3] = (v2, v3) ]
    = dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 v2 v3) v.
Corollary dsdp_alice_view_cond_sim_S (v : dsdp_alice_viewT)
    (s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ AliceView_all_zero = v | Sout = s ] = dsdp_alice_simulator s v.
```

  Proof plan for the main lemma (`bob_view_cond_sim`,
  `du2002/spp_simulator.v:173-213`, is the working template — same
  conditional-law-of-independent-blocks computation): conditioned on
  `[%V2,V3] = (v2,v3)`, every non-`Sout` slot of `AliceView_all_zero` is a
  function of coordinates independent of the `vv` block, `Sout`'s slot is
  the Dirac at `dsdp_output ... v2 v3`; expand `cpr_eqE`, split the joint
  `pfwd1` over the product blocks, and match `dsdp_alice_simulator`
  slotwise (`fdist_prodE`, `fdist1E`, `enc_fdist`'s `fdistmapE`). The
  corollary: average the main lemma over the fiber of `s` (partition
  `[% V2, V3]` events by `Sout`), guard discharged by hypothesis; template
  `bob_view_cond_sim_xy -> bob_view_commute` structure
  (`spp_simulator.v:215-263`).

- [ ] **Step 3: Ideal joint and headline:**

```coq
Definition alice_ideal_joint :
    R.-fdist (plain AHE * plain AHE * dsdp_alice_viewT) :=
  `p_ [% V2, V3] >>= (fun vv =>
     fdistmap (fun v => (vv.1, vv.2, v))
       (dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2))).

Theorem dsdp_alice_sim_advantage_fdist_le
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 0]) [set x | D x]
     - Pr (fdistmap D alice_ideal_joint) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D)
     + indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
```

  Proof plan: first `Pr (fdistmap D alice_ideal_joint) [set true]
  = Pr (`p_ [% V2, V3, AliceView_zero_prefix 2]) [set x | D x]` — by
  `Pr_fdistmap_bool` and showing
  `alice_ideal_joint = `p_ [% V2, V3, AliceView_all_zero]`: expand the
  joint law as bind over `[%V2,V3]` of the conditional law
  (`jfdist_cond` / `fdist_prod` decomposition of a joint through its first
  marginal — search `Search fdist_prod jfdist_cond`; infotheo's
  `fdistX`/`fdist_prod_of` family) and rewrite with
  `dsdp_alice_view_cond_sim`; zero-mass `vv` cells contribute equally to
  both binds (both weight 0). Then the two hop equalities + triangle as in
  Task 8, without the endpoint step.

- [ ] **Step 4: Compile (0 Admitted); commit**
  `git commit -am "dsdp infotheo leg: simulator and sim-closeness headline"`

### Task 11: Fidelity remark — full view transfer

**Files:** Modify the new file.

- [ ] **Step 1:** Full view = reduced view + Alice's two outgoing combines
  and the decrypted final receive, all recomputed (`palice`,
  `core/dsdp_pismc.v:134-143`; combine ops via the AHE `Emul`/`Epow` on
  `cipher AHE`, marshalled back and forth with `cipher_of_chcipher`):

```coq
Definition alice_view_full_of (v : dsdp_alice_viewT) :
    dsdp_alice_viewT * cipher AHE * cipher AHE * plain AHE :=
  let c2 := cipher_of_chcipher v.1.1.2 in
  let c3 := cipher_of_chcipher v.2 in
  (v,
   (c2 ^h w_u2) *h enc (pkey_of_party Bob) (v.1.1.1.1.1) (* r2 *)
        (rand_of_renc v.1.1.1.2.1),
   (c3 ^h w_u3) *h enc (pkey_of_party Charlie) (v.1.1.1.1.2)
        (rand_of_renc v.1.1.1.2.2),
   v.1.1.2 (* placeholder: decrypted g = Sout-slot recomputation *)).
```

  NOTE: the exact projection paths and the `g`-slot formula
  (`Sout - u1*v1 + r2 + r3` per `dsdp_pismc.v:142`) must be read off the
  final `dsdp_alice_viewT` nesting; the implementer fixes the projections
  against the type checker, keeps the SHAPE (view, combine1, combine2,
  decrypted-g) and proves:

```coq
Lemma alice_view_full_ok :
  (fun t => alice_view_full_of (AliceView t))
  = (fun t => (AliceView t,
       combine1-as-RV t, combine2-as-RV t, decrypted-g-as-RV t)).
Corollary dsdp_alice_guess_fdist_full_le
    (g' : dsdp_alice_viewT * cipher AHE * cipher AHE * plain AHE
          -> plain AHE) :
  Pr alice_sample_fdist
     [set t | (g' `o ((fun t => alice_view_full_of (AliceView t))
                        : {RV alice_sample_fdist -> _})) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess (g' \o alice_view_full_of)))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess (g' \o alice_view_full_of))).
```

  The corollary is `dsdp_alice_guess_fdist_V2_real_le` applied to
  `g' \o alice_view_full_of` (one-line proof). If the combine formulas
  fight the marshalling for more than ~an hour of iteration, descope: keep
  `alice_view_full_of`+`_ok` for the two combines only and drop the
  `g`-slot component, documenting the drop in the header (the `g` plaintext
  is `Sout`-derivable, so nothing is lost information-theoretically) — do
  NOT let this task block the final one.

- [ ] **Step 2: Compile; commit**
  `git commit -am "dsdp infotheo leg: full-view transfer remark"`

### Task 12: Header, style pass, axiom check, final verification

**Files:** Modify the new file.

- [ ] **Step 1: Complete the `(**md ... *)` header**: 80-column padded
  frame; a triple-backtick `==`-aligned table with one row per public
  definition (`dsdp_alice_sampleT`, `alice_sample_fdist`, the ten coordinate
  RVs, `Sout`, `hop0_cipher`, `hop1_cipher`, `dsdp_alice_viewT`,
  `AliceView_zero_prefix`, `E_bob_v2`, `E_charlie_v3`, `enc_fdist`,
  `indcpa_fdist_adversary` + fields, the two success defs,
  `indcpa_fdist_epsilon`, `Hop0Ctx`/`Hop1Ctx`, the reductions,
  `distinguisher_of_guess`, `dsdp_alice_simulator`, `alice_ideal_joint`,
  `alice_view_full_of`); one declarative sentence per row; a scope
  paragraph stating: average-case over honest inputs, single-query
  fixed-key epsilons, bounds trivial when epsilons are large, complexity
  reading on paper (spec sections 1 and 8.7).

- [ ] **Step 2: Statement-comment pass**: every Lemma/Theorem/Definition
  gets a declarative one-sentence comment (+ optional trailing `Naming:`
  paragraph); no meta/status narration (model `dsdp_main.v:750-755`).

- [ ] **Step 3: Style scan**:
  `bash /Users/cheng-huiweng/.claude/skills/mathcomp-skills/scripts/audit-quick.sh dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v`
  and `awk 'length > 80' <file>` — fix findings.

- [ ] **Step 4: Axiom hygiene**: `rocq_assumptions` (or a scratch
  `Print Assumptions` file as in the probe) on all three headline theorems.
  Expected: boolp trio only (`propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`).

- [ ] **Step 5: Full-repo touch check**: recompile the file; then
  `git status` to confirm only intended files changed.

- [ ] **Step 6: Final commit**
  `git commit -am "dsdp infotheo leg: header, style pass, axiom check"`
  (pre-commit rocq-auditor Stage 2 runs via hook; address findings before
  concluding.)

---

## Self-review notes

- Spec coverage: sections 2 (Task 1), 3 (Task 3), 4 (Tasks 2, 4, 5, 6),
  5 (Task 7), 6 (Tasks 8, 9, 10), fidelity remark (Task 11), file
  conventions + invariants (Task 12). Naming table applied throughout.
- Known intentional deviations from bite-size: Tasks 5-7 and 10 contain
  research-grade proof work; their steps carry proof plans + templates
  rather than guaranteed-correct tactic scripts. The probe de-risked their
  shapes; expect iteration, not redesign.
- Type-consistency: `AliceView_zero_prefix` indices 0/1/2 used consistently
  in Tasks 6, 7, 8, 10; `hop0_cipher 2 = hop0_cipher 1` definitionally
  (both zeroed) — Task 7's spectator uses index 2 uniformly.
- `Admitted` appears in this PLAN as an iteration marker only; every task's
  compile step requires `grep -c Admitted` = 0 before its commit.
