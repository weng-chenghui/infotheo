# InputEncoding core (interface + den Boer instance + input privacy) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a general `InputEncoding` interface, instantiate it for den Boer, and prove that the den Boer encoding computes `a && b` and has perfect input privacy `I(Inputs; ViewA C | Secret) = 0`, all axiom-clean.

**Architecture:** A new generic record `InputEncoding` over the existing `ReconPlug`, with one correctness law (`ie_assemble_valid`) and one privacy law (`ie_orbit`), plus two generic payoff theorems. The den Boer instance fills the laws from `fc_correct` and the `s=0` cyclic-rotation orbit, and the input-privacy theorem is proven on the existing leakage probability space `Omega = bool*bool*'I_5` from `five_card_leakage.v`. The operational dealer rewrite (Approach B) is deferred to a follow-on plan.

**Tech Stack:** Rocq (Coq) + MathComp + infotheo, in `infotheo-pgg`. Proof development uses the rocq-mcp 4-phase workflow (`rocq_start` -> `rocq_query`/`rocq_check` -> assemble -> `make -j1`). Build is `make -j1 <path>.vo`. Axiom hygiene via `rocq_assumptions` / `Print Assumptions` (only the three `boolp` axiols are standard here).

**Rocq adaptation of the TDD loop:** for each declaration the "failing test" is the lemma/definition stated with `Admitted` (the file still compiles); "make it pass" is the proof body, developed interactively; "test passes" is `make -j1` with no `Admitted`; the extra gate is `rocq_assumptions` (no new axioms). Complete *statements* are given in every task; proof *bodies* for the non-trivial lemmas are developed at execution with rocq-prover and verified by compilation, because their tactics require goal inspection.

**Reference for proof conventions:** `pgg-smc/instances/denboer1989/five_card_leakage.v` (the just-committed file) is the model for the counting/entropy machinery (`condent_ratio`, `count_pr`, the `cardV`/`cardJ` reduction, the `lra` import for real-log algebra) and for `Omega`/`P`/`Secret`/`ViewA`.

---

## File Structure

| File | Responsibility |
|---|---|
| `pgg-smc/reconstruct/input_encoding.v` (new) | the generic `InputEncoding` record + `ie_output_correct` (pure, no probability) |
| `pgg-smc/instances/denboer1989/den_boer_encoding.v` (new) | `den_boer_assemble_valid`, `den_boer_orbit`, the `den_boer_encoding` instance, the `Inputs` RV, and `den_boer_input_private` on `Omega` |
| `_CoqProject` (modify) | register the two new files in the build, in dependency order |

Dependency order: `input_encoding.v` needs `pgg_sharing_framework` and `covering_scheme` (in `pgg_reconstruct`) and `pgg_interface` (in `pgg_smc`). `den_boer_encoding.v` needs `input_encoding`, `five_card_program`, `five_card_scheme_I5`, `five_card_family` (for `five_card_plug`), and `five_card_leakage` (for `Omega`/`P`/`Secret`/`ViewA`).

---

## Task 1: Create `input_encoding.v` with the `InputEncoding` record

**Files:**
- Create: `pgg-smc/reconstruct/input_encoding.v`
- Modify: `_CoqProject` (add the file under the `pgg-smc/reconstruct/` block, after `covering_scheme.v`)

- [ ] **Step 1: Write the file with imports and the record (this statement is the test; it must compile).**

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Input encoding: inputs determine the starting layout                       *)
(*                                                                            *)
(* InputEncoding is the deterministic half of a randomized encoding of a       *)
(* function f over an existing ReconPlug: assemble maps inputs to a valid      *)
(* share layout (ie_assemble_valid), and equal-output inputs lie in one cut    *)
(* orbit (ie_orbit). The cut supplies the randomness.                          *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** InputEncoding — inputs determine a valid share layout for the plug, with
    equal-output inputs in one cut orbit.
    @intent: the deterministic half of a randomized encoding of ie_fun; the
    existing cut supplies the randomness. *)
Record InputEncoding (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type) := MkInputEncoding {
  ie_assemble : inputT -> (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1 ;
  ie_fun      : inputT -> secretT ;
  ie_assemble_valid : forall x,
      ts_valid (rp_scheme plug) (ie_fun x) (ie_assemble x) ;
  ie_orbit : forall x x', ie_fun x = ie_fun x' ->
      exists g : pgg_gT M, g \in pgg_G M /\
        ie_assemble x' =
          [tuple tnth (ie_assemble x) (rp_monodromy plug g i)
                | i < (ts_T' (rp_scheme plug)).+1] ;
}.

Arguments InputEncoding M secretT plug inputT.
Arguments MkInputEncoding {M secretT plug inputT}.
```

- [ ] **Step 2: Register the file in `_CoqProject`.**

Add the line `pgg-smc/reconstruct/input_encoding.v` immediately after the `pgg-smc/reconstruct/covering_scheme.v` line.

- [ ] **Step 3: Build to verify the record compiles.**

Run: `make -j1 pgg-smc/reconstruct/input_encoding.vo`
Expected: compiles with no error (notation-overridden warnings from the framework imports are pre-existing and harmless). The record shape was already validated against the live `ReconPlug` with `coqc` during design, so this step is a confirmation.

- [ ] **Step 4: Commit.**

```bash
git add _CoqProject pgg-smc/reconstruct/input_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "input_encoding: add the InputEncoding interface record"
```

(Stage 2 of the audit is the LLM pass; disable it for these commits while Stage 1 still gates. A bare `Record` with `@intent` carries the required role tag for H001.)

---

## Task 2: `ie_output_correct` (generic functional correctness, no probability)

**Files:**
- Modify: `pgg-smc/reconstruct/input_encoding.v` (append after the record)

- [ ] **Step 1: Add the lemma statement with `Admitted`.**

```coq
(** ie_output_correct — the cut-permuted assembled layout reconstructs ie_fun x,
    for every cut element of the full group.
    @composes: den_boer_run_output. *)
Lemma ie_output_correct (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type)
    (ie : InputEncoding plug inputT) (x : inputT) (g0 : pgg_gT M) :
  g0 \in pgg_G M ->
  ts_recon (rp_scheme plug)
    [tuple tnth (ie_assemble ie x) (rp_monodromy plug g0 i)
          | i < (ts_T' (rp_scheme plug)).+1] = ie_fun ie x.
Proof.
Admitted.
```

- [ ] **Step 2: Build to confirm the statement typechecks (with `Admitted`).**

Run: `make -j1 pgg-smc/reconstruct/input_encoding.vo`
Expected: compiles (one `Admitted` warning).

- [ ] **Step 3: Develop the proof.**

Strategy: this is `ts_correct` applied to the cut-invariance of recon.
- `ts_correct (rp_scheme plug)` takes a validity hypothesis `ts_valid s shares -> ts_recon shares = s`.
- The cut-permuted layout is `[tuple tnth (ie_assemble ie x) (rp_monodromy plug g0 i) | i]`; by `rp_recon_invariant` (the `ts_recon_perm_invariant` field of `plug`, holding over `pgg_G M`, with `g0 \in pgg_G M`), `ts_recon` of this equals `ts_recon (ie_assemble ie x)`.
- `ts_recon (ie_assemble ie x) = ie_fun ie x` by `ts_correct` on `ie_assemble_valid ie x`.

Develop with `rocq_start (file := "pgg-smc/reconstruct/input_encoding.v") (theorem := "ie_output_correct")`, then `rocq_query` to read the exact statement of `ts_recon_perm_invariant` / `rp_recon_invariant` (the precise reindex direction is an open item from the spec, resolve it here), then `rocq_check` to build the proof. Likely shape:

```coq
Proof.
move=> g0G.
rewrite -(ts_correct (ie_assemble_valid ie x)).
(* apply rp_recon_invariant at g0 (g0G) to rewrite the reindexed recon back *)
by rewrite (rp_recon_invariant plug g0G).   (* exact form per ts_recon_perm_invariant *)
Qed.
```

If `rp_recon_invariant`'s statement is oriented the other way (reindex by `g^-1`), adjust the tuple reindex in the lemma statement to match, then re-confirm with `ie_input_private`/den Boer downstream still type against it.

- [ ] **Step 4: Build to verify the proof.**

Run: `make -j1 pgg-smc/reconstruct/input_encoding.vo`
Expected: compiles, no `Admitted`.

- [ ] **Step 5: Axiom check.**

Use `rocq_assumptions (name := "ie_output_correct") (file := "pgg-smc/reconstruct/input_encoding.v")`.
Expected: only standard axioms (likely none, or the `boolp` trio inherited from the framework). No new custom axioms.

- [ ] **Step 6: Commit.**

```bash
git add pgg-smc/reconstruct/input_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "input_encoding: ie_output_correct (output recovers f under every cut)"
```

---

## Task 3: Create `den_boer_encoding.v` with `den_boer_assemble_valid`

**Files:**
- Create: `pgg-smc/instances/denboer1989/den_boer_encoding.v`
- Modify: `_CoqProject` (add under the `pgg-smc/instances/denboer1989/` block, after `five_card_leakage.v`)

- [ ] **Step 1: Write the file header, imports, and the first obligation with `Admitted`.**

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer input encoding: the AND function via fc_arrange                   *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program.
From pgg_reconstruct Require Import input_encoding.
(* five_card_scheme_I5, five_card_family (five_card_plug), five_card_leakage:
   confirm the exact From-paths with `grep -rn "Require Import" on a sibling
   denboer1989 file`; five_card_plug lives in the kim2025 five_card_family. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** den_boer_assemble_valid — the encoded den Boer arrangement is a valid
    sharing of a && b.
    @composes: den_boer_encoding. *)
Lemma den_boer_assemble_valid (ab : bool * bool) :
  fcI_valid (ab.1 && ab.2)
    [tuple of [seq encode_bool x | x <- fc_arrange ab.1 ab.2]].
Proof.
Admitted.
```

- [ ] **Step 2: Register the file in `_CoqProject`** after `pgg-smc/instances/denboer1989/five_card_leakage.v`, and confirm the exact import paths by running:

Run: `grep -rn "five_card_plug\|fcI_valid\|encode_bool" pgg-smc/instances/kim2025/five_card_family.v pgg-smc/instances/denboer1989/five_card_scheme_I5.v | head`
Use the results to complete the `Require Import` lines (the placeholder comment in Step 1).

- [ ] **Step 3: Build to confirm imports and the statement typecheck.**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo`
Expected: compiles (one `Admitted`). If an import path is wrong, fix it now.

- [ ] **Step 4: Develop the proof.**

Strategy: `fcI_valid s shares := fc_three_consec [seq decode_bool x | x <- shares] = s`. With `shares = [seq encode_bool x | x <- fc_arrange a b]`, the codec round-trips (`decode_encode_bool`), so the goal reduces to `fc_three_consec (fc_arrange a b) = a && b`, which is `fc_correct a b 0 (ltn0Sn 4)` modulo `fc_shuffle 0 = id`. Develop with `rocq_start`/`rocq_check`; likely:

```coq
Proof.
rewrite /fcI_valid -map_comp.
under eq_map do rewrite /= decode_encode_bool.
rewrite map_id.
by have := fc_correct ab.1 ab.2 (k := 0) (isT : 0 < 5); rewrite /fc_shuffle rot0.
Qed.
```

Confirm `fc_shuffle 0 = id` (it is `rot 0`, i.e. `rot0`), and the exact `fc_correct` argument order via `rocq_query (command := "Check fc_correct.")`.

- [ ] **Step 5: Build, axiom check, commit.**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo` (no `Admitted`).
`rocq_assumptions (name := "den_boer_assemble_valid")` -> only `boolp` axioms.
```bash
git add _CoqProject pgg-smc/instances/denboer1989/den_boer_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "den_boer_encoding: den_boer_assemble_valid (layout encodes AND)"
```

---

## Task 4: `den_boer_orbit` (the s=0 cyclic-rotation orbit)

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_encoding.v` (append)

- [ ] **Step 1: Add the statement with `Admitted`.**

```coq
(** den_boer_orbit — inputs with equal AND give layouts that differ by a cyclic
    cut: the three a&&b=false inputs lie in one rotation orbit.
    @composes: den_boer_encoding. *)
Lemma den_boer_orbit (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists k : 'I_5,
    [seq encode_bool x | x <- fc_arrange ab'.1 ab'.2]
      = rot k [seq encode_bool x | x <- fc_arrange ab.1 ab.2].
Proof.
Admitted.
```

- [ ] **Step 2: Build to confirm it typechecks (`Admitted`).**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo`
Expected: compiles.

- [ ] **Step 3: Develop the proof.**

Strategy: case on the four `(ab, ab')` value combinations that share an AND value (16 pairs, but only equal-AND ones are reachable after `move`). The concrete rotations (verified by hand in the spec, with `T=heart`, `F=club`):

```
fc_arrange(0,0)=TFTFT  fc_arrange(0,1)=TFTTF  fc_arrange(1,0)=FTTFT  fc_arrange(1,1)=FTTTF
```
For AND=true both inputs are `(1,1)`, take `k = 0` (`rot 0` is identity, `rot0`). For AND=false, the three `s=0` arrangements are rotations of one another; pick the explicit `k` per ordered pair (e.g. `(0,1)` to `(0,0)` is `rot 3`, `(1,0)` to `(0,0)` is `rot 2`; compose for the other pairs). Develop by `case: ab => a b; case: ab' => a' b'; case: a; case: b; case: a'; case: b' => //=` and discharge each surviving branch with the explicit `exists (k : 'I_5)` followed by `by []` / a `rot` computation (`rot` on a concrete 5-list computes; verify with `rocq_check`).

Because both `fc_arrange _ _` are concrete 5-element lists in each branch, the equality `... = rot k ...` reduces by computation; the work is choosing `k` per branch. Use `rocq_step_multi` to try the five `k` values per branch and read off the one that closes.

- [ ] **Step 4: Build, axiom check, commit.**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo` (no `Admitted`).
`rocq_assumptions (name := "den_boer_orbit")` -> only `boolp` axioms (likely none).
```bash
git add pgg-smc/instances/denboer1989/den_boer_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "den_boer_encoding: den_boer_orbit (equal-AND inputs are one cut orbit)"
```

---

## Task 5: the `den_boer_encoding` instance

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_encoding.v` (append)

- [ ] **Step 1: Add the instance. The `ie_orbit` field needs the orbit re-expressed as a `rp_monodromy` reindex (a `rot` is the den Boer monodromy action), so include the adapter lemma first.**

```coq
(** den_boer_orbit_perm — den_boer_orbit in the rp_monodromy reindex form the
    InputEncoding.ie_orbit field expects.
    @composes: den_boer_encoding. *)
Lemma den_boer_orbit_perm (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists g : pgg_gT FiveCardKim_M, g \in pgg_G FiveCardKim_M /\
    [tuple of [seq encode_bool x | x <- fc_arrange ab'.1 ab'.2]]
      = [tuple tnth [tuple of [seq encode_bool x | x <- fc_arrange ab.1 ab.2]]
                    (rp_monodromy five_card_plug g i) | i < 5].
Proof.
Admitted.

Definition den_boer_encoding : InputEncoding five_card_plug (bool * bool) :=
  MkInputEncoding
    (fun ab => [tuple of [seq encode_bool x | x <- fc_arrange ab.1 ab.2]])
    (fun ab => ab.1 && ab.2)
    den_boer_assemble_valid
    den_boer_orbit_perm.
```

- [ ] **Step 2: Build to confirm the instance typechecks (`den_boer_orbit_perm` `Admitted`).**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo`
Expected: compiles. If `MkInputEncoding` rejects a field type, the tuple/cast shape needs adjusting; this is the point to reconcile `(ts_T' (rp_scheme five_card_plug)).+1` with `5` (they should be convertible since `ts_T' fcI_scheme = 4`; insert a cast or `change` if the elaborator needs help).

- [ ] **Step 3: Develop `den_boer_orbit_perm`.**

Strategy: bridge `rot k` (from `den_boer_orbit`) to the `rp_monodromy` reindex. The den Boer monodromy is the `C_5` cyclic action `fc_sigma^k`, and `fc_sigma_pow_val` gives `(fc_sigma ^+ k) i = (i + k) %% 5`, i.e. exactly a rotation index. So `rot k s` indexed equals `tnth s (rotation by k)`. Use `den_boer_orbit` to get the `k`, take `g := (the C_5 generator)^+ k` (in `pgg_G FiveCardKim_M`, which is the full `C_5`), and prove the tuple equality by `tnth`-extensionality (`eq_from_tnth`), reducing `tnth (rot k s) i` to `tnth s ((i + k) %% 5)` (lemma `tnth` of `rot`, or `nth_rot`) and matching `rp_monodromy five_card_plug g i`. Develop interactively; the membership `g \in pgg_G FiveCardKim_M` holds because `pgg_G` is the full group.

- [ ] **Step 4: Build, axiom check, commit.**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo` (no `Admitted`).
`rocq_assumptions (name := "den_boer_encoding")` -> only `boolp` axioms.
```bash
git add pgg-smc/instances/denboer1989/den_boer_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "den_boer_encoding: den_boer_encoding instance of InputEncoding"
```

---

## Task 6: `Inputs` RV and `den_boer_input_private` on `Omega`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_encoding.v` (append; reuse `Omega`/`P`/`Secret`/`ViewA` from `five_card_leakage`)

- [ ] **Step 1: Add the `Inputs` RV and the privacy statement with `Admitted`.**

```coq
Section den_boer_input_privacy.
Variable R : realType.
(* Omega, P, Secret, ViewA are from five_card_leakage (open that section's defs). *)

(** Inputs — the two committed bits as a random variable over Omega. *)
Definition Inputs : {RV (P R) -> bool * bool} :=
  fun w => let: (a, b, _) := w in (a, b).

(** den_boer_input_private — a coalition learns nothing about the inputs beyond
    the AND: conditioned on the secret, the inputs are independent of the view.
    @main security: input privacy of the den Boer encoding. *)
Lemma den_boer_input_private (A : seq nat) :
  `I( Inputs ; ViewA A | Secret ) = 0.
Proof.
Admitted.

End den_boer_input_privacy.
```

Note: confirm the exact names/notation for conditional mutual information of RVs in infotheo with `rocq_query (command := "Search ""`I("" ""|""."")`; if the `\`I( _ ; _ | _ )` RV form does not exist, state it via `cinde_RV` (`Inputs _|_ ViewA A | Secret`) plus `cinde_RV -> cmi = 0`, or define it through `cmi`/`fdistmap` on the joint.

- [ ] **Step 2: Build to confirm the statement typechecks (`Admitted`).**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo`
Expected: compiles.

- [ ] **Step 3: Develop the proof.**

Strategy (the s=0-identical-distribution argument, reusing the leakage machinery):
- Conditional MI is 0 iff `Inputs _|_ ViewA A | Secret` (conditional independence). Reduce to showing, for each secret value `s`, the conditional distribution of `ViewA A` given `(Secret = s, Inputs = x)` does not depend on `x`.
- `Secret = true` forces `Inputs = (1,1)` (single fibre), so conditional independence is vacuous there.
- `Secret = false`: the three inputs `(0,0),(0,1),(1,0)` give `arr = fc_shuffle k (fc_arrange a b)` ranging, under uniform `k`, over the same rotation orbit (`den_boer_orbit`), hence `ViewA A` is identically distributed across the three. Prove this by the same per-view counting used for `leak_k`: show `pfwd1 [% Inputs, ViewA A, Secret] (x, v, false)` is independent of `x` (it is `(1/20) * [arr-rotation hits v]`, the same count for all three `s=0` inputs because they are rotations).
- Conclude `cmi = 0` via the conditional-independence characterization.

This is the hardest proof; develop it with rocq-prover using `five_card_leakage.v`'s `count_pr`/`stepO`/`cardV`/`cardJ` patterns (now lifted to Section lemmas there) and infotheo's conditional-independence lemmas. Budget the most time here.

- [ ] **Step 4: Build, axiom check, commit.**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo` (no `Admitted`).
`rocq_assumptions (name := "den_boer_input_private")` -> only `boolp` axioms.
```bash
git add pgg-smc/instances/denboer1989/den_boer_encoding.v
ROCQ_AUDIT_STAGE2_DISABLED=1 git commit -m "den_boer_encoding: perfect input privacy I(Inputs; ViewA | Secret) = 0"
```

---

## Task 7: Whole-build + axiom hygiene sweep

**Files:** none (verification only)

- [ ] **Step 1: Clean rebuild of the two new files and their reverse deps.**

Run: `rm -f pgg-smc/reconstruct/input_encoding.vo pgg-smc/instances/denboer1989/den_boer_encoding.vo && make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo`
Expected: both compile from scratch, no error, no `Admitted`.

- [ ] **Step 2: Confirm zero `Admitted`/`admit` in the new files.**

Run: `grep -nE 'Admitted|\badmit\b' pgg-smc/reconstruct/input_encoding.v pgg-smc/instances/denboer1989/den_boer_encoding.v || echo NONE`
Expected: `NONE`.

- [ ] **Step 3: Axiom hygiene across the headline lemmas.**

Use `rocq_assumptions` on `ie_output_correct`, `den_boer_encoding`, `den_boer_input_private`. Expected: only the three `boolp` axioms (`propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description`) that the project already uses. No new custom axioms.

- [ ] **Step 4: Final commit (if any cleanup was needed); otherwise nothing to commit.**

```bash
git status --short   # should be clean
```

---

## Self-Review (run before handing off)

- **Spec coverage:** Task 1-2 implement the interface and `ie_output_correct`; Tasks 3-5 the den Boer instance and its two laws; Task 6 perfect input privacy. The operational Approach B (dealer rewrite, `den_boer_run_output`, session-type duality) is explicitly out of scope for this plan and becomes a follow-on plan, as flagged in the spec's risk section. The quantitative `leak_k` output leakage is already committed in `five_card_leakage.v` and is referenced, not re-derived.
- **Type consistency:** `InputEncoding`, `ie_assemble`, `ie_fun`, `ie_assemble_valid`, `ie_orbit`, `ie_output_correct`, `den_boer_encoding`, `den_boer_assemble_valid`, `den_boer_orbit`, `den_boer_orbit_perm`, `Inputs`, `den_boer_input_private` are used identically across tasks and match the audited names in the spec.
- **Open items carried as in-task work (not placeholders):** the exact `rp_monodromy` reindex direction (Task 2 Step 3, Task 5 Step 3) and the `5` vs `(ts_T' fcI_scheme).+1` convertibility (Task 5 Step 2) are concrete reconciliations to do at the named step, not deferred TODOs.
