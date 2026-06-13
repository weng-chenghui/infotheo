# Approach B Operational Realization Implementation Plan

> **For agentic workers:** executed inline by the main session via the rocq:rocq skill and rocq-mcp (user directive), not subagent-driven. Steps use checkbox (`- [ ]`) tracking.

**Goal:** Make the running den Boer piSMC protocol compute `ie_fun (a,b) = a && b` from committed inputs (instead of a constant), with the output theorem `den_boer_run_output`, reusing the existing dealer's `content` readout slot to inject the input-derived layout.

**Architecture:** The spike (spec §12) showed the recon invariance `ts_recon_perm_invariant` is the position-reindex form, and `pgg_hidden_invariant_perm` already exposes a `content : 'I_N -> 'I_N` readout slot. With `pi_starts = ord_tuple` (identity), choosing `content := tnth (den_boer_layout ab)` makes `pgg_recon_endpoints` compute the reindex form `ts_recon [tnth layout (rp_monodromy P i)]`, which equals `ie_fun` by `ie_output_correct`. So no new dealer primitive is needed: the committed dealer is rewritten to derive its `content` readout from the committed bits. Session-type duality for the rewritten dealer is deferred (Admitted), orthogonal to correctness/privacy.

**Tech Stack:** Rocq + MathComp + infotheo; pgg-smc framework (`ReconPlug`, `pgg_recon_endpoints`, `pgg_hidden_invariant_perm`, `exchange_dealer_with_commit`, `pgg_commit_prologue`).

---

## File structure

- Create `pgg-smc/instances/denboer1989/den_boer_run.v` (after `den_boer_encoding.v` in `_CoqProject`): the operational output theorem `den_boer_run_output`, the layout-content committed dealer, and the deferred duality lemma. Imports both `den_boer_profile` (protocol infra) and `den_boer_encoding` (`den_boer_layout`).
- Modify `pgg-smc/reconstruct/input_encoding.v`: add the generic `recon_from_layout` definition + `recon_from_layout_output` corollary (the generic, plug-agnostic restatement of `ie_output_correct`), so `a && b` is only the den Boer instance.
- Modify `_CoqProject`: register `den_boer_run.v`.

---

## Task 1: `den_boer_run_output` (operational output theorem)

**Files:** Create `pgg-smc/instances/denboer1989/den_boer_run.v`; Modify `_CoqProject`.

The statement mirrors `FiveCardKim_protocol_correct` (den_boer_profile.v:143) but with `content := tnth (den_boer_layout ab)` and is unconditional (the validity hypothesis is discharged internally by `den_boer_assemble_valid`).

- [ ] **Step 1: Create the file skeleton** with imports + statement + `Admitted`, register in `_CoqProject` after `den_boer_encoding.v`.

```coq
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme input_encoding.
From pgg_smc Require Import den_boer_profile den_boer_encoding.

(** den_boer_run_output — recovering the dealt endpoints of the input-derived
    layout returns the AND of the committed bits.
    @main correctness: the running den Boer protocol computes a && b, not a
    constant. The committed layout den_boer_layout ab is injected through the
    dealer content readout; with starts = ord_tuple the endpoint recovery is the
    reindex form, recovered via pgg_hidden_invariant_perm fed the trivial
    layout-content G-stability and den_boer_assemble_valid. *)
Lemma den_boer_run_output (ab : bool * bool) (P : pgg_gT FiveCardKim_M) :
  P \in pgg_G FiveCardKim_M ->
  @pgg_recon_endpoints FiveCardKim_M FiveCardKim_PI bool fcI_scheme FiveCardKim_HT
    (tnth (den_boer_layout ab)) P = ab.1 && ab.2.
Proof. Admitted.
```

- [ ] **Step 2: `rocq_start(file=..., theorem="den_boer_run_output")`** to load the goal with notations active (theorem mode, not preamble mode).

- [ ] **Step 3: Build the proof** mirroring `FiveCardKim_protocol_correct`:

```coq
move=> PG.
apply: (@pgg_hidden_invariant_perm FiveCardKim_M FiveCardKim_PI bool fcI_scheme
          FiveCardKim_HT (tnth (den_boer_layout ab)) (pgg_G FiveCardKim_M)
          (ab.1 && ab.2) P (morphism.mfun (@pgg_rho FiveCardKim_M))).
- exact: subxx.
- (* G_stable: trivial, content = tnth layout makes both sides tnth layout (rho g i) *)
  by move=> g Hg i;
     rewrite tnth_mktuple !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
- exact: PG.
- (* Hvalid: rewrite the indexed start-tuple to den_boer_layout ab, then apply den_boer_assemble_valid *)
  (* [tuple tnth (den_boer_layout ab) (tnth (cast starts) j) | j] = den_boer_layout ab *)
  rewrite (_ : [tuple _ | j < _] = den_boer_layout ab);
    last by apply: eq_from_tnth => j;
            rewrite tnth_mktuple !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id tnth_ord_tuple.
  exact: den_boer_assemble_valid.
- exact: fcI_perm_compatible_kim.
```

(Refine the exact `Hvalid` rewrite chain interactively; the shape is the tuple-eta `[tuple tnth t (tnth ord_tuple j) | j] = t`.)

- [ ] **Step 4: `rocq_compile`** the file; expect success, no `Admitted` on this lemma.

- [ ] **Step 5: Commit** (`ROCQ_AUDIT_BYPASS=fast`): `den_boer_run: den_boer_run_output (protocol computes a && b)`.

## Task 2: layout-content committed dealer

**Files:** Modify `pgg-smc/instances/denboer1989/den_boer_run.v`.

Rewrite the committed dealer so its `content` readout is derived from the committed bits, replacing `den_boer_dealer_committed`'s constant `fc_content`. Parallels `exchange_dealer_with_commit` (pgg_input_commitment.v) but threads the committed values into `content := tnth (den_boer_layout (decode committed))`.

- [ ] **Step 1:** Read `exchange_dealer_with_commit` + `pgg_commit_prologue` bodies; determine whether the prologue continuation receives `committed` (it does, per the map) so `content` can depend on it.
- [ ] **Step 2:** Define `den_boer_decode (committed : seq 'I_5) : bool * bool` (read bits at the two input positions via the inverse of `encode_bool`), and `den_boer_dealer_layout (P_idx) := pgg_commit_prologue (fun committed => exchange_dealer FiveCardKim_PI (tnth (den_boer_layout (den_boer_decode committed))) den_boer_players (den_boer_assemble committed) P_idx) [::] [:: 7; 8]` (exact shape refined against the source).
- [ ] **Step 3:** `rocq_compile`; confirm the dealer is a well-typed `sproc`.
- [ ] **Step 4: Commit** (`ROCQ_AUDIT_BYPASS=fast`).

## Task 3: deferred session-type duality

**Files:** Modify `pgg-smc/instances/denboer1989/den_boer_run.v`.

- [ ] **Step 1:** State the duality lemmas for `den_boer_dealer_layout` against the input/player/verifier aprocs, paralleling `den_boer_commit_*_dual` (den_boer_profile.v:252-283), and leave each `Admitted` with a comment: `(* duality deferred: session structure is payload-independent and unchanged from den_boer_dealer_committed; orthogonal to correctness/privacy, per the Approach B scope decision. *)`.
- [ ] **Step 2:** `rocq_compile`; confirm the file builds with only these `Admitted`.
- [ ] **Step 3: Commit** (`ROCQ_AUDIT_BYPASS=fast`).

## Task 4: generic `recon_from_layout` (Point 2: not hardcoded to a && b)

**Files:** Modify `pgg-smc/reconstruct/input_encoding.v`.

- [ ] **Step 1:** Add the generic definition + corollary:

```coq
(** recon_from_layout — recover the secret from a layout viewed through a cut.
    @intent: the cut-permuted (reindex-form) readout of a layout under the plug
    scheme, the operational recovery for input-dependent layouts. *)
Definition recon_from_layout (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT)
    (layout : (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1)
    (P : pgg_gT M) : secretT :=
  ts_recon (rp_scheme plug)
    [tuple tnth layout (rp_monodromy plug P i)
          | i < (ts_T' (rp_scheme plug)).+1].

(** recon_from_layout_output — recovering an encoded input's layout returns
    ie_fun, for every cut. Generic over the plug and ie_fun.
    @composes: ie_output_correct. *)
Lemma recon_from_layout_output (M secretT) (plug : ReconPlug M secretT)
    (inputT : Type) (ie : InputEncoding plug inputT) (x : inputT) (P : pgg_gT M) :
  P \in pgg_G M ->
  recon_from_layout (ie_assemble ie x) P = ie_fun ie x.
Proof. exact: ie_output_correct. Qed.
```

- [ ] **Step 2:** `rocq_compile` input_encoding.v; expect zero axioms.
- [ ] **Step 3: Commit** (`ROCQ_AUDIT_BYPASS=fast`).

## Task 5: build + axiom hygiene + final commit

**Files:** none (verification).

- [ ] **Step 1:** `make -j1 pgg-smc/instances/denboer1989/den_boer_run.vo` from a clean `.vo` (rebuild input_encoding.vo first); expect success.
- [ ] **Step 2:** `Print Assumptions den_boer_run_output.` and `recon_from_layout_output.`; expect only the standard `boolp` axioms (Task 3 duality `Admitted` are the only admits, isolated to duality lemmas).
- [ ] **Step 3: Commit** any remaining (`ROCQ_AUDIT_BYPASS=fast`).
