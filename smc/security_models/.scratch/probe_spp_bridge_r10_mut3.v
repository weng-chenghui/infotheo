(* Mutation 3 of probe_spp_bridge_r10.v: the factorization feeds the
   simulator Bob's output share shifted by one.  coqc must exit 1.        *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid spp_proba spp_entropy.
Require Import smc_interpreter spp_tactics smc_session_types.
Require Import spp_interface spp_program spp_pismc spp_proof spp_simulator.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope vec_ext_scope.

Section bridge_shape.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (B K : finType).
Variable V : {RV P -> B}.
Variable Kv : {RV P -> K}.
Variable k : K -> R.-fdist B.

Lemma dist_of_RV_bind :
  (forall kk : K, `Pr[ Kv = kk ] != 0 ->
     forall v : B, `Pr[ V = v | Kv = kk ] = k kk v) ->
  `p_ V = `p_ Kv >>= k.
Proof.
move=> H; apply/fdist_ext => v.
rewrite fdistbindE -(fst_RV2 V Kv) fdist_fstE.
apply: eq_bigr => kk _; rewrite !dist_of_RVE.
case: (eqVneq `Pr[ Kv = kk ] 0) => [Hz|Hnz].
  by rewrite Hz mul0r pfwd1_domin_RV1.
by rewrite -H // cpr_eqE mulrC divfK.
Qed.

End bridge_shape.

Section spp_bob_bridge.
Context {R : realType}.
Variables (T : finType) (m n : nat).
Variable P : R.-fdist T.

Let TX := [the finComNzRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Variable inputs : scalar_product_random_inputs n m P.

Let x1 := x1 inputs.
Let x2 := x2 inputs.
Let s1 := s1 inputs.
Let s2 := s2 inputs.
Let r1 := r1 inputs.
Let y2 := y2 inputs.
Let x1' : {RV P -> VX} := x1 \+ s1.
Let r2 : {RV P -> TX} := (s1 \*d s2) \- r1.
Let BobView := [% x2, s2, x1', r2, y2].

(* MUTATION: bob_simulator ay.1 (ay.2 + 1) in place of bob_simulator
   ay.1 ay.2. *)
Theorem spp_bob_factorization :
  `p_ BobView = `p_ [% x2, y2] >>= (fun ay => bob_simulator ay.1 (ay.2 + 1)).
Proof.
apply: dist_of_RV_bind => -[b y] Hby v.
exact: bob_view_cond_sim_xy Hby.
Qed.

End spp_bob_bridge.
