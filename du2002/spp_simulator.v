From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid spp_proba spp_entropy.
Require Import smc_interpreter spp_tactics smc_session_types.
Require Import spp_interface spp_program spp_pismc spp_proof.

(******************************************************************************)
(*                                                                            *)
(* Simulator object for the SPP privacy triangle (corrupted Bob).             *)
(*                                                                            *)
(* ```                                                                        *)
(* bob_simulator xb yb == the law a simulator produces from Bob's inputs      *)
(*                        (xb, yb): Dirac xb (x) uniform (x) uniform (x)      *)
(*                        uniform (x) Dirac yb, left-nested to match BobView  *)
(* bob_ext            == projection of a BobView value onto (x2, y2)          *)
(* ```                                                                        *)
(*                                                                            *)
(* Mechanizes the on-paper (o) steps of fig:infotheo:spp-triangle (Bob side). *)
(*                                                                            *)
(******************************************************************************)

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

Section bob_simulator_def.

Context {R : realType}.
Variables (T : finType) (m n : nat).
Variable P : R.-fdist T.

Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Notation "u \*d w" := (dotproduct_rv u w).

Lemma card_TX : #|TX| = m.+2.
Proof. by rewrite card_ord. Qed.

Let q := (m.+2 ^ n).-1.
Lemma card_VX : #|VX| = q.+1.
Proof. by rewrite prednK ?expn_gt0// /VX card_mx card_TX mul1n. Qed.

Variable inputs : scalar_product_random_inputs n m P.

Let x1 := x1 inputs.
Let x2 := x2 inputs.
Let s1 := s1 inputs.
Let s2 := s2 inputs.
Let r1 := r1 inputs.
Let y2 := y2 inputs.
Let x1' : {RV P -> VX} := x1 \+ s1.
Let r2  : {RV P -> TX} := (s1 \*d s2) \- r1.
Let BobView := [% x2, s2, x1', r2, y2].

(* R1: the simulator law, coordinate order (x2, s2, x1', r2, y2). *)
Definition bob_simulator (xb : VX) (yb : TX)
  : R.-fdist ((((VX * VX) * VX) * TX) * TX) :=
  ((((fdist1 xb) `x (fdist_uniform card_VX)) `x (fdist_uniform card_VX))
      `x (fdist_uniform card_TX)) `x (fdist1 yb).

(* R5: the extraction edge projects BobView onto Bob's inputs (x2, y2). *)
Definition bob_ext (v : (((VX * VX) * VX) * TX) * TX) : VX * TX :=
  (v.1.1.1.1, v.2).

Lemma bob_ext_ok : bob_ext \o BobView = [% x2, y2].
Proof. by apply/boolp.funext => t. Qed.

(* R2: the pad block is independent of Bob's inputs and the output share. *)
Lemma bob_pads_indep : P |= [% s2, x1', r2] _|_ [% x1, x2, y2].
Proof. Admitted.

(* R3: the pad block's law is a product of uniforms. *)
Lemma bob_pads_law :
  `p_ [% s2, x1', r2]
    = ((fdist_uniform card_VX) `x (fdist_uniform card_VX))
        `x (fdist_uniform card_TX).
Proof. Admitted.

(* R4: the view law conditioned on (x1, x2, y2) is the simulator law. *)
Lemma bob_view_cond_sim v a b y :
  `Pr[ [% x1, x2, y2] = (a, b, y) ] != 0 ->
  `Pr[ BobView = v | [% x1, x2, y2] = (a, b, y) ] = bob_simulator b y v.
Proof. Admitted.

(* R4': the view law conditioned on Bob's inputs (x2, y2) is the simulator. *)
Lemma bob_view_cond_sim_xy v b y :
  `Pr[ [% x2, y2] = (b, y) ] != 0 ->
  `Pr[ BobView = v | [% x2, y2] = (b, y) ] = bob_simulator b y v.
Proof. Admitted.

(* R6: the input-indexed commutation (the triangle equation). *)
Lemma bob_view_commute v a b :
  `Pr[ [% x1, x2] = (a, b) ] != 0 ->
  `Pr[ BobView = v | [% x1, x2] = (a, b) ]
    = \sum_(y in TX) `Pr[ y2 = y ] * bob_simulator b y v.
Proof. Admitted.

End bob_simulator_def.
