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

(* The uniform laws over VX and TX, built from spp_proof's cardinalities so
   the fdist_uniform proof term matches the record's uniformity fields. *)
Let unif_VX : R.-fdist VX := fdist_uniform (card_VX n m).
Let unif_TX : R.-fdist TX := fdist_uniform (card_TX m).

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
  ((((fdist1 xb) `x unif_VX) `x unif_VX) `x unif_TX) `x (fdist1 yb).

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
  `p_ [% s2, x1', r2] = (unif_VX `x unif_VX) `x unif_TX.
Proof.
have s2_x1'_indep : P |= s2 _|_ x1'.
  exact: (RV2_inde_RV_snd (x2s2_x1'_indepP inputs)).
have s2x1'_r2_indep : P |= [% s2, x1'] _|_ r2.
  have := x2s2x1'_r2_indep inputs.
  pose f := fun (v : (VX * VX * VX)%type) => let '(_, b, c) := v in (b, c).
  pose g := fun (w : TX) => w.
  by apply_inde_rv_comp f g.
have x1_s1_indep : P |= x1 _|_ s1.
  have H := x1_indep inputs.
  rewrite inde_RV_sym in H.
  move: H.
  pose f := fun (vs : (VX * VX * VX * TX * TX)%type) =>
    let '(_, sa, _, _, _) := vs in sa.
  pose g := fun (ws : VX) => ws.
  by apply_inde_rv_comp g f.
have s1_s2_indep : P |= s1 _|_ s2.
  have := s2_indep inputs.
  pose f := fun (vs : (VX * VX * VX * TX * TX)%type) =>
    let '(_, sa, _, _, _) := vs in sa.
  pose g := fun (ws : VX) => ws.
  by apply_inde_rv_comp f g.
have s1s2_r1_indep : P |= [% s1, s2] _|_ r1.
  have := r1_indep inputs.
  pose f := fun (vs : (VX * VX * VX * TX * VX)%type) =>
    let '(_, sa, _, _, sb) := vs in (sa, sb).
  pose g := fun (ws : TX) => ws.
  by apply_inde_rv_comp f g.
have px1'_unif : `p_ x1' = fdist_uniform (card_VX n m).
  exact: (add_RV_unif x1 s1 (card_VX n m) (ps1_unif inputs) x1_s1_indep).
have pr2_unif : `p_ r2 = fdist_uniform (card_TX m).
  exact: (ps1_dot_s2_r_unif (pr1_unif inputs) s1_s2_indep s1s2_r1_indep).
rewrite (dist_inde_rv_prod s2x1'_r2_indep) (dist_inde_rv_prod s2_x1'_indep).
by rewrite (ps2_unif inputs) px1'_unif pr2_unif /unif_VX /unif_TX.
Qed.

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
