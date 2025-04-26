From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_entropy smc_interpreter.
Require Import scalar_product_program scalar_product_proof.
Require Import scalar_product_interpreter.

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_interpreter.

(******************************************************************************)
(*                                                                            *)
(*   For Connecting the Zn-to-Z2 Protocol and the SMC Interpreter             *)
(*                                                                            *)
(*   Previous Zn-to-Z2 is a global view implementation, no parties and        *)
(*   communications like in the SMC interpreter model. In this file           *)
(*   we introduce the same model for the Zn-to-Z2 protocol.                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section znto_program.
  
Variable n m : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Local Notation "u *d w" := (scp.dotproduct u w).

Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

Definition palice (xa : VX) :=
  Init xa (
  ScalarProduct alice bob xa (fun y =>
  ScalarProduct alice bob (xa+xa) (fun y =>
  Finish))).

Definition pbob (xb : VX) :=
  Init xb (
  ScalarProduct bob alice xb (fun y =>
  ScalarProduct bob alice (xb+xb) (fun y =>
  Finish))).

Variables (xa xb : VX) (sa1 sa2 sb1 sb2 : VX)(ra1 ra2 yb1 yb2 : TX).
Let smc_program := interp sa1 sa2 sb1 sb2 ra1 ra2 yb1 yb2 11 [:: palice xa; pbob xb] [::[::]].

Goal smc_program = ([::Finish; Finish], [::]).
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results /=.
Abort.

Definition sig_smc_program : {trace | smc_program =
  ([:: Finish; Finish], trace)}.
Proof.
eexists.
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results [LHS]/=.
abstract reflexivity.
Defined.

Eval simpl in sval sig_smc_program.

Lemma smc_program_ok : smc_program = 
  ([:: Finish; Finish],
   [::
       [:: out ((xa + xa + sa1) *d (xa + xa) + (sa1 *d sb1 - ra1) -
                 yb1 - (xa + xa + sb1) *d sa1 + ra1,
               yb1);
           out ((xa + sa1) *d xb + (sa1 *d sb1 - ra1) -
                 yb1 - (xb + sb1) *d sa1 + ra1,
               yb1); 
           inp xa];
       [:: out ((xa + xa + sa2) *d (xa + xa) + (sa2 *d sb2 - ra2) -
                 yb2 - (xa + xa + sb2) *d sa2 + ra2,
               yb2);
           out ((xa + sa2) *d xb + (sa2 *d sb2 - ra2) -
                 yb2 - (xb + sb2) *d sa2 + ra2,
               yb2); 
           inp xb]]).
Proof.
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results [LHS]/=.
reflexivity. Qed.

End znto_program.
