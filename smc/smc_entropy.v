From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                              SMC Proofs in entroy                          *)
(*     From: Information-theoretically Secure Number-product Protocol         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Module smc_entropy_proofs.

Section theorem_3_7.

Variables (T TX TY1 TY2: finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X: {RV P -> TX}) (Z : {RV P -> 'I_p}).
Variables (f1 : TX -> TY1) (f2 : TX -> TY2) (fm : TX -> 'I_p). 
Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_X_indep : inde_rv Z X.
Variables (y1 : TY1) (y2 : TY2) (ymz : 'I_p).

Let Y1 := f1 `o X.
Let Y2 := f2 `o X.  (* y2...ym-1*)
Let Ym := fm `o X.
Let YmZ := Ym `+ Z.
Let f x := (f1 x, f2 x, fm x).
Let Y := f `o X.

Check cond_entropy.
Search RV2.


(* H(Y|X = x) = cond_entropy R.-fdist(B * A) *)
(* What we want: H(Y1|[%Y2,YmZ])*)
(* cond_entropy : forall A B : finType, R.-fdist(B * A) -> R *)

About cond_entropy.

Let d1 := (`p_ [%Y2, YmZ] `x `p_ Y1).
Let d2 := (`p_ Y2 `x `p_ Y1).


Hypothesis H0 : `Pr[ [%YmZ, Y2] = (ymz, y2) ] != 0.

Check H0.

Check (mc_removal_pr f1 pZ_unif Z_X_indep y1 H0).

Theorem mc_removal_entropy :
  cond_entropy d1 = cond_entropy d2.
Proof.
rewrite /cond_entropy.
apply:eq_bigr => a _.
rewrite !coqRE.
rewrite /cond_entropy1.
(* TODO: At a point, after unfolding enough, we need to apply mc_removal_pr*)

End theorem_3_7.
End smc_entropy_proofs.
