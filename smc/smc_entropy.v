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
Local Open Scope chap2_scope.

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
Search cond_entropy.
About cond_entropy1_RV.

Let d1 := (`p_ [%Y2, YmZ] `x `p_ Y1).
Let d2 := (`p_ Y2 `x `p_ Y1).

Hypothesis H0 : `Pr[ [%YmZ, Y2] = (ymz, y2) ] != 0.


Theorem mc_removal_entropy :
  cond_entropy1_RV [%Y2, YmZ] Y1 (y2, ymz) =
  cond_entropy1_RV Y2 Y1 y2.
Proof.
rewrite /cond_entropy1_RV.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have:=(@mc_removal_pr _ _ _ _ P n X Z f1 f2 fm pZ_unif Z_X_indep a y2 ymz H0).
rewrite -/Y1 -/Y2 -/YmZ.
rewrite cinde_alt.
Abort.

End theorem_3_7.
  

Section pr_entropy.

Variables (T TW TV1 TV2: finType) (P : R.-fdist T).
Variable n : nat.
Notation p := n.+1.
Variables (W: {RV P -> TW}) (V1: {RV P -> TV1}) (V2: {RV P -> 'I_p}).

(* Cannot use fdist_uniform (#|TV2|) (TV2 could be empty if it is arbitrary finType. *)
Variable pV2_unif : `p_ V2 = fdist_uniform (card_ord p).
Hypothesis V1V2indep : P|= V1 _|_ V2.

Lemma cpr_cond_entropy1_RV v1 v2:
  (forall w ,
  `Pr[ W = w | V1 = v1 ] = `Pr[ W = w | [%V1, V2] = (v1, v2) ]) ->
  cond_entropy1_RV V1 W v1 = cond_entropy1_RV [% V1, V2] W (v1, v2). 
Proof.
move => H.
case /boolP : ((`p_ [% V1, W])`1 v1 == 0)  => Hv1.
  rewrite /cond_entropy1_RV.
  rewrite /entropy.
  congr -%R.
  apply:eq_bigr => a _.
  (*rewrite jfdist_condE. -- it brings `(fdistmap [% V1, V2, W] P)`1 (v1, v2) != 0%coqR` so we cannot use it*)
  rewrite /jfdist_cond.
  have Hv2: ((`p_ [% V1, V2, W])`1 (v1, v2) == 0).
    rewrite fst_RV2.
    apply/eqP.
    move:(@Pr_domin_setX TV1 'I_p (`p_ [%V1, V2]) [set v1] [set v2]).
    rewrite !Pr_set1.
    rewrite setX1.
    rewrite !Pr_set1.
    rewrite fst_RV2.
    apply.
    rewrite fst_RV2 in Hv1.
    exact/eqP. 
  destruct (boolP _).
    exfalso.
    by rewrite Hv1 in i. 
  destruct (boolP _).
    exfalso.
    by rewrite Hv2 in i0. 
  by rewrite !fdist_uniformE.

rewrite cond_entropy1_RVE //.
rewrite cond_entropy1_RVE; last first.
  rewrite fst_RV2.
  rewrite fst_RV2 in Hv1.
  rewrite -pr_eqE'.
  rewrite V1V2indep.
  rewrite !pr_eqE'.
  rewrite mulR_neq0'.
  rewrite Hv1 /=.
  rewrite pV2_unif.
  rewrite fdist_uniformE /=.
  rewrite card_ord.
  rewrite invr_eq0.
  by rewrite pnatr_eq0.

rewrite /cond_entropy1.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have -> // : \Pr_`p_ [% W, V1][[set a] | [set v1]] = \Pr_`p_ [% W, [%V1, V2]][[set a] | [set (v1, v2)]].
rewrite !jPr_Pr.
by rewrite !cpr_eq_set1.
Qed.

End pr_entropy.


End smc_entropy_proofs.