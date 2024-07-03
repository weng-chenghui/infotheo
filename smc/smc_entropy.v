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
  
Section pr_entropy.
  
Variables (T: finType) (P : R.-fdist T).
Variables (W1 W2 V1 V2: {RV P -> T}).

Lemma eq_cpr_cond_entropy1_RV w1 w2 v1 v2:
  `Pr[ W1 = w1 | V1 = v1 ] = `Pr[ W2 = w2 | V2 = v2 ] <->
  cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W2 v2. 
Proof.
split.
move => Hpr.
rewrite /cond_entropy1_RV.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
(* NOTE: From

2.20 of Elements of Information Theory,

It seems that conditional entropies and conditional probabilities
of random variables can be exchanged by injecting or removing `log`.


So I suspect that this lemma can be done in the same way.

The problem is: conditional entropy is defined by jfdist_cond,
which I need to find a way to pack it back to the random variable form so this simple `log` method could work.



*)
(* TODO: need the relation between jdist_cond and dist_of_RV *)
Search jfdist_cond.
Search ({RV (_) -> (_)} -> R.-fdist_).

 
End pr_entropy.

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

(*

`Pr[ Y1 = a | YmZ = ymz ] = `Pr[ Y1 = a | Y2 = y2 ] ->


so goal is to prove Y1 _|_ YmZ /\ Y1 _|_ Y2.
(equally, Y1 _|_ (Y2, YmZ) ).
*)


End theorem_3_7.
End smc_entropy_proofs.
