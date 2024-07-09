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
  

Section pr_entropy.

Variables (T: finType) (P : R.-fdist T).
Variables (X Y W1 W2 V1 V2: {RV P -> T}).
Variables (x y : T).

Let E := finset (X @^-1 x).
Hypothesis E0 : Pr P E != 0.
Let PYX := fdist_cond E0.
Variable (Y': {RV (fdist_cond E0) -> T}).
Hypothesis EX' : Y' = Y.

Check Ex P (neg_RV (log_RV P)). (* how the H = E defined in infotheo; no RV required *)
Fail Check cEx Y [set x]. (* Won't work because Y is a RV_of T instead of RV_of R (required by cEx because of `log` requires it. )*)

Variables (A B : finType) (QP : {fdist B * A}).

(* H(Y|X = x), see eqn 2.10 *)
Definition cond_entropy1' a := - \sum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Print cond_entropy1.

Let P' := QP`2.

Lemma cond_entropy1_RV_Ex:
  `H( Y | X ) = `E (`-- (`log PYX)).
Proof.
rewrite /cond_entropy /cond_entropy1.
rewrite /log_RV /=.
Search (\sum_( _ in _ ) _).
idtac. (* no-op *)
  

Variables (T: finType) (P : R.-fdist T).
Variables (W V1 V2: {RV P -> T}).

Lemma cpr_cond_entropy1_RV v1 v2:
  (forall w ,
  `Pr[ W = w | V1 = v1 ] = `Pr[ W = w | V2 = v2 ]) ->
  cond_entropy1_RV V1 W v1 = cond_entropy1_RV V2 W v2. 
Proof.
move => H.
rewrite !cond_entropy1_RVE.
rewrite /cond_entropy1.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have -> // : \Pr_`p_ [% W, V1][[set a] | [set v1]] = \Pr_`p_ [% W, V2][[set a] | [set v2]].
rewrite !jPr_Pr.
by rewrite !cpr_eq_set1.
rewrite /cPr in H.
rewrite fst_RV2.
assert (Hv2 := H).
(* forall blocks rewrite and no eq_bigr style tool for `under`*)
specialize (Hv2 v2).
rewrite !cpr_eqE in Hv2.
rewrite pr_eq_ge0 in Hv2.
rewrite pr_eq in Hv2.

(*

  negb (eq_op (dist_of_RV V2 v2) 0%coqR)

*)

rewrite /cpr_eq in H.
Admitted.

Lemma cpr_cond_entropy1_RV v1 v2:
 (`p_ [% V2, W1])`1 v2 != 0%coqR ->
 (`p_ [% V1, W1])`1 v1 != 0%coqR ->
  (forall w1 ,
  `Pr[ W1 = w1 | V1 = v1 ] = `Pr[ W1 = w1 | V2 = v2 ]) ->
  cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W1 v2. 
Proof.
move => Hv1 Hv2 H.
rewrite !cond_entropy1_RVE.
rewrite /cond_entropy1.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have -> // : \Pr_`p_ [% W1, V1][[set a] | [set v1]] = \Pr_`p_ [% W1, V2][[set a] | [set v2]].
rewrite !jPr_Pr.
by rewrite !cpr_eq_set1.
Admitted.

Section pr_entropy_expectation.
  

Variables (T: finType) (P : R.-fdist T).
Variables (X Y W1 W2 V1 V2: {RV P -> T}).
Variables (x y : T).

Let E := finset (X @^-1 x).
Hypothesis E0 : Pr P E != 0.
Let PYX := fdist_cond E0.
Variable (Y': {RV (fdist_cond E0) -> T}).
Hypothesis EX' : Y' = Y.

Check Ex P (neg_RV (log_RV P)). (* how the H = E defined in infotheo; no RV required *)
Fail Check cEx Y [set x]. (* Won't work because Y is a RV_of T instead of RV_of R (required by cEx because of `log` requires it. )*)

Variables (A B : finType) (QP : {fdist B * A}).

(* H(Y|X = x), see eqn 2.10 *)
Definition cond_entropy1' a := - \sum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Unset Printing Notations.
Print cond_entropy1.

Let P' := QP`2.

(*eqn 2.11 *)
Definition cond_entropy' := \sum_(a in A) P' a * cond_entropy1' a.
(*
   \Pr_QP [ [set b] | [set a] ]: means `p(y|x)` in the book.
   --> jcPr QP (set1.body b) (set1.body a)

   QP`2: means `p(x)` in the book, in 2.11.
   QP: means `p(x, y)` in the book.
*)



(*eqn 2.13 *)
Lemma cond_entropy1_RV_Ex:
  `H( Y | X ) = `E (`-- (`log PYX)).
Proof.
rewrite /cond_entropy /cond_entropy1.
rewrite /log_RV /=.
rewrite big_morph_oppR.


`H P = `E (`-- (`log P)).


Search cond_entropy.
About entropy_Ex.
About cond_entropyE.

Lemma entropy_Ex_RV : `H X

(* 2.3 from Elements of Information Theory *)
Lemma eq_H_Ex :
  entropy P = Ex P (log \o GRing.inv \o W1).
Proof.
rewrite //.
rewrite /entropy.
rewrite /Ex.

End pr_entropy_expectation.


Lemma tryv1v2 v1 v2:
(`p_ [% V2, W1])`1 v2 != 0%coqR -> cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W1 v2.


Lemma tryv1v2 v1 v2:
  (forall i : T,  `p_ [% V2, W1] (v2, i) >= 0) ->
  (forall w1 ,
  `Pr[ W1 = w1 | V1 = v1 ] = `Pr[ W1 = w1 | V2 = v2 ]) ->
  cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W1 v2. 
Proof.
move => H0 H.
have [Heq0|] := eqVneq ((`p_ [% V2, W1])`1 v2) 0%coqR.
rewrite /cond_entropy1_RV.
rewrite /entropy.
rewrite fdist_fstE in Heq0.
congr -%R.
apply:eq_bigr => a _.
rewrite !jfdist_condE.
rewrite !jPr_Pr.
rewrite !cpr_eq_set1.
About big_nil.


(*

  Heq0 :
   eq
    (bigop.body GRing.zero (index_enum T) (fun i : T =>
      BigBody i GRing.add (in_mem i (mem T)) (dist_of_RV (RV2 V2 W1) (pair v2 i))))
        0%coqR


  eq
    (Rmult (jfdist_cond (dist_of_RV (RV2 V1 W1)) v1 a)
       (log (jfdist_cond (dist_of_RV (RV2 V1 W1)) v1 a)))
    (Rmult (jfdist_cond (dist_of_RV (RV2 V2 W1)) v2 a)
       (log (jfdist_cond (dist_of_RV (RV2 V2 W1)) v2 a)))



*)

Lemma tryv1v2 v1 v2:
  (forall i : T,  `p_ [% V2, W1] (v2, i) >= 0) ->
  (forall w1 ,
  `Pr[ W1 = w1 | V1 = v1 ] = `Pr[ W1 = w1 | V2 = v2 ]) ->
  cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W1 v2. 
Proof.
move => H0 H.
case:(boolP ( ((`p_ [% V2, W1])`1 v2)==0%coqR)) => Heq0.
rewrite /cond_entropy1_RV.
rewrite /entropy.
(* Summation form of the marginal prob of fst in the joint dist *)
rewrite fdist_fstE in Heq0.
rewrite psumr_eq0 in Heq0.
congr -%R.
apply:eq_bigr => a _.

Lemma tryv1v2 v1 v2:
  (forall i : T,  `p_ [% V2, W1] (v2, i) >= 0) ->
  (forall w1 ,
  `Pr[ W1 = w1 | V1 = v1 ] = `Pr[ W1 = w1 | V2 = v2 ]) ->
  cond_entropy1_RV V1 W1 v1 = cond_entropy1_RV V2 W1 v2. 
Proof.
move => H0 H.
have [Heq0|] := eqVneq ((`p_ [% V2, W1])`1 v2) 0%coqR.
rewrite /cond_entropy1_RV.
rewrite /entropy.
rewrite fdist_fstE in Heq0.
congr -%R.
apply:eq_bigr => a _.
Fail rewrite psumr_eq0P in Heq0.
Undo 5.

Search jfdist_cond.




rewrite !jcPrE.
rewrite -!cpr_eq_setE.
rewrite !cpr_eq_set1.
rewrite !cpr_eqE.
rewrite !pr_eqE.
rewrite /dist_of_RV.
rewrite /Pr.
under eq_bigr do rewrite !fdistmapE.
Search "cpr_".
About Ex.
Abort.
apply (f_equal log) in H.


 
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
