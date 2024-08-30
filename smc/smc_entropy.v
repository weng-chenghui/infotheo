From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc graphoid.

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
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Module smc_entropy_proofs.

  
Section extra_pr.

Variables (T TX TY: finType).
Variable P : R.-fdist T.

Lemma fst_RV2_neq0 (X : {RV P -> TX}) (Y : {RV P -> TY}) x y:
  `Pr[[%X, Y] = (x, y)] != 0 -> `Pr[ X = x] != 0.
Proof.
apply: contra => /eqP /pr_eq_domin_RV2 H.
by apply/eqP.
Qed.


End extra_pr.
  
Section entropy_with_indeRV.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.

Lemma inde_rv_alt (X : {RV P -> TX}) (Y : {RV P -> TY}):
  inde_rv X Y <-> forall x y,`p_ [%X, Y] (x, y) = `p_ X x * `p_ Y y.
Proof.
rewrite /inde_rv.
split => H x y.
by rewrite -!pr_eqE'.
by rewrite !pr_eqE'.
Qed.
About boolp.eq_forall.

Lemma joint_entropy_indeRV (X : {RV P -> TX}) (Y : {RV P -> TY}):
  inde_rv X Y -> joint_entropy `p_[%X, Y] = `H (`p_X) + `H (`p_Y).
Proof.
rewrite /joint_entropy.
rewrite /entropy.
rewrite !coqRE.
transitivity (- (\sum_(a in TX) \sum_(b in TY) `p_ [% X, Y] (a, b) * log (`p_ X a * `p_ Y b))).
  congr (- _).
  rewrite pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log _).
  rewrite coqRE.
  by apply inde_rv_alt. (* cannot `apply: ` but can `apply `*)
transitivity (
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ X a))
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ Y b))).
  rewrite -[RHS]oppRB.
  congr (- _).
  rewrite -addR_opp.
  rewrite oppRK.
  rewrite -big_split /=. (* merge two \sum_a...\sum_a in RHS so we can apply eq_bigr*)
  apply eq_bigr => a _.
  rewrite -big_split /=.
  apply eq_bigr => b _.
  have [->|H0] := eqVneq (`p_ [%X, Y](a, b)) 0.
    rewrite !mul0r.
    by rewrite add0R.
  rewrite mulRC.
  rewrite logM //. (* from log (x*y) to log x + log y *)
  - by rewrite [LHS]mulRDr.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE' pr_eq_pairC coqRE.
    exact: fst_RV2_neq0.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE' coqRE.
    exact: fst_RV2_neq0.
(* From \sum_a \sum_b `p_ [%X, Y](a, b) to \sum_a `p_ X a*)
under eq_bigr do rewrite -big_distrl -fdist_fstE fst_RV2 /=.
congr (- _ - _).
rewrite exchange_big /=.
apply: eq_bigr => i _.
by rewrite -big_distrl -fdist_sndE snd_RV2 /=.
Qed.

End entropy_with_indeRV.

  
Section joint_entropyA.

Variables (A B C: finType) (P : {fdist A * B * C}).

Lemma joint_entropyA : `H P = `H (fdistA P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1.1, a.1.2, a.2) * log (P (a.1.1, a.1.2, a.2)))); last by case => -[].
rewrite -(pair_bigA _ (fun a1 a2 => P (a1.1, a1.2, a2) * log (P (a1.1, a1.2, a2)))) /=.
rewrite -(pair_bigA _ (fun a1 a2 => \sum_j P (a1, a2, j) * log (P (a1, a2, j)))) /=.
rewrite [RHS](eq_bigr (fun a => fdistA P (a.1, (a.2.1, a.2.2)) * log (fdistA P (a.1, (a.2.1, a.2.2))))); last by case => i [].
rewrite -(pair_bigA _ (fun a1 a2 => fdistA P (a1, (a2.1, a2.2)) * log (fdistA P (a1, (a2.1, a2.2))))) /=.
apply: eq_bigr => i _.
rewrite -(pair_bigA _ (fun a1 a2 => fdistA P (i, (a1, a2)) * log (fdistA P (i, (a1, a2))))) /=.
apply: eq_bigr => j _.
apply: eq_bigr => k _.
rewrite fdistAE //.
Qed.

End joint_entropyA.

Section pr_entropy.
  

Variables (T TW TV1 TV2: finType) (P : R.-fdist T).
Variable n : nat.
Notation p := n.+2.
Variables (W: {RV P -> TW}) (V1: {RV P -> TV1}) (V2: {RV P -> 'I_p}).

(* Cannot use fdist_uniform (#|TV2|) (TV2 could be empty if it is arbitrary finType. *)
Hypothesis pV2_unif : `p_ V2 = fdist_uniform (card_ord p).
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

Section lemma_3_8_prep.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ).
Let Z := f `o Y.

Section lemma_3_8_proof.
Variables (y : TY) (z : TZ).

Lemma pr_eq_ZY_Y :
  `Pr[ [% Z, Y] = (f y, y) ] = `Pr[ Y = y ].
Proof.
rewrite !pr_eqE.
congr (Pr P _).
apply/setP => t.
rewrite !inE.
rewrite xpair_eqE.
apply andb_idl => /eqP <- //.
Qed.

Hypothesis pr_Y_neq0 : `Pr[ Y = y ] != 0.
(* TODO tried to define it as `Pr[ Y = y ] > 0 and then use `Rlt_not_eq` in the proof,
   but this hypothesis would be wrapped by `is_true` that `Rlt_not_eq` cannot be applied directly. 
*)

(* H(f(Y)|X,Y) = H(f(Y)|Y) = 0 *)
(* Meaning: f(Y) is completely determined by Y.
   (Because `f` only has one input which is Y).

   And because it is completely determined by Y,
   `(X, Y)` won't increase the uncertanty.
*)
(*
  Search (`Pr[ _ = _ ])(`p_ _ _).
*)
Lemma fun_cond_entropy_eq0_RV :
  cond_entropy1_RV Y Z y = 0.
Proof.
(* If `Pr[Y = y] = 0, it makes the  \Pr_QP[[set b] | [set a]] zero because the condition will be never true; need to do this before the cond_entropy1RVE *)
(*
have [H|] := eqVneq (`Pr[ Y = y]) 0.
  rewrite /cond_entropy1_RV.
  rewrite /entropy.
  under eq_bigr => a _ .
    rewrite (_ : jfdist_cond _ _ _ = 0).
      rewrite mul0R.
      over.
    rewrite /jfdist_cond.
*)
rewrite cond_entropy1_RVE; last by rewrite fst_RV2 -pr_eqE'.
rewrite /cond_entropy1.
rewrite big1 -1?oppr0 // => i _.
have [<-|] := eqVneq (f y) i.
  set pZY := (X in (X * log X)%coqR).
  have HpZY: pZY = 1.
    rewrite /pZY.
    rewrite jPr_Pr.
    rewrite cpr_eq_set1.
    rewrite cpr_eqE.
    rewrite coqRE.
    rewrite pr_eq_ZY_Y //=.
    by rewrite divff //=.
  rewrite HpZY.
  rewrite log1.
  by rewrite mulR0.
move => Hfy_neq_i.
rewrite jPr_Pr.
rewrite cpr_eq_set1.
rewrite /Z.
(* Try to state that because `f y != i`,  `Pr[ (f `o Y) = i | Y = y ] = 0 *)
have ->: `Pr[ (f `o Y) = i | Y = y ] = 0.
  rewrite cpr_eqE.
  rewrite pr_eqE.
  rewrite (_: finset _ = set0).
    by rewrite Pr_set0 div0R. 
  apply/setP => t.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite /comp_RV.
  apply/negbTE /negP => /andP [] /[swap] /eqP ->.
  by apply/negP.
by rewrite mul0R.
Qed.

End lemma_3_8_proof.

Lemma fun_cond_entropy_ZY_eq0:
  `H( Z | Y) = 0.
Proof.
rewrite /cond_entropy.
rewrite big1 // => i _.
rewrite snd_RV2.
have [->|Hi] := eqVneq (`p_ Y i) 0.
  by rewrite mul0R.
rewrite -cond_entropy1_RVE ?fst_RV2 //.
by rewrite fun_cond_entropy_eq0_RV ?mulR0 // pr_eqE'.
Qed.

End lemma_3_8_prep.

Section fun_cond_entropy_proof.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ).
Let Z := f `o Y.

Local Open Scope ring_scope.
Variable (P': R.-fdist (TX * TY * TZ)).

Lemma fun_cond_removal :
  `H(X|[% Y, Z]) = `H(X| Y ).
Proof.
transitivity (joint_entropy `p_[%Y, Z, X] - entropy `p_[%Y, Z]). (* joint PQ = H P + cond QP*)
  apply/eqP.
  rewrite eq_sym.
  rewrite subr_eq.
  rewrite addrC.
  apply/eqP.
  have -> // : `p_[%X, [%Y, Z]] = fdistX `p_[%[%Y, Z], X].
    by rewrite fdistX_RV2.
  have -> // : `p_[%Y, Z] = (`p_ [%[%Y, Z], X])`1.
    by rewrite fst_RV2.
  rewrite -coqRE.
  by rewrite -chain_rule.
transitivity (joint_entropy `p_[%[%X, Y], Z] - entropy `p_[%Y, Z]). (* H(Y,f(Y),X) -> H(X,Y,f(Y))*)
  rewrite joint_entropyC.
  rewrite /joint_entropy.
  rewrite joint_entropyA.
  by rewrite fdistX_RV2 fdistA_RV3 .
transitivity (joint_entropy `p_[%X,Y] + cond_entropy `p_[%Z, [%X, Y]] - entropy `p_Y - cond_entropy `p_[%Z, Y]).
  rewrite [in LHS]chain_rule.
  rewrite !coqRE.
  rewrite fdistX_RV2.
  rewrite fst_RV2.
  rewrite -![in RHS]addrA.
  rewrite [RHS]addrCA.
  rewrite [RHS]addrC.
  rewrite [LHS]addrAC.
  congr (_ + _ + _).
  rewrite -opprD.
  congr (-_).
  have -> // : `p_[%Z, Y] = fdistX `p_[%Y, Z].
    by rewrite fdistX_RV2.
  have -> // : `p_Y = (`p_[%Y, Z])`1.
    by rewrite fst_RV2.
  exact:chain_rule.
transitivity (joint_entropy `p_[%X, Y] - entropy `p_Y).
  rewrite [LHS]addrAC.
  have -> // : cond_entropy `p_[%Z, Y] = 0.
    exact:fun_cond_entropy_ZY_eq0.
  have -> // : cond_entropy `p_[%Z, [%X, Y]] = 0.
    rewrite /Z.
    have -> // : f `o Y = (f \o snd) `o [%X, Y].
      by apply/boolp.funext => x //=.
    exact:fun_cond_entropy_ZY_eq0.
  by rewrite addrK.
rewrite joint_entropyC fdistX_RV2.
rewrite -/(joint_entropy `p_ [%Y, X]).
rewrite chain_rule coqRE.
rewrite fst_RV2 fdistX_RV2. 
rewrite addrAC.
by rewrite subrr add0r.
Qed.

End fun_cond_entropy_proof.

Section pi2.

Variable m : nat.
Let TX := [the finComRingType of 'I_m.+2]. (* not .+1: at least need 0 and 1 *)

Variables (T: finType).
Variable P : R.-fdist T.
Variable n : nat.

Variables (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Variables (y2 r1 r2 : {RV P -> TX}).

Definition dotproduct (a b:'rV[TX]_n) := (a *m b^T)``_ord0.
Definition dotproduct_rv (A B:{RV P -> 'rV[TX]_n}) := fun p => dotproduct (A p) (B p).

Local Notation "u *d w" := (dotproduct u w).
Local Notation "u \*d w" := (dotproduct_rv u w).

Let x1' : {RV P -> 'rV[TX]_n} := x1 \+ s1.
Let x2' : {RV P -> 'rV[TX]_n} := x2 \+ s2.

Let t : ({RV P -> TX}) := x1'\*d x2 \+ r2 \- y2.
Let y1 : ({RV P -> TX}) := t \- x2' \*d s1 \+ r1.


Section eq2_proof.

Let f : ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(x1, s1, r1, x2', t) := z in t - (x2' *d s1) + r1.

Lemma y1_fcomp :
  y1 = f `o [%x1, s1, r1, x2', t].
Proof. by apply boolp.funext. Qed.

Lemma eq2:
  `H(x2|[%[%x1, s1, r1, x2', t], y1]) = `H(x2|[%x1, s1, r1, x2', t]).
Proof. rewrite y1_fcomp. exact: fun_cond_removal. Qed.

End eq2_proof.

Section eq3_proof.
  
Notation p := m.+2.

About mc_removal_pr.

(* All random variables will be used here. *)
Let O := [%x1, x2, s1, s2, r1, r2].

(* f1 `o X in mc_removal_pr must be x2 in eq3 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in x2.

(* f2 `o X in mc_removal_pr must be (x1, s1, r1, x2 + s2) in eq3 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1, s1, r1, x2 + s2).

(* (fm `o X)+Z in mc_removal_pr must be t+(-y2) in eq3 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1 + s1) *d x2 + r2.

(* in mc_removal_pr they are named as Y1 Y2 Ym but we already have Y so renaming them. *)
Let Z := y2.
Let W1 := f1 `o O.  (* x2; It is okay in Alice's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x1, s1, r1, x2']; cannot have x2, s2, r2 here otherwise Alice knows the secret*)
Let Wm := fm `o O.
Let WmZ := Wm `+ Z. (* t; It should be (neg_RV y2) but neg_RV requires the domain is R, not TX*)

Variable Z_O_indep : inde_rv Z O.
Variable (w1 : 'rV[TX]_n) (w2 : 'rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) (wmz : 'I_p) .
Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).

Variable W2_WmZ_indep : P |= W2 _|_ WmZ.
Variable pWmZ_unif : `p_ WmZ = fdist_uniform (card_ord p).
            
Hypothesis Hneq0 : `Pr[ [%WmZ, W2] = (wmz, w2) ] != 0.

Lemma eq3:
  `H(x2|[%[%x1, s1, r1, x2'], t]) = `H(x2|[%x1, s1, r1, x2']).
Proof.
have Ha :=(@mc_removal_pr _ _ _ _ P m O Z f1 f2 fm pZ_unif Z_O_indep w1 w2 wmz Hneq0).
(* Things used in mc_removal_pr are not directly x1...xn but y1...ym, so even if O has x2, s2 and r2,
   Alice only see outputs of functions. So secrets are kept safe.

   That is: x2 in the condition is w1, [%x1...x2'] is w2 and t is wmz. 
   `H(w1 | [%w2, wmz]) = `H(w1 | w2).
*)
About cpr_cond_entropy1_RV.
have Hb := (@cpr_cond_entropy1_RV _ _ _ P m W1 W2 WmZ pWmZ_unif W2_WmZ_indep w2 wmz).

End eq3_proof.

Section eq_fin_proof.

Hypothesis x1_indep1 : P|= x1 _|_ [%s1, r1, x2', t, y1].
Hypothesis x1_indep2 : P|= x1 _|_ [%x2, s1, s2, r1, y2].  (* from the paper. *)

About pairwise.

Hypothesis Hinde : {homo nth x1 [:: x1; x2; s1; s2] : i j / i < j >-> inde_rv i j}%nat.
Check @Hinde 0 1.

Hypothesis Hinde_r : P|= r1 _|_ y2.

Hypothesis Hinde_all : forall i j, P|= nth x1 [:: x1; x2; s1; s2] i _|_ nth r1 [:: r1; y2] j.


Lemma inde_cinde (X Y Z: {RV P-> TX}):
  inde_rv X Y -> inde_rv [%X, Y] Z -> cinde_rv X Y Z.
Proof.
Admitted.

Lemma eq_fin:
  `H(x2|[%x1, s1, r1]) = entropy `p_ x2.
Proof.
transitivity (joint_entropy `p_ [%x1, s1, r1, x2] - entropy `p_ [%x1, s1, r1]).
  apply/eqP.
  rewrite eq_sym subr_eq addrC.
  apply/eqP.
  have -> : `p_[%x2, [%x1, s1, r1]] = fdistX `p_[%x1, s1, r1, x2].
    by rewrite fdistX_RV2.
  by rewrite chain_rule fst_RV2.
rewrite joint_entropy_indeRV.
  by rewrite addrAC subrr add0r.
  


move:x1_indep2.
move/cinde_rv_unit.  
(*
move/contraction.
move => a b c.
*)

move/decomposition.
move/cinde_rv_unit.
move => /[dup] x1_indep3_x2_s1_s2_r1.
move/cinde_rv_unit.

move/decomposition.
move/cinde_rv_unit.
move => /[dup] x1_indep4_x2_s1_s2.
move/cinde_rv_unit.

move/decomposition.
move/cinde_rv_unit.
move => /[dup] x1_indep_x2_s1.
move/cinde_rv_unit.

move/decomposition.
move/cinde_rv_unit.
move => x1_indep_x2.

Abort.

End eq_fin_proof.

End pi2.

(* Using graphoid for combinations of independ random variables. *)

End smc_entropy_proofs.
