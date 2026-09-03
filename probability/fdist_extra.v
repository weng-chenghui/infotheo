(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot ssralg ssrnum reals.
Require Import fdist.

(**md**************************************************************************)
(* # Companion lemmas for fdist.v                                             *)
(*                                                                            *)
(* Facts about the finite-distribution monad that fdist.v does not state.     *)
(* Kept beside it, and depending on nothing beyond it, so that any file       *)
(* requiring fdist can require these too.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*               fdist_prod2 == the second marginal of a product is its       *)
(*                              second factor, the counterpart of             *)
(*                              fdist_prod1                                   *)
(*             fdistmap_bind == the fdistmap/fdistbind commutation of the     *)
(*                              fdist monad                                   *)
(*      fdistmap_bij_uniform == the pushforward of a uniform law along a      *)
(*                              bijection is uniform                          *)
(* fdistmap_uniform_supp_img == the pushforward of a uniform law along a      *)
(*                              map whose fibers over its image are           *)
(*                              equinumerous is uniform on that image         *)
(*               eq_fdistmap == fdistmap is congruent in a pointwise-equal    *)
(*                              transported map                               *)
(*              fdistmap_cst == the transport of a law along a constant map   *)
(*                              with value b is fdist1 b                      *)
(*           eq_fdistmap_cst == the transport of a law along a map pointwise  *)
(*                              equal to a constant b is fdist1 b             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section fdist_extra.

Context {R : realType}.

(* The second marginal of a genuine product is the second factor. *)
Lemma fdist_prod2 (T1 T2 : finType) (Q1 : R.-fdist T1)
    (Q2 : R.-fdist T2) : (Q1 `x Q2)`2 = Q2.
Proof. by rewrite -fdistX1 fdistX_prod fdist_prod1. Qed.

(* The fdistmap/fdistbind commutation of the fdist monad.  A convenience rather
   than a necessity, though the obvious inline spelling does not substitute for
   it: [rewrite /fdistmap fdistbindA] at a use site unfolds every [fdistmap] in
   the goal, destroying the nested ones a later [fdistmap_comp] must match. *)
Lemma fdistmap_bind (T1 T2 T3 : finType) (Q : R.-fdist T1)
    (g : T1 -> R.-fdist T2) (h : T2 -> T3) :
  fdistmap h (Q >>= g) = Q >>= (fun a => fdistmap h (g a)).
Proof. by rewrite /fdistmap fdistbindA. Qed.

(* The pushforward of a uniform along a bijection is uniform. *)
Lemma fdistmap_bij_uniform (T1 T2 : finType) (n1 n2 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1) (g : T1 -> T2) :
  bijective g ->
  fdistmap g (fdist_uniform (R:=R) c1) = fdist_uniform c2.
Proof.
move=> bg; have [h ghK hgK] := bg; apply/fdist_ext => b.
rewrite fdistmapE fdist_uniformE (big_pred1 (h b)); last first.
  by move=> a; rewrite !inE /=; apply/eqP/eqP => [<-|->].
by rewrite fdist_uniformE (bij_eq_card bg).
Qed.

(* The pushforward of a uniform distribution along a map with equal fiber
   cardinalities over its image is the uniform distribution on the image. *)
Lemma fdistmap_uniform_supp_img (T U : finType) (n : nat)
    (cardT : #|T| = n.+1) (f : T -> U)
    (Himg : (0 < #|f @: [set: T]|)%N)
    (Hfib : forall u u', u \in f @: [set: T] -> u' \in f @: [set: T] ->
        #|[set t | f t == u]| = #|[set t | f t == u']|) :
  fdistmap f (fdist_uniform (R:=R) cardT) = fdist_uniform_supp R Himg.
Proof.
apply/fdist_ext => u; rewrite fdistmapE.
case/boolP : (u \in f @: [set: T]) => Hu; last first.
  rewrite fdist_uniform_supp_notin // big_pred0 // => t.
  by apply/negbTE; apply: contra Hu => /eqP <-; exact: imset_f.
rewrite fdist_uniform_supp_in //.
under eq_bigr do rewrite fdist_uniformE.
rewrite sumr_const (_ : #|preim f (pred1 u)| = #|[set t | f t == u]|);
  last by apply: eq_card => t; rewrite !inE.
have Hpart : #|T| = (#|f @: [set: T]| * #|[set t | f t == u]|)%N.
  rewrite -[LHS]sum1_card (partition_big_imset f) /= -sum_nat_const.
  have -> : [set f x | x : T] = f @: [set: T].
    by apply/setP => y; apply/imsetP/imsetP => -[t _ ->]; exists t;
       rewrite ?inE.
  by apply: eq_bigr => j Hj; rewrite sum1dep_card; exact: (Hfib _ _ Hj Hu).
rewrite -[LHS]mulr_natr Hpart natrM invfM -mulrA mulVf ?mulr1 //.
rewrite pnatr_eq0 -lt0n.
by case/imsetP : Hu => r _ ->; apply/card_gt0P; exists r; rewrite inE.
Qed.

(* Pointwise equal maps transport a law to the same law. *)
Lemma eq_fdistmap (A B : finType) (g h : A -> B) (p : R.-fdist A) :
  g =1 h -> fdistmap g p = fdistmap h p.
Proof.
move=> gh; apply/fdist_ext => b; rewrite !fdistmapE.
by apply: eq_bigl => a; rewrite !inE gh.
Qed.

(* The transport of a law along a constant map with value b is the point mass
   at b. *)
Lemma fdistmap_cst (A B : finType) (p : R.-fdist A) (b : B) :
  fdistmap (fun=> b) p = fdist1 b.
Proof.
apply/fdist_ext => b'.
by rewrite /fdistmap fdistbindE -big_distrl/= FDist.f1 mul1r.
Qed.

(* The transport of a law along a map pointwise equal to the constant b is the
   point mass at b. *)
Lemma eq_fdistmap_cst (A B : finType) (g : A -> B) (p : R.-fdist A) (b : B) :
  g =1 (fun=> b) -> fdistmap g p = fdist1 b.
Proof. by move=> gb; rewrite -(fdistmap_cst p b); apply: eq_fdistmap. Qed.

End fdist_extra.
