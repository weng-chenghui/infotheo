(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG Weighted Word Distribution                                             *)
(*                                                                             *)
(* Generalization of the uniform word distribution to arbitrary generator      *)
(* weights. The IID product distribution on L-tuples uses fdist_rV (P `^ L)   *)
(* composed with tuple_of_row to convert from row vectors to tuples.           *)
(*                                                                             *)
(* Definitions:                                                                *)
(*   word_weighted W L == IID product distribution on L-words from weights W   *)
(*   rho_from_words_weighted W L == pushforward through word_eval              *)
(*   fiber_weighted W g == preimage set {w | word_eval w = g}                  *)
(*   fiber_prob_weighted W L g == P(word_eval = g) under weighted dist         *)
(*   endpoint_dist_weighted W L s == marginal distribution at sheet s          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
  pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*   Section 1: Weighted word distribution                                    *)
(******************************************************************************)

Section weighted_words.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(* Generator weight distribution *)
Variable W : R.-fdist 'I_Tg.

(* IID product distribution on L-words (as row vectors) *)
Let word_rV : R.-fdist 'rV['I_Tg]_L := W `^ L.

(* Convert row vector distribution to tuple distribution *)
Definition word_weighted : R.-fdist (L.-tuple 'I_Tg) :=
  fdistmap (@tuple_of_row _ L) word_rV.

(* Pushforward through word evaluation *)
Definition rho_from_words_weighted : R.-fdist {perm 'I_N} :=
  fdistmap (@word_eval M L) word_weighted.

(* Fiber: set of words evaluating to a given group element *)
Definition fiber_weighted (g : {perm 'I_N}) : {set L.-tuple 'I_Tg} :=
  [set w | @word_eval M L w == g].

(* Probability of each word under the weighted distribution *)
Lemma word_weightedE (w : L.-tuple 'I_Tg) :
  word_weighted w = \prod_(i < L) W (tnth w i).
Proof.
rewrite /word_weighted fdistmapE.
rewrite (bigD1 (row_of_tuple w)) /=; last first.
  by rewrite inE /= row_of_tupleK eqxx.
rewrite big1; last first.
  move=> v /andP []; rewrite inE /= => /eqP Hv Hneq.
  exfalso; move/negP: Hneq; apply.
  by apply/eqP; rewrite -Hv tuple_of_rowK.
rewrite addr0 fdist_rVE.
apply: eq_bigr => i _.
by congr (W _); rewrite /row_of_tuple mxE.
Qed.

(* The probability of g under the weighted distribution *)
Lemma fiber_prob_weighted (g : {perm 'I_N}) :
  rho_from_words_weighted g =
  \sum_(w | w \in fiber_weighted g) word_weighted w.
Proof.
rewrite /rho_from_words_weighted fdistmapE.
apply: eq_bigl => w.
by rewrite !inE.
Qed.

(* Endpoint distribution: push rho_from_words_weighted through
   sigma |-> sigma(s) for a given starting sheet s *)
Definition endpoint_dist_weighted (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s) rho_from_words_weighted.

End weighted_words.
