(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype bigop div.
From mathcomp Require Import zify.

(******************************************************************************)
(* Free Group Ball-Size Formula (Combinatorial)                               *)
(* Group presentation: <a_1,...,a_r | > (free group, no relations)            *)
(*                                                                            *)
(* Pure nat-level counting of reduced words in a free group with r generators *)
(* (2r letters total: each generator and its inverse).                        *)
(*                                                                            *)
(* No free group type is constructed — only sequences with a "no adjacent     *)
(* inverses" constraint. This suffices for the ball-size formula needed by     *)
(* PGG-SMC search space analysis.                                             *)
(*                                                                            *)
(* Section 1 — Reduced words and sphere counting:                             *)
(*   letter_inv r i == inverse of letter i in alphabet {0,...,2r-1}           *)
(*   reduced r w    == no adjacent pair (a, inv(a)) in word w                 *)
(*   sphere_size r k == number of reduced words of length exactly k           *)
(*                                                                            *)
(* Section 2 — Ball size as sum of spheres:                                   *)
(*   ball_size r L == number of reduced words of length at most L             *)
(*                                                                            *)
(* Section 3 — Geometric series over nat:                                     *)
(*   geom_series_nat == (q-1) * sum_{k=0}^{L} q^k = q^{L+1} - 1             *)
(*                                                                            *)
(* Section 4 — Closed-form ball-size formula (multiplicative, no division):   *)
(*   ball_size_formula ==                                                     *)
(*     (2r-2) * (ball_size r L - 1) = 2r * ((2r-1)^L - 1)                    *)
(*   ball_size_lower == ball_size r L >= (2r-1)^L                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Reduced words and sphere counting                               *)
(* ========================================================================== *)

Section reduced_words.

Variable r : nat.
Hypothesis Hr : 0 < r.

Let alpha := (r.*2).
(* Letters: 0,...,2r-1. Letter i has inverse (i + r) mod 2r. *)

Definition letter_inv (i : nat) : nat := (i + r) %% alpha.

Lemma letter_inv_lt (i : nat) : i < alpha -> letter_inv i < alpha.
Proof. by move=> _; rewrite /letter_inv ltn_mod double_gt0. Qed.

Lemma letter_invK (i : nat) : i < alpha -> letter_inv (letter_inv i) = i.
Proof.
move=> Hi; rewrite /letter_inv.
have Halpha : 0 < alpha by rewrite double_gt0.
rewrite modnDml -addnA.
have -> : r + r = 1 * alpha by rewrite mul1n /alpha addnn.
rewrite addnC modnMDl.
exact: modn_small.
Qed.

Lemma letter_inv_neq (i : nat) : i < alpha -> letter_inv i != i.
Proof.
move=> Hi; rewrite /letter_inv.
have Halpha : 0 < alpha by rewrite double_gt0.
apply/negP => /eqP Heq.
have Hdvd : alpha %| r.
  apply/dvdnP.
  exists ((i + r) %/ alpha).
  have := divn_eq (i + r) alpha.
  rewrite Heq => Heq2.
  by lia.
move/dvdn_leq: Hdvd => /(_ Hr).
by rewrite /alpha; lia.
Qed.

(* A word is reduced if no adjacent letters are inverses *)
Fixpoint reduced (w : seq nat) : bool :=
  match w with
  | [::] | [:: _] => true
  | a :: ((b :: _) as w') => (letter_inv a != b) && reduced w'
  end.

(* Sphere: set of reduced words of length exactly k *)
(* sphere_size r 0 = 1 *)
(* sphere_size r k.+1 = 2r * (2r-1)^k *)

Definition sphere_size (k : nat) : nat :=
  match k with
  | 0 => 1
  | k'.+1 => alpha * (alpha - 1) ^ k'
  end.

(* Key recurrence: each reduced word of length k extends to exactly
   (2r - 1) reduced words of length k+1 (all letters except the inverse
   of the last letter). The first letter has 2r choices. *)

Lemma sphere_size_0 : sphere_size 0 = 1.
Proof. by []. Qed.

Lemma sphere_size_1 : sphere_size 1 = alpha.
Proof. by rewrite /= muln1. Qed.

Lemma sphere_size_S (k : nat) :
  0 < k -> sphere_size k.+1 = sphere_size k * (alpha - 1).
Proof.
case: k => [//|k _].
by rewrite /= expnSr mulnA.
Qed.

End reduced_words.

(* ========================================================================== *)
(* Section 2: Ball size = sum of spheres                                      *)
(* ========================================================================== *)

Section ball_size_def.

Variable r : nat.
Hypothesis Hr : 0 < r.

Definition ball_size (L : nat) : nat :=
  \sum_(k < L.+1) sphere_size r k.

Lemma ball_size_0 : ball_size 0 = 1.
Proof. by rewrite /ball_size big_ord_recl big_ord0. Qed.

Lemma ball_size_S (L : nat) :
  ball_size L.+1 = ball_size L + sphere_size r L.+1.
Proof. by rewrite /ball_size big_ord_recr. Qed.

Lemma ball_size_ge1 (L : nat) : 0 < ball_size L.
Proof. by rewrite /ball_size big_ord_recl /=; lia. Qed.

End ball_size_def.

(* ========================================================================== *)
(* Section 3: Geometric series over nat                                       *)
(* ========================================================================== *)

Section geometric_series.

(* (q - 1) * sum_{k=0}^{L} q^k = q^{L+1} - 1, for q >= 1 *)
Lemma geom_series_nat (q L : nat) :
  1 <= q ->
  q.-1 * (\sum_(k < L.+1) q ^ k) = q ^ L.+1 - 1.
Proof.
move=> Hq.
elim: L => [|L IH].
  by rewrite big_ord_recl big_ord0 expn0 addn0 muln1 expn1; lia.
rewrite big_ord_recr /= mulnDr IH.
have Hpow : 0 < q ^ L.+1 by rewrite expn_gt0; lia.
have Hpow2 : q ^ L.+1 <= q ^ L.+2.
  by rewrite leq_pexp2l //; lia.
have HqL : q.-1 * q ^ L.+1 + q ^ L.+1 = q ^ L.+2.
  by rewrite addnC -mulSn prednK // expnS.
lia.
Qed.

(* Variant: sum_{k=0}^{L} q^k = (q^{L+1} - 1) / (q - 1), for q >= 2 *)
Lemma geom_series_div (q L : nat) :
  2 <= q ->
  \sum_(k < L.+1) q ^ k = (q ^ L.+1 - 1) %/ q.-1.
Proof.
move=> Hq.
have Hq1 : 0 < q.-1 by lia.
have Hq1' : 1 <= q by lia.
rewrite -geom_series_nat // mulKn //.
Qed.

End geometric_series.

(* ========================================================================== *)
(* Section 4: Ball-size closed form                                           *)
(* ========================================================================== *)

Section ball_size_formula.

Variable r : nat.
Hypothesis Hr : 1 < r.

Let alpha := (r.*2).
Let q := alpha - 1.

Lemma alpha_gt1 : 1 < alpha.
Proof. by rewrite /alpha; lia. Qed.

Lemma q_gt0 : 0 < q.
Proof. by rewrite /q /alpha; lia. Qed.

(* ball_size r L = 1 + alpha * sum_{k=0}^{L-1} q^k *)
Lemma ball_size_sum (L : nat) :
  ball_size r L = 1 + alpha * \sum_(k < L) q ^ k.
Proof.
rewrite /ball_size big_ord_recl /=; congr (_ + _).
by rewrite -big_distrr.
Qed.

(* Main formula, stated multiplicatively to avoid division:
   (q - 1) * (ball_size r L - 1) = alpha * (q^L - 1) *)
Lemma ball_size_formula (L : nat) :
  0 < L ->
  q.-1 * (ball_size r L - 1) = alpha * (q ^ L - 1).
Proof.
move=> HL.
case: L HL => [//|L _].
rewrite ball_size_sum addKn mulnCA; congr (alpha * _).
have Hq1 : 1 <= q by rewrite /q /alpha; lia.
by rewrite geom_series_nat.
Qed.

(* Division form for display:
   ball_size r L = 1 + alpha * (q^L - 1) / (q - 1)
   i.e., 1 + 2r * ((2r-1)^L - 1) / (2r - 2) *)
Lemma ball_size_div (L : nat) :
  0 < L ->
  ball_size r L = 1 + alpha * ((q ^ L - 1) %/ q.-1).
Proof.
case: L => [//|L _].
rewrite ball_size_sum; congr (1 + alpha * _).
rewrite geom_series_div //.
by rewrite /q /alpha; lia.
Qed.

(* Exponential lower bound: ball_size r L >= q^L = (2r-1)^L *)
Lemma ball_size_lower (L : nat) : q ^ L <= ball_size r L.
Proof.
case: L => [|L].
  by rewrite expn0; exact: (ball_size_ge1 (ltnW Hr)).
rewrite ball_size_sum.
apply: (leq_trans _ (leq_addl 1 _)).
rewrite expnS.
have Hq_le_a : q <= alpha by rewrite /q /alpha; lia.
have Hsum : q ^ L <= \sum_(k < L.+1) q ^ k.
  by rewrite big_ord_recr /=; apply: leq_addl.
exact: leq_mul Hq_le_a Hsum.
Qed.

End ball_size_formula.

(* ========================================================================== *)
(* Section 5: Connection to L-freeness search space                           *)
(* ========================================================================== *)

Section lfree_ball_connection.

(* For L-free generators with branching factor Tg = 2r,
   the search space is Tg^L by lfree_search_space.
   The ball_size gives the size when restricted to reduced words.

   Key insight: L-freeness gives search_space = Tg^L (all words distinct),
   which is always >= ball_size (reduced words only).

   For free groups specifically, ALL reduced words give distinct elements,
   and non-reduced words collapse. So the ball size counts the distinct
   group elements reachable.

   Exponential growth: ball_size r L >= (2r-1)^L for r >= 2. *)

Lemma search_space_exp_growth (r L : nat) :
  1 < r -> (r.*2 - 1) ^ L <= 1 + r.*2 * (\sum_(k < L) (r.*2 - 1) ^ k).
Proof.
move=> Hr.
have := @ball_size_lower r Hr L.
by rewrite ball_size_sum.
Qed.

End lfree_ball_connection.
