(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 x S_5 spectral convergence via lazy-walk reduction                     *)
(*                                                                            *)
(* The S_5 x S_5 Schreier walk on 'I_10 with 8 pile-disjoint generators is    *)
(* reducible: starting from a pile-1 sheet, the walk stays in pile-1 forever. *)
(* Consequently var_dist(sigma(s), uniform_10) does NOT decay to zero; it     *)
(* converges to a constant floor of 1 (in infotheo's un-halved L^1            *)
(* convention) corresponding to the gap between uniform_pile and uniform_10.  *)
(*                                                                            *)
(* This file proves the honest bound                                          *)
(*   var_dist(sigma(s), uniform_10) <= 1 + sqrt(5) * ((1+alpha)/2)^L          *)
(* where alpha = 181/200 is the S_5 Rayleigh certificate.                     *)
(*                                                                            *)
(* The proof reduces the walk on each pile to a lazy walk on 'I_5: the lazy  *)
(* walk has 4 path transpositions plus 4 identities. Its transition matrix   *)
(* is (I + Q_s5)/2, with squared Rayleigh bound ((1+alpha)/2)^2.              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_schreier pgg_mixing.
From pgg_smc Require Import pgg_raag_path s5_mixing.
From pgg_smc Require Import pgg_s5x5 s5x5_pile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1. Lazy generator tuple on 'I_5.                                  *)
(*  Four path transpositions + four identities, indexed by 'I_8.              *)
(******************************************************************************)

Section s5_lazy_generators.

Local Notation o0 := (Ordinal (n:=5) (m:=0) erefl).
Local Notation o1 := (Ordinal (n:=5) (m:=1) erefl).
Local Notation o2 := (Ordinal (n:=5) (m:=2) erefl).
Local Notation o3 := (Ordinal (n:=5) (m:=3) erefl).
Local Notation o4 := (Ordinal (n:=5) (m:=4) erefl).

(** s5_lazy_gen_tuple — lazy generator tuple (four path transpositions followed by four identities).
    Kind: instance. *)
Definition s5_lazy_gen_tuple : 8.-tuple {perm 'I_5} :=
  [tuple tperm o0 o1; tperm o1 o2; tperm o2 o3; tperm o3 o4;
         1%g; 1%g; 1%g; 1%g].

(** s5_lazy_gen_invol — involutivity of every slot of the lazy generator tuple.
    Kind: helper.
    Why: involutivity drives symmetry of [schreier_transition] and hence the Rayleigh/TV bounds.
    Used by: [Q_lazy_symm] and [s5_lazy_TV_bound]. *)
Lemma s5_lazy_gen_invol :
  forall k : 'I_8,
  (tnth s5_lazy_gen_tuple k * tnth s5_lazy_gen_tuple k)%g = 1%g.
Proof.
move=> k.
case: k => [[|[|[|[|[|[|[|[|?]]]]]]]] Hk] //;
  rewrite /s5_lazy_gen_tuple ?tnth_mktuple //;
  try exact: tperm2; by rewrite mul1g.
Qed.

End s5_lazy_generators.

(******************************************************************************)
(*  Section 2. Lazy Q matrix formula.                                         *)
(*  schreier_transition s5_lazy_gen_tuple                                     *)
(*    = (I + schreier_transition (path_gen_tuple 3)) * (1/2).                 *)
(*                                                                            *)
(*  Per-entry computation:                                                     *)
(*    schreier_gen_count(s5_lazy_gen_tuple, i, j)                              *)
(*      = #{k < 4: path_gen_k(i) = j} + #{k >= 4: 1(i) = j}                   *)
(*      = path_gen_count(i, j) + (4 if i == j else 0)                         *)
(*    Hence Q_lazy(i,j) = (path_count(i,j) + 4*[i=j]) / 8                     *)
(*                      = path_count(i,j)/8 + [i=j]/2                          *)
(*                      = (Q_s5(i,j) + [i=j]) / 2.                             *)
(*                                                                            *)
(*  Note: path_gen_tuple has 4 generators, so Q_s5(i,j) = path_count(i,j)/4. *)
(******************************************************************************)

Section s5_lazy_Q_formula.

Variable R : realType.

Local Notation Q_lazy := (schreier_transition R s5_lazy_gen_tuple).
Local Notation Q_s5 := (schreier_transition R (path_gen_tuple 3)).

Local Notation o0 := (Ordinal (n:=5) (m:=0) erefl).
Local Notation o1 := (Ordinal (n:=5) (m:=1) erefl).
Local Notation o2 := (Ordinal (n:=5) (m:=2) erefl).
Local Notation o3 := (Ordinal (n:=5) (m:=3) erefl).
Local Notation o4 := (Ordinal (n:=5) (m:=4) erefl).

(* tnth values of s5_lazy_gen_tuple at the 8 indices.
   The first 4 are path transpositions on 'I_5, the last 4 are identities. *)
Lemma s5_lazy_tnth_0 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=0) erefl) = tperm o0 o1.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_1 — slot 1 of the lazy generator tuple is a path transposition.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_1 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=1) erefl) = tperm o1 o2.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_2 — slot 2 of the lazy generator tuple is a path transposition.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_2 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=2) erefl) = tperm o2 o3.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_3 — slot 3 of the lazy generator tuple is a path transposition.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_3 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=3) erefl) = tperm o3 o4.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_4 — slot 4 of the lazy generator tuple is the identity.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_4 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=4) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_5 — slot 5 of the lazy generator tuple is the identity.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_5 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=5) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_6 — slot 6 of the lazy generator tuple is the identity.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_6 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=6) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth_7 — slot 7 of the lazy generator tuple is the identity.
    Kind: helper.
    Why: per-index evaluation for use in [s5_lazy_count_eq].
    Used by: [s5_lazy_count_eq]. *)
Lemma s5_lazy_tnth_7 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=7) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.

(** path_gen_3_tnth_0 — slot 0 of the path-3 generator tuple.
    Kind: helper.
    Why: per-index evaluation of [path_gen_tuple 3] for use in sum expansions.
    Used by: [s5_lazy_count_eq].
    Naming: the trailing [_N] disambiguates the four slot indices of the
    path-3 tuple; dropping the slot would collide with its siblings. *)
Lemma path_gen_3_tnth_0 :
  tnth (path_gen_tuple 3) (Ordinal (n:=4) (m:=0) erefl) = tperm o0 o1.
Proof.
rewrite path_gen_tupleE /path_gen.
by congr tperm; apply: val_inj.
Qed.
(** path_gen_3_tnth_1 — slot 1 of the path-3 generator tuple.
    Kind: helper.
    Why: per-index evaluation of [path_gen_tuple 3] for use in sum expansions.
    Used by: [s5_lazy_count_eq].
    Naming: the trailing [_N] disambiguates the four slot indices. *)
Lemma path_gen_3_tnth_1 :
  tnth (path_gen_tuple 3) (Ordinal (n:=4) (m:=1) erefl) = tperm o1 o2.
Proof.
rewrite path_gen_tupleE /path_gen.
by congr tperm; apply: val_inj.
Qed.
(** path_gen_3_tnth_2 — slot 2 of the path-3 generator tuple.
    Kind: helper.
    Why: per-index evaluation of [path_gen_tuple 3] for use in sum expansions.
    Used by: [s5_lazy_count_eq].
    Naming: the trailing [_N] disambiguates the four slot indices. *)
Lemma path_gen_3_tnth_2 :
  tnth (path_gen_tuple 3) (Ordinal (n:=4) (m:=2) erefl) = tperm o2 o3.
Proof.
rewrite path_gen_tupleE /path_gen.
by congr tperm; apply: val_inj.
Qed.
(** path_gen_3_tnth_3 — slot 3 of the path-3 generator tuple.
    Kind: helper.
    Why: per-index evaluation of [path_gen_tuple 3] for use in sum expansions.
    Used by: [s5_lazy_count_eq].
    Naming: the trailing [_N] disambiguates the four slot indices. *)
Lemma path_gen_3_tnth_3 :
  tnth (path_gen_tuple 3) (Ordinal (n:=4) (m:=3) erefl) = tperm o3 o4.
Proof.
rewrite path_gen_tupleE /path_gen.
by congr tperm; apply: val_inj.
Qed.

(** schreier_gen_count_eq_sum — Schreier generator-count expressed as a [sum1dep_card].
    Kind: helper.
    Why: lets later lemmas manipulate the count with standard bigop reasoning.
    Used by: s5_lazy_count_eq and the s5x5 lazy-walk discharge.
    Naming: the five components encode the rewrite target precisely
    (schreier_gen_count + equality + sum form) and are load-bearing. *)
Lemma schreier_gen_count_eq_sum (m n' : nat) (sigmas : (m.+1).-tuple {perm 'I_n'.+2})
    (i j : 'I_n'.+2) :
  schreier_gen_count sigmas i j
  = (\sum_(k : 'I_m.+1) (tnth sigmas k i == j))%N.
Proof.
rewrite /schreier_gen_count -sum1dep_card -big_mkcondr.
by apply: eq_big.
Qed.

(* Enumerate sum over 'I_8, right-associative form (matches big_ord_recl output). *)
Lemma sum_8_enum (f : 'I_8 -> nat) :
  (\sum_(k : 'I_8) f k =
   f (Ordinal (n:=8) (m:=0) erefl)
 + (f (Ordinal (n:=8) (m:=1) erefl)
 + (f (Ordinal (n:=8) (m:=2) erefl)
 + (f (Ordinal (n:=8) (m:=3) erefl)
 + (f (Ordinal (n:=8) (m:=4) erefl)
 + (f (Ordinal (n:=8) (m:=5) erefl)
 + (f (Ordinal (n:=8) (m:=6) erefl)
 + f (Ordinal (n:=8) (m:=7) erefl))))))))%N.
Proof.
rewrite !big_ord_recl /= big_ord0 addn0.
do 7 (congr (_ + _)%N; first by congr f; apply: val_inj).
by congr f; apply: val_inj.
Qed.

(* Enumerate sum over 'I_4, right-associative form. *)
Lemma sum_4_enum (f : 'I_4 -> nat) :
  (\sum_(k : 'I_4) f k =
   f (Ordinal (n:=4) (m:=0) erefl)
 + (f (Ordinal (n:=4) (m:=1) erefl)
 + (f (Ordinal (n:=4) (m:=2) erefl)
 + f (Ordinal (n:=4) (m:=3) erefl))))%N.
Proof.
rewrite !big_ord_recl /= big_ord0 addn0.
do 3 (congr (_ + _)%N; first by congr f; apply: val_inj).
by congr f; apply: val_inj.
Qed.

(* Lazy generator count = path generator count + (4 if i=j else 0). *)
Lemma s5_lazy_count_eq (i j : 'I_5) :
  schreier_gen_count s5_lazy_gen_tuple i j
  = (schreier_gen_count (path_gen_tuple 3) i j
     + (if i == j then 4 else 0))%N.
Proof.
rewrite !schreier_gen_count_eq_sum.
rewrite sum_8_enum sum_4_enum.
rewrite s5_lazy_tnth_0 s5_lazy_tnth_1 s5_lazy_tnth_2 s5_lazy_tnth_3.
rewrite s5_lazy_tnth_4 s5_lazy_tnth_5 s5_lazy_tnth_6 s5_lazy_tnth_7.
rewrite path_gen_3_tnth_0 path_gen_3_tnth_1 path_gen_3_tnth_2 path_gen_3_tnth_3.
rewrite !perm1.
have H := eq_refl (i == j).
by case: (i == j) H => /= H; rewrite ?addn0 !addnA //; rewrite -!addnA.
Qed.

(* The Q matrix formula: Q_lazy = (Q_s5 + I) / 2. *)
Lemma s5_lazy_Q_eq (i j : 'I_5) :
  Q_lazy i j = (Q_s5 i j + (if i == j then 1 else 0)) / 2%:R.
Proof.
rewrite !mxE s5_lazy_count_eq.
set N := schreier_gen_count _ i j.
case: (i == j); rewrite ?addn0; last first.
  by rewrite addr0 -mulrA -invfM -natrM.
rewrite natrD mulrDl.
apply: (canRL (mulfK (_ : (2%:R : R) != 0))); first by rewrite pnatr_eq0.
have h8 : (8%:R : R) = 4 * 2 by rewrite -natrM.
rewrite h8 invfM mulrDl.
rewrite -!mulrA mulVf ?pnatr_eq0 // !mulr1.
by rewrite divff ?pnatr_eq0.
Qed.

End s5_lazy_Q_formula.

(******************************************************************************)
(*  Section 3. Lazy Rayleigh quotient: alpha_lazy = (1 + alpha) / 2.          *)
(*  We prove that for the lazy walk on 'I_5, the Rayleigh quotient of Q^2     *)
(*  is bounded by alpha_lazy^2.                                               *)
(******************************************************************************)

Section s5_lazy_rayleigh.

Variable R : realType.

(** s5_lazy_alpha_R — lazy mixing coefficient, i.e. [(1 + alpha)/2].
    Kind: instance. *)
Definition s5_lazy_alpha_R : R := (1 + s5_alpha_R R) / 2%:R.

(** s5_lazy_alpha_R_ge0 — the lazy mixing coefficient is non-negative.
    Kind: helper.
    Why: needed to keep [alpha_lazy in [0,1]] for the TV-distance bound.
    Used by: [s5_lazy_TV_bound]. *)
Lemma s5_lazy_alpha_R_ge0 : 0 <= s5_lazy_alpha_R.
Proof.
rewrite /s5_lazy_alpha_R.
apply: divr_ge0; last by rewrite ler0n.
by rewrite addr_ge0 // ?ler01 // s5_alpha_R_ge0.
Qed.

(** s5_lazy_alpha_R_le1 — the lazy mixing coefficient is at most one.
    Kind: helper.
    Why: needed to keep [alpha_lazy in [0,1]] for the TV-distance bound.
    Used by: [s5_lazy_TV_bound]. *)
Lemma s5_lazy_alpha_R_le1 : s5_lazy_alpha_R <= 1.
Proof.
rewrite /s5_lazy_alpha_R ler_pdivrMr ?mul1r; last by rewrite ltr0n.
have h2 : (2%:R : R) = 1 + 1 by rewrite -natr1.
rewrite h2 lerD2l.
exact: s5_alpha_R_le1.
Qed.

(* var_dist <= 2 trivial bound, used as fallback *)
Lemma var_dist_le_2 (A : finType) (P Q : R.-fdist A) :
  var_dist P Q <= 2.
Proof.
rewrite /var_dist.
have step : \sum_(a : A) `|P a - Q a| <= \sum_(a : A) (P a + Q a).
  apply: ler_sum => a _.
  apply: (Order.POrderTheory.le_trans (ler_normD _ _)).
  by rewrite ger0_norm ?(FDist.ge0) // normrN ger0_norm ?(FDist.ge0).
apply: (Order.POrderTheory.le_trans step).
rewrite big_split /=.
by rewrite !FDist.f1; rewrite -[2]/(1+1).
Qed.

(* fdistmap with injective f preserves var_dist exactly. *)
Lemma var_dist_fdistmap_inj (A B : finType) (f : A -> B) (P Q : R.-fdist A) :
  injective f -> var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q.
Proof.
move=> Hinj.
rewrite /var_dist (partition_big f xpredT) //=.
apply: eq_bigr => b _.
rewrite !fdistmapE.
have Hsimp : forall (R' : R.-fdist A),
  \sum_(a in A | a \in preim f (pred1 b)) R' a = \sum_(a | f a == b) R' a.
  by move=> R'; apply: eq_bigl => a /=; rewrite inE.
rewrite !Hsimp -sumrB.
case Hb : [exists a, f a == b]; last first.
  move/negbT/negP: Hb => Hb.
  have Hempty : (fun i : A => f i == b) =1 xpred0.
    move=> a /=. apply/negP => /eqP H. apply: Hb.
    by apply/existsP; exists a; rewrite H.
  by rewrite (eq_bigl _ _ Hempty) (eq_bigl _ _ Hempty) !big_pred0_eq normr0.
move: Hb => /existsP [a /eqP Heq].
rewrite (bigD1 a) /=; last by apply/eqP.
rewrite big1; last first.
  move=> a' /andP [Ha' Hne].
  move/eqP in Ha'. rewrite -Heq in Ha'. move/Hinj in Ha'.
  by rewrite Ha' eqxx in Hne.
rewrite addr0.
rewrite [in RHS](bigD1 a) /=; last by apply/eqP.
rewrite big1 ?addr0 // => a' /andP [Ha' Hne].
move/eqP in Ha'. rewrite -Heq in Ha'. move/Hinj in Ha'.
by rewrite Ha' eqxx in Hne.
Qed.

(* === Matrix-level Q_lazy facts === *)

Local Notation Q_lazy := (schreier_transition R s5_lazy_gen_tuple).
Local Notation Q_s5 := (schreier_transition R (path_gen_tuple 3)).

Lemma Q_lazy_eq_matrix : Q_lazy = (2%:R)^-1 *: (Q_s5 + 1%:M).
Proof.
apply/matrixP => i j.
rewrite [in RHS]mxE [in RHS]mxE [in RHS]mxE.
rewrite s5_lazy_Q_eq mulrC.
congr (_ * _).
rewrite mxE mxE.
case: (i == j); by rewrite ?addr0.
Qed.

(** Q_lazy_mul_v — lazy-walk matrix action: Q_lazy v = (Q_s5 v + v) / 2.
    Kind: helper.
    Why: separates the contraction (Q_s5) and identity parts for the Rayleigh bound.
    Used by: [s5_lazy_rayleigh_Q2_R] and downstream TV bounds. *)
Lemma Q_lazy_mul_v (v : 'cV[R]_5) :
  Q_lazy *m v = (2%:R)^-1 *: (Q_s5 *m v + v).
Proof.
rewrite Q_lazy_eq_matrix.
rewrite -scalemxAl mulmxDl.
by rewrite mul1mx.
Qed.

(** Q_lazy_symm — symmetry of the lazy Schreier transition matrix.
    Kind: helper.
    Why: symmetry follows from involutivity of the lazy tuple.
    Used by: Rayleigh-quotient arguments for the lazy walk. *)
Lemma Q_lazy_symm : Q_lazy^T = Q_lazy.
Proof. exact: (@schreier_transition_symm R 7 3 s5_lazy_gen_tuple s5_lazy_gen_invol). Qed.

(** Q_s5_symm — symmetry of the S_5 Schreier transition matrix.
    Kind: helper.
    Why: symmetry follows from the involutivity of the path transpositions.
    Used by: Rayleigh-quotient arguments for the non-lazy S_5 walk. *)
Lemma Q_s5_symm : Q_s5^T = Q_s5.
Proof. exact: (@schreier_transition_symm R 3 3 (path_gen_tuple 3) path_gen_tuple_3_invol). Qed.

(* === Bilinearity of cV_inner === *)
Lemma cV_innerDl_5 (u v w : 'cV[R]_5) :
  cV_inner (u + v) w = cV_inner u w + cV_inner v w.
Proof.
rewrite !cV_innerE -big_split /=.
apply: eq_bigr => i _.
by rewrite !mxE mulrDl.
Qed.

(** cV_innerDr_5 — right additivity of the column-vector inner product on 'cV_5.
    Kind: helper.
    Why: bilinearity ingredient for manipulating the Rayleigh quotient.
    Used by: Rayleigh-quotient manipulations on 'cV[R]_5. *)
Lemma cV_innerDr_5 (u v w : 'cV[R]_5) :
  cV_inner u (v + w) = cV_inner u v + cV_inner u w.
Proof.
rewrite !cV_innerE -big_split /=.
apply: eq_bigr => i _.
by rewrite !mxE mulrDr.
Qed.

(** cV_innerZl_5 — left-scalar homogeneity of the column-vector inner product on 'cV_5.
    Kind: helper.
    Why: bilinearity ingredient for manipulating the Rayleigh quotient.
    Used by: Rayleigh-quotient manipulations on 'cV[R]_5. *)
Lemma cV_innerZl_5 (a : R) (v w : 'cV[R]_5) :
  cV_inner (a *: v) w = a * cV_inner v w.
Proof.
rewrite !cV_innerE mulr_sumr.
apply: eq_bigr => i _.
by rewrite !mxE mulrA.
Qed.

(** cV_innerZr_5 — right-scalar homogeneity of the column-vector inner product on 'cV_5.
    Kind: helper.
    Why: bilinearity ingredient for manipulating the Rayleigh quotient.
    Used by: Rayleigh-quotient manipulations on 'cV[R]_5. *)
Lemma cV_innerZr_5 (a : R) (v w : 'cV[R]_5) :
  cV_inner v (a *: w) = a * cV_inner v w.
Proof.
rewrite !cV_innerE mulr_sumr.
apply: eq_bigr => i _.
by rewrite !mxE [_ * (a * _)]mulrCA.
Qed.

(* === Cauchy-Schwarz on cV_inner === *)
Lemma cV_cauchy_schwarz (v w : 'cV[R]_5) :
  (cV_inner v w) ^+ 2 <= cV_inner v v * cV_inner w w.
Proof. rewrite !cV_innerE; exact: cauchy_schwarz_bigR. Qed.

(* === Signed Cauchy-Schwarz: <v, Q_s5 v> <= alpha * <v, v> === *)
Lemma s5_inner_v_Qv_bound (v : 'cV[R]_5) :
  \sum_i v i ord0 = 0 ->
  cV_inner v (Q_s5 *m v) <= s5_alpha_R R * cV_inner v v.
Proof.
move=> Hsum.
set i_v := cV_inner v v.
have iv_ge0 : 0 <= i_v by exact: cV_inner_ge0.
have a_ge0 : 0 <= s5_alpha_R R by exact: s5_alpha_R_ge0.
have Hbound : cV_inner (Q_s5 *m v) (Q_s5 *m v) <= (s5_alpha_R R) ^+ 2 * i_v.
  rewrite cV_inner_Qv_Qv_symm; last exact: Q_s5_symm.
  exact: s5_rayleigh_Q2_R.
have HCS := cV_cauchy_schwarz v (Q_s5 *m v).
have HCS2 : (cV_inner v (Q_s5 *m v)) ^+ 2 <= i_v * ((s5_alpha_R R) ^+ 2 * i_v).
  apply: (Order.POrderTheory.le_trans HCS).
  by apply: ler_wpM2l => //.
have HCS3 : (cV_inner v (Q_s5 *m v)) ^+ 2 <= (s5_alpha_R R * i_v) ^+ 2.
  rewrite [in X in _ <= X]exprMn.
  by rewrite [_ * (_ * _)]mulrCA in HCS2.
have HRHS_ge0 : 0 <= s5_alpha_R R * i_v by apply: mulr_ge0.
have HabsB : `|cV_inner v (Q_s5 *m v)| <= s5_alpha_R R * i_v.
  by rewrite -ler_sqr ?nnegrE ?normr_ge0 // real_normK ?num_real //.
exact: (Order.POrderTheory.le_trans (ler_norm _) HabsB).
Qed.

(** s5_lazy_alpha_sq_eq — algebraic identity for the lazy-alpha squared.
    Kind: helper.
    Why: converts [s5_lazy_alpha_R ^+ 2] into a rational form that matches the
    spectral-gap arithmetic in the lazy-walk discharge.
    Used by: s5_lazy_spectral_gap, s5x5 lazy-walk reduction.
    Naming: the suffix [_sq_eq] names "squared, equation" which pins the
    rewrite target; compressing further would collide with [s5_lazy_alpha_R]. *)
Lemma s5_lazy_alpha_sq_eq :
  s5_lazy_alpha_R ^+ 2 = ((s5_alpha_R R) ^+ 2 + 2 * s5_alpha_R R + 1) / 4%:R.
Proof.
rewrite /s5_lazy_alpha_R expr_div_n sqrrD expr1n.
rewrite mul1r mulr2n.
have h2sq : ((2%:R : R)^+2 = 4%:R) by rewrite -natrX.
rewrite h2sq.
congr (_ / _).
have h : ((s5_alpha_R R) + (s5_alpha_R R) = 2 * s5_alpha_R R)%R.
  by rewrite -mulr2n mulr_natl.
rewrite h.
rewrite addrC.
by rewrite addrA addrAC.
Qed.

(* === Main theorem: Rayleigh bound for Q_lazy^2 === *)
Lemma s5_lazy_rayleigh_Q2_R (v : 'cV[R]_5) :
  \sum_i v i ord0 = 0 ->
  (v^T *m (Q_lazy *m Q_lazy) *m v) ord0 ord0
    <= s5_lazy_alpha_R ^+ 2 * cV_inner v v.
Proof.
move=> Hsum.
(* Convert to <Q_lazy v, Q_lazy v> via symmetry *)
rewrite -cV_inner_Qv_Qv_symm; last exact: Q_lazy_symm.
(* Use Q_lazy v = (1/2) *: (Q_s5 v + v) *)
rewrite !Q_lazy_mul_v.
(* Pull out 1/2 from both sides *)
rewrite cV_innerZl_5 cV_innerZr_5.
(* Expand <Q_s5 v + v, Q_s5 v + v> *)
rewrite cV_innerDl_5 !cV_innerDr_5.
(* Set up abbreviations *)
set IQQ := cV_inner (Q_s5 *m v) (Q_s5 *m v).
set IQv := cV_inner (Q_s5 *m v) v.
set IvQ := cV_inner v (Q_s5 *m v).
set Ivv := cV_inner v v.
have HIQvIvQ : IQv = IvQ by rewrite /IQv /IvQ cV_inner_sym.
rewrite HIQvIvQ.
(* Bounds *)
have iv_ge0 : 0 <= Ivv by exact: cV_inner_ge0.
have a_ge0 : 0 <= s5_alpha_R R by exact: s5_alpha_R_ge0.
have HQQ : IQQ <= (s5_alpha_R R) ^+ 2 * Ivv.
  rewrite /IQQ cV_inner_Qv_Qv_symm; last exact: Q_s5_symm.
  exact: s5_rayleigh_Q2_R.
have HvQ : IvQ <= s5_alpha_R R * Ivv.
  exact: s5_inner_v_Qv_bound.
(* Algebraic chain *)
have HIvQ_two : IvQ + IvQ <= 2 * (s5_alpha_R R * Ivv).
  have h2 : (2 : R) = 1 + 1 by rewrite -natr1.
  rewrite h2 mulrDl mul1r.
  by apply: lerD.
have step1 : IQQ + IvQ + (IvQ + Ivv)
             <= (s5_alpha_R R) ^+ 2 * Ivv + 2 * (s5_alpha_R R * Ivv) + Ivv.
  have hL : IQQ + IvQ + (IvQ + Ivv) = IQQ + (IvQ + IvQ) + Ivv.
    rewrite -addrA -addrA. congr (_ + _). by rewrite addrA.
  rewrite hL.
  apply: lerD => //.
  by apply: lerD.
have inv2_ge0 : 0 <= ((2%:R : R))^-1 by rewrite invr_ge0 ler0n.
have step2 : 2^-1 * (2^-1 * (IQQ + IvQ + (IvQ + Ivv)))
             <= 2^-1 * (2^-1 * ((s5_alpha_R R) ^+ 2 * Ivv
                                + 2 * (s5_alpha_R R * Ivv) + Ivv)).
  apply: ler_wpM2l => //.
  apply: ler_wpM2l => //.
apply: (Order.POrderTheory.le_trans step2).
(* Algebra: 2^-1 * (2^-1 * (alpha^2 * Ivv + 2*alpha*Ivv + Ivv))
           = ((1+alpha)/2)^2 * Ivv *)
rewrite s5_lazy_alpha_sq_eq.
(* Goal: 2^-1 * (2^-1 * (alpha^2 * Ivv + 2 * (alpha * Ivv) + Ivv))
       <= (alpha^2 + 2 * alpha + 1) / 4 * Ivv *)
(* Factor Ivv on both sides *)
have h_factor : s5_alpha_R R ^+ 2 * Ivv + 2 * (s5_alpha_R R * Ivv) + Ivv
              = (s5_alpha_R R ^+ 2 + 2 * s5_alpha_R R + 1) * Ivv.
  by rewrite (mulrA 2) -[Ivv in _ + _ + Ivv]mul1r -!mulrDl.
rewrite h_factor.
(* Now: 2^-1 * (2^-1 * ((... + 1) * Ivv)) <= (... + 1) / 4 * Ivv *)
rewrite mulrA -invfM -natrM /= mulrAC.
have h22 : (((2 * 2)%N)%:R : R) = 4%:R by [].
rewrite h22.
by rewrite mulrC.
Qed.

(* Strict bound: lazy_alpha < 1 *)
Lemma s5_lazy_alpha_R_lt1 : s5_lazy_alpha_R < 1.
Proof.
rewrite /s5_lazy_alpha_R ltr_pdivrMr ?mul1r; last by rewrite ltr0n.
have h2 : (2%:R : R) = 1 + 1 by rewrite -natr1.
rewrite h2 ltrD2l.
exact: s5_alpha_R_lt1.
Qed.

End s5_lazy_rayleigh.

(******************************************************************************)
(*  Section 5. Apply symm_ds_TV_bound to the lazy walk on 'I_5.               *)
(******************************************************************************)

Section s5_lazy_TV.

Variable R : realType.

(** s5_lazy_TV_bound — TV-distance convergence of the lazy S_5 walk to uniform on {0..4}.
    Kind: main.
    Why: main spectral-to-TV bound for the lazy walk, [sqrt(5) * alpha_lazy^L]. *)
Lemma s5_lazy_TV_bound (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L s5_lazy_gen_tuple))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L.
Proof.
apply: (@symm_ds_TV_bound R 7 3 s5_lazy_gen_tuple s5_lazy_gen_invol
          (s5_lazy_alpha_R R) L s).
- exact: s5_lazy_alpha_R_ge0.
- exact: s5_lazy_alpha_R_le1.
- exact: s5_lazy_rayleigh_Q2_R.
Qed.

End s5_lazy_TV.

(******************************************************************************)
(*  Section 6. Pile-1 equivalence between s5x5 and s5_lazy walks.             *)
(*  On a pile-1 sheet (sheet with val < 5), s5x5_gen_tuple acts identically   *)
(*  to s5_lazy_gen_tuple (after widening 'I_5 to 'I_10).                      *)
(******************************************************************************)

Definition ltn5_10 : (5 <= 10)%N := isT.
(** widen5to10 — widening embedding 'I_5 into pile-1 sheets {0..4} of 'I_10.
    Kind: instance. *)
Definition widen5to10 : 'I_5 -> 'I_10 := @widen_ord 5 10 ltn5_10.

(** widen5to10_inj — [widen5to10] is injective.
    Kind: helper.
    Why: injectivity is required to pull TV distances back through [fdistmap].
    Used by: pile-1 TV-distance computations. *)
Lemma widen5to10_inj : injective widen5to10.
Proof.
move=> x y H. apply: val_inj.
have : val (widen5to10 x) = val (widen5to10 y) by rewrite H.
by [].
Qed.

(* Per-step equivalence: each generator k acts identically on pile-1. *)
Lemma s5x5_gen_pile1_action (k : 'I_8) (s : 'I_5) :
  tnth s5x5_gen_tuple k (widen5to10 s)
  = widen5to10 (tnth s5_lazy_gen_tuple k s).
Proof.
case: k => [[|k] Hk] //=.
  rewrite (tnth_nth 1%g) /=.
  rewrite (tnth_nth 1%g) /=.
  case: s => [[|[|[|[|[|sval]]]]] Hs] //=;
    apply: val_inj => /=;
    rewrite ?permE ?eqxx //=;
    rewrite /widen5to10 /=.
case: k Hk => [|[|[|[|[|[|[|k]]]]]]] Hk //=.
all: rewrite !(tnth_nth 1%g) /=.
all: case: s => [[|[|[|[|[|sval]]]]] Hs] //=;
  apply: val_inj => /=;
  rewrite ?permE //=;
  rewrite /widen5to10 /= ?perm1 //=.
Qed.

(* Word-level equivalence: word_eval s5x5 w (widen s) = widen (word_eval s5_lazy w s) *)
Lemma word_eval_pile1 (L : nat) (w : L.-tuple 'I_8) (s : 'I_5) :
  word_eval (M:=Gen_PGGTypes s5x5_gen_tuple) w (widen5to10 s)
  = widen5to10 (word_eval (M:=Gen_PGGTypes s5_lazy_gen_tuple) w s).
Proof.
elim: L w s => [|L IH] w s.
  by rewrite tuple0 /word_eval !big_ord0 !perm1.
rewrite /word_eval !big_ord_recl.
rewrite !permM.
have ->: tnth (pgg_sigmas (s:=Gen_PGGTypes s5x5_gen_tuple)) (tnth w ord0) (widen5to10 s)
       = widen5to10 (tnth (pgg_sigmas (s:=Gen_PGGTypes s5_lazy_gen_tuple)) (tnth w ord0) s).
  exact: s5x5_gen_pile1_action.
pose w' := [tuple tnth w (lift ord0 i) | i < L].
have Hw' : forall i : 'I_L, tnth w (lift ord0 i) = tnth w' i.
  by move=> i; rewrite tnth_mktuple.
have IH' := IH w'.
rewrite /word_eval in IH'.
rewrite (eq_bigr (fun i => tnth pgg_sigmas (tnth w' i))); last by move=> i _; rewrite Hw'.
rewrite [in RHS](eq_bigr (fun i => tnth pgg_sigmas (tnth w' i))); last by move=> i _; rewrite Hw'.
by rewrite IH'.
Qed.

Section s5x5_rho_pile1.

Variable R : realType.

(* Distribution equivalence *)
Lemma s5x5_rho_pile1_eq (L : nat) (s : 'I_5) :
  fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
           (@rho_from_words R 8 7 L s5x5_gen_tuple)
  = fdistmap (fun sigma' : {perm 'I_5} => widen5to10 (sigma' s))
             (@rho_from_words R 3 7 L s5_lazy_gen_tuple).
Proof.
rewrite /rho_from_words !fdistmap_comp.
apply/fdist_ext => x.
rewrite !fdistmapE.
apply: eq_bigl => w.
rewrite !inE /=.
by rewrite word_eval_pile1.
Qed.

End s5x5_rho_pile1.

(******************************************************************************)
(*  Section 6b. Pile-2 sheets and shifted lazy generator tuple.               *)
(*  Pile-2 sheets are positions 5-9 in 'I_10. The action of s5x5_gen_tuple    *)
(*  on a pile-2 sheet is the shifted analogue of pile-1: generators k in 4-7  *)
(*  act as path transpositions on the upper half, generators 0-3 are inert.   *)
(******************************************************************************)

Lemma rshift5_lt10 (s : 'I_5) : (val s + 5 < 10)%N.
Proof. by have := ltn_ord s; rewrite -(ltn_add2r 5). Qed.

(** rshift5to10 — right-shift embedding 'I_5 into pile-2 sheets {5..9} of 'I_10.
    Kind: instance. *)
Definition rshift5to10 (s : 'I_5) : 'I_10 := Ordinal (rshift5_lt10 s).

(** rshift5to10_inj — [rshift5to10] is injective.
    Kind: helper.
    Why: injectivity is required to pull TV distances back through [fdistmap].
    Used by: pile-2 TV-distance computations. *)
Lemma rshift5to10_inj : injective rshift5to10.
Proof.
move=> x y H. apply: val_inj.
have HH : val (rshift5to10 x) = val (rshift5to10 y) by rewrite H.
move: HH => /=.
by move/eqP; rewrite eqn_add2r => /eqP.
Qed.

(* Shifted lazy generator tuple: identities in slots 0-3, path tperms in 4-7. *)
Section s5_lazy_shifted_generators.

Local Notation o0 := (Ordinal (n:=5) (m:=0) erefl).
Local Notation o1 := (Ordinal (n:=5) (m:=1) erefl).
Local Notation o2 := (Ordinal (n:=5) (m:=2) erefl).
Local Notation o3 := (Ordinal (n:=5) (m:=3) erefl).
Local Notation o4 := (Ordinal (n:=5) (m:=4) erefl).

(** s5_lazy_gen_tuple' — shifted lazy generator tuple (identities first, path transpositions last).
    Kind: instance. *)
Definition s5_lazy_gen_tuple' : 8.-tuple {perm 'I_5} :=
  [tuple 1%g; 1%g; 1%g; 1%g;
         tperm o0 o1; tperm o1 o2; tperm o2 o3; tperm o3 o4].

End s5_lazy_shifted_generators.

(* Pile-2 per-step equivalence: generators k act on rshift5to10 s. *)
Lemma s5x5_gen_pile2_action (k : 'I_8) (s : 'I_5) :
  tnth s5x5_gen_tuple k (rshift5to10 s)
  = rshift5to10 (tnth s5_lazy_gen_tuple' k s).
Proof.
case: k => [[|k] Hk] //=.
  rewrite (tnth_nth 1%g) /=.
  rewrite (tnth_nth 1%g) /=.
  case: s => [[|[|[|[|[|sval]]]]] Hs] //=;
    apply: val_inj => /=;
    rewrite ?permE ?eqxx //=;
    rewrite /rshift5to10 /=.
case: k Hk => [|[|[|[|[|[|[|k]]]]]]] Hk //=.
all: rewrite !(tnth_nth 1%g) /=.
all: case: s => [[|[|[|[|[|sval]]]]] Hs] //=;
  apply: val_inj => /=;
  rewrite ?permE //=;
  rewrite /rshift5to10 /= ?perm1 //=.
Qed.

(* Word-level equivalence for pile-2 *)
Lemma word_eval_pile2 (L : nat) (w : L.-tuple 'I_8) (s : 'I_5) :
  word_eval (M:=Gen_PGGTypes s5x5_gen_tuple) w (rshift5to10 s)
  = rshift5to10 (word_eval (M:=Gen_PGGTypes s5_lazy_gen_tuple') w s).
Proof.
elim: L w s => [|L IH] w s.
  by rewrite tuple0 /word_eval !big_ord0 !perm1.
rewrite /word_eval !big_ord_recl.
rewrite !permM.
have ->: tnth (pgg_sigmas (s:=Gen_PGGTypes s5x5_gen_tuple)) (tnth w ord0) (rshift5to10 s)
       = rshift5to10 (tnth (pgg_sigmas (s:=Gen_PGGTypes s5_lazy_gen_tuple')) (tnth w ord0) s).
  exact: s5x5_gen_pile2_action.
pose w' := [tuple tnth w (lift ord0 i) | i < L].
have Hw' : forall i : 'I_L, tnth w (lift ord0 i) = tnth w' i.
  by move=> i; rewrite tnth_mktuple.
have IH' := IH w'.
rewrite /word_eval in IH'.
rewrite (eq_bigr (fun i => tnth pgg_sigmas (tnth w' i))); last by move=> i _; rewrite Hw'.
rewrite [in RHS](eq_bigr (fun i => tnth pgg_sigmas (tnth w' i))); last by move=> i _; rewrite Hw'.
by rewrite IH'.
Qed.

Section s5x5_rho_pile2.

Variable R : realType.

(** s5x5_rho_pile2_eq — pile-2 restriction of the S_5 x S_5 monodromy agrees with the shifted lazy walk.
    Kind: helper.
    Why: reduces the pile-2 endpoint distribution to the shifted lazy walk on 'I_5.
    Used by: pile-2 TV bound in the S_5 x S_5 convergence proof. *)
Lemma s5x5_rho_pile2_eq (L : nat) (s : 'I_5) :
  fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
           (@rho_from_words R 8 7 L s5x5_gen_tuple)
  = fdistmap (fun sigma' : {perm 'I_5} => rshift5to10 (sigma' s))
             (@rho_from_words R 3 7 L s5_lazy_gen_tuple').
Proof.
rewrite /rho_from_words !fdistmap_comp.
apply/fdist_ext => x.
rewrite !fdistmapE.
apply: eq_bigl => w.
rewrite !inE /=.
by rewrite word_eval_pile2.
Qed.

End s5x5_rho_pile2.

(******************************************************************************)
(*  Section 7. Pile uniform distributions and the gap to fdist_uniform_10.   *)
(******************************************************************************)

Section s5x5_pile_uniform.

Variable R : realType.

(** fdist_uniform_pile1 — uniform distribution on pile-1 sheets {0..4}, pushed forward into 'I_10.
    Kind: instance. *)
Definition fdist_uniform_pile1 : R.-fdist 'I_10 :=
  fdistmap widen5to10 (fdist_uniform (card_ord 5)).

(** fdist_uniform_pile2 — uniform distribution on pile-2 sheets {5..9}, pushed forward into 'I_10.
    Kind: instance. *)
Definition fdist_uniform_pile2 : R.-fdist 'I_10 :=
  fdistmap rshift5to10 (fdist_uniform (card_ord 5)).

(** fdist_uniform_pile1E — pointwise mass of the pile-1 uniform distribution.
    Kind: helper.
    Why: case-by-case formula for the pile-1 distribution on {0..9}.
    Used by: [var_dist_uniform_pile1_uniform10]. *)
Lemma fdist_uniform_pile1E (i : 'I_10) :
  fdist_uniform_pile1 i = if (val i < 5)%N then (5%:R^-1 : R) else 0.
Proof.
rewrite /fdist_uniform_pile1 fdistmapE.
case: (ltnP (val i) 5) => Hi.
- rewrite (bigD1 (Ordinal Hi)) //=; last by apply/eqP/val_inj.
  rewrite [X in _ + X = _]big1; first by rewrite addr0 fdist_uniformE card_ord.
  move=> j /andP [Hj1 Hj2].
  exfalso.
  apply: (negP Hj2).
  apply/eqP/widen5to10_inj.
  apply: val_inj => /=.
  by move: Hj1; rewrite inE => /eqP /(congr1 val) /=.
- apply: big1 => j /eqP Hj.
  exfalso.
  have Hjv : (val j < 5)%N by case: j {Hj}.
  have Hvi : (val (widen5to10 j) = val i)%N by rewrite Hj.
  have HV : (val i < 5)%N by rewrite -Hvi.
  by have := leq_ltn_trans Hi HV; rewrite ltnn.
Qed.

(** fdist_uniform_pile2E — pointwise mass of the pile-2 uniform distribution.
    Kind: helper.
    Why: case-by-case formula for the pile-2 distribution on {0..9}.
    Used by: [var_dist_uniform_pile2_uniform10]. *)
Lemma fdist_uniform_pile2E (i : 'I_10) :
  fdist_uniform_pile2 i = if (val i < 5)%N then 0 else (5%:R^-1 : R).
Proof.
rewrite /fdist_uniform_pile2 fdistmapE.
case: (ltnP (val i) 5) => Hi.
- apply: big1 => j /eqP Hj.
  exfalso.
  have Hge5 : (5 <= val (rshift5to10 j))%N by rewrite /= leq_addl.
  rewrite Hj in Hge5.
  by rewrite leqNgt Hi in Hge5.
- have Hj : (val i - 5 < 5)%N by rewrite ltn_subLR //; have := ltn_ord i.
  rewrite (bigD1 (Ordinal Hj)) //=; last first.
  + apply/eqP/val_inj => /=. by rewrite subnK.
  rewrite [X in _ + X = _]big1; first by rewrite addr0 fdist_uniformE card_ord.
  move=> k /andP [Hk1 Hk2].
  exfalso.
  apply: (negP Hk2).
  apply/eqP/val_inj => /=.
  move/eqP: Hk1 => Hk1.
  have Hkv : (val (rshift5to10 k) = val i)%N by rewrite Hk1.
  move: Hkv => /= Hkv.
  by apply/eqP; rewrite -(eqn_add2r 5) Hkv subnK.
Qed.

(** var_dist_uniform_pile1_uniform10 — TV-distance between uniform on pile-1 and uniform on {0..9} equals one.
    Kind: helper.
    Why: quantifies the residual gap from pile-supported distributions to the full-sheet uniform.
    Used by: final S_5 x S_5 convergence bound combining pile and full-sheet terms.
    Naming: the five components name both operands of the TV-distance precisely
    (pile-1 uniform vs uniform on 10 symbols); dropping any is ambiguous. *)
Lemma var_dist_uniform_pile1_uniform10 :
  var_dist fdist_uniform_pile1 (fdist_uniform (card_ord 10)) = 1.
Proof.
rewrite /var_dist.
rewrite (eq_bigr (fun _ : 'I_10 => 10%:R^-1 : R)); last first.
- move=> i _.
  rewrite fdist_uniform_pile1E fdist_uniformE card_ord.
  case: (ltnP (val i) 5) => _.
  + have step1 : (5%:R^-1 - 10%:R^-1 : R) = 10%:R^-1.
      apply: (mulIf (x := 10%:R)); first by rewrite pnatr_eq0.
      rewrite mulrBl mulVf ?pnatr_eq0 //.
      have ->: (10%:R = 5%:R * 2%:R :> R) by rewrite -natrM.
      rewrite mulrA mulVf ?pnatr_eq0 // mul1r.
      have ->: (2%:R = 1 + 1 :> R) by rewrite -natr1.
      by rewrite addrK.
    by rewrite step1 ger0_norm.
  + by rewrite sub0r normrN ger0_norm.
- rewrite sumr_const card_ord.
  rewrite -[X in (X *+ _)](mul1r).
  rewrite -mulrnAr.
  rewrite -mulr_natl.
  by rewrite divff ?pnatr_eq0 // mulr1.
Qed.

(** var_dist_uniform_pile2_uniform10 — TV-distance between uniform on pile-2 and uniform on {0..9} equals one.
    Kind: helper.
    Naming: the five components name both operands of the TV-distance precisely
    (pile-2 uniform vs uniform on 10 symbols); dropping any is ambiguous.
    Why: quantifies the residual gap from pile-supported distributions to the full-sheet uniform.
    Used by: final S_5 x S_5 convergence bound combining pile and full-sheet terms. *)
Lemma var_dist_uniform_pile2_uniform10 :
  var_dist fdist_uniform_pile2 (fdist_uniform (card_ord 10)) = 1.
Proof.
rewrite /var_dist.
rewrite (eq_bigr (fun _ : 'I_10 => 10%:R^-1 : R)); last first.
- move=> i _.
  rewrite fdist_uniform_pile2E fdist_uniformE card_ord.
  case: (ltnP (val i) 5) => _.
  + by rewrite sub0r normrN ger0_norm.
  + have step1 : (5%:R^-1 - 10%:R^-1 : R) = 10%:R^-1.
      apply: (mulIf (x := 10%:R)); first by rewrite pnatr_eq0.
      rewrite mulrBl mulVf ?pnatr_eq0 //.
      have ->: (10%:R = 5%:R * 2%:R :> R) by rewrite -natrM.
      rewrite mulrA mulVf ?pnatr_eq0 // mul1r.
      have ->: (2%:R = 1 + 1 :> R) by rewrite -natr1.
      by rewrite addrK.
    by rewrite step1 ger0_norm.
- rewrite sumr_const card_ord.
  rewrite -[X in (X *+ _)](mul1r).
  rewrite -mulrnAr.
  rewrite -mulr_natl.
  by rewrite divff ?pnatr_eq0 // mulr1.
Qed.

End s5x5_pile_uniform.

(******************************************************************************)
(*  Section 7b. Q matrix equality for the shifted lazy generator tuple.      *)
(*  Show schreier_transition R s5_lazy_gen_tuple' = schreier_transition R     *)
(*  s5_lazy_gen_tuple, hence the Rayleigh bound carries over.                 *)
(******************************************************************************)

Lemma s5_lazy_gen_invol' :
  forall k : 'I_8,
  (tnth s5_lazy_gen_tuple' k * tnth s5_lazy_gen_tuple' k)%g = 1%g.
Proof.
move=> k.
case: k => [[|[|[|[|[|[|[|[|?]]]]]]]] Hk] //;
  rewrite /s5_lazy_gen_tuple' ?tnth_mktuple //;
  try exact: tperm2; by rewrite mul1g.
Qed.

(** s5_lazy_tnth'_0 — slot 0 of the shifted lazy tuple is the identity.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_0 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=0) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_1 — slot 1 of the shifted lazy tuple is the identity.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_1 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=1) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_2 — slot 2 of the shifted lazy tuple is the identity.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_2 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=2) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_3 — slot 3 of the shifted lazy tuple is the identity.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_3 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=3) erefl) = 1%g.
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_4 — slot 4 of the shifted lazy tuple is a path transposition.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_4 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=4) erefl)
  = tperm (Ordinal (n:=5) (m:=0) erefl) (Ordinal (n:=5) (m:=1) erefl).
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_5 — slot 5 of the shifted lazy tuple is a path transposition.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_5 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=5) erefl)
  = tperm (Ordinal (n:=5) (m:=1) erefl) (Ordinal (n:=5) (m:=2) erefl).
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_6 — slot 6 of the shifted lazy tuple is a path transposition.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_6 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=6) erefl)
  = tperm (Ordinal (n:=5) (m:=2) erefl) (Ordinal (n:=5) (m:=3) erefl).
Proof. by rewrite (tnth_nth 1%g). Qed.
(** s5_lazy_tnth'_7 — slot 7 of the shifted lazy tuple is a path transposition.
    Kind: helper.
    Why: evaluates [tnth] at a specific index for use in entry-wise count proofs.
    Used by: [s5_lazy_count_eq']. *)
Lemma s5_lazy_tnth'_7 :
  tnth s5_lazy_gen_tuple' (Ordinal (n:=8) (m:=7) erefl)
  = tperm (Ordinal (n:=5) (m:=3) erefl) (Ordinal (n:=5) (m:=4) erefl).
Proof. by rewrite (tnth_nth 1%g). Qed.

(** s5_lazy_count_eq' — per-entry Schreier count for the shifted lazy tuple.
    Kind: helper.
    Why: entry-wise bridge between [s5_lazy_gen_tuple'] and [path_gen_tuple 3].
    Used by: [s5_lazy_Q_eq_swap]. *)
Lemma s5_lazy_count_eq' (i j : 'I_5) :
  schreier_gen_count s5_lazy_gen_tuple' i j
  = (schreier_gen_count (path_gen_tuple 3) i j
     + (if i == j then 4 else 0))%N.
Proof.
rewrite !schreier_gen_count_eq_sum.
rewrite sum_8_enum sum_4_enum.
rewrite s5_lazy_tnth'_0 s5_lazy_tnth'_1 s5_lazy_tnth'_2 s5_lazy_tnth'_3.
rewrite s5_lazy_tnth'_4 s5_lazy_tnth'_5 s5_lazy_tnth'_6 s5_lazy_tnth'_7.
rewrite path_gen_3_tnth_0 path_gen_3_tnth_1 path_gen_3_tnth_2 path_gen_3_tnth_3.
rewrite !perm1.
have H := eq_refl (i == j).
case: (i == j) H => /= H; rewrite ?addn0 //.
rewrite -[(_ + 4)%N]/(_ + (1 + 1 + 1 + 1))%N.
by rewrite [in RHS]addnC -!addnA.
Qed.

(** s5_lazy_Q_eq_swap — Schreier transition is invariant under the pile-1/pile-2 swap of generator slots.
    Kind: helper.
    Why: lets us reuse the pile-1 Rayleigh bound on the shifted tuple [s5_lazy_gen_tuple'].
    Used by: the pile-2 Rayleigh and TV-distance bounds. *)
Lemma s5_lazy_Q_eq_swap (R : realType) :
  schreier_transition R s5_lazy_gen_tuple'
  = schreier_transition R s5_lazy_gen_tuple.
Proof.
apply/matrixP => i j.
rewrite !mxE.
have ->: schreier_gen_count s5_lazy_gen_tuple' i j
       = schreier_gen_count s5_lazy_gen_tuple i j.
  by rewrite s5_lazy_count_eq' s5_lazy_count_eq.
by [].
Qed.

(******************************************************************************)
(*  Section 7c. TV bound for the shifted lazy walk.                           *)
(******************************************************************************)

Lemma s5_lazy_TV_bound' (R : realType) (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L s5_lazy_gen_tuple'))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L.
Proof.
apply: (@symm_ds_TV_bound R 7 3 s5_lazy_gen_tuple' s5_lazy_gen_invol'
          (s5_lazy_alpha_R R) L s).
- exact: s5_lazy_alpha_R_ge0.
- exact: s5_lazy_alpha_R_le1.
- move=> v Hv.
  have -> : schreier_transition R s5_lazy_gen_tuple'
          = schreier_transition R s5_lazy_gen_tuple.
    by rewrite (s5_lazy_Q_eq_swap R).
  exact: s5_lazy_rayleigh_Q2_R.
Qed.

(******************************************************************************)
(*  Section 8. Final triangle bound for s5x5 mixing.                          *)
(*  For each starting sheet s : 'I_10, the var_dist between the s5x5 walk    *)
(*  distribution and uniform_10 is bounded by                                  *)
(*    1 + sqrt(5) * lazy_alpha^L                                               *)
(*  via triangle inequality with the appropriate uniform_pile distribution.   *)
(******************************************************************************)

Section s5x5_spectral_bound.

Variable R : realType.

(* Pile-1 TV bound: distance to uniform_pile1 decays exponentially. *)
Lemma s5x5_pile1_TV_bound (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                     (@rho_from_words R 8 7 L s5x5_gen_tuple))
           (fdist_uniform_pile1 R)
  <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L.
Proof.
rewrite (@s5x5_rho_pile1_eq R L s).
rewrite /fdist_uniform_pile1.
have ->: fdistmap (fun sigma' : {perm 'I_5} => widen5to10 (sigma' s))
                  (@rho_from_words R 3 7 L s5_lazy_gen_tuple)
       = fdistmap widen5to10
                  (fdistmap (fun sigma' : {perm 'I_5} => sigma' s)
                            (@rho_from_words R 3 7 L s5_lazy_gen_tuple)).
  by rewrite -fdistmap_comp.
rewrite var_dist_fdistmap_inj; last exact: widen5to10_inj.
exact: s5_lazy_TV_bound.
Qed.

(* Pile-2 TV bound: distance to uniform_pile2 decays exponentially. *)
Lemma s5x5_pile2_TV_bound (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
                     (@rho_from_words R 8 7 L s5x5_gen_tuple))
           (fdist_uniform_pile2 R)
  <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L.
Proof.
rewrite (@s5x5_rho_pile2_eq R L s).
rewrite /fdist_uniform_pile2.
have ->: fdistmap (fun sigma' : {perm 'I_5} => rshift5to10 (sigma' s))
                  (@rho_from_words R 3 7 L s5_lazy_gen_tuple')
       = fdistmap rshift5to10
                  (fdistmap (fun sigma' : {perm 'I_5} => sigma' s)
                            (@rho_from_words R 3 7 L s5_lazy_gen_tuple')).
  by rewrite -fdistmap_comp.
rewrite var_dist_fdistmap_inj; last exact: rshift5to10_inj.
exact: s5_lazy_TV_bound'.
Qed.

(* Final triangle bound: combines the pile bound with the gap to uniform_10. *)
Lemma s5x5_spectral_TV_bound (L : nat) (s : 'I_10) :
  var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                     (@rho_from_words R 8 7 L s5x5_gen_tuple))
           (fdist_uniform (card_ord 10))
  <= 1 + Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L.
Proof.
case: (ltnP (val s) 5) => Hs.
- (* pile-1: s = widen5to10 s' for some s' : 'I_5 *)
  set s' : 'I_5 := Ordinal Hs.
  have Hseq : s = widen5to10 s' by apply: val_inj.
  rewrite Hseq.
  apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (fdist_uniform_pile1 R) _)).
  rewrite var_dist_uniform_pile1_uniform10.
  rewrite addrC.
  by rewrite lerD2l; exact: s5x5_pile1_TV_bound.
- (* pile-2: s = rshift5to10 s' for some s' : 'I_5 *)
  have Hs' : (val s - 5 < 5)%N by rewrite ltn_subLR //; have := ltn_ord s.
  set s' : 'I_5 := Ordinal Hs'.
  have Hseq : s = rshift5to10 s'.
    apply: val_inj => /=.
    by rewrite subnK.
  rewrite Hseq.
  apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (fdist_uniform_pile2 R) _)).
  rewrite var_dist_uniform_pile2_uniform10.
  rewrite addrC.
  by rewrite lerD2l; exact: s5x5_pile2_TV_bound.
Qed.

End s5x5_spectral_bound.
