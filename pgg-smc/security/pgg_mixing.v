(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* General Mixing Lemma for Symmetric Doubly-Stochastic Schreier Matrices     *)
(*                                                                            *)
(* This file proves the generic total-variation-distance bound                *)
(*                                                                            *)
(*   var_dist(Q^L e_s, U) <= sqrt(N) * alpha^L                                *)
(*                                                                            *)
(* for any symmetric doubly-stochastic matrix Q whose restriction to the      *)
(* orthogonal complement of the all-ones vector has operator norm at most     *)
(* alpha.  The operator-norm hypothesis is stated in its per-instance form as *)
(* a Rayleigh bound on Q^2 (not Q): for every column vector v with sum zero   *)
(*                                                                            *)
(*   <v, Q^2 v> <= alpha^2 <v, v>.                                            *)
(*                                                                            *)
(* This is the correct shape because ||Q v||^2 = <v, Q^T Q v> = <v, Q^2 v>    *)
(* when Q is symmetric, so bounding <v, Q v> alone does not imply             *)
(* ||Q v|| <= alpha ||v||.                                                    *)
(*                                                                            *)
(* Instances (e.g. pgg_smc/instances/s5/s5_mixing.v) discharge the Rayleigh   *)
(* hypothesis by a concrete Sylvester check on B^T (alpha^2 I - Q^2) B where  *)
(* B is a basis matrix for the sum-zero subspace.                             *)
(*                                                                            *)
(* == Contents ==                                                             *)
(*                                                                            *)
(* Cauchy-Schwarz over finite index sums:                                     *)
(*   cauchy_schwarz_bigR                                                      *)
(*                                                                            *)
(* Bridge from variation distance (L1) to L2 norm:                            *)
(*   var_dist_le_sqrtN_norm2                                                  *)
(*                                                                            *)
(* Power-norm contraction under Rayleigh-on-Q^2:                              *)
(*   symm_ds_step_norm_sq_bound, symm_ds_power_norm_sq_bound                  *)
(*                                                                            *)
(* Total-variation bound (main theorem):                                      *)
(*   symm_ds_TV_bound                                                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg matrix mxalgebra.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_collusion_bound pgg_schreier.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Section 1: Cauchy-Schwarz inequality over a finite index               *)
(******************************************************************************)

(* Lagrange identity route:
     A * C - B^2 = (1/2) * sum_{i,j} (v_i w_j - v_j w_i)^2 >= 0. *)
Lemma cauchy_schwarz_bigR (R : realType) (I : finType) (vv ww : I -> R) :
  (\sum_i vv i * ww i) ^+ 2 <= (\sum_i (vv i) ^+ 2) * (\sum_i (ww i) ^+ 2).
Proof.
rewrite -subr_ge0.
have Hlag :
  (\sum_i (vv i) ^+ 2) * (\sum_i (ww i) ^+ 2) - (\sum_i vv i * ww i) ^+ 2
  = \sum_i \sum_j vv i * ww j * (vv i * ww j - vv j * ww i).
  rewrite mulr_suml.
  under eq_bigr do rewrite mulr_sumr.
  rewrite expr2 mulr_suml.
  under [X in _ - X]eq_bigr do rewrite mulr_sumr.
  rewrite -sumrB.
  apply: eq_bigr => i _.
  rewrite -sumrB.
  apply: eq_bigr => j _.
  rewrite mulrBr; congr (_ - _).
    by rewrite !expr2 mulrACA.
  by rewrite mulrACA [ww i * _]mulrC mulrACA.
have Hsym :
  \sum_i \sum_j vv i * ww j * (vv i * ww j - vv j * ww i)
  = \sum_i \sum_j vv j * ww i * (vv j * ww i - vv i * ww j).
  by rewrite exchange_big.
have Hdouble :
  (\sum_i \sum_j vv i * ww j * (vv i * ww j - vv j * ww i)) *+ 2
  = \sum_i \sum_j (vv i * ww j - vv j * ww i) ^+ 2.
  rewrite mulr2n {2}Hsym -big_split /=.
  apply: eq_bigr => i _.
  rewrite -big_split /=.
  apply: eq_bigr => j _.
  have -> :
    vv j * ww i * (vv j * ww i - vv i * ww j)
    = - (vv j * ww i) * (vv i * ww j - vv j * ww i).
    by rewrite mulNr -mulrN opprB.
  by rewrite -mulrDl expr2.
have Hnneg :
  0 <= \sum_i \sum_j (vv i * ww j - vv j * ww i) ^+ 2.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; exact: sqr_ge0.
rewrite Hlag -Hdouble in Hnneg *.
by rewrite pmulrn_lge0 in Hnneg.
Qed.

(******************************************************************************)
(*     Section 2: Bridge from variation distance to L^2 norm                  *)
(******************************************************************************)

(* For any two distributions P, Q over a finite set of size N,
     var_dist(P, Q) = sum_a |P a - Q a|
                   <= sqrt(N) * sqrt(sum_a (P a - Q a)^2)
   by Cauchy-Schwarz applied to constant 1 against |P - Q|. *)
Lemma var_dist_le_sqrtN_norm2 (R : realType) (A : finType)
    (P Q : R.-fdist A) :
  var_dist P Q
  <= Num.sqrt #|A|%:R * Num.sqrt (\sum_(a : A) (P a - Q a) ^+ 2).
Proof.
rewrite /var_dist.
set x := \sum_(a : A) `|P a - Q a|.
set y := \sum_(a : A) (P a - Q a) ^+ 2.
have x_ge0 : 0 <= x by apply: sumr_ge0 => a _; exact: normr_ge0.
have y_ge0 : 0 <= y by apply: sumr_ge0 => a _; exact: sqr_ge0.
have CardA_ge0 : 0 <= (#|A|%:R : R) by rewrite ler0n.
have Hsq : x ^+ 2 <= #|A|%:R * y.
  have H := cauchy_schwarz_bigR (fun a : A => (1 : R)) (fun a : A => `|P a - Q a|).
  have Hx : \sum_(a : A) (1 : R) * `|P a - Q a| = x.
    by apply: eq_bigr => a _; rewrite mul1r.
  have H1 : \sum_(a : A) (1 : R) ^+ 2 = #|A|%:R.
    by rewrite (eq_bigr (fun _ => 1)); [rewrite sumr_const// | move=> a _; rewrite expr1n].
  have Hy : \sum_(a : A) `|P a - Q a| ^+ 2 = y.
    by rewrite /y; apply: eq_bigr => a _; rewrite real_normK // num_real.
  by rewrite Hx H1 Hy in H.
(* From x^2 <= #A * y and x, y, #A >= 0, deduce x <= sqrt(#A) * sqrt(y). *)
have sqN_ge0 : 0 <= Num.sqrt (#|A|%:R : R) by exact: sqrtr_ge0.
have sqy_ge0 : 0 <= Num.sqrt y by exact: sqrtr_ge0.
rewrite -[X in X <= _](@ger0_norm _ x x_ge0) -(@sqrtr_sqr R).
have Hless : Num.sqrt (x ^+ 2) <= Num.sqrt (#|A|%:R * y).
  by apply: ler_wsqrtr; rewrite Hsq.
by rewrite -sqrtrM ?ler0n.
Qed.

(******************************************************************************)
(*     Section 3: Inner product and norm for column vectors                   *)
(******************************************************************************)

Section cV_inner.

Variable R : realType.
Variable N : nat.

(* <v, w> = v^T * w, read off as a scalar *)
Definition cV_inner (v w : 'cV[R]_N) : R := (v^T *m w) ord0 ord0.

(** cV_innerE — column-vector inner product expressed as a sum over coordinates.
    Kind: helper.
    Why: turns the matrix-product definition of cV_inner into a sum, enabling pointwise reasoning.
    Used by: cV_inner_sym, cV_inner_ge0, cV_inner_self_sum.
*)
Lemma cV_innerE (v w : 'cV[R]_N) :
  cV_inner v w = \sum_i v i ord0 * w i ord0.
Proof. by rewrite /cV_inner mxE; apply: eq_bigr => i _; rewrite mxE. Qed.

(** cV_inner_sym — column-vector inner product is symmetric.
    Kind: helper.
    Used by: downstream norm manipulations where commutativity is invoked.
*)
Lemma cV_inner_sym (v w : 'cV[R]_N) : cV_inner v w = cV_inner w v.
Proof.
rewrite !cV_innerE.
by apply: eq_bigr => i _; rewrite mulrC.
Qed.

(** cV_inner_ge0 — self inner product is non-negative.
    Kind: helper.
    Used by: Cauchy--Schwarz and spectral bounds in this file.
*)
Lemma cV_inner_ge0 (v : 'cV[R]_N) : 0 <= cV_inner v v.
Proof. rewrite cV_innerE; apply: sumr_ge0 => i _; rewrite -expr2; exact: sqr_ge0. Qed.

(** cV_inner_self_sum — self inner product equals the sum of squared coordinates.
    Kind: helper.
    Why: expresses ||v||^2 as a plain coordinate sum, needed to compare against vec_norm2.
    Used by: vec_norm2 identities and norm-squared bound derivations.
*)
Lemma cV_inner_self_sum (v : 'cV[R]_N) :
  cV_inner v v = \sum_i (v i ord0) ^+ 2.
Proof. by rewrite cV_innerE; apply: eq_bigr => i _; rewrite expr2. Qed.

(* ||Q v||^2 = <Q v, Q v> = v^T Q^T Q v.  When Q^T = Q this equals v^T Q^2 v. *)
Lemma cV_inner_Qv_Qv (Q : 'M[R]_N) (v : 'cV[R]_N) :
  cV_inner (Q *m v) (Q *m v) = (v^T *m (Q^T *m Q) *m v) ord0 ord0.
Proof.
rewrite /cV_inner trmx_mul.
by rewrite !mulmxA.
Qed.

(** cV_inner_Qv_Qv_symm — for symmetric Q, ||Qv||^2 equals v^T Q^2 v.
    Kind: helper.
    Why: exploits Q^T = Q to collapse Q^T Q to Q^2 in the quadratic form, used in spectral bound derivations.
    Used by: symm_ds_step_norm_sq_bound and other symmetric-Q bounds.
*)
Lemma cV_inner_Qv_Qv_symm (Q : 'M[R]_N) (v : 'cV[R]_N) :
  Q^T = Q ->
  cV_inner (Q *m v) (Q *m v) = (v^T *m (Q *m Q) *m v) ord0 ord0.
Proof. by move=> Qsym; rewrite cV_inner_Qv_Qv Qsym. Qed.

End cV_inner.

(******************************************************************************)
(*     Section 4: Symmetric doubly-stochastic structure                       *)
(******************************************************************************)

Section symm_ds.

Variable R : realType.
Variable N' : nat.
Let N := N'.+1.
Variable Q : 'M[R]_N.

(* Q is doubly stochastic: every row and every column sums to 1. *)
Hypothesis Q_ge0 : forall i j, 0 <= Q i j.
Hypothesis Q_row_sum : forall i, \sum_j Q i j = 1.
Hypothesis Q_col_sum : forall j, \sum_i Q i j = 1.

(* For a sum-zero column vector v (i.e. sum_i v_i = 0), Q *m v also has sum zero. *)
Lemma sum_Qv_zero (v : 'cV[R]_N) :
  \sum_i v i ord0 = 0 ->
  \sum_i (Q *m v) i ord0 = 0.
Proof.
move=> Hsum.
under eq_bigr do rewrite mxE.
rewrite exchange_big /=.
transitivity (\sum_j v j ord0 * \sum_i Q i j).
  apply: eq_bigr => j _.
  rewrite mulr_sumr; apply: eq_bigr => i _; by rewrite mulrC.
under eq_bigr do rewrite Q_col_sum mulr1.
exact: Hsum.
Qed.

Variable alpha : R.
Hypothesis alpha_ge0 : 0 <= alpha.

(* The Rayleigh-on-Q^2 hypothesis: for v in 1-perp, <v, Q^2 v> <= alpha^2 <v, v>. *)
Hypothesis rayleigh_Qsq :
  forall v : 'cV[R]_N,
  \sum_i v i ord0 = 0 ->
  (v^T *m (Q *m Q) *m v) ord0 ord0 <= alpha ^+ 2 * cV_inner v v.

Hypothesis Q_symm : Q^T = Q.

(** symm_ds_step_norm_sq_bound — one-step Rayleigh bound: <Qv,Qv> <= alpha^2 <v,v> on the 1-perp subspace.
    Kind: helper.
    Why: single-step spectral contraction on the mean-zero subspace used to seed the iterated bound.
    Used by: symm_ds_power_norm_sq_bound.
    Naming: five components capture subject (symm_ds) / granularity (step) / quantity (norm_sq) / direction (bound); shorter names conflict with the iterated variant below.
    Step 1: <Q v, Q v> <= alpha^2 * <v, v> for v in 1-perp.
*)
Lemma symm_ds_step_norm_sq_bound (v : 'cV[R]_N) :
  \sum_i v i ord0 = 0 ->
  cV_inner (Q *m v) (Q *m v) <= alpha ^+ 2 * cV_inner v v.
Proof.
move=> Hsum.
rewrite cV_inner_Qv_Qv_symm //.
exact: rayleigh_Qsq.
Qed.

(** symm_ds_power_norm_sq_bound — iterated Rayleigh bound: <Q^L v, Q^L v> <= alpha^{2L} <v,v> on 1-perp.
    Kind: helper.
    Why: the L-iterated spectral contraction; follows symm_ds_step_norm_sq_bound by induction on L.
    Used by: symm_ds_power_norm2_bound and symm_ds_TV_bound_cV.
    Naming: parallels symm_ds_step_norm_sq_bound; the power variant is explicitly tagged.
    Iterated power: <Q^L v, Q^L v> <= alpha^{2L} * <v, v> for v in 1-perp.
*)
Lemma symm_ds_power_norm_sq_bound (L : nat) (v : 'cV[R]_N) :
  \sum_i v i ord0 = 0 ->
  cV_inner (Q ^+ L *m v) (Q ^+ L *m v) <= alpha ^+ (2 * L) * cV_inner v v.
Proof.
move=> Hsum.
elim: L => [|L IH].
  rewrite expr0 mul1mx muln0 expr0 mul1r.
  exact: Order.POrderTheory.lexx.
(* Q^{L+1} v = Q (Q^L v). Let w = Q^L v; by induction <w,w> <= alpha^{2L} <v,v>. *)
rewrite exprS -mulmxA.
set w := Q ^+ L *m v.
have Hw_sum : \sum_i w i ord0 = 0.
  rewrite /w {w IH}.
  elim: L => [|K IHK].
    by rewrite expr0 mul1mx.
  rewrite exprS -mulmxA.
  exact: sum_Qv_zero.
(* <Q w, Q w> <= alpha^2 <w, w> <= alpha^2 * alpha^{2L} <v, v>. *)
apply: (@Order.POrderTheory.le_trans _ _ (alpha ^+ 2 * cV_inner w w)).
  by apply: symm_ds_step_norm_sq_bound.
rewrite mulnS exprD -mulrA.
apply: ler_wpM2l.
  by apply: exprn_ge0.
exact: IH.
Qed.

End symm_ds.

(******************************************************************************)
(*     Section 5: Total-variation bound                                       *)
(*                                                                            *)
(* Combines the power-norm bound with the sqrt(N) bridge and the identity     *)
(* ||e_s - U||_2^2 = 1 - 1/N <= 1 to conclude                                 *)
(*                                                                            *)
(*   var_dist(Q^L e_s, U) <= sqrt(N) * alpha^L.                               *)
(******************************************************************************)

Section TV_bound.

Variable R : realType.
Variable N' : nat.
Let N := N'.+1.

(* The endpoint column vector P_L from starting sheet s: (Q^L) *m e_s. *)
(* Convention: we assume the bridge lemma supplies us with an fdist P whose
   column representation satisfies P a = (Q^L *m e_s) a 0.  See
   pgg-smc/security/pgg_schreier.v's schreier_walk_eq_endpoint for the concrete
   bridge from fdistmap ... rho_from_words to entries of the matrix power. *)

Variable Q : 'M[R]_N.
Hypothesis Q_ge0 : forall i j, 0 <= Q i j.
Hypothesis Q_row_sum : forall i, \sum_j Q i j = 1.
Hypothesis Q_col_sum : forall j, \sum_i Q i j = 1.
Hypothesis Q_symm : Q^T = Q.

Variable alpha : R.
Hypothesis alpha_ge0 : 0 <= alpha.
Hypothesis alpha_le1 : alpha <= 1.
Hypothesis rayleigh_Qsq :
  forall v : 'cV[R]_N,
  \sum_i v i ord0 = 0 ->
  (v^T *m (Q *m Q) *m v) ord0 ord0 <= alpha ^+ 2 * cV_inner v v.

(* A distribution's difference-from-uniform as a column vector. *)
(* For a finite distribution P over 'I_N, we form the difference column vector
     diffcol P := P - (1/N) * 1,
   and show ||diffcol P||_2^2 <= 1 and use the mixing lemma on it. *)

(* Given an fdist P : R.-fdist 'I_N, its column vector. *)
Definition fdist_cV (P : R.-fdist 'I_N) : 'cV[R]_N :=
  \col_i P i.

(* The uniform column vector. *)
Definition uniform_cV : 'cV[R]_N := \col_i (#|'I_N|%:R^-1 : R).

(* Q takes uniform to uniform (Q is row-stochastic => Q * 1 = 1 => Q U = U). *)
Lemma Q_fixes_uniform : Q *m uniform_cV = uniform_cV.
Proof.
apply/matrixP => i j; rewrite !mxE.
have -> : \sum_(j0 : 'I_N) Q i j0 * uniform_cV j0 j
        = #|'I_N|%:R^-1 * \sum_(j0 : 'I_N) Q i j0.
  rewrite mulr_sumr.
  by apply: eq_bigr => j0 _; rewrite mxE mulrC.
by rewrite Q_row_sum mulr1.
Qed.

(* The point mass e_s. *)
Definition e_cV (s : 'I_N) : 'cV[R]_N := \col_i (i == s)%:R.

(** e_cV_sum — coordinates of a point-mass column vector sum to 1.
    Kind: helper.
    Why: records that the indicator column e_s is a probability vector.
    Used by: symm_ds_TV_bound_cV, where the mean-zero witness is e_s - U.
*)
Lemma e_cV_sum (s : 'I_N) : \sum_i (e_cV s) i ord0 = 1.
Proof.
rewrite /e_cV.
under eq_bigr do rewrite mxE.
by rewrite (bigD1 s)//= eqxx big1 ?addr0// => j /negPf->.
Qed.

(** uniform_cV_sum — coordinates of the uniform column vector sum to 1.
    Kind: helper.
    Why: records that the uniform column is itself a probability vector.
    Used by: mean-zero witnessing for e_s - U in the Rayleigh bound pipeline.
*)
Lemma uniform_cV_sum : \sum_i uniform_cV i ord0 = 1.
Proof.
rewrite /uniform_cV.
under eq_bigr do rewrite mxE.
rewrite sumr_const card_ord /=.
by rewrite -[LHS]mulr_natr mulVf // pnatr_eq0.
Qed.

(* The centred vector v_s := e_s - U has sum zero. *)
Lemma es_minus_U_sum_zero (s : 'I_N) :
  \sum_i (e_cV s - uniform_cV) i ord0 = 0.
Proof.
rewrite /e_cV /uniform_cV.
under eq_bigr do rewrite !mxE.
rewrite sumrB.
rewrite sumr_const card_ord -[_ *+ _]mulr_natr mulVf;
  last by rewrite pnatr_eq0.
rewrite (bigD1 s)//= eqxx big1; last by move=> j /negPf->.
by rewrite addr0 subrr.
Qed.

(* <e_s - U, e_s - U> = 1 - 1/N. *)
Lemma es_minus_U_norm_sq (s : 'I_N) :
  cV_inner (e_cV s - uniform_cV) (e_cV s - uniform_cV) = 1 - #|'I_N|%:R^-1.
Proof.
rewrite cV_inner_self_sum /e_cV /uniform_cV.
under eq_bigr do rewrite !mxE.
under eq_bigr do rewrite sqrrB.
rewrite big_split /=.
rewrite big_split /=.
have H1 : \sum_(i : 'I_N) ((i == s)%:R : R) ^+ 2 = 1.
  rewrite (bigD1 s)//= eqxx expr1n big1 ?addr0// => j /negPf->.
  by rewrite expr0n.
have H3 : \sum_(i : 'I_N) (#|'I_N|%:R^-1 : R) ^+ 2 = #|'I_N|%:R^-1.
  rewrite big_const card_ord iter_addr addr0 expr2.
  rewrite -(mulr_natr (N%:R^-1 / N%:R) N).
  by rewrite -mulrA mulVf ?pnatr_eq0 // mulr1.
rewrite H1 H3.
under eq_bigr do rewrite -mulNrn.
rewrite (bigD1 s)//= eqxx big1; last first.
  by move=> j /negPf->; rewrite mul0r oppr0 mul0rn.
rewrite addr0 /= mul1r mulr2n.
by rewrite -addrA -[_ - _ + _]addrA addNr addr0.
Qed.

(** es_minus_U_norm_sq_le1 — ||e_s - U||^2 is at most 1.
    Kind: helper.
    Why: bounds the norm of the point-mass mean-zero witness used in the spectral-to-TV conversion.
    Used by: symm_ds_TV_bound_cV.
*)
Lemma es_minus_U_norm_sq_le1 (s : 'I_N) :
  cV_inner (e_cV s - uniform_cV) (e_cV s - uniform_cV) <= 1.
Proof.
rewrite es_minus_U_norm_sq.
by rewrite gerBl invr_ge0 ler0n.
Qed.

(* The L^2 norm of a column vector. *)
Definition vec_norm2 (v : 'cV[R]_N) : R := Num.sqrt (cV_inner v v).

(** vec_norm2_ge0 — the L^2 norm is non-negative.
    Kind: helper.
    Why: sanitises sqrt-based norms for downstream algebraic manipulations.
    Used by: symm_ds_power_norm2_bound and sqrt-based spectral derivations.
*)
Lemma vec_norm2_ge0 (v : 'cV[R]_N) : 0 <= vec_norm2 v.
Proof. exact: sqrtr_ge0. Qed.

(** symm_ds_power_norm2_bound — ||Q^L v|| <= alpha^L ||v|| on the 1-perp subspace.
    Kind: helper.
    Why: the sqrt form of symm_ds_power_norm_sq_bound, directly usable in Cauchy--Schwarz arguments.
    Used by: symm_ds_TV_bound_cV.
    Naming: five components match the sibling symm_ds_power_norm_sq_bound; "norm2" disambiguates from "norm_sq".
    Task 1: sqrt of the power norm bound.
*)
Lemma symm_ds_power_norm2_bound (L : nat) (v : 'cV[R]_N) :
  \sum_i v i ord0 = 0 ->
  vec_norm2 (Q ^+ L *m v) <= alpha ^+ L * vec_norm2 v.
Proof.
move=> Hsum.
rewrite /vec_norm2.
have Hbound :=
  symm_ds_power_norm_sq_bound Q_col_sum alpha_ge0 rayleigh_Qsq Q_symm L Hsum.
have Heq : alpha ^+ (2 * L) = (alpha ^+ L) ^+ 2 by rewrite mulnC exprM.
rewrite Heq in Hbound.
have aL_ge0 : 0 <= alpha ^+ L by exact: exprn_ge0.
have inner_ge0 : 0 <= cV_inner v v by exact: cV_inner_ge0.
have Hrhs :
  Num.sqrt ((alpha ^+ L) ^+ 2 * cV_inner v v)
  = alpha ^+ L * Num.sqrt (cV_inner v v).
  by rewrite sqrtrM ?sqr_ge0// sqrtr_sqr ger0_norm.
rewrite -Hrhs.
exact: ler_wsqrtr.
Qed.

(* Q^L also fixes the uniform vector. *)
Lemma Q_power_fixes_uniform (L : nat) :
  Q ^+ L *m uniform_cV = uniform_cV.
Proof.
elim: L => [|L IH].
  by rewrite expr0 mul1mx.
by rewrite exprS -mulmxA IH Q_fixes_uniform.
Qed.

(* L^1 to L^2 bridge for column vectors. *)
Lemma cV_l1_le_sqrtN_norm2 (w : 'cV[R]_N) :
  \sum_a `|w a ord0| <= Num.sqrt (#|'I_N|%:R) * vec_norm2 w.
Proof.
rewrite /vec_norm2 cV_inner_self_sum.
set x := \sum_a `|w a ord0|.
set y := \sum_a (w a ord0) ^+ 2.
have x_ge0 : 0 <= x by apply: sumr_ge0 => a _; exact: normr_ge0.
have y_ge0 : 0 <= y by apply: sumr_ge0 => a _; exact: sqr_ge0.
have CardA_ge0 : 0 <= (#|'I_N|%:R : R) by rewrite ler0n.
have Hsq : x ^+ 2 <= #|'I_N|%:R * y.
  have H := cauchy_schwarz_bigR
    (fun a : 'I_N => (1 : R)) (fun a : 'I_N => `|w a ord0|).
  have Hx : \sum_a (1 : R) * `|w a ord0| = x.
    by apply: eq_bigr => a _; rewrite mul1r.
  have H1 : \sum_(a : 'I_N) (1 : R) ^+ 2 = #|'I_N|%:R.
    by rewrite (eq_bigr (fun _ => 1));
       [rewrite sumr_const// | move=> a _; rewrite expr1n].
  have Hy : \sum_a `|w a ord0| ^+ 2 = y.
    by rewrite /y; apply: eq_bigr => a _; rewrite real_normK // num_real.
  by rewrite Hx H1 Hy in H.
rewrite -[X in X <= _](@ger0_norm _ x x_ge0) -(@sqrtr_sqr R).
have Hless : Num.sqrt (x ^+ 2) <= Num.sqrt (#|'I_N|%:R * y).
  by apply: ler_wsqrtr; rewrite Hsq.
by rewrite -sqrtrM ?ler0n.
Qed.

(* The L^2 norm of e_s - U is at most 1. *)
Lemma es_minus_U_norm2_le1 (s : 'I_N) :
  vec_norm2 (e_cV s - uniform_cV) <= 1.
Proof.
rewrite /vec_norm2.
have H1 : Num.sqrt (1 : R) = 1 by exact: sqrtr1.
rewrite -[X in _ <= X]H1.
apply: ler_wsqrtr.
exact: es_minus_U_norm_sq_le1.
Qed.

(* Task 2 (column-vector form): the main TV bound, in vector form.
   Combines L1-to-L2 bridge, the sqrt'd power bound, and ||e_s - U||_2 <= 1. *)
Lemma symm_ds_TV_bound_cV (L : nat) (s : 'I_N) :
  \sum_a `|(Q ^+ L *m e_cV s) a ord0 - uniform_cV a ord0|
  <= Num.sqrt (#|'I_N|%:R) * alpha ^+ L.
Proof.
have HQU : Q ^+ L *m uniform_cV = uniform_cV by exact: Q_power_fixes_uniform.
set w := Q ^+ L *m (e_cV s - uniform_cV).
have Hw_eq : w = Q ^+ L *m e_cV s - uniform_cV.
  rewrite /w mulmxBr; congr (_ - _); exact: HQU.
have Hsum_eq :
  \sum_a `|(Q ^+ L *m e_cV s) a ord0 - uniform_cV a ord0|
  = \sum_a `|w a ord0|.
  by apply: eq_bigr => a _; rewrite Hw_eq !mxE.
rewrite Hsum_eq.
apply: (@Order.POrderTheory.le_trans _ _
  (Num.sqrt #|'I_N|%:R * vec_norm2 w)).
  exact: cV_l1_le_sqrtN_norm2.
have HsqN_ge0 : 0 <= Num.sqrt (#|'I_N|%:R : R) by exact: sqrtr_ge0.
apply: ler_wpM2l => //.
have Hsum0 : \sum_i (e_cV s - uniform_cV) i ord0 = 0.
  exact: es_minus_U_sum_zero.
apply: (@Order.POrderTheory.le_trans _ _
  (alpha ^+ L * vec_norm2 (e_cV s - uniform_cV))).
  exact: symm_ds_power_norm2_bound.
have HaL_ge0 : 0 <= alpha ^+ L by exact: exprn_ge0.
rewrite -[X in _ <= X]mulr1.
apply: ler_wpM2l => //.
exact: es_minus_U_norm2_le1.
Qed.

End TV_bound.

(******************************************************************************)
(*     Section 6: Schreier matrix bridges                                     *)
(*                                                                            *)
(* When the generators are all involutions, the Schreier transition matrix    *)
(* `schreier_transition R sigmas` is symmetric and doubly stochastic, so the  *)
(* general TV bound applies.                                                  *)
(******************************************************************************)

Section schreier_bridges.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Hypothesis sigmas_invol :
  forall k : 'I_Tg, (tnth sigmas k * tnth sigmas k)%g = 1%g.

(* Task 3: under self-inverse generators, the Schreier transition is symmetric. *)
Lemma schreier_transition_symm :
  (schreier_transition R sigmas)^T = schreier_transition R sigmas.
Proof.
apply/matrixP => i j; rewrite !mxE.
congr (_%:R / _).
rewrite /schreier_gen_count.
have Heq :
  forall k : 'I_Tg, (tnth sigmas k j == i) = (tnth sigmas k i == j).
  move=> k.
  apply/eqP/eqP => Hk.
    have step : tnth sigmas k (tnth sigmas k j) = j.
      by move: (sigmas_invol k);
         move/(congr1 (fun g : {perm _} => g j)); rewrite permM perm1.
    by rewrite -Hk; exact: step.
  have step : tnth sigmas k (tnth sigmas k i) = i.
    by move: (sigmas_invol k);
       move/(congr1 (fun g : {perm _} => g i)); rewrite permM perm1.
  by rewrite -Hk; exact: step.
apply: eq_card => k; rewrite !inE.
exact: Heq.
Qed.

(** schreier_transition_doubly_stochastic_col — column sums of the Schreier transition matrix equal 1.
    Kind: helper.
    Why: combined with the row-sum version this yields double stochasticity, required for the symmetric spectral argument.
    Used by: symm_ds_TV_bound.
    Naming: five components capture subject (schreier_transition) / property (doubly_stochastic) / axis (col); renaming would lose parallel structure with the row variant.
    Task 4: column sum equals 1, completing doubly stochastic.
*)
Lemma schreier_transition_doubly_stochastic_col (j : 'I_N) :
  \sum_i schreier_transition R sigmas i j = 1.
Proof.
have Hsym := schreier_transition_symm.
transitivity (\sum_i schreier_transition R sigmas j i).
  apply: eq_bigr => i _.
  have entry_eq :
    forall i j,
      schreier_transition R sigmas i j = schreier_transition R sigmas j i.
    move=> i' j'.
    have /matrixP /(_ j' i') := Hsym.
    by rewrite mxE.
  by rewrite (entry_eq j i).
exact: schreier_transition_stochastic.
Qed.

(* Task 5: bridge from fdistmap-of-rho to the (Q^L *m e_s) column entry. *)
Lemma schreier_endpoint_eq_Q_power (L : nat) (s a : 'I_N) :
  fdistmap (fun sigma : {perm 'I_N} => sigma s) (rho_from_words L sigmas) a
  = ((schreier_transition R sigmas) ^+ L *m \col_i (i == s)%:R) a ord0.
Proof.
have Hsym := schreier_transition_symm.
have HQLsymm :
  ((schreier_transition R sigmas) ^+ L)^T = (schreier_transition R sigmas) ^+ L.
  elim: L => [|L IH].
    by rewrite expr0 trmx1.
  by rewrite exprS trmx_mul IH -exprS exprSr Hsym.
have entry_eq :
  forall i j,
    ((schreier_transition R sigmas) ^+ L) i j
    = ((schreier_transition R sigmas) ^+ L) j i.
  move=> i j.
  have /matrixP /(_ j i) := HQLsymm.
  by rewrite mxE.
rewrite mxE.
rewrite (bigD1 s)//= mxE eqxx mulr1 big1; last first.
  by move=> j /negPf Hj; rewrite mxE Hj mulr0.
rewrite addr0.
rewrite entry_eq.
by rewrite -schreier_walk_eq_endpoint.
Qed.

End schreier_bridges.

(******************************************************************************)
(*     Section 7: Schreier-form total-variation bound                         *)
(*                                                                            *)
(* Task 2 (final form): combines the column-vector TV bound, the bridge       *)
(* lemmas of Section 6, and the Rayleigh hypothesis on Q^2 to deliver the     *)
(* exact shape of `SchreierCertificate.sc_convergence`.                       *)
(******************************************************************************)

Section schreier_TV_bound.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Hypothesis sigmas_invol :
  forall k : 'I_Tg, (tnth sigmas k * tnth sigmas k)%g = 1%g.

(** symm_ds_TV_bound — TV bound between iterated Schreier transition from e_s and uniform, in terms of the spectral constant alpha.
    Kind: main.
    Why: headline spectral-mixing result for the symmetric doubly-stochastic transition kernel.
*)
Lemma symm_ds_TV_bound (alpha : R) (L : nat) (s : 'I_N) :
  0 <= alpha ->
  alpha <= 1 ->
  (forall v : 'cV[R]_N,
    \sum_i v i ord0 = 0 ->
    (v^T *m (schreier_transition R sigmas *m schreier_transition R sigmas) *m v)
      ord0 ord0
    <= alpha ^+ 2 * cV_inner v v) ->
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
             (rho_from_words L sigmas))
           (fdist_uniform (card_ord N))
  <= Num.sqrt (N%:R) * alpha ^+ L.
Proof.
move=> alpha_ge0 alpha_le1 rayleigh_Qsq.
set Q := schreier_transition R sigmas.
have Q_ge0 : forall i j : 'I_N, 0 <= Q i j
  by exact: schreier_transition_entry_ge0.
have Q_row_sum : forall i : 'I_N, \sum_j Q i j = 1
  by exact: schreier_transition_stochastic.
have Q_col_sum : forall j : 'I_N, \sum_i Q i j = 1.
  exact: (@schreier_transition_doubly_stochastic_col R m n' sigmas sigmas_invol).
have Q_symm : Q^T = Q.
  exact: (@schreier_transition_symm R m n' sigmas sigmas_invol).
rewrite /var_dist.
have HtoCol :
  \sum_a `|fdistmap (fun sigma : {perm 'I_N} => sigma s)
            (rho_from_words L sigmas) a
        - fdist_uniform (card_ord N) a|
  = \sum_a `|(Q ^+ L *m \col_i (i == s)%:R) a ord0
            - (\col_i (#|'I_N|%:R^-1 : R)) a ord0|.
  apply: eq_bigr => a _.
  congr `|_|.
  congr (_ - _).
    rewrite /Q.
    exact: (@schreier_endpoint_eq_Q_power R m n' sigmas sigmas_invol L s a).
  by rewrite mxE fdist_uniformE.
rewrite HtoCol.
have HsqrtN_eq : Num.sqrt (N%:R : R) = Num.sqrt (#|'I_N|%:R)
  by rewrite card_ord.
rewrite HsqrtN_eq.
exact: (@symm_ds_TV_bound_cV R n'.+1 Q Q_row_sum Q_col_sum Q_symm
          alpha alpha_ge0 rayleigh_Qsq L s).
Qed.

End schreier_TV_bound.

