(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Reed-Solomon Privacy via Lagrange Interpolation                            *)
(*                                                                            *)
(* This file proves Massey's privacy_surj hypothesis for Reed-Solomon codes:  *)
(* for any set S of coordinates with |S| < d_perp (dual distance), any       *)
(* target values on S can be achieved by some RS codeword.                    *)
(*                                                                            *)
(* For MDS codes (including RS), d_perp = k + 1 where k = dim(C).            *)
(* The proof uses Lagrange interpolation: given target values at |S| <= k     *)
(* positions, interpolate a polynomial of degree < k, then show its          *)
(* evaluation vector is an RS codeword.                                       *)
(*                                                                            *)
(*   rs_privacy_surj == the main result: privacy surjectivity for RS codes   *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect ssralg finalg poly polydiv cyclic.
From mathcomp Require Import perm matrix mxpoly vector mxalgebra zmodp.
Require Import ssr_ext ssralg_ext hamming linearcode dft.
Require Import reed_solomon.
From pgg_reconstruct Require Import lagrange.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Evaluation Map for RS Codes                                 *)
(******************************************************************************)

Section rs_eval.

Variable F : finFieldType.
Variable a : F.
Variable n' : nat.
Let n := n'.+1.
Variable d : nat.

Hypothesis dn : RS.redundancy_ub d n.
Hypothesis a_prim : n.-primitive_root a.

Let a_neq0 : a != 0 := primitive_uroot_neq0 a_prim.
Let a_not_uroot_on : not_uroot_on a n := prim_root_not_uroot_on a_prim.

Let C := RS.code a n d.

(* Evaluation: polynomial -> row vector via powers of a *)
Definition poly_eval_rV (p : {poly F}) : 'rV[F]_n :=
  \row_(i < n) p.[a ^+ i].

(* An evaluation vector of a polynomial of degree < n-d is a codeword *)
Lemma poly_eval_in_code (p : {poly F}) :
  size p <= n - d ->
  poly_eval_rV p \in C.
Proof.
move=> Hsize.
(* Decompose p into monomials and use linearity *)
have Hdecomp : poly_eval_rV p =
  \sum_(k < size p) p`_k *: poly_eval_rV ('X^(k : nat) : {poly F}).
  apply/rowP => j; rewrite mxE summxE.
  rewrite horner_coef; apply: eq_bigr => k _.
  by rewrite mxE /poly_eval_rV mxE hornerXn.
rewrite Hdecomp.
apply: rpred_sum => /= k _.
apply: rpredZ.
(* Show poly_eval_rV ('X^k) \in C for k < size p <= n - d *)
rewrite mem_kernel_syndrome0 -RS.codebook_syndrome //.
rewrite inE; apply/forallP => /= t; apply/implyP => Ht.
apply/eqP.
have Htn : (t : nat) < n := leq_trans (ltn_ord t) dn.
rewrite fdcoorE.
rewrite (eq_bigr (fun j : 'I_n => a ^+ (j * ((k : nat) + (t : nat))))); last first.
  move=> j _; rewrite mxE hornerXn mxE inordK //.
  rewrite -exprM -exprM -exprD.
  by congr (a ^+ _); rewrite (mulnC (t : nat) j) -mulnDr.
rewrite (primitive_is_principal a_prim); first by [].
apply/andP; split.
- by rewrite addn_gt0 Ht orbT.
- have Hk_lt : (k : nat) < n - d := leq_trans (ltn_ord k) Hsize.
  have Hkd : (k : nat) + d < n.
    by move: Hk_lt; rewrite -(ltn_add2r d) subnK // ltnW.
  have Htd : (t : nat) <= d.
    by move: (ltn_ord t); rewrite ltnS.
  exact: leq_ltn_trans (leq_add (leqnn _) Htd) Hkd.
Qed.

End rs_eval.

(******************************************************************************)
(*     Section 2: Privacy Surjectivity for RS/MDS Codes                       *)
(******************************************************************************)

Section rs_privacy.

Variables (q m' : nat).
Hypothesis primeq : prime q.
Let F := GF m' primeq.
Variable a : F.
Variable n' : nat.
Let n := n'.+1.
Variable d : nat.

Hypothesis dn : RS.redundancy_ub d n.
Hypothesis qn : ~~ (q %| n)%nat.
Hypothesis an : n.-primitive_root a.

Let a_neq0 : a != 0 := primitive_uroot_neq0 an.
Let a_nuroot : not_uroot_on a n := prim_root_not_uroot_on an.

Let C := RS.code a n d.
Let C_nt := RS_not_trivial a dn.

(* For MDS codes, the dual distance equals k + 1 = (n - d) + 1 *)
(* This is the key structural property we need *)

(* Main result: privacy surjectivity for RS codes.
   For any set S with |S| < (n-d)+1 (= dim(C)+1) and any target vector,
   there exists a codeword agreeing with target on S.

   Proof strategy:
   1. Extract the positions in S and their target values
   2. Lagrange-interpolate a polynomial of degree <= |S|-1 < n-d
   3. The evaluation of this polynomial at (a^0, a^1, ..., a^{n-1})
      gives an RS codeword matching target on S positions *)
Lemma rs_privacy_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (n - d).+1 ->
    exists c : 'rV[F]_n, c \in C /\ vproj c S = vproj target S.
Proof.
move=> S target HS.
set sS := #|S|.
(* Build tuples via mktuple for clean tnth access *)
pose pts : sS.-tuple F :=
  mktuple (fun j : 'I_sS => a ^+ (enum_val j : nat) : F).
pose vals : sS.-tuple F :=
  mktuple (fun j : 'I_sS => target ord0 (enum_val j)).
(* Show points are distinct *)
have Huniq : uniq pts.
  rewrite /pts /= map_inj_uniq ?enum_uniq //.
  move=> x y Heq; apply: enum_val_inj.
  apply: (rVexp_inj a_neq0 a_nuroot).
  by rewrite !ffunE !mxE.
(* Interpolate *)
pose p := lagrange_interp pts vals.
(* Degree bound *)
have Hsize : size p <= n - d.
  apply: (leq_trans (lagrange_interp_size pts vals)).
  by rewrite -ltnS.
(* Build the codeword *)
exists (poly_eval_rV a n' p).
split.
- exact: (@poly_eval_in_code _ a n' d dn an p Hsize).
- apply/rowP => i; rewrite !mxE.
  case: ifPn => Hi; last by [].
  set j := enum_rank_in Hi i.
  have Hj : enum_val j = i by rewrite enum_rankK_in.
  have -> : a ^+ (i : nat) = tnth pts j by rewrite tnth_mktuple Hj.
  rewrite lagrange_interp_eval //.
  by rewrite tnth_mktuple Hj.
Qed.

(* Corollary: instantiate massey_scheme for RS codes *)
Lemma rs_privacy_surj_massey (Hd2 : 1 < min_dist C_nt) :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (n - d) ->
    exists c : 'rV[F]_n, c \in C /\ vproj c S = vproj target S.
Proof.
move=> S target HS.
apply: rs_privacy_surj.
exact: (ltn_trans HS (ltnSn _)).
Qed.

End rs_privacy.
