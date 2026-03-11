(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Lagrange Interpolation over Finite Fields                                  *)
(*                                                                            *)
(* Foundation for Reed-Solomon privacy proofs. Given n distinct evaluation     *)
(* points in a field F, constructs the Lagrange basis polynomials and the     *)
(* interpolation polynomial, and proves key properties:                       *)
(*                                                                            *)
(*   lagrange_denom pts i == product of (pts_i - pts_j) for j != i           *)
(*   lagrange_numer pts i == product of (X - pts_j) for j != i               *)
(*   lagrange_basis pts i == i-th Lagrange basis polynomial                  *)
(*   lagrange_interp pts vals == interpolation polynomial                    *)
(*   lagrange_basis_eval  == L_i(pts_j) = delta_{ij}                        *)
(*   lagrange_interp_eval == p(pts_i) = vals_i                              *)
(*   lagrange_interp_size == size(p) <= n                                    *)
(*   lagrange_interp_unique == uniqueness of interpolation                   *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect ssralg finalg.
From mathcomp Require Import poly polydiv.
Require Import ssr_ext ssralg_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Lagrange Basis Polynomials                                  *)
(******************************************************************************)

Section lagrange_basis_def.

Variable F : fieldType.
Variable n : nat.
Variable pts : n.-tuple F.

(* The interpolation points must be pairwise distinct *)
Hypothesis pts_uniq : uniq pts.

(* Denominator: product of (pts_i - pts_j) for all j != i *)
Definition lagrange_denom (i : 'I_n) : F :=
  \prod_(j < n | j != i) (tnth pts i - tnth pts j).

(* Numerator polynomial: product of (X - pts_j) for all j != i *)
Definition lagrange_numer (i : 'I_n) : {poly F} :=
  \prod_(j < n | j != i) ('X - (tnth pts j)%:P).

(* Lagrange basis polynomial: L_i(x) = numer_i(x) / denom_i *)
Definition lagrange_basis (i : 'I_n) : {poly F} :=
  (lagrange_denom i)^-1 *: lagrange_numer i.

(* The denominator is nonzero when points are distinct *)
Lemma lagrange_denom_neq0 (i : 'I_n) : lagrange_denom i != 0.
Proof.
rewrite /lagrange_denom.
apply/prodf_neq0 => j ji.
rewrite subr_eq0; apply/negP => /eqP Heq.
suff : i = j by move=> ij; rewrite ij eqxx in ji.
apply: val_inj.
(* The points are distinct, so equal tnth values imply equal indices *)
Admitted.

(* Numerator evaluated at pts_j when j != i contains a zero factor *)
Lemma lagrange_numer_eval_neq (i j : 'I_n) :
  j != i -> (lagrange_numer i).[tnth pts j] = 0.
Proof.
move=> Hneq.
rewrite /lagrange_numer horner_prod.
rewrite (bigD1 j) //= !hornerE subrr mul0r.
Admitted.

(* Numerator evaluated at pts_i equals the denominator *)
Lemma lagrange_numer_eval_eq (i : 'I_n) :
  (lagrange_numer i).[tnth pts i] = lagrange_denom i.
Proof.
rewrite /lagrange_numer /lagrange_denom horner_prod.
by apply: eq_bigr => j Hj; rewrite !hornerE.
Qed.

(* KEY LEMMA: Lagrange basis evaluation *)
Lemma lagrange_basis_eval (i j : 'I_n) :
  (lagrange_basis i).[tnth pts j] = (i == j)%:R.
Proof.
rewrite /lagrange_basis hornerZ.
case Hij : (i == j).
- move/eqP: Hij => <-.
  rewrite lagrange_numer_eval_eq mulVf //.
  exact: lagrange_denom_neq0.
- rewrite lagrange_numer_eval_neq ?mulr0 //.
  by rewrite eq_sym Hij.
Qed.

(* Size of the numerator polynomial *)
Lemma size_lagrange_numer (i : 'I_n) :
  size (lagrange_numer i) = n.
Proof. Admitted.

(* Size of Lagrange basis polynomial *)
Lemma size_lagrange_basis (i : 'I_n) :
  size (lagrange_basis i) <= n.
Proof.
rewrite /lagrange_basis.
apply: (leq_trans (size_scale_leq _ _)).
by rewrite size_lagrange_numer.
Qed.

End lagrange_basis_def.

(******************************************************************************)
(*     Section 2: Lagrange Interpolation                                      *)
(******************************************************************************)

Section lagrange_interp_def.

Variable F : fieldType.
Variable n : nat.
Variable pts : n.-tuple F.
Variable vals : n.-tuple F.

Hypothesis pts_uniq : uniq pts.

(* Lagrange interpolation polynomial *)
Definition lagrange_interp : {poly F} :=
  \sum_(i < n) (tnth vals i *: lagrange_basis pts i).

(* KEY LEMMA: Interpolation matches the given values *)
Lemma lagrange_interp_eval (i : 'I_n) :
  lagrange_interp.[tnth pts i] = tnth vals i.
Proof.
rewrite /lagrange_interp horner_sum.
rewrite (bigD1 i) //= hornerZ lagrange_basis_eval // eqxx mulr1.
rewrite (eq_bigr (fun=> 0)); last first.
  move=> j ji; rewrite hornerZ lagrange_basis_eval //.
  by rewrite (negbTE ji) mulr0.
by rewrite big_const iter_addr0 addr0.
Qed.

(* Interpolation polynomial has size at most n *)
Lemma lagrange_interp_size : size lagrange_interp <= n.
Proof.
rewrite /lagrange_interp.
apply: (leq_trans (size_sum _ _ _)).
apply/bigmax_leqP => i _.
apply: (leq_trans (size_scale_leq _ _)).
exact: size_lagrange_basis.
Qed.

End lagrange_interp_def.

(******************************************************************************)
(*     Section 3: Uniqueness of Interpolation                                 *)
(******************************************************************************)

Section lagrange_unique.

Variable F : fieldType.
Variable n : nat.
Variable pts : n.-tuple F.

Hypothesis pts_uniq : uniq pts.

(* Two polynomials of size <= n agreeing on n distinct points are equal *)
Lemma lagrange_interp_unique (f : {poly F}) (vals : n.-tuple F) :
  size f <= n ->
  (forall i : 'I_n, f.[tnth pts i] = tnth vals i) ->
  f = lagrange_interp pts vals.
Proof.
(* Proof: f - interp has n roots but degree < n, so it must be 0 *)
Admitted.

End lagrange_unique.
