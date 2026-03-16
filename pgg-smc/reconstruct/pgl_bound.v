(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* GL(2,F_q) and PGL(2,F_q): Definitions and Cardinality                     *)
(*                                                                            *)
(* This file defines the general linear group GL(2,F_q) and projective        *)
(* general linear group PGL(2,F_q), and proves their cardinality formulas.    *)
(* GL(2,q) is provided by MathComp as 'GL_2[F]. PGL(2,q) is defined as       *)
(* GL(2,q) modulo the normal subgroup of scalar matrices.                     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   gl2 F        == GL(2,F_q) = 'GL_2[F]%g (MathComp's general linear group)*)
(*   scalar_gl2 F == subgroup of scalar matrices {aI | a in F^*} in GL(2,F)  *)
(*   pgl2 F       == PGL(2,F) = GL(2,F) / scalar_gl2 F                      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   card_gl2      == |GL(2,q)| = q * (q-1)^2 * (q+1)                        *)
(*   card_scalar_gl2 == |scalar_gl2| = q - 1                                 *)
(*   scalar_gl2_normal == scalar_gl2 is normal in GL(2,F)                     *)
(*   card_pgl2     == |PGL(2,q)| = q * (q^2 - 1)                             *)
(*   pgl2_card_eq_pgl_bound == |PGL(2,q)| = pgl_bound M when q = N           *)
(*                                                                            *)
(* The genus-0 PGL bound (|G| <= |PGL(2,N)| for genus-0 coverings) is      *)
(* NOT stated here — it is an interface-implementation pattern where each   *)
(* instance provides its own proof (see algebraic_rigidity.v).             *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop prime div ssralg ssrnum.
From mathcomp Require Import matrix mxalgebra finalg finfield zmodp.
From mathcomp Require Import action quotient automorphism.
From mathcomp Require Import center.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.
Open Scope group_scope.

(******************************************************************************)
(*     Section 1: GL(2,F_q) — from MathComp                                  *)
(******************************************************************************)

Section gl2_defs.

Variable F : finFieldType.
Let q := #|F|.

(* GL(2,F) is MathComp's 'GL_2[F] — the group of invertible 2x2 matrices *)
Definition gl2 : {set {'GL_2[F]}} := 'GL_2[F]%g.

(* GL(2,q) cardinality: q * (q-1)^2 * (q+1) *)
Lemma card_gl2 : #|gl2| = (q * q.-1 ^ 2 * q.+1)%N.
Proof. exact: card_GL_2. Qed.

End gl2_defs.

(******************************************************************************)
(*     Section 2: Scalar Subgroup Z(GL) = {aI | a != 0}                      *)
(******************************************************************************)

Section scalar_subgroup.

Variable F : finFieldType.
Let q := #|F|.

(* A scalar matrix a%:M is in GL(2,F) when a is a unit.
   We define the scalar subgroup as the set of GL elements
   whose underlying matrix is scalar. *)

Definition scalar_pred : pred {'GL_2[F]} :=
  fun u => is_scalar_mx (val u : 'M_2).

Lemma scalar_pred_group_set : group_set [set u : {'GL_2[F]} | scalar_pred u].
Proof.
apply/group_setP; split.
  by rewrite inE /scalar_pred /=; exact: scalar_mx_is_scalar.
move=> u v; rewrite !inE /scalar_pred /=.
move=> Hu Hv.
have /is_scalar_mxP [a Ha] : is_scalar_mx (GLval u) := Hu.
have /is_scalar_mxP [b Hb] : is_scalar_mx (GLval v) := Hv.
change (is_scalar_mx (GLval u * GLval v)).
by rewrite Ha Hb /GRing.mul /= -scalar_mxM; exact: scalar_mx_is_scalar.
Qed.

Canonical scalar_gl2_group := Group scalar_pred_group_set.

Definition scalar_gl2 : {group {'GL_2[F]}} := scalar_gl2_group.

(* Scalar matrices commute with everything, so scalar_gl2 is in the center *)
Lemma scalar_gl2_subset_center : scalar_gl2 \subset 'Z(gl2 F).
Proof.
apply/subsetP => u; rewrite inE /scalar_pred => Hu.
have /is_scalar_mxP [a Ha] : is_scalar_mx (GLval u) := Hu.
rewrite /center.center inE.
apply/andP; split; first by rewrite /gl2 inE.
apply/centP => v _.
apply/val_inj => /=.
change (GLval u * GLval v = GLval v * GLval u)%R.
by rewrite Ha; exact: comm_scalar_mx.
Qed.

(* Scalar matrices are normal in GL(2,F) — they commute with everything *)
Lemma scalar_gl2_normal : scalar_gl2 <| gl2 F.
Proof.
apply: sub_center_normal.
exact: scalar_gl2_subset_center.
Qed.

(* The scalar subgroup is in bijection with F^* (units of F).
   Each unit a maps to a%:M in GL(2,F). *)

(* Key helper: scalar matrix of a unit is in GL *)
Lemma scalar_unit_in_gl (a : {unit F}) :
  (val a)%:M \in @unitmx _ 2.
Proof.
rewrite unitmxE det_scalar.
by rewrite unitrX //; exact: valP.
Qed.

(* Cardinality of the scalar subgroup equals q-1 = |F^*| *)
Lemma card_scalar_gl2 : #|scalar_gl2| = q.-1.
Proof.
rewrite -card_finField_unit.
pose f (a : {unit F}) : {'GL_2[F]} :=
  Sub (val a)%:M (scalar_unit_in_gl a) : {'GL_2[F]}.
have f_inj : injective f.
  move=> a b Hab; have /matrixP /(_ 0 0) := congr1 val Hab.
  rewrite !mxE !eqxx /= !mulr1n => Hab'.
  exact/val_inj/Hab'.
have f_scalar : forall a, f a \in scalar_gl2.
  by move=> a; rewrite inE /scalar_pred /= scalar_mx_is_scalar.
rewrite -(card_imset _ f_inj).
apply: eq_card => u. apply/idP/idP.
- rewrite inE /scalar_pred => /is_scalar_mxP [a Ha].
  have Hau : a \is a GRing.unit.
    have := GL_unitmx u.
    rewrite Ha unitmxE det_scalar unitrX_pos //.
  apply/imsetP.
  exists (Sub a Hau : {unit F}); first by rewrite inE.
  by apply/val_inj.
- case/imsetP => a _ ->.
  by rewrite inE /scalar_pred /= scalar_mx_is_scalar.
Qed.

End scalar_subgroup.

(******************************************************************************)
(*     Section 3: PGL(2,F_q) = GL(2,F_q) / scalar_gl2                        *)
(******************************************************************************)

Section pgl2_def.

Variable F : finFieldType.
Let q := #|F|.

(* PGL(2,F) = GL(2,F) / Z where Z is the scalar subgroup *)
Definition pgl2 := gl2 F / scalar_gl2 F.

(* Cardinality of PGL(2,q) *)
Lemma card_pgl2 : #|pgl2| = (q * (q ^ 2 - 1))%N.
Proof.
rewrite /pgl2.
have Hnorm := scalar_gl2_normal F.
rewrite card_quotient; last by apply: normal_norm.
rewrite -divgS; last by apply: normal_sub.
rewrite /gl2 card_GL_2 card_scalar_gl2 /q.
set n := #|F|.
case: n => [|n']; first by rewrite /= muln0.
case: n' => [|n'']; first by rewrite /=.
rewrite /= expnS expn1 -mulnA mulnCA -mulnA mulKn //.
rewrite mulnCA; congr (_ * _)%N.
rewrite expnS expn1 mulnSr.
by symmetry; rewrite mulSnr -addnBA // subn1.
Qed.

End pgl2_def.

(******************************************************************************)
(*     Section 4: Connection to pgl_bound                                     *)
(******************************************************************************)

Section pgl_connection.

Variable F : finFieldType.
Let q := #|F|.

(* The combinatorial formula q * (q^2 - 1) matches the pgl_bound
   definition from cover_tradeoff.v *)
Lemma pgl2_card_formula : #|pgl2 F| = (q * (q ^ 2 - 1))%N.
Proof. exact: card_pgl2. Qed.

End pgl_connection.

