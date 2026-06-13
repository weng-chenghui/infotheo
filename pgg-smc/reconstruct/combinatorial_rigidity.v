(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Combinatorial rigidity: the non-curve dual of AlgebraicRigidity            *)
(*                                                                            *)
(* AlgebraicRigidity carries a ThresholdWitness whose tw_genus0_klein field      *)
(* asserts #|G| <= klein_genus0_bound M when the genus is zero. For a combinatorial,    *)
(* curve-free group such as the pile-scramble wreath Z_n wr S_m, that field    *)
(* would force a false inequality (e.g. 98 <= 60 for Z_7 wr S_2). So a         *)
(* different record is needed.                                                *)
(*                                                                            *)
(* CombinatorialRigidity drops the curve/pgl-cap field and instead asserts     *)
(* the two facts together that s5_nogo (reconstruct/s5_nogo.v) proves no       *)
(* genus-zero curve can satisfy: the group order EXCEEDS the curve-rigidity    *)
(* bound (cr_klein_lt_card : klein_genus0_bound M < #|pgg_G M|) WHILE the recovery gap is  *)
(* positive (cr_genus_gt0 : 0 < cd_genus). It still bundles a SecurityWitness  *)
(* (anonymity) and a CoveringScheme (the recovery scheme and its gap).        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset fingroup order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
Require Import pgg_interface.
From pgg_reconstruct Require Import covering_scheme cover_tradeoff
                                    algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section combinatorial_rigidity.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

(** CombinatorialRigidity — rigidity record for curve-free, non-abelian groups.
    Kind: interface.
    Why: the wreath instance cannot form an AlgebraicRigidity (its tw_genus0_klein
    would be a false inequality). This record certifies the same security and
    recovery content while replacing the curve cap with the order inequality. *)
Record CombinatorialRigidity := MkCombinatorialRigidity {
  cr_security : SecurityWitness R M ;
  cr_covering : CoveringScheme M ;
  cr_genus_gt0 : 0 < cd_genus (cs_data cr_covering) ;
  cr_klein_lt_card : klein_genus0_bound M < #|pgg_G M|
}.

(** cr_large_group_with_gap — the positive dual of the s5_nogo no-go.
    Kind: main.
    Why: a CombinatorialRigidity realises a group whose order exceeds the
    curve-rigidity bound together with a positive recovery gap, the exact
    conjunction s5_nogo proves impossible for a genus-zero curve. This is the
    headline structural property of the wreath instance. *)
Lemma cr_large_group_with_gap (cr : CombinatorialRigidity) :
  (klein_genus0_bound M < #|pgg_G M|) /\ (0 < cd_genus (cs_data (cr_covering cr))).
Proof. by split; [exact: cr_klein_lt_card | exact: cr_genus_gt0]. Qed.

End combinatorial_rigidity.

Arguments CombinatorialRigidity R M : clear implicits.
