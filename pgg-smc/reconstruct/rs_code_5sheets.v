(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Concrete RSCodeWitness for instances with N = 5 sheets                     *)
(*                                                                            *)
(* Provides RS5_witness_trivial, the one-call factory for instances with     *)
(* (pgg_N' M).+1 = 5. Uses GF(5), code length 4, primitive 4-th root 2,      *)
(* and the trivial code automorphism `fun _ => 1%g`.                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp poly cyclic.
From mathcomp Require Import fingroup perm matrix mxalgebra vector finfield.
Require Import ssralg_ext hamming linearcode reed_solomon.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Field GF(5) basic facts                                     *)
(******************************************************************************)

(** prime5 — 5 is a prime number.
    Kind: helper.
    Why: primitivity certificate required to construct GF(5) as GF 0 prime5;
    every field operation in this file consumes it.
    Used by: char_GF5, card_GF5, prim_root_prim4_GF5, RS5 factory. *)
Lemma prime5 : prime 5. Proof. by []. Qed.

(** char_GF5 - characteristic of GF(5) is 5.
    Kind: helper.
    Why: records that 5 = 0 in the field used for the 5-sheet RS factory.
    Used by: field arithmetic inside the primitive-root proofs below.
*)
Lemma char_GF5 : (5%:R : GF 0 prime5) = 0.
Proof. by have := @char_GFqm 5 0 prime5; rewrite !inE => /andP[_ /eqP]. Qed.

(** card_GF5 - GF(5) has exactly 5 elements.
    Kind: helper.
    Why: cardinality certificate consumed by the RS factory built on GF(5).
    Used by: RS_witness construction when matching sheet count to field size.
*)
Lemma card_GF5 : #|GF 0 prime5| = 5.
Proof. by rewrite card_GFqm expn1. Qed.

(* Identity helper: for 0 < n < 5, n%:R != 0 in GF(5).                        *)
Lemma nat_inj_GF5_neq0 (n : nat) : ~~ (5 %| n)%N -> (n%:R : GF 0 prime5) != 0.
Proof.
apply: contra => /eqP H. apply/eqP. apply/eqP. change (5 %| n)%N.
by rewrite (@dvdn_pcharf (GF 0 prime5) 5 (@char_GFqm 5 0 prime5)) H.
Qed.

(* Powers of 2 reduce mod 5.                                                 *)
Lemma expr_2_mod_5 (k : nat) : (2%:R : GF 0 prime5) ^+ k = (2^k %% 5)%:R.
Proof.
by rewrite -natrX (@GRing.natr_mod_pchar (GF 0 prime5) 5 (@char_GFqm 5 0 prime5)).
Qed.

(******************************************************************************)
(*     Section 2: 2 is a primitive 4-th root of unity in GF(5)                *)
(******************************************************************************)

(* Helper: if n is in {1,2,3,4} (i.e., 1 <= n < 5), then n%:R != 0 in GF(5). *)
Lemma small_nat_neq0_GF5 (n : nat) : (0 < n < 5)%N ->
  (n%:R : GF 0 prime5) != 0.
Proof.
move=> /andP[Hn1 Hn5]. apply: nat_inj_GF5_neq0.
case: n Hn1 Hn5 => [|[|[|[|[|]]]]] //.
Qed.

(** nat_minus1_neq0_GF5 — for n in {2,3,4}, n%:R - 1 is non-zero in GF(5).
    Kind: helper.
    Why: separates the non-identity fourth-roots-of-unity candidates from 1
    when showing 2 is a primitive 4th root.
    Used by: prim_root_prim4_GF5. *)
Lemma nat_minus1_neq0_GF5 (n : nat) : (1 < n < 5)%N ->
  (n%:R - 1 : GF 0 prime5) != 0.
Proof.
move=> /andP[H1 H5].
have -> : (n%:R - 1 : GF 0 prime5) = (n - 1)%N%:R.
  have ->: (1 : GF 0 prime5) = 1%N%:R by [].
  by rewrite -natrB // ltnW.
apply: small_nat_neq0_GF5.
case: n H1 H5 => [|[|[|[|[|]]]]] //.
Qed.

(** prim_root_prim4_GF5 - 2 is a primitive 4th root of unity in GF(5).
    Kind: helper.
    Why: certifies that 2 has multiplicative order 4 in GF(5), which is the
    input required by the Reed-Solomon factory with n = 4 evaluation points.
    Used by: the RS5 factory's call to RS.code with primitive root parameter.
*)
Lemma prim_root_prim4_GF5 : 4.-primitive_root (2%:R : GF 0 prime5).
Proof.
apply/andP; split=> //.
apply/forallP => i.
rewrite unity_rootE expr_2_mod_5.
case: i => i Hi /=.
case: i Hi => [|[|[|[|//]]]] _.
- (* k = 1: 2^1 mod 5 = 2; goal: (2%:R == 1) == false *)
  apply/eqP. apply/negbTE. apply/eqP => H.
  have : ((2 : GF 0 prime5) - 1) = 0 by rewrite H subrr.
  by apply/eqP; apply: (nat_minus1_neq0_GF5 (n:=2)).
- (* k = 2: 2^2 mod 5 = 4; goal: (4%:R == 1) == false *)
  apply/eqP. apply/negbTE. apply/eqP => H.
  have : ((4 : GF 0 prime5) - 1) = 0 by rewrite H subrr.
  by apply/eqP; apply: (nat_minus1_neq0_GF5 (n:=4)).
- (* k = 3: 2^3 mod 5 = 3; goal: (3%:R == 1) == false *)
  apply/eqP. apply/negbTE. apply/eqP => H.
  have : ((3 : GF 0 prime5) - 1) = 0 by rewrite H subrr.
  by apply/eqP; apply: (nat_minus1_neq0_GF5 (n:=3)).
- (* k = 4: 2^4 mod 5 = 1; goal: (1%:R == 1) == true *)
  have ->: ((2 ^ 4) %% 5)%N = 1%N by [].
  by rewrite (eqxx 1) (eqxx 4%N).
Qed.

(******************************************************************************)
(*     Section 3: Factory for RSCodeWitness with 5 sheets                     *)
(******************************************************************************)

Definition prim4_GF5 : GF 0 prime5 := 2%:R.

(** qn5_4 - 5 does not divide 4.
    Kind: helper.
    Why: side-condition for the Reed-Solomon length hypothesis (char q coprime
    to n) specialised to q = 5, n = 4.
    Used by: RS5 factory when discharging the primitive-root divisibility check.
*)
Lemma qn5_4 : ~~ (5 %| 4)%N. Proof. by []. Qed.

(* The trivial code automorphism: every group element maps to identity. *)
Definition trivial_sigma (M : MonodromyReprType) :
  pgg_gT M -> {perm 'I_4} := fun _ => 1%g.

Arguments trivial_sigma M _ : clear implicits.

(** trivial_sigma_fix0 - trivial code automorphism fixes sheet 0.
    Kind: helper.
    Why: discharges the fix-base-point obligation of the RSCodeWitness interface
    for the trivial automorphism choice.
    Used by: RS5_witness_trivial factory when instantiating the witness record.
*)
Lemma trivial_sigma_fix0 (M : MonodromyReprType) :
  forall g, g \in pgg_G M -> trivial_sigma M g ord0 = ord0.
Proof. by move=> g _; rewrite perm1. Qed.

(* The identity permutation preserves any code (since col_perm 1%g c = c). *)
Local Lemma coord_perm_compatible_id
  (F : finFieldType) (n : nat) (C : Lcode0.t F n) :
  coord_perm_compatible C 1%g.
Proof. by move=> c Hc; rewrite col_perm1. Qed.

(** trivial_sigma_auto - trivial sigma yields a coordinate-permutation automorphism.
    Kind: helper.
    Why: discharges the coord_perm_compatible obligation of RSCodeWitness for
    the trivial-automorphism instance, reducing to coord_perm_compatible_id.
    Used by: RS5_witness_trivial factory below.
*)
Lemma trivial_sigma_auto (M : MonodromyReprType) :
  forall g, g \in pgg_G M ->
    coord_perm_compatible (RS.code prim4_GF5 4 1) (trivial_sigma M g).
Proof. by move=> g _; apply: coord_perm_compatible_id. Qed.

(* The factory: instance-side just supplies the sheet-count equation. *)
Definition RS5_witness_trivial (M : MonodromyReprType)
    (HN5 : (pgg_N' M).+1 = 5) : RSCodeWitness M :=
  @MkRSCodeWitness M
    5 0 prime5 1 prim4_GF5
    qn5_4 prim_root_prim4_GF5
    (eq_trans HN5 (esym card_GF5))
    (trivial_sigma M)
    (@trivial_sigma_fix0 M)
    (@trivial_sigma_auto M).
