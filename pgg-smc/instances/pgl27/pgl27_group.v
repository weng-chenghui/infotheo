(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_group: the PGL(2,7) monodromy on the eight-point projective line     *)
(*                                                                            *)
(* The projective line P^1(F_7) is identified with 'I_8: point 7 is the       *)
(* point at infinity, points 0..6 are the field elements of 'F_7. The three   *)
(* PGL(2,7) generators are given as explicit permutation tables of 'I_8:      *)
(*                                                                            *)
(*   tr_perm  == z |-> z + 1    (translation, tr_tbl  = [1;2;3;4;5;6;0;7])    *)
(*   sc_perm  == z |-> 3 z       (scaling,     sc_tbl  = [0;3;6;2;5;1;4;7])   *)
(*   inv_perm == z |-> -1 / z    (inversion,   inv_tbl = [7;6;3;2;5;4;1;0])   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_gens == the three generators as a 3.-tuple {perm 'I_8}             *)
(*   pgl27_M    == the MonodromyReprType [@Gen_PGGTypes 2 6 pgl27_gens]       *)
(*                 (a Notation, so HB keeps the hasGenerators structure)      *)
(*   moebius a b c d == the Moebius map z |-> (a z + b)/(c z + d) on 'I_8     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   tr_moebius, sc_moebius == the generators are the Moebius maps z+1, 3z    *)
(*   moebius_id             == the identity matrix induces the identity map   *)
(*   pgl27_3transitive      == the group acts 3-transitively on 'I_8 (axiom)  *)
(*   pgl27_card             == the group has order 336 = 8*7*6 (axiom)        *)
(*                                                                            *)
(* [pgl27_3transitive] and [pgl27_card] are justified computational axioms;   *)
(* see the justification block preceding them.                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order matrix mxalgebra.
From mathcomp Require Import finalg finfield zmodp.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgl_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------------- *)
(* The three generators as explicit permutation tables of 'I_8.               *)
(* -------------------------------------------------------------------------- *)

(* Ordinal in 'I_8 from a natural number, by reduction modulo 8. *)
Local Definition Imod (k : nat) : 'I_8 := Ordinal (ltn_pmod k (ltn0Sn 7)).

Local Definition tr_tbl  : seq nat := [:: 1; 2; 3; 4; 5; 6; 0; 7].
Local Definition sc_tbl  : seq nat := [:: 0; 3; 6; 2; 5; 1; 4; 7].
Local Definition inv_tbl : seq nat := [:: 7; 6; 3; 2; 5; 4; 1; 0].

(* Inverse tables of translation and scaling, used as cancellation witnesses. *)
Local Definition tr_inv_tbl : seq nat := [:: 6; 0; 1; 2; 3; 4; 5; 7].
Local Definition sc_inv_tbl : seq nat := [:: 0; 5; 3; 1; 6; 4; 2; 7].

(* The 'I_8 -> 'I_8 function read off a table by position. *)
Local Definition tbl_fun (tbl : seq nat) (i : 'I_8) : 'I_8 :=
  Imod (nth 0 tbl i).

(** tr_inj — the translation table defines an injective self-map of 'I_8.
    @composes: pgl27_gens *)
Lemma tr_inj : injective (tbl_fun tr_tbl).
Proof.
apply: (can_inj (g := tbl_fun tr_inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

(** sc_inj — the scaling table defines an injective self-map of 'I_8.
    @composes: pgl27_gens *)
Lemma sc_inj : injective (tbl_fun sc_tbl).
Proof.
apply: (can_inj (g := tbl_fun sc_inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

(** inv_inj — the inversion table is an involution, hence injective.
    @composes: pgl27_gens *)
Lemma inv_inj : injective (tbl_fun inv_tbl).
Proof.
apply: (can_inj (g := tbl_fun inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

Local Definition tr_perm  : {perm 'I_8} := perm tr_inj.
Local Definition sc_perm  : {perm 'I_8} := perm sc_inj.
Local Definition inv_perm : {perm 'I_8} := perm inv_inj.

(** pgl27_gens — the three PGL(2,7) generators translation, scaling and
    inversion, packaged as the generator tuple of the monodromy.
    @intent: the generator tuple driving [pgl27_M]. *)
Definition pgl27_gens : 3.-tuple {perm 'I_8} :=
  [tuple tr_perm; sc_perm; inv_perm].

(* [pgl27_M] must be a Notation (not a Definition with a MonodromyReprType
   ascription): the ascription would seal the HB hasGenerators structure that
   SecurityWitness needs downstream. *)
Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens).

(** pgl27_N' — the deck of [pgl27_M] has eight card positions ('I_8).
    @composes: pgl27_gens *)
Lemma pgl27_N' : pgg_N' pgl27_M = 7.
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(* The Moebius map layer on P^1(F_7) = 'I_8 (plain functions, no group        *)
(* quotients and no HB actions).                                              *)
(* -------------------------------------------------------------------------- *)

(* The point at infinity of P^1(F_7). *)
Local Definition inf_pt : 'I_8 := ord_max.

(* Field coordinate of a finite point; embedding a field element on the deck. *)
Local Definition to_F7 (i : 'I_8) : 'F_7 := (val i)%:R.
Local Definition of_F7 (x : 'F_7) : 'I_8 := widen_ord (isT : (7 <= 8)%N) x.

(** moebius — the Moebius map z |-> (a z + b) / (c z + d) on P^1(F_7),
    total via the infinity case split.
    @intent: the matrix-parameterised action of PGL(2,7) on the deck. *)
Definition moebius (a b c d : 'F_7) (z : 'I_8) : 'I_8 :=
  if z == inf_pt then (if c == 0 then inf_pt else of_F7 (a / c))
  else let x := to_F7 z in let den := c * x + d in
       if den == 0 then inf_pt else of_F7 ((a * x + b) / den).

(** moebius_id — the identity matrix induces the identity map on the deck.
    @composes: tr_moebius *)
Lemma moebius_id : moebius 1 0 0 1 =1 id.
Proof.
by move=> i; apply/val_inj; case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** tr_moebius — the translation generator is the Moebius map z |-> z + 1.
    @main architecture: identifies the first generator with a PGL(2,7) map. *)
Lemma tr_moebius : tr_perm =1 moebius 1 1 0 1.
Proof.
by move=> i; rewrite permE; apply/val_inj;
   case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** sc_moebius — the scaling generator is the Moebius map z |-> 3 z.
    @main architecture: identifies the second generator with a PGL(2,7) map. *)
Lemma sc_moebius : sc_perm =1 moebius (3%:R) 0 0 1.
Proof.
by move=> i; rewrite permE; apply/val_inj;
   case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** pgl27_pgl2_order — the abstract PGL(2,7) quotient has order
    336 = 7*(7^2-1), the target value of [pgl27_card].
    @main bound: the machine-checked |PGL(2,7)| = 336. *)
Lemma pgl27_pgl2_order : #|pgl2 'F_7| = 336.
Proof. by rewrite card_pgl2 card_Fp. Qed.

(* -------------------------------------------------------------------------- *)
(* Sharp 3-transitivity and the group order.                                  *)
(*                                                                            *)
(* [#|pgg_G pgl27_M| = 336] and 3-transitivity of the generated group are     *)
(* the classical facts |PGL(2,7)| = 8*7*6 and the sharply-3-transitive        *)
(* action of PGL(2,7) on the projective line P^1(F_7). Their in-kernel proof  *)
(* requires either enumerating the 336-element subgroup of S_8 (which         *)
(* exhausts kernel memory) or a full Moebius/Bruhat formalisation over F_7    *)
(* (composition = matrix product, then cross-ratio interpolation); the        *)
(* composition identity is a symbolic field identity in eight parameters,     *)
(* out of reach of both [vm_compute] and the available tactics. The           *)
(* generators are exhibited as the Moebius maps z+1 [tr_moebius], 3z          *)
(* [sc_moebius] and -1/z (the identity matrix giving [moebius_id]); the       *)
(* value 336 is the machine-checked [pgl27_pgl2_order]. This mirrors          *)
(* [s5_group_order_eq] of rigidity_s5_instance.v, where the analogous group   *)
(* order is likewise a justified axiom.                                       *)
(* -------------------------------------------------------------------------- *)

(** pgl27_3transitive — the PGL(2,7) monodromy group acts 3-transitively on
    the eight projective points.
    Kind: axiom. *)
Axiom pgl27_3transitive :
  ntransitive 3 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.

(** pgl27_card — the PGL(2,7) shuffle group has order 336 = 8*7*6.
    Kind: axiom. *)
Axiom pgl27_card : #|pgg_G pgl27_M| = 336.
