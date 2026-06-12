(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer input encoding: the AND function via fc_arrange                   *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program five_card_scheme_I5.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** den_boer_layout — the den Boer starting layout: the two committed bits
    encoded into the five-card arrangement as 'I_5 shares.
    @intent: map_tuple encode_bool over fc_arrange_tup of the input bits. *)
Definition den_boer_layout (ab : bool * bool) : 5.-tuple 'I_5 :=
  map_tuple encode_bool (fc_arrange_tup ab.1 ab.2).

(** den_boer_assemble_valid — the encoded den Boer arrangement is a valid
    sharing of a && b.
    @composes: den_boer_encoding. *)
Lemma den_boer_assemble_valid (ab : bool * bool) :
  fcI_valid (ab.1 && ab.2) (den_boer_layout ab).
Proof.
rewrite /fcI_valid /den_boer_layout /=.
rewrite -map_comp.
under eq_map => x do rewrite /comp decode_encode_bool.
rewrite map_id.
by have := fc_correct ab.1 ab.2 (k:=0) isT; rewrite /fc_shuffle rot0.
Qed.

(** den_boer_orbit — inputs with equal AND give layouts that differ by a cyclic
    rotation: the three a&&b=false inputs lie in one rotation orbit.
    @composes: den_boer_encoding. *)
Lemma den_boer_orbit (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists k : 'I_5, val (den_boer_layout ab') = rot k (val (den_boer_layout ab)).
Proof.
move=> H; move: H; case: ab => a b; case: ab' => a' b'.
case: a; case: b; case: a'; case: b' => //=; move=> _;
  first [ exists (inord 0); by rewrite inordK// rot0
        | exists (inord 1); by rewrite inordK
        | exists (inord 2); by rewrite inordK
        | exists (inord 3); by rewrite inordK
        | exists (inord 4); by rewrite inordK ].
Qed.
