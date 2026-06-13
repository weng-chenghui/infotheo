(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick: Protocol Program                               *)
(*                                                                            *)
(* Models the five-card trick protocol of den Boer (EUROCRYPT 1989,           *)
(* LNCS 434, pp. 208-217) as pure functions on sequences.                     *)
(*                                                                            *)
(* The protocol has 5 steps:                                                  *)
(*   1. Encode: each player commits a bit as a pair of face-down cards        *)
(*      (0 -> club-heart, 1 -> heart-club).                                   *)
(*   2. Arrange: negate Alice's encoding, place an extra heart card           *)
(*      between the two pairs to form a 5-card row                            *)
(*      [neg(a)_1, neg(a)_2, heart, b_1, b_2].                               *)
(*   3. Shuffle: apply a uniformly random cyclic shift sigma^k               *)
(*      (k in {0,...,4}) to the 5-card arrangement.                           *)
(*   4. Reveal: turn all cards face up.                                       *)
(*   5. Read: check whether three consecutive hearts appear.                  *)
(*      Three consecutive hearts iff a AND b = 1.                             *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   fc_encode b    == encode bit b as a 2-card sequence                      *)
(*   fc_negate cs   == negate a committed pair (reverse the two cards)        *)
(*   fc_arrange a b == build the 5-card arrangement from bits a and b        *)
(*   fc_shuffle k s == apply cyclic shift sigma^k to arrangement s           *)
(*   fc_three_consec s == check for three consecutive hearts                 *)
(*                                                                            *)
(* Main result:                                                               *)
(*   fc_correct : for all bits a, b and shift k < 5,                         *)
(*     fc_three_consec (fc_shuffle k (fc_arrange a b)) = (a && b)            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import five_card_group.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope group_scope.

Section five_card_program.

(******************************************************************************)
(** * Card encoding                                                           *)
(******************************************************************************)

(** Encode a bit as a pair of face-down cards.
    Hearts = [true], clubs = [false].
      0 -> [false; true]  (club, heart)
      1 -> [true; false]  (heart, club) *)
Definition fc_encode (b : bool) : seq bool :=
  if b then [:: true; false] else [:: false; true].

(** Negation: swap the two cards in a committed pair. *)
Definition fc_negate (cs : seq bool) : seq bool := rev cs.

(******************************************************************************)
(** * Arrangement                                                             *)
(******************************************************************************)

(** Build the 5-card row [neg(a)_1, neg(a)_2, heart, b_1, b_2].
    The extra heart card (position 2) is always [true]. *)
Definition fc_arrange (a b : bool) : seq bool :=
  fc_negate (fc_encode a) ++ [:: true] ++ fc_encode b.

(** fc_arrange_size — the arrangement seq always has length 5.
    Kind: helper.
    Why: Size invariant of fc_arrange used when iota-based windows traverse the 5-card row.
    Used by: fc_correct, downstream size-dependent reasoning.
*)
Lemma fc_arrange_size (a b : bool) : size (fc_arrange a b) = 5.
Proof. by case: a; case: b. Qed.

(******************************************************************************)
(** * Shuffle (cyclic shift)                                                  *)
(******************************************************************************)

(** Apply sigma^k as a cyclic rotation of the card row.
    After applying sigma^k, the card at position i is the card that was
    at position (i - k) mod 5 = sigma^{-k}(i) before the shuffle.
    This is exactly what MathComp's [rot k s] computes. *)
Definition fc_shuffle (k : nat) (s : seq bool) : seq bool := rot k s.

(******************************************************************************)
(** * Three consecutive hearts check                                          *)
(******************************************************************************)

(** Check whether three consecutive hearts appear in the cyclic 5-card row.
    We duplicate the sequence to handle wraparound, then check
    windows of size 3 at each of the 5 starting positions. *)
Definition fc_three_consec (s : seq bool) : bool :=
  let s2 := s ++ s in
  has (fun i => nth false s2 i && nth false s2 i.+1 && nth false s2 i.+2)
  (iota 0 5).

(******************************************************************************)
(** * Main correctness theorem                                                *)
(******************************************************************************)

(** Three consecutive hearts appear in the shuffled arrangement
    iff both input bits are 1. Proved by exhaustive computation
    over 4 (bool x bool) * 5 (shift) = 20 cases. *)
Lemma fc_correct (a b : bool) (k : nat) (Hk : k < 5) :
  fc_three_consec (fc_shuffle k (fc_arrange a b)) = (a && b).
Proof. by case: a; case: b; case: k Hk => [|[|[|[|[|]]]]] //. Qed.

(******************************************************************************)
(** * Tuple wrapper (for connection to PGG formalization)                      *)
(******************************************************************************)

(** fc_arrange_size_proof — boolean-equality form of fc_arrange_size, usable as a size witness for Tuple.
    Kind: helper.
    Why: The Tuple constructor expects a bool-valued size equality (size s == n), while fc_arrange_size proves the Prop-level version; this lemma supplies the boolean view.
    Used by: fc_arrange_tup.
    Naming: the `_proof` suffix distinguishes the bool-equality witness from the Prop-equality fc_arrange_size sibling; it names the data (boolean proof term) rather than the kind (Lemma).
*)
Lemma fc_arrange_size_proof (a b : bool) : size (fc_arrange a b) == 5.
Proof. by case: a; case: b. Qed.

(** Arrangement as a 5-tuple, for use with PGG infrastructure. *)
Definition fc_arrange_tup (a b : bool) : 5.-tuple bool :=
  Tuple (fc_arrange_size_proof a b).

(** [fc_sigma] applied to an ordinal equals the plain function
    [fc_sigma_fun] from [five_card_group.v]. *)
Lemma fc_sigma_funE (i : 'I_5) : fc_sigma i = fc_sigma_fun i.
Proof. by rewrite permE. Qed.

(******************************************************************************)
(** * Boolean codec on card positions ('I_5)                                 *)
(*                                                                            *)
(* The 'I_5/bool threshold scheme (five_card_scheme_I5.v) stores each card    *)
(* face as a position in 'I_5 rather than a raw bool. [encode_bool] places a  *)
(* heart-marked card at position 1 (true) or a club-marked card at position 0 *)
(* (false); [decode_bool] reads a position back as "is this the heart mark".  *)
(* The pair is a section-retraction, so [encode_bool] is injective; this lets *)
(* the bool-level privacy and validity facts transport to the 'I_5 scheme.    *)
(******************************************************************************)

(** encode_bool — store a committed bit as a card position in 'I_5.
    Kind: definition. What: true -> position 1, false -> position 0. Why: the
    'I_5 threshold scheme's share alphabet is 'I_5, so each boolean face is
    embedded as a distinguished position. Used-by: fcI_encode, fc_content (via
    fc_face), the codec round-trip decode_encode_bool. *)
Definition encode_bool (x : bool) : 'I_5 := if x then inord 1 else inord 0.

(** decode_bool — read a card position back as a committed bit.
    Kind: definition. What: position equals 1 iff the bit was true. Why: the
    left inverse of encode_bool, used to decode 'I_5 shares back to the boolean
    faces that fc_three_consec consumes. Used-by: fcI_valid, fcI_recon,
    fc_face. *)
Definition decode_bool (s : 'I_5) : bool := s == inord 1.

(** decode_encode_bool — the codec round-trips: decoding an encoded bit
    returns it.
    Kind: helper.
    Why: makes encode_bool a section of decode_bool, which gives injectivity
    (encode_bool_inj) and lets the bool-level scheme facts lift to 'I_5.
    Used by: encode_bool_inj, fcI_encode_valid, fcI_reconK. *)
Lemma decode_encode_bool (x : bool) : decode_bool (encode_bool x) = x.
Proof.
rewrite /decode_bool /encode_bool; case: x => //=.
by rewrite eqxx.
apply/negbTE/eqP => /(congr1 (@nat_of_ord 5)); rewrite !inordK //.
Qed.

(** encode_bool_inj — the position codec is injective.
    Kind: helper.
    Why: distinct bits map to distinct positions; lets a single-position
    coalition argument and the validity witness transport across the codec.
    Used by: fcI_private. *)
Lemma encode_bool_inj : injective encode_bool.
Proof. exact: (can_inj decode_encode_bool). Qed.

(** fc_face — the fixed physical face reading of a card position.
    Kind: definition. What: the heart mark sits at position 1, every other
    position reads as a club; this is decode_bool. Why: documents the physical
    "is this card a heart" readout of the identity card layout. The protocol's
    secret lives in the card LAYOUT (the starts) and the correctness theorem
    parameterizes over the starting layout (as the s5 and s5x5 instances do),
    so the content readout need not itself encode the secret. Used-by: fc_content
    documentation; the encode_bool (fc_face _) form is the position-faithful
    content map. *)
Definition fc_face (c : 'I_5) : bool := decode_bool c.

(** fc_content — the content readout baked into each dealt card position.
    Kind: definition. What: the identity on 'I_5. Why: with content = id and
    starts = ord_tuple 5, the protocol's G_stable condition collapses to
    reflexivity exactly as in s5x5_G_stable, which makes the end-to-end
    correctness theorem provable without assuming a layout-dependent face
    permutation. The position-faithful readout
    [fun c => encode_bool (fc_face c)] is definitionally the identity on the
    two used marks (positions 0 and 1) but not on positions 2..4; choosing id
    keeps the G_stable collapse, with the boolean reading recovered by
    fcI_recon's per-position decode_bool. Used-by: five_card_plug,
    den_boer_profile (five_card_family.v, den_boer_profile.v). *)
Definition fc_content (c : 'I_5) : 'I_5 := c.

End five_card_program.
