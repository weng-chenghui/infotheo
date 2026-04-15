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

Lemma fc_arrange_size_proof (a b : bool) : size (fc_arrange a b) == 5.
Proof. by case: a; case: b. Qed.

(** Arrangement as a 5-tuple, for use with PGG infrastructure. *)
Definition fc_arrange_tup (a b : bool) : 5.-tuple bool :=
  Tuple (fc_arrange_size_proof a b).

(** [fc_sigma] applied to an ordinal equals the plain function
    [fc_sigma_fun] from [five_card_group.v]. *)
Lemma fc_sigma_funE (i : 'I_5) : fc_sigma i = fc_sigma_fun i.
Proof. by rewrite permE. Qed.

End five_card_program.
