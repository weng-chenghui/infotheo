(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick: the two permutation generators                 *)
(*                                                                            *)
(* Provides the two permutations of 'I_5 used by the five-card trick          *)
(* (den Boer, EUROCRYPT 1989), shared by the Kim-family monodromy instance    *)
(* and the bool/'I_5 ThresholdScheme.                                         *)
(*                                                                            *)
(* Setup:                                                                     *)
(*   N = 5 cards: 3 black (spades) + 2 red (hearts)                          *)
(*   Positions: 0, 1, 2, 3, 4 (indexed by 'I_5)                              *)
(*   Each player commits one bit using 2 adjacent cards:                      *)
(*     Player A: positions 0, 1  (bit b_A encoded as BW or WB)               *)
(*     Player B: positions 2, 3  (bit b_B encoded as BW or WB)               *)
(*     Extra card: position 4                                                 *)
(*                                                                            *)
(* Involution g = (0 1)(2 3) fixes position 4:                                *)
(*   - Swaps each player's card pair                                          *)
(*   - Bit 1: (s, g(s)) = matched pair                                       *)
(*   - Bit 0: (s, s) = same position                                         *)
(*                                                                            *)
(* Shuffle generator: sigma = (0 1 2 3 4), the 5-cycle cyclic shift of all    *)
(*   five positions; sigma^5 = 1. This is the generator fc_kim_sigmas is      *)
(*   built from in the Kim-family instance.                                   *)
(*                                                                            *)
(* References:                                                                *)
(*   den Boer (1989), "More Efficient Match-Making and Satisfiability:        *)
(*     The Five Card Trick," EUROCRYPT, LNCS 434, pp. 208-217                 *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_reconstruct Require Import pgg_deck_pairing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Generator: 5-cycle sigma = (0 1 2 3 4)                                  *)
(******************************************************************************)

Section five_card_generators.

(** fc_sigma_fun — the shuffle generator as a plain function on 'I_5.
    @intent: cyclic shift of all 5 positions, sigma = (0 1 2 3 4), i.e.
    sigma(i) = (i + 1) mod 5; the underlying map packaged into the {perm 'I_5}
    generator fc_sigma. Used-by: fc_sigmaK, fc_sigma. *)
Definition fc_sigma_fun (x : 'I_5) : 'I_5 :=
  match val x with
  | 0 => @Ordinal 5 1 isT
  | 1 => @Ordinal 5 2 isT
  | 2 => @Ordinal 5 3 isT
  | 3 => @Ordinal 5 4 isT
  | _ => @Ordinal 5 0 isT
  end.

(** fc_sigma_inv — the inverse shuffle map on 'I_5.
    @intent: sigma^{-1} = (0 4 3 2 1); the cancel partner that witnesses
    fc_sigma_fun is a permutation. Used-by: fc_sigmaK. *)
Definition fc_sigma_inv (x : 'I_5) : 'I_5 :=
  match val x with
  | 0 => @Ordinal 5 4 isT
  | 1 => @Ordinal 5 0 isT
  | 2 => @Ordinal 5 1 isT
  | 3 => @Ordinal 5 2 isT
  | _ => @Ordinal 5 3 isT
  end.

(** fc_sigmaK — fc_sigma_inv cancels fc_sigma_fun on every sheet.
    @main architecture: the injectivity witness that lets fc_sigma_fun be
    packaged as the {perm 'I_5} generator fc_sigma. *)
Lemma fc_sigmaK : cancel fc_sigma_fun fc_sigma_inv.
Proof. by move=> x; apply/val_inj; case: x => [[|[|[|[|[|]]]]]]. Qed.

(** fc_sigma — the five-cycle shuffle generator (0 1 2 3 4).
    @intent: the sole generator of the cyclic PGG underlying the five-card
    trick; its order-5 action determines the search space and security. *)
Definition fc_sigma : {perm 'I_5} := perm (can_inj fc_sigmaK).

End five_card_generators.
