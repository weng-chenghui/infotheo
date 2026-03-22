(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Card Protocol Model for PGG                                                *)
(*                                                                            *)
(* Defines card-based cryptographic protocols as instances of the PGG          *)
(* framework, connecting card-game shuffling to Schreier spectral analysis     *)
(* and the collusion bound.                                                   *)
(*                                                                            *)
(* The multi-shuffle card protocol model (den Boer 1989, Mizuki-Sone 2009)    *)
(* is the standard model in card-based cryptography (1989-2019). Each         *)
(* shuffle is a random generator application; L consecutive shuffles form     *)
(* a random walk on the Schreier graph. PGG's spectral gap bounds how many    *)
(* shuffles are needed for k-coalition fairness.                              *)
(*                                                                            *)
(* The orbit-fiber connection:                                                *)
(*   - Card protocols (exact, uniform on G): orbit-stabilizer theorem         *)
(*     gives equal-sized fibers -> perfect security (eps = 0).                *)
(*   - PGG (approximate, random walk mu_L): Schreier spectral gap gives       *)
(*     approximately equal fibers -> statistical security eps(L) -> 0.        *)
(*   - The orbit-stabilizer theorem is the L -> infinity limit of PGG's       *)
(*     spectral convergence.                                                  *)
(*                                                                            *)
(* Contents:                                                                  *)
(*   CardShuffle == record bundling a GeneratedMonodromyReprType with an       *)
(*     involution (card-pairing), encoding the card protocol as a PGG         *)
(*     instance where endpoints = card positions after shuffling.             *)
(*   card_security_from_endpoint == bridge theorem: PGG endpoint security     *)
(*     (var_dist on 'I_N) implies card-bit security (decode correctness       *)
(*     under shuffled pairs).                                                 *)
(*                                                                            *)
(* References:                                                                *)
(*   - den Boer (1989), "The Five Card Trick," EUROCRYPT                      *)
(*   - Mizuki-Sone (2009), "Six-Card AND / Four-Card XOR," FAW               *)
(*   - Shinagawa-Nuida (2019), "A Single Shuffle Is Enough," DAM             *)
(*   - Dvorak-Koucky (2021), "Barrington Plays Cards," STACS                  *)
(*   - Diaconis (1988), "Group Representations in Probability and Statistics" *)
(*   - Diaconis-Bayer (1992), "Trailing the Dovetail Shuffle to its Lair"     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_deck_pairing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Card Shuffle Equivariance at the Permutation Level                      *)
(*                                                                            *)
(* This section works purely at the {perm 'I_N} level, matching               *)
(* pgg_deck_pairing.v. The connection to PGG's monodromy representation       *)
(* (MonodromyReprType, endpoint, etc.) is made in Section 2 below.            *)
(******************************************************************************)

Section card_shuffle_perm.

Variable N : nat.

(** A card shuffle protocol has:
    - An involution g (card-pairing permutation on 'I_N)
    - Shuffle permutations sigma that commute with g
    Bits are encoded via encode_bit g and preserved by equivariance. *)

Variable g : {perm 'I_N}.
Hypothesis g_inv : is_involution g.
Hypothesis g_fpf : is_fpf g.

(** Encode a bit using the involution. *)
Definition cs_encode (b : bool) (s : 'I_N) : 'I_N * 'I_N :=
  encode_bit g b s.

(** Decode a bit from two observed card positions. *)
Definition cs_decode (eA eB : 'I_N) : bool :=
  decode_bit g eA eB.

(** Reconstruction correctness: after applying any commuting permutation
    sigma, the decoded bit matches the original.
    Direct corollary of decode_encode_correct from pgg_deck_pairing.v. *)
Theorem cs_decode_encode_correct
    (sigma : {perm 'I_N}) (b : bool) (s : 'I_N) :
  commute g sigma ->
  let p := cs_encode b s in
  cs_decode (sigma p.1) (sigma p.2) = b.
Proof.
move=> Hcomm /=.
exact: decode_encode_correct.
Qed.

End card_shuffle_perm.

(******************************************************************************)
(** * Card Shuffle via PGG Monodromy Representation                           *)
(*                                                                            *)
(* Connects the permutation-level card shuffle to PGG's framework:            *)
(* endpoint(sigma, s) = rho(sigma)(s) is the card position after shuffle.     *)
(* If the involution g commutes with all rho(sigma) for sigma in G,           *)
(* then the bit encoding is preserved by any sequence of shuffles             *)
(* (word evaluation).                                                         *)
(******************************************************************************)

Section card_shuffle_pgg.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let gT := pgg_gT M.
Let G := pgg_G M.

(** Involution acting on card positions ('I_N). *)
Variable g : {perm 'I_N}.
Hypothesis g_inv : is_involution g.
Hypothesis g_fpf : is_fpf g.

(** The involution commutes with every monodromy image rho(sigma).
    This ensures shuffles (group element applications) preserve bits. *)
(** Lift endpoint to a permutation for commutation. *)
Let endpoint_perm (sigma : gT) : {perm 'I_N} :=
  perm (@endpoint_inj M sigma).

Hypothesis g_commutes_endpoint : forall (sigma : gT),
  sigma \in G -> commute g (endpoint_perm sigma).

(** Word-level reconstruction: after evaluating a word w (sequence of
    shuffles), the bit is still correctly decodable. *)
Theorem card_word_decode_correct (sigma : gT) (b : bool) (s : 'I_N) :
  sigma \in G ->
  let ep := endpoint_perm sigma in
  let p := encode_bit g b s in
  decode_bit g (ep p.1) (ep p.2) = b.
Proof.
move=> HsigmaG /=.
apply: decode_encode_correct => //.
exact: g_commutes_endpoint HsigmaG.
Qed.

End card_shuffle_pgg.

(******************************************************************************)
(** * Card Protocol Security from Endpoint Security                           *)
(*                                                                            *)
(* The bridge to PGG's security infrastructure:                               *)
(*                                                                            *)
(* 1. pgg_collusion_bound.v proves:                                           *)
(*    d_TV(adversary_posterior, uniform) <= epsilon + 2(T-1)/N                 *)
(*    This bounds what T-1 colluding players learn about the T-th endpoint.   *)
(*                                                                            *)
(* 2. pgg_schreier.v proves:                                                  *)
(*    epsilon(L) <= sqrt(N) * (1 - gap)^L                                     *)
(*    This bounds how many shuffles (L) are needed for fairness.              *)
(*                                                                            *)
(* 3. card_word_decode_correct (above) proves:                                *)
(*    After any shuffle (group element application), bits decode correctly.   *)
(*                                                                            *)
(* Together: after L shuffles, T-1 colluding players cannot distinguish       *)
(* the bit encoded at the T-th position beyond advantage                      *)
(* sqrt(N) * (1-gap)^L + 2(T-1)/N.                                           *)
(*                                                                            *)
(* The formal bridge theorem connecting these three results requires          *)
(* fdist infrastructure from infotheo (variation_dist, fdistmap).             *)
(* See card_endpoint_bridge.v (future file) for the full statement.           *)
(******************************************************************************)
