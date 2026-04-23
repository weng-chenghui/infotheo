(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick as a PGG Instance                               *)
(*                                                                            *)
(* Formalizes the foundational card-based protocol (den Boer, EUROCRYPT 1989) *)
(* as a concrete PGG monodromy instance. This is the base case of the         *)
(* generalization spectrum: card protocols -> PGG -> spectral analysis.        *)
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
(* Generator (shuffle): sigma = random cyclic shift of all 5 positions        *)
(*   sigma = (0 1 2 3 4) -- 5-cycle                                           *)
(*   This generates Z_5 (cyclic group of order 5)                             *)
(*                                                                            *)
(* PGG parameters: m = 0 (1 generator), n = 3 (N = n+2 = 5 sheets)           *)
(*   M = Gen_PGGTypes [tuple sigma]                                           *)
(*   word_eval at L=1: achievable = {sigma} (1 element)                       *)
(*   word_eval at L=4: achievable = {sigma, sigma^2, sigma^3, sigma^4}        *)
(*     (4 elements, since sigma^5 = 1)                                        *)
(*                                                                            *)
(* Security analysis:                                                         *)
(*   At L=4: achievable has 4 distinct non-identity elements                  *)
(*   Fiber counting per sheet determines epsilon                              *)
(*   For cyclic group: transitive action -> eps determined by uniformity      *)
(*                                                                            *)
(* References:                                                                *)
(*   den Boer (1989), "More Efficient Match-Making and Satisfiability:        *)
(*     The Five Card Trick," EUROCRYPT, LNCS 434, pp. 208-217                 *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
Require Import pgg_interface.
From pgg_smc Require Import pgg_weval_inj.
From pgg_reconstruct Require Import pgg_deck_pairing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Generator: 5-cycle sigma = (0 1 2 3 4)                                  *)
(******************************************************************************)

Section five_card_generators.

(** The shuffle generator: cyclic shift of all 5 positions.
    sigma = (0 1 2 3 4), i.e., sigma(i) = (i + 1) mod 5. *)
Definition fc_sigma_fun (x : 'I_5) : 'I_5 :=
  match val x with
  | 0 => @Ordinal 5 1 isT
  | 1 => @Ordinal 5 2 isT
  | 2 => @Ordinal 5 3 isT
  | 3 => @Ordinal 5 4 isT
  | _ => @Ordinal 5 0 isT
  end.

(** Inverse: sigma^{-1} = (0 4 3 2 1). *)
Definition fc_sigma_inv (x : 'I_5) : 'I_5 :=
  match val x with
  | 0 => @Ordinal 5 4 isT
  | 1 => @Ordinal 5 0 isT
  | 2 => @Ordinal 5 1 isT
  | 3 => @Ordinal 5 2 isT
  | _ => @Ordinal 5 3 isT
  end.

(** fc_sigmaK — fc_sigma_inv cancels fc_sigma_fun on every sheet.
    Kind: helper.
    Why: Injectivity witness that lets us package fc_sigma_fun as a {perm 'I_5}.
    Used by: fc_sigma.
*)
Lemma fc_sigmaK : cancel fc_sigma_fun fc_sigma_inv.
Proof. by move=> x; apply/val_inj; case: x => [[|[|[|[|[|]]]]]]. Qed.

(** fc_sigma — the five-cycle shuffle generator (0 1 2 3 4).
    Kind: instance.
    Why: Sole generator of the cyclic PGG underlying the five-card trick; its order-5 action determines the search space and security.
*)
Definition fc_sigma : {perm 'I_5} := perm (can_inj fc_sigmaK).

(** The involution: g = (0 1)(2 3), fixing position 4.
    Swaps each player's card pair. *)
Definition fc_g_fun (x : 'I_5) : 'I_5 :=
  match val x with
  | 0 => @Ordinal 5 1 isT
  | 1 => @Ordinal 5 0 isT
  | 2 => @Ordinal 5 3 isT
  | 3 => @Ordinal 5 2 isT
  | _ => x
  end.

Definition fc_g_inv := fc_g_fun. (* g is its own inverse *)

Lemma fc_gK : cancel fc_g_fun fc_g_inv.
Proof. by move=> x; apply/val_inj; case: x => [[|[|[|[|[|]]]]]]. Qed.

(** fc_g — the involution g = (0 1)(2 3) used in the five-card trick.
    Kind: instance.
    Why: Models the swap of each player's card pair; paired with the shuffle generator fc_sigma to analyse security of the protocol.
*)
Definition fc_g : {perm 'I_5} := perm (can_inj fc_gK).

(** Generator tuple for Gen_PGGTypes (1 generator). *)
Definition fc_sigmas : 1.-tuple {perm 'I_5} := [tuple fc_sigma].

End five_card_generators.

(******************************************************************************)
(** * PGG Instance: Gen_PGGTypes from the 5-cycle generator                   *)
(******************************************************************************)

Section five_card_pgg.

(** m = 0 (1 generator), n = 3 (N = n+2 = 5 sheets) *)
Definition FiveCard_M : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 0 3 fc_sigmas.

(** Involution properties *)
Lemma fc_g_involution : is_involution fc_g.
Proof.
rewrite /is_involution.
apply/permP => x.
rewrite permM perm1 permE permE.
by apply/val_inj; case: x => [[|[|[|[|[|]]]]] ?].
Qed.

(** fc_g = (0 1)(2 3) fixes position 4, so is_fpf does NOT hold.
    The five-card trick intentionally has a fixed point (the extra card).
    The former fc_g_fpf statement has been removed as it is unprovable. *)

(** Nat-level generator function for vm_compute reflection *)
Definition fc_gens_nat (i x : nat) : nat :=
  match i with
  | _ => match x with 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | _ => 0 end
  end.

(** fc_sigmasE — tuple lookup in the singleton generator tuple always returns fc_sigma.
    Kind: helper.
    Why: Rewrite lemma used to unfold fc_sigmas inside word-evaluation and reflection reasoning.
    Used by: fc_gens_agree.
*)
Lemma fc_sigmasE (i : 'I_1) : tnth fc_sigmas i = fc_sigma.
Proof. by rewrite (tnth_nth fc_sigma) /=; case: i => [[|?] ?]. Qed.

(** fc_gens_agree — nat-level generator function fc_gens_nat agrees with the perm action of tnth fc_sigmas.
    Kind: helper.
    Why: Reflection bridge feeding the weval_inj_of_natB reflection lemma so vm_compute can discharge word-eval injectivity obligations.
    Used by: fc_weval_inj1, fc_weval_inj4.
*)
Lemma fc_gens_agree (i : 'I_1) (x : 'I_5) :
  fc_gens_nat (val i) (val x) = val (tnth fc_sigmas i x).
Proof.
by case: i => [[|?] ?]; case: x => [[|[|[|[|[|?]]]]] ?];
  rewrite fc_sigmasE /= permE.
Qed.

(** Word-eval injectivity at L=1: trivially true since there's only 1 generator
    and it is not the identity. *)
Lemma fc_weval_inj1 : @weval_inj FiveCard_M 1.
Proof.
apply: (weval_inj_of_natB fc_gens_agree).
by vm_compute.
Qed.

(** Word-eval injectivity at L=4: the 4 words [0], [0,0], [0,0,0], [0,0,0,0]
    evaluate to sigma, sigma^2, sigma^3, sigma^4, all distinct since
    sigma has order 5. *)
Lemma fc_weval_inj4 : @weval_inj FiveCard_M 4.
Proof.
apply: (weval_inj_of_natB fc_gens_agree).
by vm_compute.
Qed.

End five_card_pgg.
