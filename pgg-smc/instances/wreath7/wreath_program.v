(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: the physical false-shuffle program for Z_7 wr S_2                     *)
(*                                                                            *)
(* The denboer five_card_program analog. A secret is dealt onto the 14-card   *)
(* deck (two piles of seven) by wreath2_scheme's encoding; the performer then *)
(* applies a false shuffle and the holder still recovers the secret.          *)
(*                                                                            *)
(* False-shuffle dictionary (note 20260603_205936):                          *)
(*   wreath_encode             the deal: secret -> 14 face-down cards          *)
(*   a within-pile cut (cut1,cut2 in wcore)  the free cut the audience sees    *)
(*   wreath_false_shuffle_recover   the reveal: a cut leaves recovery intact   *)
(*   the pile swap wswap     an anonymity move, NOT required to keep recovery  *)
(*                                                                            *)
(* Recovery is invariant under the abelian core wcore = Z_7^2 of cuts; the    *)
(* pile swap is deliberately excluded (it is a security operation, see        *)
(* wreath_recovery.wcore). Correctness reduces to the scheme's ts_correct and  *)
(* to the recon-invariance wreath_recon_inv.                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
Require Import pgg_interface.
From pgg_smc Require Import pgg_wreath wreath_recovery.
From pgg_reconstruct Require Import pgg_sharing_framework product_threshold
                                    covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** wreath_encode — deal a secret onto the 14-card deck.
    Kind: instance.
    Why: the physical deal; the encoding of wreath2_scheme presented as a card
    layout. *)
Definition wreath_encode (s : 'I_14) : 14.-tuple 'I_14 :=
  ts_encode wreath2_scheme s.

(** wreath_recover_encode — dealing then recovering returns the secret.
    Kind: helper.
    Why: end-to-end correctness of the deal with no shuffle; the base case of
    the program's correctness. *)
Lemma wreath_recover_encode (s : 'I_14) :
  ts_recon wreath2_scheme (wreath_encode s) = s.
Proof. exact: ts_correct (ts_encode_valid wreath2_scheme s). Qed.

(** wreath_false_shuffle_recover — a within-pile cut leaves recovery intact.
    Kind: main.
    Why: the false-shuffle guarantee. Permuting the dealt cards by any element
    of the abelian core (the cuts) still reconstructs the secret. The pile swap
    is not in wcore, so it carries anonymity, not recovery. Reduces to the
    covering's recon-invariance. *)
Lemma wreath_false_shuffle_recover (g : pgg_gT M_wreath) (s : 'I_14)
    (shares : 14.-tuple 'I_14) :
  g \in wcore ->
  ts_valid wreath2_scheme s shares ->
  ts_recon wreath2_scheme [tuple tnth shares (g i) | i < 14] = s.
Proof. exact: wreath_recon_inv. Qed.

(** wreath_cut1_recover — the concrete pile-1 cut is a recovery-preserving shuffle.
    Kind: example.
    Why: a named instance of the false-shuffle guarantee at the generator cut1,
    making the card-meaning concrete. *)
Lemma wreath_cut1_recover (s : 'I_14) (shares : 14.-tuple 'I_14) :
  ts_valid wreath2_scheme s shares ->
  ts_recon wreath2_scheme [tuple tnth shares (cut1 i) | i < 14] = s.
Proof.
apply: wreath_false_shuffle_recover.
by apply: mem_gen; rewrite !inE eqxx.
Qed.
