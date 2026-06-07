(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* den_boer_profile: the five-card (C_5) plug of the shared MonodromyProfile   *)
(*                                                                            *)
(* The plug bundles the five-card starting interface (FiveCard_PI, the five    *)
(* card positions in order), the uniform dealing-phase security witness        *)
(* (epsilon = 0, perfect security), and den_boer_plug: the bool/'I_5 threshold *)
(* scheme fcI_scheme, the identity content readout fc_content, the C_5          *)
(* monodromy pgg_rho, and the proven full-group reconstruction invariance       *)
(* fcI_perm_compatible. This routes the foundational five-card trick through    *)
(* the same shared exchange_* program as the s5, s5x5 and abelian instances.    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program
                            five_card_scheme_I5 five_card_security.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** den_boer_profile — plug the five-card C_5 cyclic-shift monodromy (N = 5).
    Kind: instance. What: the MonodromyProfile bundling FiveCard_PI, the
    perfect (epsilon = 0) uniform security witness, and den_boer_plug, with
    secret type bool. Why: the foundational five-card-trick plug of the shared
    program; its dealing phase is perfectly anonymous and its reconstruction
    recovers one bit (a AND b). Used-by: contrast demos, landscape. *)
Definition den_boer_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCard_M bool FiveCard_PI
    (fc_security_uniform R) den_boer_plug.

(** run_k_den_boer — the five-card plug's privacy threshold is 2.
    Kind: example. What: run_k (den_boer_profile R) = 2. Why: contrast
    character (any single revealed card leaks nothing about the AND, but two
    may), read off the shared run_k. *)
Lemma run_k_den_boer (R : realType) : run_k (den_boer_profile R) = 2.
Proof. by []. Qed.
