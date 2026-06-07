(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5_profile: the S_5 x S_5 plug of the shared MonodromyProfile program     *)
(*                                                                            *)
(* Mirrors s5_profile but for the two-pile-of-five product instance. The plug *)
(* reuses the product covering plug (cs_plug s5x5_covering): the product       *)
(* sum-mod scheme on 'I_10, identity content readout, the S_5 x S_5 monodromy  *)
(* pgg_rho, and the proven full-group reconstruction invariance               *)
(* s5x5_perm_compatible.                                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_raag.
From pgg_smc Require Import pgg_s5x5 s5x5_pile.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_s5x5_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5x5_plug — the S_5 x S_5 reconstruction plug. Kind: instance. What: the
    product covering plug (product sum-mod scheme on 'I_10, id content, the
    S_5 x S_5 monodromy pgg_rho, proven invariance s5x5_perm_compatible). Why:
    routes S_5 x S_5 through the general MonodromyProfile program. Used-by:
    s5x5_profile. *)
Definition s5x5_plug : ReconPlug (@Gen_PGGTypes 7 8 s5x5_gen_tuple) :=
  cs_plug s5x5_covering.

(** s5x5_profile — plug the S_5 x S_5 product monodromy (N = 10, two piles of
    five). Kind: instance. What: the MonodromyProfile bundling s5x5_PI, the L=1
    fiber-counted security witness, and s5x5_plug. Why: the S_5 x S_5 plug of
    the shared program; its privacy threshold is k = 5 (per-pile sum-mod).
    Used-by: contrast demos. *)
Definition s5x5_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R (@Gen_PGGTypes 7 8 s5x5_gen_tuple) s5x5_PI
    (s5x5_security_witness_1 R) s5x5_plug.

(** run_k_s5x5 — the S_5 x S_5 plug's privacy threshold is 5.
    Kind: example. What: run_k (s5x5_profile R) = 5. Why: contrast character
    (the product sum-mod scheme reconstructs per pile at k = 5), read off the
    shared run_k. *)
Lemma run_k_s5x5 (R : realType) : run_k (s5x5_profile R) = 5.
Proof. by []. Qed.
