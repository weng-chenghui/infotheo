(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_profile: the S_5 plug of the shared MonodromyProfile program            *)
(*                                                                            *)
(* Relocated from the wreath7 contrast file. The plug reuses Bring's covering *)
(* plug (cs_plug s5_brings_covering): the sum-mod scheme on 'I_5, identity     *)
(* content readout, the S_5 monodromy pgg_rho, and the proven full-group       *)
(* reconstruction invariance s5_sum_mod_perm_compatible.                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_raag pgg_raag_path pgg_raag_s5.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_s5_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5_starts_uniq — the five starting card positions are distinct.
    Kind: helper. What: uniq (ord_tuple 5). Why: the uniqueness witness for
    s5_PI. Used-by: s5_PI. *)
Lemma s5_starts_uniq : uniq (ord_tuple 5).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** s5_PI — the concrete five-sheet starting interface for the S_5 plug.
    Kind: instance. What: the identity start tuple (ord_tuple 5). Why: the
    interface the shared exchange_* program plugs at for S_5. Used-by:
    s5_profile. *)
Definition s5_PI : PGGInterface (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) :=
  @MkPGGI (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 4 (ord_tuple 5) s5_starts_uniq.

(** s5_plug — the S_5 reconstruction plug. Kind: instance. What: Bring's
    covering plug (sum-mod scheme, id content, S_5 monodromy, proven
    invariance). Why: routes S_5 through the general MonodromyProfile program.
    Used-by: s5_profile. *)
Definition s5_plug : ReconPlug (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 'I_5 :=
  cs_plug s5_brings_covering.

(** s5_profile — plug the S_5 adjacent-transposition monodromy (N = 5).
    Kind: instance. What: the MonodromyProfile bundling s5_PI, the Schreier-walk
    security witness, and s5_plug. Why: the S_5 plug of the shared program; its
    anonymity bound decays geometrically to 0, k = 5. Used-by: contrast demos. *)
Definition s5_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 'I_5 s5_PI
    (s5_security_witness_schreier R 285) s5_plug.

(** run_k_s5 — the S_5 plug's privacy threshold is 5.
    Kind: example. What: run_k (s5_profile R) = 5. Why: contrast character
    (vs the abelian k = 2), read off the shared run_k. *)
Lemma run_k_s5 (R : realType) : run_k (s5_profile R) = 5.
Proof. by []. Qed.
