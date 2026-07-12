(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_scheme: the eight-card PGL(2,7) threshold scheme and its plug        *)
(*                                                                            *)
(* The orbit-class secret of pgl27_orbit is packaged as a ThresholdScheme     *)
(* bool 'I_8 with privacy threshold three: a coalition of at most three card  *)
(* positions learns nothing of the secret, while reconstruction reads all     *)
(* eight endpoints. Privacy is discharged by the                              *)
(* transitivity bridge ttrans_private applied to the sharp 3-transitivity of  *)
(* PGL(2,7) (pgl27_3transitive), the coordinate invariance of the classifier  *)
(* (orbit_class_invariant), deck stability (deck_stable) and population of    *)
(* both orbit classes (orbit_populated).                                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   orbit_valid s sh == sh is a valid deck whose orbit class is s            *)
(*   orbit_scheme     == the ThresholdScheme bool 'I_8, privacy threshold 3   *)
(*   pgl27_plug       == the ReconPlug over pgl27_M with content the identity *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_private         == coalitions of size at most three are private    *)
(*   orbit_recon_invariant == recovery is invariant under the shuffle action  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** orbit_valid — the arrangement sh is a valid deck whose orbit class is s.
    @intent: the validity predicate of the eight-card orbit scheme. *)
Definition orbit_valid (s : bool) (sh : 8.-tuple 'I_8) : Prop :=
  deck_ok sh /\ orbit_class sh = s.

(** orbit_correct — a valid deck reconstructs its orbit class.
    @composes: orbit_scheme *)
Lemma orbit_correct (s : bool) (sh : 8.-tuple 'I_8) :
  orbit_valid s sh -> orbit_class sh = s.
Proof. by move=> [_ ->]. Qed.

(** pgl27_private — every coalition of at most three positions is re-dealable
    to either orbit secret while matching the coalition's exact view.
    @main security: three-card coalitions of the orbit scheme are private. *)
Lemma pgl27_private (s1 s2 : bool) (sh : 8.-tuple 'I_8) (C : {set 'I_8}) :
  (#|C| < 3.+1)%N -> orbit_valid s1 sh ->
  exists sh', orbit_valid s2 sh' /\
    (forall i : 'I_8, i \in C -> tnth sh' i = tnth sh i).
Proof.
rewrite ltnS => HC [Hdeck _].
have [sh' [Hdeck' Hclass' Hagree]] :=
  @ttrans_private (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
    (@pgg_rho pgl27_M) 3 pgl27_3transitive orbit_class deck_ok
    (fun sh0 (H : deck_ok sh0) => H) orbit_class_invariant deck_stable
    orbit_populated s2 sh C HC Hdeck.
by exists sh'; split; [split | exact: Hagree].
Qed.

(** orbit_encode_valid — the encoder outputs a valid deck of the requested
    orbit class.
    @composes: orbit_scheme *)
Lemma orbit_encode_valid (s : bool) : orbit_valid s (orbit_encode s).
Proof. by split; [exact: orbit_encode_deck | exact: orbit_encodeK]. Qed.

(** orbit_scheme — the eight-card PGL(2,7) orbit ThresholdScheme, secret bool,
    shares 'I_8, privacy threshold three. Recovery reads all eight endpoints.
    @intent: the threshold scheme dealt by the eight-card protocol. *)
Definition orbit_scheme : ThresholdScheme bool 'I_8 :=
  @MkThresholdScheme bool 'I_8 (pgg_N' pgl27_M) 3
    orbit_valid orbit_class orbit_encode
    orbit_correct pgl27_private orbit_encode_valid.

(** orbit_recon_invariant — the orbit reconstruction is invariant under the
    coordinate action of any shuffle-group element.
    @composes: pgl27_plug *)
Lemma orbit_recon_invariant :
  @ts_recon_perm_invariant _ (pgg_G pgl27_M) bool 'I_8
    orbit_scheme (fun g => @pgg_rho pgl27_M g).
Proof.
by move=> g s shares gG [_ <-]; exact: (orbit_class_invariant g shares gG).
Qed.

(** pgl27_plug — the reconstruction plug over pgl27_M, content the identity.
    @intent: the covering plug of the orbit scheme, content the identity. *)
Definition pgl27_plug : ReconPlug pgl27_M bool :=
  @MkReconPlug pgl27_M bool orbit_scheme id
    (fun g => @pgg_rho pgl27_M g) orbit_recon_invariant.
