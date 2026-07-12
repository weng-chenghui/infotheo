(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_secrecy: coalition view independence of the eight-card orbit scheme  *)
(*                                                                            *)
(* The uniformly shuffled dealt arrangement of the PGL(2,7) orbit scheme has  *)
(* a coalition view independent of the orbit secret for every coalition of at *)
(* most three cards, instantiating the bridge's ttrans_view_indep_gen         *)
(* (reconstruct/transitivity_privacy.v) at t = 3.                             *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_view_indep == the PGL(2,7) coalition view independence at three    *)
(*     cards                                                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

Section pgl27_secrecy.
Local Open Scope proba_scope.
Variable R : realType.

(** pgl27P == the joint law of a uniform orbit secret and a uniform PGL(2,7)
    shuffle.
    @intent: the joint sample space of the eight-card orbit scheme. *)
Definition pgl27P : R.-fdist (bool * pgg_gT pgl27_M)%type :=
  (fdist_uniform card_bool) `x (`U pgl27_G_pos).

(** pgl27_secret == the dealt orbit-class secret component of a sample.
    @intent: the orbit-secret random variable. *)
Definition pgl27_secret : {RV pgl27P -> bool} := fun u => u.1.

(** pgl27_view == the dealt card values a coalition C observes at a sample,
    and ord0 outside C.
    @intent: the coalition observable random variable. *)
Definition pgl27_view (C : {set 'I_8}) : {RV pgl27P -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then
              tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i) else ord0].

(** pgl27_view_indep == any coalition of at most three cards has a view of the
    shuffled dealt arrangement independent of the orbit secret.
    @main security: instance coalition view independence from the bridge. *)
Lemma pgl27_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P |= pgl27_view C _|_ pgl27_secret.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R (fdist_uniform card_bool) pgl27_G_pos
  orbit_encode C HC isT orbit_encode_deck).
Qed.

End pgl27_secrecy.
