(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* SampleAdapter: the sample layer over an ExecutionPlug                      *)
(*                                                                            *)
(* A SampleAdapter over an ExecutionPlug carries a finite sample space with a *)
(* law on it and the two maps reading a sample point as one run: the run      *)
(* argument sa_arg and the cut sa_cut. The plug itself is unchanged: a sample *)
(* adapter is a third value over an existing profile and plug.                *)
(*                                                                            *)
(* Section sample_layers derives the three layers of the sample space. Layer  *)
(* one is the interpreter run at a sample point. Layer two is a seat's or a   *)
(* coalition's endpoint reading as a random variable on the sample space.     *)
(* Layer three is the pushforward of the sample law along a layer-two reader  *)
(* or along the cut map. Its inner section sample_of_static_observation       *)
(* replaces, from a pointwise endpoint equation, every executed reader by the *)
(* static group-action observation, at the level of the random variables and  *)
(* at the level of their laws.                                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   SampleAdapter e         == the sample layer over the execution plug e    *)
(*   sa_run                  == layer 1: the run at a sample point            *)
(*   sa_seat_view            == layer 2: seat i's endpoint reader             *)
(*   sa_coalition_view       == layer 2: a coalition's endpoint reader        *)
(*   sa_seat_dist            == layer 3: the law of seat i's endpoint         *)
(*   sa_coalition_dist       == layer 3: the law of a coalition's reading     *)
(*   sa_cut_dist             == layer 3: the law of the cut                   *)
(*   sa_cut_dist_image       == the law of the cut's permutation image        *)
(*   sa_static_seat_view     == the static observation at seat i              *)
(*   sa_static_coalition_view == the static observation over a coalition      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   sa_seat_view_of_run  == the layer-two reader reads the layer-one run     *)
(*   sa_seat_dist_law     == the pushforward is the law of the random         *)
(*                           variable                                         *)
(*   sa_seat_viewE        == the executed seat reader is the static           *)
(*                           observation                                      *)
(*   sa_seat_distE        == the executed seat law is the static              *)
(*                           observation's law                                *)
(*   sa_coalition_viewE   == the executed coalition reader is the static      *)
(*                           observation over the coalition                   *)
(*   sa_coalition_distE   == the executed coalition law is the static         *)
(*                           observation's law                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The sample adapter                                                     *)
(******************************************************************************)

(** SampleAdapter — the probabilistic layer over an execution plug.
    Kind: interface.
    A value of this type carries a finite sample space sa_sampleT with a law
    sa_sampleP on it, the run argument map sa_arg and the cut map sa_cut. *)
Record SampleAdapter (R : realType) (mp : MonodromyProfile R)
    (e : ExecutionPlug mp) :=
  MkSampleAdapter {
    sa_sampleT : finType ;
    sa_sampleP : R.-fdist sa_sampleT ;
    sa_arg     : sa_sampleT -> ep_inputT e ;
    sa_cut     : sa_sampleT -> pgg_gT (mp_M mp) ;
  }.

(******************************************************************************)
(*     The three layers derived from the adapter                              *)
(******************************************************************************)

Section sample_layers.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : ExecutionPlug mp.
Variable sa : SampleAdapter e.
Variable P_idx : nat.

(* LAYER 1: raw execution. One interpreter result per sample point. *)

(** sa_run — the run at a sample point.
    @intent: exec_run at the sample's argument and cut, a pair of the final
    process states and the per-process traces. *)
Definition sa_run (u : sa_sampleT sa) :=
  @exec_run R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx.

(* LAYER 2: endpoint readers on sample points, typed as random variables. *)

(** sa_seat_view — seat i's endpoint as a random variable.
    @intent: the sample point mapped to exec_seat_endpoint at its argument and
    cut. *)
Definition sa_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sa.(sa_sampleP) -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => @exec_seat_endpoint R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx i.

(** sa_coalition_view — a coalition's endpoint readings as a random variable.
    @intent: the sample point mapped to exec_coalition_endpoints at its
    argument and cut. *)
Definition sa_coalition_view (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {RV sa.(sa_sampleP) -> {ffun 'I_(pi_T' (mp_PI mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1}} :=
  fun u => @exec_coalition_endpoints R mp e (sa.(sa_arg) u) (sa.(sa_cut) u)
             P_idx C.

(** sa_seat_view_of_run — the layer-two reader reads the layer-one run.
    @main architecture: sa_seat_view i u = nth ord0 (endpoints_of_trace (nth
    [::] (sa_run u).2 exec_verifier_id)) i.
    Naming: intentional; _of_run names the layer-one source the layer-two
    reader is read from, and no MathComp suffix denotes that relation. *)
Lemma sa_seat_view_of_run (u : sa_sampleT sa)
    (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_view i u
  = nth ord0 (endpoints_of_trace (nth [::] (sa_run u).2 exec_verifier_id)) i.
Proof. by []. Qed.

(* LAYER 3: pushforwards of the sample law along the layer-two readers. The
   raw trace has no layer 3: seq (pgg_data _) is not a finType. The cut laws
   do not mention P_idx, so section discharge gives them one argument fewer
   than the seat and coalition laws. *)

(** sa_seat_dist — the law of seat i's endpoint.
    @intent: the pushforward of sa_sampleP along sa_seat_view i. *)
Definition sa_seat_dist (i : 'I_(pi_T' (mp_PI mp)).+1)
    : R.-fdist 'I_(pgg_N' (mp_M mp)).+1 :=
  fdistmap (sa_seat_view i) sa.(sa_sampleP).

(** sa_coalition_dist — the law of a coalition's endpoint readings.
    @intent: the pushforward of sa_sampleP along sa_coalition_view C. *)
Definition sa_coalition_dist (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :=
  fdistmap (sa_coalition_view C) sa.(sa_sampleP).

(** sa_seat_dist_law — the pushforward is the law of the random variable.
    @main architecture: sa_seat_dist i = `p_ (sa_seat_view i). *)
Lemma sa_seat_dist_law (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_dist i = `p_ (sa_seat_view i).
Proof. by []. Qed.

(** sa_cut_dist — the law of the cut.
    @intent: the pushforward of sa_sampleP along sa_cut. *)
Definition sa_cut_dist : R.-fdist (pgg_gT (mp_M mp)) :=
  fdistmap sa.(sa_cut) sa.(sa_sampleP).

(** sa_cut_dist_image — the law of the cut's permutation image.
    @intent: the pushforward of sa_cut_dist along the representation pgg_rho,
    the carrier in which a SecurityWitness states its bound. *)
Definition sa_cut_dist_image : R.-fdist {perm 'I_(pgg_N' (mp_M mp)).+1} :=
  fdistmap (@pgg_rho (mp_M mp)) sa_cut_dist.

(******************************************************************************)
(*     The sample layers against the static observation                       *)
(******************************************************************************)

Section sample_of_static_observation.

Variable content_obs :
  ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
    -> 'I_(pgg_N' (mp_M mp)).+1.

(* Endpoint equation at every sample point: the executed endpoints are the
   static observation. *)
Hypothesis Hep : forall u : sa_sampleT sa,
  @exec_endpoints R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx
  = @exec_static_endpoints R mp e content_obs (sa.(sa_arg) u) (sa.(sa_cut) u).

(** sa_static_seat_view — the static observation at seat i as a random
    variable.
    @intent: the sample point mapped to content_obs of its argument at its cut
    and seat i's starting position. *)
Definition sa_static_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sa.(sa_sampleP) -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => content_obs (sa.(sa_arg) u)
             (sa.(sa_cut) u, tnth (pi_starts (mp_PI mp)) i).

(** sa_static_coalition_view — the static observation over a coalition as a
    random variable.
    @intent: the finfun sending a seat in C to content_obs of the argument at
    the cut and that seat's starting position, and a seat outside C to
    ord0. *)
Definition sa_static_coalition_view (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {RV sa.(sa_sampleP) -> {ffun 'I_(pi_T' (mp_PI mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1}} :=
  fun u => [ffun i => if i \in C
            then content_obs (sa.(sa_arg) u)
                   (sa.(sa_cut) u, tnth (pi_starts (mp_PI mp)) i)
            else ord0].

(** sa_seat_viewE — the executed seat reader is the static observation.
    @composes: sa_seat_distE *)
Lemma sa_seat_viewE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_view i = sa_static_seat_view i.
Proof. by apply: funext => u; exact: (exec_seat_endpointE (Hep u) i). Qed.

(** sa_seat_distE — the executed seat law is the static observation's law.
    @main architecture: sa_seat_dist i = fdistmap (sa_static_seat_view i)
    sa_sampleP. *)
Lemma sa_seat_distE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_dist i = fdistmap (sa_static_seat_view i) sa.(sa_sampleP).
Proof. by rewrite /sa_seat_dist sa_seat_viewE. Qed.

(** sa_coalition_viewE — the executed coalition reader is the static
    observation over the coalition.
    @composes: sa_coalition_distE *)
Lemma sa_coalition_viewE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  sa_coalition_view C = sa_static_coalition_view C.
Proof. by apply: funext => u; exact: (exec_coalition_endpointsE (Hep u) C). Qed.

(** sa_coalition_distE — the executed coalition law is the static
    observation's law.
    @main architecture: sa_coalition_dist C = fdistmap
    (sa_static_coalition_view C) sa_sampleP. *)
Lemma sa_coalition_distE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  sa_coalition_dist C = fdistmap (sa_static_coalition_view C) sa.(sa_sampleP).
Proof. by rewrite /sa_coalition_dist sa_coalition_viewE. Qed.

End sample_of_static_observation.

End sample_layers.
