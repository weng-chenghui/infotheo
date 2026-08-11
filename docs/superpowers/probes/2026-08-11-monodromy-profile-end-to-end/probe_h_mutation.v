(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-H mutation: the adapter without the seat/share count bridge        *)
(*                                                                            *)
(* MUST FAIL. EPPnb is the record of probe_h_adapter_decomposition.v with the *)
(* field ep_players_bridge deleted; every other field is kept. The endpoint   *)
(* decoder is then attempted. The failure is at the DEFINITION, not at a      *)
(* proof: the endpoint tuple has one entry per seat while run_recover takes   *)
(* one entry per share, and with the bridge gone there is no equation to cast *)
(* along, so eppnb_decode does not elaborate.                                 *)
(*                                                                            *)
(* Expected error (rocq 9, verbatim):                                         *)
(*                                                                            *)
(*   In environment                                                           *)
(*   R : realType                                                             *)
(*   mp : MonodromyProfile R                                                  *)
(*   e : EPPnb mp                                                             *)
(*   ep : seq 'I_(pgg_N' (mp_M mp)).+1                                        *)
(*   Hsz : size ep = (pi_T' (mp_PI mp)).+1                                    *)
(*   The term "tcast Hsz (in_tuple ep)" has type                              *)
(*    "((pi_T' (mp_PI mp)).+1).-tuple 'I_(pgg_N' (mp_M mp)).+1"               *)
(*   while it is expected to have type                                        *)
(*    "((ts_T' (rp_scheme (mp_plug ?mp))).+1).-tuple                          *)
(*     'I_(pgg_N' (mp_M ?mp)).+1".                                            *)
(*                                                                            *)
(* Run: rocq compile with the flags of rebuild.sh; exit status 1, no .vo.     *)
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
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** EPPnb — the execution adapter without the seat/share count bridge.
    Kind: interface.
    The record of probe_h_adapter_decomposition.v with ep_players_bridge
    deleted: the run argument type, the card/share bridge, the participant list
    with its enumeration equation, the content readout, the input processes and
    the interpreter fuel. *)
Record EPPnb (R : realType) (mp : MonodromyProfile R) := MkEPPnb {
  epnb_inputT       : Type ;
  epnb_cards_bridge : (pgg_N' (mp_M mp)).+1
                        = (ts_T' (rp_scheme (mp_plug mp))).+1 ;
  epnb_players      : seq 'I_(pi_T' (mp_PI mp)).+1 ;
  epnb_playersE     : epnb_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
  epnb_content      : epnb_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                        -> ('I_(pgg_N' (mp_M mp)).+1
                            -> 'I_(pgg_N' (mp_M mp)).+1) ;
  epnb_input_procs  : epnb_inputT
                        -> seq (aproc pgg_dtype
                                  (pgg_data (pgg_N' (mp_M mp)).+1)) ;
  epnb_fuel         : nat ;
}.

Section decode_without_bridge.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPPnb mp.

(** eppnb_decode — the endpoint decoder attempted without the seat/share
    bridge.
    @intent: an endpoint list of one card per seat passed to run_recover, which
    takes one card per share; the two counts are unrelated without
    ep_players_bridge. *)
Definition eppnb_decode (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mp)).+1) : mp_secretT mp :=
  run_recover (tcast Hsz (in_tuple ep)).

End decode_without_bridge.
