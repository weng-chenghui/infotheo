(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-C mutation: the execution adapter at the wrong fuel                *)
(*                                                                            *)
(* The record and the derived run of probe_c_pgl27_exec.v, copied, with the  *)
(* PGL(2,7) adapter's fuel changed from pgl27_fuel to 1. The process         *)
(* equality against pgl27_procs still holds, since the process list does not *)
(* mention the fuel. The transport of pgl27_run_terminates is then rejected: *)
(* the landed lemma runs the interpreter at pgl27_fuel = 220.                *)
(*                                                                           *)
(* The transport is staged through the fuel equation rather than through a   *)
(* direct [exact: pgl27_run_terminates]. At a mismatched fuel the direct     *)
(* step does not fail: conversion unfolds run_interp 1 and run_interp 220 on *)
(* the ten-process list and does not return (over 180 s under rocq-mcp,      *)
(* against 36 ms for the matched-fuel transport of probe_c_pgl27_exec.v).    *)
(* Staging makes the rejection immediate and names the two fuels.            *)
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
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** EPP — the execution adapter over a MonodromyProfile.
    Kind: interface. *)
Record EPP (R : realType) (mp : MonodromyProfile R) := MkEPP {
  ep_inputT         : Type ;
  ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
  ep_cards_bridge   : (pgg_N' (mp_M mp)).+1
                        = (ts_T' (rp_scheme (mp_plug mp))).+1 ;
  ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                        -> ('I_(pgg_N' (mp_M mp)).+1
                            -> 'I_(pgg_N' (mp_M mp)).+1) ;
  ep_input_procs    : ep_inputT
                        -> seq (aproc pgg_dtype
                                  (pgg_data (pgg_N' (mp_M mp)).+1)) ;
  ep_fuel           : nat ;
}.

Section execution_of_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.

(** epp_players — the participant list of the run.
    @intent: the enumeration of the (pi_T' (mp_PI mp)).+1 seats. *)
Definition epp_players : seq 'I_(pi_T' (mp_PI mp)).+1 :=
  enum 'I_(pi_T' (mp_PI mp)).+1.

(** epp_input_ids — the party identifiers of the input processes.
    @intent: iota (pi_T' (mp_PI mp)).+2 (size (ep_input_procs e x)). *)
Definition epp_input_ids (x : ep_inputT e) : seq nat :=
  iota (pi_T' (mp_PI mp)).+2 (size (e.(ep_input_procs) x)).

(** epp_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI mp with the adapter's content
    readout, the singleton deck [:: w0], the input identifiers and the seats. *)
Definition epp_dealer (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
    (epp_input_ids x) epp_players P_idx.

(** epp_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per seat, then the input processes, in
    process-identifier order. *)
Definition epp_saprocs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (epp_dealer x w0 P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) epp_players)
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- epp_players]
       ++ e.(ep_input_procs) x.

(** epp_procs — the erased process list.
    @intent: the plain-proc image of epp_saprocs. *)
Definition epp_procs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (epp_saprocs x w0 P_idx).

(** epp_run — the interpreter result.
    @intent: run_interp at ep_fuel e on epp_procs. *)
Definition epp_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (epp_procs x w0 P_idx).

End execution_of_profile.

Section pgl27_execution_mutated.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** mut_epp — the PGL(2,7) execution adapter at fuel 1.
    @intent: pgl_epp of probe_c_pgl27_exec.v with ep_fuel 1 in place of
    pgl27_fuel. *)
Definition mut_epp : EPP mpP :=
  @MkEPP R mpP bool erefl erefl
    (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) 1.

(** mut_playersE — the derived participant list is the instance's list.
    @composes: mut_procsE *)
Lemma mut_playersE : @epp_players R mpP = pgl27_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** mut_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs mut_epp s w0 0 = pgl27_procs s w0, the fuel
    playing no part in the process list. *)
Lemma mut_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_procs R mpP mut_epp s w0 0 = pgl27_procs s w0.
Proof.
rewrite /epp_procs /pgl27_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /pgl27_saprocs /pgl27_dealer_run.
by rewrite mut_playersE.
Qed.

(** mut_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run mut_epp s w0 0).1 = nseq 10 Finish. *)
Lemma mut_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@epp_run R mpP mut_epp s w0 0).1 = nseq 10 Finish.
Proof.
rewrite /epp_run mut_procsE.
have Hfuel : @ep_fuel R mpP mut_epp = pgl27_fuel := erefl.
rewrite Hfuel; exact: pgl27_run_terminates.
Qed.

End pgl27_execution_mutated.
