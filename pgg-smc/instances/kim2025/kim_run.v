(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Kim five-card family: executed-trace bridge.                               *)
(*                                                                            *)
(* Kim's biased five-card family and den Boer share the same monodromy        *)
(* FiveCardKim_M, interface FiveCardKim_PI and scheme fcI_scheme; the bias    *)
(* (five_card_family) drives only the security/mixing analysis. Trace-bridge  *)
(* correctness is word-independent (the cut is the identity here), so the     *)
(* executed program and its recovered secret are exactly den Boer's. This     *)
(* file records that the Kim instance runs the shared program and recovers the *)
(* committed AND, reusing den_boer_run's verified bridge.                      *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface.
From pgg_smc Require Import card_exchange_pismc pgg_run five_card_program.
From pgg_smc Require Import five_card_kim five_card_family den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** kim_procs — the Kim family executed-program list. Kim shares FiveCardKim_M
    and the five-card layout with den Boer, so the program is den_boer_procs. *)
Definition kim_procs := den_boer_procs.

(** kim_run_terminates — every process of the Kim run reaches Finish. *)
Lemma kim_run_terminates (a b : bool) (P_idx : nat) :
  (run_interp 100 (kim_procs a b P_idx)).1 = nseq 9 Finish.
Proof. exact: den_boer_run_terminates. Qed.

(** kim_run_recovers — reconstructing the Kim run's executed verifier endpoints
    returns the committed AND, for the full C_5 five-card family. *)
Lemma kim_run_recovers (a b : bool) :
  fc_three_consec [seq decode_bool x | x <-
    endpoints_of_trace (nth [::] (run_interp 100 (kim_procs a b 0)).2 1)]
  = a && b.
Proof. exact: den_boer_run_recovers. Qed.
