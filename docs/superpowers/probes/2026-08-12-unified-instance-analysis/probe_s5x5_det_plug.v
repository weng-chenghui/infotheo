(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_s5x5_det_plug: the S_5 x S_5 deterministic correctness plug          *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 6.3, 6.4 *)
(* and 8.1. The deterministic execution path of s5x5_profile carries an       *)
(* ExecutionPlug whose run argument is the dealt position 'I_10, whose        *)
(* content readout is the canonical product encoding ts_encode s5x5_scheme,   *)
(* whose participant list is s5x5_run.s5x5_players and whose fuel is 300; the *)
(* derived process list is convertible to s5x5_procs, so the landed run facts *)
(* transport unchanged.                                                       *)
(*                                                                            *)
(* Probe claims:                                                             *)
(*   s5x5_det_procsE      == exec_procs of the plug is s5x5_procs             *)
(*   s5x5_det_terminates  == the derived run reaches Finish at 12 processes   *)
(*   s5x5_det_endpoints   == the derived endpoints are the static reading     *)
(*   s5x5_det_recon       == decoding the static reading returns s            *)
(*   s5x5_det_observed    == the packaged ObservedExecution                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import product_threshold.
From pgg_smc Require Import pgg_s5x5 s5x5_pile rigidity_s5x5_instance.
From pgg_smc Require Import s5x5_profile s5x5_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section s5x5_deterministic_execution.

Let mpX : MonodromyProfile := s5x5_profile.

(** s5x5_players_enumE — the ten-element participant list is the seat
    enumeration.
    @composes: s5x5_det_endpoints *)
Lemma s5x5_players_enumE :
  s5x5_run.s5x5_players = enum 'I_(pi_T' (mp_PI mpX)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** s5x5_det_plug — the S_5 x S_5 deterministic execution plug.
    @intent: the execution layer over s5x5_profile with run argument 'I_10,
    the seat/share bridge erefl at 10 seats and 10 shares, participant list
    s5x5_run.s5x5_players, content the shares ts_encode s5x5_scheme s of the
    dealt position s and fuel 300; the dealer-secret constructor fixes the
    input-process list to the empty list. *)
Definition s5x5_det_plug : ExecutionPlug mpX :=
  @dealer_secret_plug mpX 'I_10 erefl s5x5_run.s5x5_players s5x5_players_enumE
    (fun s _ => tnth (ts_encode s5x5_scheme s)) 300.

(** s5x5_content_obs — the S_5 x S_5 deterministic static observation.
    @intent: the share of the position s at the cut image of a starting
    position, namely tnth (ts_encode s5x5_scheme s) (pgg_rho w0 p). *)
Definition s5x5_content_obs (s : 'I_10)
    (p : pgg_gT (mp_M mpX) * 'I_(pgg_N' (mp_M mpX)).+1)
    : 'I_(pgg_N' (mp_M mpX)).+1 :=
  tnth (ts_encode s5x5_scheme s) (@pgg_rho (mp_M mpX) p.1 p.2).

(** s5x5_det_procsE — the derived process list is the instance's process list.
    @composes: s5x5_det_terminates, s5x5_det_endpoints, s5x5_det_recon *)
Lemma s5x5_det_procsE (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  @exec_procs mpX s5x5_det_plug s w0 0 = s5x5_procs s w0.
Proof. by []. Qed.

(** s5x5_det_fuelE — the plug's fuel is the instance's fuel.
    @composes: s5x5_det_terminates, s5x5_det_endpoints, s5x5_det_recon *)
Lemma s5x5_det_fuelE : ep_fuel s5x5_det_plug = 300.
Proof. by []. Qed.

(** s5x5_det_playersE — the plug's participant list is the instance's list.
    @composes: s5x5_det_endpoints *)
Lemma s5x5_det_playersE : ep_players s5x5_det_plug = s5x5_run.s5x5_players.
Proof. by []. Qed.

(** s5x5_det_procs_size — the derived run has twelve processes.
    @composes: s5x5_det_terminates *)
Lemma s5x5_det_procs_size (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  size (@exec_procs mpX s5x5_det_plug s w0 0) = 12.
Proof. by []. Qed.

(** s5x5_det_terminates — every process of the derived run reaches Finish.
    @composes: s5x5_det_observed *)
Lemma s5x5_det_terminates (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  (@exec_run mpX s5x5_det_plug s w0 0).1
  = nseq (size (@exec_procs mpX s5x5_det_plug s w0 0)) Finish.
Proof.
rewrite s5x5_det_procs_size /exec_run s5x5_det_fuelE s5x5_det_procsE.
exact: s5x5_run_terminates.
Qed.

(** s5x5_det_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @composes: s5x5_det_recon, s5x5_det_observed *)
Lemma s5x5_det_endpoints (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  @exec_endpoints mpX s5x5_det_plug s w0 0
  = @exec_static_endpoints mpX s5x5_det_plug s5x5_content_obs s w0.
Proof.
rewrite /exec_endpoints /exec_run s5x5_det_fuelE s5x5_det_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5x5_det_playersE s5x5_players_enumE.
exact: s5x5_endpoints.
Qed.

(** s5x5_det_endpoint_count — the derived run collects ten endpoints.
    @main correctness: size (exec_endpoints s5x5_det_plug s w0 0) = 10. *)
Lemma s5x5_det_endpoint_count (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  size (@exec_endpoints mpX s5x5_det_plug s w0 0) = 10.
Proof. by rewrite (exec_endpoints_size (s5x5_det_endpoints s w0)). Qed.

(** s5x5_det_decodeE — the plug's decoder is the instance's reconstruction.
    @composes: s5x5_det_recon *)
Lemma s5x5_det_decodeE (ep : seq 'I_(pgg_N' (mp_M mpX)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpX)).+1)
    (Hsz' : size ep = (ts_T' s5x5_scheme).+1) :
  @exec_decode mpX s5x5_det_plug ep Hsz
  = ts_recon s5x5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5x5_det_recon — decoding the static observation returns the dealt
    position, for any cut in the group and any proof of the endpoint count.
    @composes: s5x5_det_observed *)
Lemma s5x5_det_recon (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  w0 \in pgg_G s5x5_M ->
  forall Hsz : size (@exec_static_endpoints mpX s5x5_det_plug
                       s5x5_content_obs s w0)
               = (pi_T' (mp_PI mpX)).+1,
  @exec_decode mpX s5x5_det_plug
    (@exec_static_endpoints mpX s5x5_det_plug s5x5_content_obs s w0) Hsz = s.
Proof.
move=> Hw0.
rewrite -s5x5_det_endpoints /exec_endpoints /exec_run s5x5_det_fuelE
        s5x5_det_procsE /exec_verifier_id => Hsz.
rewrite (s5x5_det_decodeE Hsz (s5x5_endpoints_size s w0)).
exact: (s5x5_run_recovers s Hw0).
Qed.

(** s5x5_det_observed — the S_5 x S_5 deterministic observed execution.
    @intent: s5x5_profile with plug s5x5_det_plug at process offset 0, static
    observation s5x5_content_obs and expected value the dealt position; the
    three run facts are s5x5_det_terminates, s5x5_det_endpoints and
    s5x5_det_recon. *)
Definition s5x5_det_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpX s5x5_det_plug 0
    s5x5_content_obs (fun s : 'I_10 => s)
    s5x5_det_terminates s5x5_det_endpoints (@s5x5_det_recon).

(** s5x5_det_observed_recovers — the packaged deterministic run decodes to the
    dealt position.
    @main correctness: exec_decode of the executed endpoints of
    s5x5_det_observed at position s and cut w0 is s, for any cut w0 in the
    group. *)
Theorem s5x5_det_observed_recovers (s : 'I_10) (w0 : pgg_gT s5x5_M)
    (Hw0 : w0 \in pgg_G s5x5_M) :
  @exec_decode mpX s5x5_det_plug
    (@exec_endpoints mpX s5x5_det_plug s w0 0)
    (OE.oe_endpoints_size s5x5_det_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers s5x5_det_observed s w0 Hw0). Qed.

(** s5x5_det_correct — termination, endpoint count and recovery of the derived
    deterministic run.
    @main correctness: the run of s5x5_det_plug reaches Finish at each of its
    twelve processes, collects one endpoint per seat, and decodes to the dealt
    position s, for any cut w0 in the group. *)
Theorem s5x5_det_correct (s : 'I_10) (w0 : pgg_gT s5x5_M)
    (Hw0 : w0 \in pgg_G s5x5_M) :
  [/\ (@exec_run mpX s5x5_det_plug s w0 0).1
        = nseq (size (@exec_procs mpX s5x5_det_plug s w0 0)) Finish,
      size (@exec_endpoints mpX s5x5_det_plug s w0 0)
        = (pi_T' (mp_PI mpX)).+1 &
      @exec_decode mpX s5x5_det_plug
        (@exec_endpoints mpX s5x5_det_plug s w0 0)
        (exec_endpoints_size (s5x5_det_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct mpX s5x5_det_plug s5x5_content_obs (fun s : 'I_10 => s)
          s w0 0 (s5x5_det_terminates s w0) (s5x5_det_endpoints s w0)
          (s5x5_det_recon Hw0)).
Qed.

(******************************************************************************)
(*     The observer types read off the deterministic plug                     *)
(******************************************************************************)

(** s5x5_det_seat_endpointE — seat i's endpoint is the share at the cut image
    of seat i's start.
    @main correctness: exec_seat_endpoint s5x5_det_plug s w0 0 i =
    s5x5_content_obs s (w0, tnth (pi_starts (mp_PI mpX)) i). *)
Lemma s5x5_det_seat_endpointE (s : 'I_10) (w0 : pgg_gT s5x5_M)
    (i : 'I_(pi_T' (mp_PI mpX)).+1) :
  @exec_seat_endpoint mpX s5x5_det_plug s w0 0 i
  = s5x5_content_obs s (w0, tnth (pi_starts (mp_PI mpX)) i).
Proof. exact: (exec_seat_endpointE (s5x5_det_endpoints s w0) i). Qed.

(** s5x5_det_coalition_endpointsE — a coalition's endpoint readings are the
    shares at the cut images of its seats.
    @main correctness: the finfun sends a seat in C to the share of s at the
    cut image of that seat's start, and every seat outside C to ord0. *)
Lemma s5x5_det_coalition_endpointsE (s : 'I_10) (w0 : pgg_gT s5x5_M)
    (C : {set 'I_(pi_T' (mp_PI mpX)).+1}) :
  @exec_coalition_endpoints mpX s5x5_det_plug s w0 0 C
  = [ffun i => if i \in C
               then s5x5_content_obs s (w0, tnth (pi_starts (mp_PI mpX)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (s5x5_det_endpoints s w0) C). Qed.

(** s5x5_det_verifier_traceE — the derived verifier row is the verifier row of
    s5x5_procs.
    @main architecture: exec_verifier_trace s5x5_det_plug s w0 0 = nth [::]
    (run_interp 300 (s5x5_procs s w0)).2 1. *)
Lemma s5x5_det_verifier_traceE (s : 'I_10) (w0 : pgg_gT s5x5_M) :
  @exec_verifier_trace mpX s5x5_det_plug s w0 0
  = nth [::] (run_interp 300 (s5x5_procs s w0)).2 1.
Proof.
by rewrite /exec_verifier_trace /exec_run s5x5_det_fuelE s5x5_det_procsE.
Qed.

(** s5x5_det_raw_traceE — the derived raw seat trace is the trace of s5x5_procs
    at the seat's process identifier.
    @main architecture: exec_participant_trace s5x5_det_plug s w0 0 i = nth [::]
    (run_interp 300 (s5x5_procs s w0)).2 (2 + i). *)
Lemma s5x5_det_raw_traceE (s : 'I_10) (w0 : pgg_gT s5x5_M)
    (i : 'I_(pi_T' (mp_PI mpX)).+1) :
  @exec_participant_trace mpX s5x5_det_plug s w0 0 i
  = nth [::] (run_interp 300 (s5x5_procs s w0)).2 (2 + i).
Proof.
by rewrite /exec_participant_trace /exec_seat_id /exec_run s5x5_det_fuelE
   s5x5_det_procsE.
Qed.

(** s5x5_det_seat_countE — the profile's seat index type is 'I_10.
    @main architecture: (pi_T' (mp_PI mpX)).+1 = 10, the seat index type shared
    by the execution layer and the two five-seat pile coalitions. *)
Lemma s5x5_det_seat_countE : (pi_T' (mp_PI mpX)).+1 = 10.
Proof. by []. Qed.

End s5x5_deterministic_execution.

(******************************************************************************)
(*     Library signatures probed for the randomized and adapter files         *)
(******************************************************************************)

Check @pile1_shares.
Check @pile2_shares.
Check @project_pile1.
Check @project_pile2.
Check @combine_secret.
Check @split_combineK.

Print Assumptions s5x5_det_observed_recovers.
Print Assumptions s5x5_det_correct.
Print Assumptions s5x5_det_endpoints.
Print Assumptions s5x5_det_terminates.
