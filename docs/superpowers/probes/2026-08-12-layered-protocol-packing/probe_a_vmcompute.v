(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe A, computation half: the participant list must stay a record field   *)
(*                                                                            *)
(* Removing mp_security and ep_cards_bridge does not touch ep_players and     *)
(* ep_playersE, and this file re-establishes the measurement that justifies   *)
(* keeping them, now over the revised records. The instrument is the one of   *)
(* docs/superpowers/probes/2026-08-11-monodromy-profile-end-to-end/           *)
(* probe_g_vmcompute.v: the process assembly is repeated with the             *)
(* participant list abstracted, so the concrete list and enum 'I_8 differ by  *)
(* one token and nothing else.                                                *)
(*                                                                            *)
(* Three measurements, with the wall times in the timing block at the end:    *)
(*                                                                            *)
(*  (a) exec_run_at at the concrete list pgl27_players closes by vm_compute.  *)
(*      exec_run, which reads the participant list off the record field,      *)
(*      closes the same way: exec_run is exec_run_at ep_players by            *)
(*      conversion.                                                           *)
(*                                                                            *)
(*  (b1) size (enum 'I_8) = 8 does NOT close by vm_compute. The enumeration   *)
(*      of an ordinal finType is stuck on the Qed-opaque idP inside           *)
(*      Finite.enum, so the virtual machine cannot learn the length of the    *)
(*      participant list, hence not the length of the process list.           *)
(*                                                                            *)
(*  (b2) exec_run_at at enum 'I_8 does NOT close by vm_compute either. The    *)
(*      attempt is wrapped in Timeout 30 so that the compile cannot run away; *)
(*      an unguarded attempt at this statement was killed at 70 s in the      *)
(*      2026-08-11 session.                                                   *)
(*                                                                            *)
(* Module PS below repeats the two revised records of                         *)
(* probe_a_profile_split.v. It is a copy rather than an import because the    *)
(* probe directory carries a dash-bearing name and so is not a legal Rocq     *)
(* logical path under the -R flags of rebuild.sh.                             *)
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

(******************************************************************************)
(*     The revised records and the participant-list-indexed assembly          *)
(******************************************************************************)

Module PS.

(** MonodromyProfile — a plugged monodromy group with its starting layout and
    its reconstruction plug.
    Kind: interface.
    The record of pgg_monodromy_profile.v:49-55 without the parameter R and
    without the field mp_security. *)
Record MonodromyProfile := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_secretT  : Type ;
  mp_PI       : PGGInterface mp_M ;
  mp_plug     : ReconPlug mp_M mp_secretT ;
}.

(** ExecutionPlug — the execution layer over a MonodromyProfile.
    Kind: interface.
    The record of pgg_execution_plug.v:57-72 without the parameter R and
    without the field ep_cards_bridge. *)
Record ExecutionPlug (mp : MonodromyProfile) :=
  MkExecutionPlug {
    ep_inputT         : Type ;
    ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
    ep_players        : seq 'I_(pi_T' (mp_PI mp)).+1 ;
    ep_playersE       : ep_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
    ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                          -> ('I_(pgg_N' (mp_M mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1) ;
    ep_input_procs    : ep_inputT
                          -> seq (aproc pgg_dtype
                                    (pgg_data (pgg_N' (mp_M mp)).+1)) ;
    ep_fuel           : nat ;
  }.

Section execution_of_profile.

Variable mp : MonodromyProfile.
Variable e : ExecutionPlug mp.

(** exec_input_id — committing party j's process identifier.
    @intent: process identifier (pi_T' (mp_PI mp)).+3 + j. *)
Definition exec_input_id (j : nat) : nat := (pi_T' (mp_PI mp)).+3 + j.

(** exec_input_ids — the party identifiers of the input processes.
    @intent: exec_input_id read at each position of ep_input_procs e x. *)
Definition exec_input_ids (x : ep_inputT e) : seq nat :=
  [seq exec_input_id j | j <- iota 0 (size (e.(ep_input_procs) x))].

(* The _at family is the measurement instrument: the assembly of exec_saprocs
   with the participant list abstracted, so that enum 'I_T.+1 and an instance's
   concrete list differ by one token and nothing else. *)

(** exec_saprocs_at — the session-typed process list over a given participant
    list.
    @intent: dealer, verifier, one player per entry of ps, then the input
    processes, in process-identifier order. *)
Definition exec_saprocs_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
              (exec_input_ids x) ps P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) ps)
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- ps]
       ++ e.(ep_input_procs) x.

(** exec_procs_at — the erased process list over a given participant list.
    @intent: the plain-proc image of exec_saprocs_at. *)
Definition exec_procs_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (exec_saprocs_at ps x w0 P_idx).

(** exec_run_at — the interpreter result over a given participant list.
    @intent: run_interp at ep_fuel e on exec_procs_at. *)
Definition exec_run_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (exec_procs_at ps x w0 P_idx).

(** exec_run — the interpreter result at the plug's own participant list.
    @intent: exec_run_at at ep_players e. *)
Definition exec_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (exec_procs_at e.(ep_players) x w0 P_idx).

(** exec_run_atE — the run is the participant-list-indexed run at the record's
    participant list.
    @main architecture: exec_run x w0 P_idx = exec_run_at (ep_players e) x w0
    P_idx, by conversion. *)
Lemma exec_run_atE (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :
  exec_run x w0 P_idx = exec_run_at e.(ep_players) x w0 P_idx.
Proof. by []. Qed.

End execution_of_profile.

End PS.

(******************************************************************************)
(*     The instrument filled at the eight-card orbit profile                  *)
(******************************************************************************)

(** pgl27_profileV — the eight-card orbit profile over the revised record.
    @intent: pgl27_M with secret type bool, starting layout pgl27_PI and
    reconstruction plug pgl27_plug.
    Naming: intentional; the trailing V marks the vm_compute-probe twin of the
    production pgl27_profile, which this file must not shadow. *)
Definition pgl27_profileV : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_plug.

(** pgl27_players_enumEV — the eight-element participant list is the seat
    enumeration.
    @composes: pgl27_exec_plugV *)
Lemma pgl27_players_enumEV :
  pgl27_players = enum 'I_(pi_T' (PS.mp_PI pgl27_profileV)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl27_exec_plugV — the eight-card orbit execution plug.
    @intent: run argument bool, participant list pgl27_players, content the
    shares of the dealt orbit secret, no input processes and fuel
    pgl27_fuel. *)
Definition pgl27_exec_plugV : PS.ExecutionPlug pgl27_profileV :=
  @PS.MkExecutionPlug pgl27_profileV bool erefl pgl27_players
    pgl27_players_enumEV (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) pgl27_fuel.

(******************************************************************************)
(*     (a) The concrete participant list reduces                              *)
(******************************************************************************)

(** pgl27_concrete_terminates — every process of the assembly at the concrete
    participant list reaches Finish.
    @main correctness: (exec_run_at pgl27_exec_plugV pgl27_players s w0 0).1 =
    nseq 10 Finish, for any cut w0, closed by vm_compute with no appeal to a
    landed lemma. *)
Lemma pgl27_concrete_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@PS.exec_run_at pgl27_profileV pgl27_exec_plugV pgl27_players s w0 0).1
  = nseq 10 Finish.
Proof. Time by vm_compute. Qed.

(** pgl27_field_terminates — every process of the assembly at the record's own
    participant list reaches Finish.
    @main correctness: (exec_run pgl27_exec_plugV s w0 0).1 = nseq 10 Finish,
    for any cut w0, closed by vm_compute; the ep_players field carries the
    concrete list, so the record path and the concrete path reduce alike. *)
Lemma pgl27_field_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@PS.exec_run pgl27_profileV pgl27_exec_plugV s w0 0).1 = nseq 10 Finish.
Proof. Time by vm_compute. Qed.

(******************************************************************************)
(*     (b1) The seat enumeration does not reduce                              *)
(******************************************************************************)

(* Observed message, head and leaf shape of a normal form of about 385 KB:

     Error: Unable to unify "8" with
      "(fix Ffix (x : seq 'I_8) : nat := match x with
                                         | [::] => 0
                                         | _ :: x1 => (Ffix x1).+1
                                         end)
         ((fix Ffix (x : seq 'I_8) : seq 'I_8 := ...)
            (Finite.enum {| Finite.sort := 'I_8; Finite.class := ... |}))"

   with leaves of the form

     match idP with
     | @ReflectT _ x0 => Some (Ordinal x0)
     | @ReflectF _ _ => None
     end

   The virtual machine reduces the goal but stops at Finite.enum of the
   ordinal Finite class record, whose unpickle leaf is a match on the
   Qed-opaque idP, so reflexivity then fails on a stuck term rather than
   vm_compute failing. *)
Time Fail Timeout 30 Definition pgl27_enum_size_reduces :
  size (enum 'I_(pi_T' (PS.mp_PI pgl27_profileV)).+1) = 8
  := ltac:(vm_compute; reflexivity).

(******************************************************************************)
(*     (b2) The run over the seat enumeration does not reduce                 *)
(******************************************************************************)

(* Observed message, with the Fail removed so that the diagnostic is printed:

     Error: Timeout!

   The guard is what stops the command: vm_compute is still running on the
   process list built over the stuck enumeration when the thirty seconds
   expire. The 2026-08-11 session ran the same statement unguarded and it was
   killed at seventy seconds with the goal untouched. *)
Time Fail Timeout 30 Definition pgl27_enum_terminates
  (s : bool) (w0 : pgg_gT pgl27_M) :
  (@PS.exec_run_at pgl27_profileV pgl27_exec_plugV
     (enum 'I_(pi_T' (PS.mp_PI pgl27_profileV)).+1) s w0 0).1
  = nseq 10 Finish
  := ltac:(vm_compute; reflexivity).

(******************************************************************************)
(*     Timing block                                                           *)
(*                                                                            *)
(* Machine: darwin 25.5.0, rocq 9, one worker, one compile at a time. Every   *)
(* number is the Time vernacular of a compile run of this file.               *)
(*                                                                            *)
(*   participant list          statement      route                  time     *)
(*   ----------------          ---------      -----                  ----     *)
(*   pgl27_players (argument)  whole run      vm_compute             0.022 s  *)
(*   ep_players    (field)     whole run      vm_compute             0.016 s  *)
(*   enum 'I_8                 size only      vm_compute, Timeout    0.115 s  *)
(*   enum 'I_8                 whole run      vm_compute, Timeout   30.01  s  *)
(*                                                                            *)
(*   The first three figures are stable across the four compile runs of this  *)
(*   text: 0.019 / 0.016, then 0.019 / 0.016 / 0.113, then                    *)
(*   0.018 / 0.016 / 0.113, then 0.022 / 0.016 / 0.115.                       *)
(*                                                                            *)
(*   The last figure is the guard, not a measurement of the reduction: the    *)
(*   command is still running when the thirty seconds expire. The 2026-08-11  *)
(*   unguarded run of the same statement was killed at seventy seconds.       *)
(*                                                                            *)
(*   whole file (time sh rebuild.sh probe_a_vmcompute.v)          34.9 s      *)
(*   of which the two guarded commands account for                30.1 s      *)
(*                                                                            *)
(* Verdict: the concrete participant list and the record field reduce in the  *)
(* same twentieth of a second, while the seat enumeration does not reduce at  *)
(* all, not even to its own length. The ratio is not finite as measured, so   *)
(* ep_players and ep_playersE stay fields of the revised ExecutionPlug.       *)
(******************************************************************************)
