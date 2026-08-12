(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe C, mutation check: the endpoint field is load-bearing and the        *)
(* raw-row layer stays per-instance                                           *)
(*                                                                            *)
(* Section 15.4 packs one profile, one execution plug, one cut index, the     *)
(* static observation, the expected value and three run facts into a single   *)
(* record. This file checks the two claims that make that packing honest:     *)
(*                                                                            *)
(*   M1  the endpoint equation oe_endpoints is load-bearing. A seven-field    *)
(*       variant that drops it still yields the termination conjunct, but the *)
(*       recovery derivation no longer elaborates: the size proof that indexes *)
(*       exec_decode cannot be built (M1a), and the gluing term itself has no  *)
(*       candidate for the Hep argument of PS.exec_run_recovers (M1b).        *)
(*                                                                            *)
(*   M2  no semantic raw-row equation is derivable at the generic record. In  *)
(*       the readout form the statement cannot even be written, because the   *)
(*       committed-value argument of ep_content is not a field of the package *)
(*       (M2a). In the static-observation form the statement is well typed,   *)
(*       since content_of is polymorphic in the sheet count, but neither      *)
(*       by [] nor vm_compute closes it (M2b, M2c): the package carries no    *)
(*       field relating ep_content to oe_content_obs, and that relation is    *)
(*       what the per-instance trace lemmas such as denboer_abs_p0 establish  *)
(*       by vm_compute on a concrete process list.                            *)
(*                                                                            *)
(* Each rejection is wrapped in Fail, so the file compiles green exactly when *)
(* all four are rejected. The unmutated twins are declared first as positive  *)
(* controls, so a Fail cannot pass by a mistake shared with the honest case.  *)
(*                                                                            *)
(* The message quoted above a Fail is the verbatim diagnostic obtained by     *)
(* removing that one Fail and re-elaborating the declaration, one at a time,  *)
(* under the interactive checker: batch mode does not echo the message of a   *)
(* Fail that succeeds. M2c carries no quoted message, for the reason given    *)
(* at that check.                                                             *)
(*                                                                            *)
(* Modules PS and OE below repeat the parts of                                *)
(* probe_c_observed_execution.v that these four checks need. They are copies  *)
(* rather than imports because the probe directory carries a dash-bearing     *)
(* name and so is not a legal Rocq logical path under the -R flags of         *)
(* rebuild.sh.                                                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import denboer_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The program layer these checks need (from probe_a_profile_split.v)     *)
(******************************************************************************)

Module PS.

(** MonodromyProfile — a plugged monodromy group with its starting layout and
    its reconstruction plug.
    Kind: interface. *)
Record MonodromyProfile := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_secretT  : Type ;
  mp_PI       : PGGInterface mp_M ;
  mp_plug     : ReconPlug mp_M mp_secretT ;
}.

Section protocol_of_profile.

Variable mp : MonodromyProfile.

Let M    := mp_M mp.
Let N    := (pgg_N' M).+1.
Let plug := mp_plug mp.

(** run_recover — reconstruction via the plug's scheme.
    @intent: ts_recon of the plug's scheme, valued in mp_secretT. *)
Definition run_recover (collected : (ts_T' (rp_scheme plug)).+1.-tuple 'I_N)
    : mp_secretT mp :=
  ts_recon (rp_scheme plug) collected.

End protocol_of_profile.

(** ExecutionPlug — the execution layer over a MonodromyProfile.
    Kind: interface. *)
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

(** exec_dealer_id — the dealer's process identifier.
    @intent: process identifier 0. *)
Definition exec_dealer_id : nat := 0.

(** exec_verifier_id — the verifier's process identifier.
    @intent: process identifier 1. *)
Definition exec_verifier_id : nat := 1.

(** exec_seat_id — seat i's process identifier.
    @intent: process identifier 2 + i. *)
Definition exec_seat_id (i : 'I_(pi_T' (mp_PI mp)).+1) : nat := 2 + i.

(** exec_input_id — committing party j's process identifier.
    @intent: process identifier (pi_T' (mp_PI mp)).+3 + j. *)
Definition exec_input_id (j : nat) : nat := (pi_T' (mp_PI mp)).+3 + j.

(** exec_input_ids — the party identifiers of the input processes.
    @intent: exec_input_id read at each position of ep_input_procs e x. *)
Definition exec_input_ids (x : ep_inputT e) : seq nat :=
  [seq exec_input_id j | j <- iota 0 (size (e.(ep_input_procs) x))].

(** exec_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI mp with the plug's content
    readout, the singleton deck [:: w0], the input identifiers and the
    participant list. *)
Definition exec_dealer (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
    (exec_input_ids x) e.(ep_players) P_idx.

(** exec_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per participant, then the input
    processes, in process-identifier order. *)
Definition exec_saprocs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (exec_dealer x w0 P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) e.(ep_players))
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- e.(ep_players)]
       ++ e.(ep_input_procs) x.

(** exec_procs — the erased process list.
    @intent: the plain-proc image of exec_saprocs. *)
Definition exec_procs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (exec_saprocs x w0 P_idx).

(** exec_run — the interpreter result.
    @intent: run_interp at ep_fuel e on exec_procs, a pair of the final process
    states and the per-process traces. *)
Definition exec_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (exec_procs x w0 P_idx).

(** exec_endpoints — the verifier's collected endpoints.
    @intent: endpoints_of_trace of entry exec_verifier_id of exec_run.2. *)
Definition exec_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  endpoints_of_trace (nth [::] (exec_run x w0 P_idx).2 exec_verifier_id).

(** exec_verifier_trace — the executed trace of the verifier.
    @intent: entry exec_verifier_id of exec_run.2. *)
Definition exec_verifier_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  nth [::] (exec_run x w0 P_idx).2 exec_verifier_id.

(** exec_participant_trace — the executed trace of the seat-i player.
    @intent: entry exec_seat_id i of exec_run.2. *)
Definition exec_participant_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  nth [::] (exec_run x w0 P_idx).2 (exec_seat_id i).

(** exec_input_trace — the executed trace of committing party j.
    @intent: entry exec_input_id j of exec_run.2. *)
Definition exec_input_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (j : nat) :=
  nth [::] (exec_run x w0 P_idx).2 (exec_input_id j).

(** exec_dealer_trace — the executed trace of the dealer.
    @intent: entry exec_dealer_id of exec_run.2. *)
Definition exec_dealer_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  nth [::] (exec_run x w0 P_idx).2 exec_dealer_id.

(** exec_coalition_trace — the coalition's executed raw traces.
    @intent: the finfun sending a seat in C to its executed trace and a seat
    outside C to the empty trace. *)
Definition exec_coalition_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> seq (pgg_data (pgg_N' (mp_M mp)).+1)} :=
  [ffun i => if i \in C then exec_participant_trace x w0 P_idx i else [::]].

(** exec_players_size — the participant list has one entry per seat.
    @composes: exec_static_endpoints_size *)
Lemma exec_players_size : size e.(ep_players) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite e.(ep_playersE) size_enum_ord. Qed.

(** exec_seat_share_count — the seat/share bridge in successor form.
    @composes: exec_run_recovers *)
Lemma exec_seat_share_count :
  (pi_T' (mp_PI mp)).+1 = (ts_T' (rp_scheme (mp_plug mp))).+1.
Proof. by rewrite e.(ep_players_bridge). Qed.

(** exec_decode — the endpoint decoder of the plug.
    @intent: an endpoint list of one card per seat, transported along the
    seat/share bridge into the argument type of run_recover and reconstructed
    there. *)
Definition exec_decode (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mp)).+1) : mp_secretT mp :=
  run_recover (tcast (etrans Hsz exec_seat_share_count) (in_tuple ep)).

(** exec_static_endpoints — the static group-action observation over the seats.
    @intent: content_obs x read at the cut w0 and each participant's starting
    position. *)
Definition exec_static_endpoints
    (content_obs : ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
                     -> 'I_(pgg_N' (mp_M mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) :=
  [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- e.(ep_players)].

(** exec_static_endpoints_size — the static observation has one entry per seat.
    @composes: exec_endpoints_size *)
Lemma exec_static_endpoints_size content_obs x w0 :
  size (exec_static_endpoints content_obs x w0) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite size_map exec_players_size. Qed.

Section run_of_static_observation.

Variable content_obs :
  ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
    -> 'I_(pgg_N' (mp_M mp)).+1.
Variable expected : ep_inputT e -> mp_secretT mp.
Variables (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat).

(* Termination: every process of the run reaches Finish. *)
Hypothesis Hterm : (exec_run x w0 P_idx).1
  = nseq (size (exec_procs x w0 P_idx)) Finish.

(* Endpoint equation: the executed endpoints are the static observation. *)
Hypothesis Hep : exec_endpoints x w0 P_idx
  = exec_static_endpoints content_obs x w0.

(* Static recovery: decoding the static observation returns the expected
   value. *)
Hypothesis Hrecon : forall Hsz : size (exec_static_endpoints content_obs x w0)
    = (pi_T' (mp_PI mp)).+1,
  @exec_decode (exec_static_endpoints content_obs x w0) Hsz = expected x.

(** exec_endpoints_size — the run collects one endpoint per seat.
    @composes: exec_run_recovers *)
Lemma exec_endpoints_size : size (exec_endpoints x w0 P_idx)
  = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite Hep exec_static_endpoints_size. Qed.

(** exec_run_recovers — decoding the executed endpoints returns the expected
    value.
    @main correctness: exec_decode (exec_endpoints x w0 P_idx) = expected x, for
    a plug whose endpoints are the static observation and whose static
    observation decodes to expected x. *)
Theorem exec_run_recovers :
  @exec_decode (exec_endpoints x w0 P_idx) exec_endpoints_size = expected x.
Proof. by move: exec_endpoints_size; rewrite Hep; exact: Hrecon. Qed.

End run_of_static_observation.

End execution_of_profile.

End PS.

(******************************************************************************)
(*     The package and its seven-field mutant                                 *)
(******************************************************************************)

Module OE.

(* FORCED ADJUSTMENT, as in probe_c_observed_execution.v: Set Implicit
   Arguments demotes the record argument of the constructor, of the three
   proof-field projections and of every derived declaration, because that
   argument occurs in the type of the following one. *)
Unset Implicit Arguments.

(** ObservedExecution — one executed run of a plugged monodromy profile at a
    fixed cut index, together with the static observation it realises and the
    value it recovers.
    Kind: interface. *)
Record ObservedExecution := MkObservedExecution {
  oe_profile     : PS.MonodromyProfile ;
  oe_execution   : PS.ExecutionPlug oe_profile ;
  oe_P_idx       : nat ;
  oe_content_obs : PS.ep_inputT oe_execution
                     -> pgg_gT (PS.mp_M oe_profile)
                        * 'I_(pgg_N' (PS.mp_M oe_profile)).+1
                     -> 'I_(pgg_N' (PS.mp_M oe_profile)).+1 ;
  oe_expected    : PS.ep_inputT oe_execution -> PS.mp_secretT oe_profile ;
  oe_terminates  : forall (x : PS.ep_inputT oe_execution)
                          (w0 : pgg_gT (PS.mp_M oe_profile)),
    (@PS.exec_run oe_profile oe_execution x w0 oe_P_idx).1
    = nseq (size (@PS.exec_procs oe_profile oe_execution x w0 oe_P_idx))
        Finish ;
  oe_endpoints   : forall (x : PS.ep_inputT oe_execution)
                          (w0 : pgg_gT (PS.mp_M oe_profile)),
    @PS.exec_endpoints oe_profile oe_execution x w0 oe_P_idx
    = @PS.exec_static_endpoints oe_profile oe_execution oe_content_obs x w0 ;
  oe_static_recon : forall (x : PS.ep_inputT oe_execution)
                           (w0 : pgg_gT (PS.mp_M oe_profile)),
    w0 \in pgg_G (PS.mp_M oe_profile) ->
    forall Hsz : size (@PS.exec_static_endpoints oe_profile oe_execution
                         oe_content_obs x w0)
                 = (pi_T' (PS.mp_PI oe_profile)).+1,
    @PS.exec_decode oe_profile oe_execution
      (@PS.exec_static_endpoints oe_profile oe_execution oe_content_obs x w0)
      Hsz
    = oe_expected x ;
}.

(** oe_endpoints_size — the observed run collects one endpoint per seat.
    @composes: oe_run_recovers_ctrl *)
Definition oe_endpoints_size (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :
  size (@PS.exec_endpoints (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe))
  = (pi_T' (PS.mp_PI (oe_profile oe))).+1
  := PS.exec_endpoints_size (oe_endpoints oe x w0).

(** oe_participant_trace — the executed trace of the observed run's seat-i
    player.
    @intent: PS.exec_participant_trace at the package's plug and cut index. *)
Definition oe_participant_trace (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe)))
    (i : 'I_(pi_T' (PS.mp_PI (oe_profile oe))).+1) :=
  @PS.exec_participant_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) i.

(** oe_input_trace — the executed trace of the observed run's committing party
    j.
    @intent: PS.exec_input_trace at the package's plug and cut index. *)
Definition oe_input_trace (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) (j : nat) :=
  @PS.exec_input_trace (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe) j.

(** oe_dealer_trace — the executed trace of the observed run's dealer.
    @intent: PS.exec_dealer_trace at the package's plug and cut index. *)
Definition oe_dealer_trace (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :=
  @PS.exec_dealer_trace (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe).

(** oe_verifier_trace — the executed trace of the observed run's verifier.
    @intent: PS.exec_verifier_trace at the package's plug and cut index. *)
Definition oe_verifier_trace (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :=
  @PS.exec_verifier_trace (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe).

(** oe_coalition_trace — the observed run's coalition raw traces.
    @intent: PS.exec_coalition_trace at the package's plug and cut index. *)
Definition oe_coalition_trace (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe)))
    (C : {set 'I_(pi_T' (PS.mp_PI (oe_profile oe))).+1}) :=
  @PS.exec_coalition_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) C.

End OE.

Set Implicit Arguments.

(******************************************************************************)
(*     M1: the endpoint field is load-bearing                                 *)
(******************************************************************************)

(* The mutant is declared outside module OE, since it is not part of the
   package. Implicit Arguments is turned off around it for the reason recorded
   in module OE above. *)
Unset Implicit Arguments.

(** ObservedExecutionNoEp — the mutant of ObservedExecution with the endpoint
    equation removed.
    Kind: interface.
    The seven remaining fields are those of ObservedExecution in the same
    order.
    Naming: intentional; NoEp names the dropped field oe_endpoints. *)
Record ObservedExecutionNoEp := MkObservedExecutionNoEp {
  oeNoEp_profile     : PS.MonodromyProfile ;
  oeNoEp_execution   : PS.ExecutionPlug oeNoEp_profile ;
  oeNoEp_P_idx       : nat ;
  oeNoEp_content_obs : PS.ep_inputT oeNoEp_execution
                         -> pgg_gT (PS.mp_M oeNoEp_profile)
                            * 'I_(pgg_N' (PS.mp_M oeNoEp_profile)).+1
                         -> 'I_(pgg_N' (PS.mp_M oeNoEp_profile)).+1 ;
  oeNoEp_expected    : PS.ep_inputT oeNoEp_execution
                         -> PS.mp_secretT oeNoEp_profile ;
  oeNoEp_terminates  : forall (x : PS.ep_inputT oeNoEp_execution)
                              (w0 : pgg_gT (PS.mp_M oeNoEp_profile)),
    (@PS.exec_run oeNoEp_profile oeNoEp_execution x w0 oeNoEp_P_idx).1
    = nseq (size (@PS.exec_procs oeNoEp_profile oeNoEp_execution
                    x w0 oeNoEp_P_idx)) Finish ;
  oeNoEp_static_recon : forall (x : PS.ep_inputT oeNoEp_execution)
                               (w0 : pgg_gT (PS.mp_M oeNoEp_profile)),
    w0 \in pgg_G (PS.mp_M oeNoEp_profile) ->
    forall Hsz : size (@PS.exec_static_endpoints oeNoEp_profile
                         oeNoEp_execution oeNoEp_content_obs x w0)
                 = (pi_T' (PS.mp_PI oeNoEp_profile)).+1,
    @PS.exec_decode oeNoEp_profile oeNoEp_execution
      (@PS.exec_static_endpoints oeNoEp_profile oeNoEp_execution
         oeNoEp_content_obs x w0) Hsz
    = oeNoEp_expected x ;
}.

Set Implicit Arguments.

(* Positive control 1: on the eight-field record the gluing term elaborates. *)

(** oe_run_recovers_ctrl — decoding the observed run's endpoints returns the
    expected value.
    @main correctness: exec_decode (exec_endpoints (oe_execution oe) x w0
    (oe_P_idx oe)) = oe_expected oe x, for any cut w0 in the group.
    Naming: intentional; _ctrl marks the unmutated positive control of the M1
    rejections below. *)
Definition oe_run_recovers_ctrl (oe : OE.ObservedExecution)
    (x : PS.ep_inputT (OE.oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (OE.oe_profile oe)))
    (Hw0 : w0 \in pgg_G (PS.mp_M (OE.oe_profile oe))) :
  @PS.exec_decode (OE.oe_profile oe) (OE.oe_execution oe)
    (@PS.exec_endpoints (OE.oe_profile oe) (OE.oe_execution oe)
       x w0 (OE.oe_P_idx oe))
    (OE.oe_endpoints_size oe x w0)
  = OE.oe_expected oe x
  := @PS.exec_run_recovers (OE.oe_profile oe) (OE.oe_execution oe)
       (OE.oe_content_obs oe) (OE.oe_expected oe) x w0 (OE.oe_P_idx oe)
       (OE.oe_endpoints oe x w0) (OE.oe_static_recon oe x w0 Hw0).

(* Positive control 2: the mutant keeps the termination conjunct, so the
   rejections below isolate the endpoint half of the package and nothing
   else. *)

(** oeNoEp_terminatesE — every process of the mutant's run reaches Finish.
    @intent: the oeNoEp_terminates field, read at the mutant's own cut index. *)
Definition oeNoEp_terminatesE (oe : ObservedExecutionNoEp)
    (x : PS.ep_inputT (oeNoEp_execution oe))
    (w0 : pgg_gT (PS.mp_M (oeNoEp_profile oe))) :
  (@PS.exec_run (oeNoEp_profile oe) (oeNoEp_execution oe)
     x w0 (oeNoEp_P_idx oe)).1
  = nseq (size (@PS.exec_procs (oeNoEp_profile oe)
                  (oeNoEp_execution oe) x w0 (oeNoEp_P_idx oe))) Finish
  := oeNoEp_terminates oe x w0.

(* M1a. The size proof that indexes exec_decode is built from the endpoint
   equation, so on the mutant it cannot be built at all.

   The reference oeNoEp_endpoints was not found in the current environment. *)
Fail Definition oeNoEp_endpoints_size (oe : ObservedExecutionNoEp)
    (x : PS.ep_inputT (oeNoEp_execution oe))
    (w0 : pgg_gT (PS.mp_M (oeNoEp_profile oe))) :
  size (@PS.exec_endpoints (oeNoEp_profile oe) (oeNoEp_execution oe)
          x w0 (oeNoEp_P_idx oe))
  = (pi_T' (PS.mp_PI (oeNoEp_profile oe))).+1
  := PS.exec_endpoints_size (oeNoEp_endpoints oe x w0).

(* M1b. Weakening the statement to take an arbitrary size proof does not save
   the derivation: PS.exec_run_recovers still demands the endpoint equation as
   its Hep argument, and the mutant offers no term of that type.

   Cannot apply lemma (PS.exec_run_recovers _ (oeNoEp_static_recon oe x w0
   Hw0)) *)
Fail Definition oeNoEp_run_recovers (oe : ObservedExecutionNoEp)
    (x : PS.ep_inputT (oeNoEp_execution oe))
    (w0 : pgg_gT (PS.mp_M (oeNoEp_profile oe)))
    (Hw0 : w0 \in pgg_G (PS.mp_M (oeNoEp_profile oe)))
    (Hsz : size (@PS.exec_endpoints (oeNoEp_profile oe)
                   (oeNoEp_execution oe) x w0 (oeNoEp_P_idx oe))
           = (pi_T' (PS.mp_PI (oeNoEp_profile oe))).+1) :
  @PS.exec_decode (oeNoEp_profile oe) (oeNoEp_execution oe)
    (@PS.exec_endpoints (oeNoEp_profile oe) (oeNoEp_execution oe)
       x w0 (oeNoEp_P_idx oe)) Hsz
  = oeNoEp_expected oe x
  := ltac:(exact: (@PS.exec_run_recovers (oeNoEp_profile oe)
       (oeNoEp_execution oe) (oeNoEp_content_obs oe)
       (oeNoEp_expected oe) x w0 (oeNoEp_P_idx oe) _
       (oeNoEp_static_recon oe x w0 Hw0))).

(******************************************************************************)
(*     M2: the raw-row layer stays per-instance                               *)
(******************************************************************************)

(* Scope of probe_c_observed_execution.v. Derived at the generic record, each
   from the record's own fields and nothing else:

     OE.oe_endpoints_size        := PS.exec_endpoints_size (oe_endpoints ..)
     OE.oe_run_recovers          := PS.exec_run_recovers  (oe_endpoints ..)
                                                          (oe_static_recon ..)
     OE.oe_run_correct           := PS.exec_run_correct   (oe_terminates ..)
                                                          (oe_endpoints ..)
                                                          (oe_static_recon ..)
     OE.oe_seat_endpointE        := PS.exec_seat_endpointE (oe_endpoints ..)
     OE.oe_coalition_endpointsE  := PS.exec_coalition_endpointsE
                                                          (oe_endpoints ..)

   Defined at the generic record, with no equation attached:

     OE.oe_participant_trace     OE.oe_input_trace     OE.oe_dealer_trace
     OE.oe_verifier_trace        OE.oe_coalition_trace

   Instantiated at the two carriers: pgl27_observed and five_card_observed,
   with pgl27_observed_recovers, five_card_observed_recovers,
   pgl27_observed_correct, five_card_observed_correct,
   pgl27_observed_seat_endpointE and
   five_card_observed_coalition_endpointsE.

   The five extractors carry no equation because none is derivable, which is
   what M2a to M2c below check. *)

(* Positive control 3: the per-instance raw-row equation is provable, by
   vm_compute over a concrete process list with the content readout held
   abstract. denboer_abs_p0 is that equation at seat 0 of the den Boer run. *)
Check denboer_abs_p0.

(* M2a. In the readout form the equation cannot even be stated. The row content
   is the plug's content readout at the monodromy image of the seat's start,
   but ep_content takes the committed values as its second argument, and the
   package exposes no field holding them: the placeholder below has no
   solution.

   The following term contains unresolved implicit arguments:
     (fun oe : OE.ObservedExecution =>
      forall (x : PS.ep_inputT (OE.oe_execution oe))
        (w0 : pgg_gT (PS.mp_M (OE.oe_profile oe)))
        (i : 'I_(pi_T' (PS.mp_PI (OE.oe_profile oe))).+1),
      content_of (OE.oe_participant_trace oe x w0 i) =
      PS.ep_content x ?l
        (pgg_rho w0 (tnth (pi_starts (PS.mp_PI (OE.oe_profile oe))) i)))
   More precisely:
   - ?l: Cannot infer this placeholder of type
     "seq 'I_(pgg_N' (PS.mp_M (OE.oe_profile oe))).+1" in
     environment:
     oe : OE.ObservedExecution
     x : PS.ep_inputT (OE.oe_execution oe)
     w0 : pgg_gT (PS.mp_M (OE.oe_profile oe))
     i : 'I_(pi_T' (PS.mp_PI (OE.oe_profile oe))).+1 *)
Fail Definition oe_generic_row_readout (oe : OE.ObservedExecution) : Prop :=
  forall (x : PS.ep_inputT (OE.oe_execution oe))
         (w0 : pgg_gT (PS.mp_M (OE.oe_profile oe)))
         (i : 'I_(pi_T' (PS.mp_PI (OE.oe_profile oe))).+1),
  content_of (OE.oe_participant_trace oe x w0 i)
  = @PS.ep_content (OE.oe_profile oe) (OE.oe_execution oe) x _
      (@pgg_rho (PS.mp_M (OE.oe_profile oe)) w0
         (tnth (pi_starts (PS.mp_PI (OE.oe_profile oe))) i)).

(* In the static-observation form the equation IS well typed, because
   content_of of denboer_trace.v:39 is polymorphic in the sheet count and the
   generic row has type seq (pgg_data (pgg_N' (mp_M (oe_profile oe))).+1). The
   two rejections below are therefore about provability, not typing. *)

(** oe_generic_row_content — the raw row of a seat carries the static
    observation at that seat.
    @intent: the semantic raw-row equation, stated at the generic package. *)
Definition oe_generic_row_content (oe : OE.ObservedExecution) : Prop :=
  forall (x : PS.ep_inputT (OE.oe_execution oe))
         (w0 : pgg_gT (PS.mp_M (OE.oe_profile oe)))
         (i : 'I_(pi_T' (PS.mp_PI (OE.oe_profile oe))).+1),
  content_of (OE.oe_participant_trace oe x w0 i)
  = OE.oe_content_obs oe x
      (w0, tnth (pi_starts (PS.mp_PI (OE.oe_profile oe))) i).

(* M2b. The equation is not definitional: the package has no field relating
   ep_content to oe_content_obs, and oe_endpoints constrains only the
   verifier's endpoint list, not the players' rows.

   No applicable tactic. *)
Fail Definition oe_generic_row_contentP (oe : OE.ObservedExecution)
  : oe_generic_row_content oe := ltac:(by []).

(* M2c. Normalising first does not help either, and here the failure is not a
   mismatch but a non-termination. ep_fuel is a projection of a variable, so
   run_interp never exposes a constructor, yet vm_compute still expands the
   dealer program under the stuck fixpoint and does not come back: measured,
   the unguarded command was killed at ten minutes, and the interactive checker
   died on timeout 90 vm_compute. The 30-second guard is therefore what makes
   this check red, and that is the point being recorded: vm_compute does not
   close the generic equation.

   No message is quoted above this Fail. Removing it does not produce one,
   because the command does not terminate; the rejection is the Timeout raised
   by the guard, which the command-level Fail catches. A tactic-level Fail does
   not: in the interactive checker Fail timeout 20 vm_compute reports Coq:
   Timeout! rather than succeeding. This one command is about 29 of the file's
   35 seconds. *)
Fail Definition oe_generic_row_contentV (oe : OE.ObservedExecution)
  : oe_generic_row_content oe :=
  ltac:(move=> x w0 i; timeout 30 (vm_compute; reflexivity)).
