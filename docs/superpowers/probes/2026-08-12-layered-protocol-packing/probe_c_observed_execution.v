(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe C: the self-contained ObservedExecution package                      *)
(*                                                                            *)
(* Section 15.4 of the layered-packing request asks for one dependent record  *)
(* that carries a profile, the execution plug over that profile, the cut      *)
(* index, the static observation, the expected value, and the three run       *)
(* facts (termination, endpoint equation, static recovery), with no external  *)
(* parameter. Module OE below is that record together with:                   *)
(*                                                                            *)
(*   - the five generic derivations, each a single application of the         *)
(*     corresponding generic theorem of module PS (no proof body repeated);   *)
(*   - the five raw-row extractor specialisations, definitions only.          *)
(*                                                                            *)
(* Two closed values instantiate it:                                          *)
(*                                                                            *)
(*   pgl27_observed       the eight-card orbit run at cut index 0;            *)
(*   five_card_observed   the five-card run at cut index 0, shared by the     *)
(*                        den Boer and the Kim shuffle models.               *)
(*                                                                            *)
(* Module PS is copied verbatim from probe_a_profile_split.v (the R-free      *)
(* program layer, its derived execution API, the two instance profiles and    *)
(* plugs and the transported discharge chains). It is a copy rather than an   *)
(* import because the probe directory carries a dash-bearing name and so is   *)
(* not a legal Rocq logical path under the -R flags of rebuild.sh.            *)
(*                                                                            *)
(* Measured claims (all confirmed unless stated otherwise in the report):     *)
(*                                                                            *)
(*  1. THE RECORD ELABORATES IN THE STATED DEPENDENCY ORDER. oe_execution     *)
(*     depends on oe_profile, the three proof fields quantify over every run  *)
(*     argument and cut, and only oe_static_recon carries the group           *)
(*     membership hypothesis.                                                 *)
(*                                                                            *)
(*  2. THE FIVE DERIVATIONS ARE PURE GLUING. Each is one exact: of a PS       *)
(*     theorem applied to the record's own fields.                            *)
(*                                                                            *)
(*  3. BOTH CARRIERS INSTANTIATE FROM PROBE A'S CHAINS. The eight-card        *)
(*     fields are the probe A lemmas verbatim; the five-card fields need one  *)
(*     case split each, because the probe A lemmas take the committed pair    *)
(*     split into two bits while the record quantifies over the pair.         *)
(*                                                                            *)
(*  4. five_card_observed CARRIES NO SHUFFLE DATA. Its type and its body      *)
(*     mention no bias, no hypothesis pack and no word length, so the den     *)
(*     Boer and the Kim members of the family share this one value.           *)
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
From pgg_smc Require Import pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_word_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The revised program layer (copied from probe_a_profile_split.v)        *)
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

Section protocol_of_profile.

Variable mp : MonodromyProfile.

Let M    := mp_M mp.
Let PI   := mp_PI mp.
Let N    := (pgg_N' M).+1.
Let plug := mp_plug mp.
Let players := enum 'I_(pi_T' PI).+1.

(** run_party — a participant of the shared program.
    @intent: exchange_player at the profile's starting layout. *)
Definition run_party (i : 'I_(pi_T' PI).+1) := exchange_player PI i.

(** run_verifier — the verifier of the shared program.
    @intent: exchange_verifier at the profile's starting layout over the seat
    enumeration. *)
Definition run_verifier := exchange_verifier PI players.

(** run_recover — reconstruction via the plug's scheme.
    @intent: ts_recon of the plug's scheme, valued in mp_secretT. *)
Definition run_recover (collected : (ts_T' (rp_scheme plug)).+1.-tuple 'I_N)
    : mp_secretT mp :=
  ts_recon (rp_scheme plug) collected.

(** profile_k — the privacy-threshold character of the profile.
    @intent: the threshold k read off the plug's scheme. *)
Definition profile_k : nat := ts_k (rp_scheme plug).

(** profile_private — fewer than profile_k shares cannot distinguish two
    secrets.
    @intent: the ts_private field of the plug's scheme. *)
Definition profile_private := ts_private (rp_scheme plug).

(** profile_recon_encode — reconstructing the canonical encoding returns the
    dealt secret.
    @main correctness: run_recover (ts_encode (rp_scheme plug) s) = s. *)
Lemma profile_recon_encode (s : mp_secretT mp) :
  run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.

End protocol_of_profile.

(******************************************************************************)
(*     The revised execution layer                                            *)
(******************************************************************************)

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

(** dealer_secret_plug — the execution plug of a dealer-dealt secret.
    @intent: the plug whose input process list is empty at every run argument,
    so that the dealt secret is the only input of the run. *)
Definition dealer_secret_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content (fun _ => [::]) fuel.

(** committed_input_plug — the execution plug of a committed input.
    @intent: the plug whose runs carry one commit process per committing
    party, so that the run argument is the committed value. *)
Definition committed_input_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (input_procs : inputT
                     -> seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content input_procs fuel.

(******************************************************************************)
(*     The run, the traces and the decoder derived from the plug              *)
(******************************************************************************)

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

(** exec_endpoints_verifier_traceE — the endpoints are the endpoint reading of
    the verifier's executed trace.
    @main architecture: exec_endpoints x w0 P_idx = endpoints_of_trace
    (exec_verifier_trace x w0 P_idx). *)
Lemma exec_endpoints_verifier_traceE (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :
  exec_endpoints x w0 P_idx
  = endpoints_of_trace (exec_verifier_trace x w0 P_idx).
Proof. by []. Qed.

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

(** exec_seat_endpoint — the endpoint recorded for seat i.
    @intent: entry i of exec_endpoints. *)
Definition exec_seat_endpoint (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) : 'I_(pgg_N' (mp_M mp)).+1 :=
  nth ord0 (exec_endpoints x w0 P_idx) i.

(** exec_coalition_endpoints — the coalition's endpoint readings.
    @intent: the finfun sending a seat in C to its endpoint and a seat outside
    C to ord0. *)
Definition exec_coalition_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1} :=
  [ffun i => if i \in C then exec_seat_endpoint x w0 P_idx i else ord0].

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

(******************************************************************************)
(*     The interpreter output against the static observation                  *)
(******************************************************************************)

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

(** exec_seat_endpointE — seat i's endpoint is the static observation at seat i.
    @main correctness: exec_seat_endpoint x w0 P_idx i = content_obs x (w0, tnth
    (pi_starts (mp_PI mp)) i). *)
Lemma exec_seat_endpointE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  exec_seat_endpoint x w0 P_idx i
  = content_obs x (w0, tnth (pi_starts (mp_PI mp)) i).
Proof.
rewrite /exec_seat_endpoint Hep /exec_static_endpoints e.(ep_playersE).
by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
Qed.

(** exec_coalition_endpointsE — a coalition's endpoint readings are the static
    observation restricted to its seats.
    @main correctness: exec_coalition_endpoints x w0 P_idx C = [ffun i => if i
    \in C then content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) else ord0]. *)
Lemma exec_coalition_endpointsE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  exec_coalition_endpoints x w0 P_idx C
  = [ffun i => if i \in C
               then content_obs x (w0, tnth (pi_starts (mp_PI mp)) i)
               else ord0].
Proof.
apply/ffunP => i; rewrite /exec_coalition_endpoints !ffunE.
by case: ifP => // _; exact: exec_seat_endpointE.
Qed.

(** exec_coalition_endpoints_seqE — the coalition's endpoints in seat order are
    the static observation over its seats.
    @main correctness: [seq exec_seat_endpoint x w0 P_idx i | i <- enum C] =
    [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- enum C]. *)
Lemma exec_coalition_endpoints_seqE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  [seq exec_seat_endpoint x w0 P_idx i | i <- enum C]
  = [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- enum C].
Proof. by apply: eq_map => i; exact: exec_seat_endpointE. Qed.

(** exec_run_correct — termination, endpoint count and recovery of one run.
    @main correctness: the run reaches Finish at every process, collects one
    endpoint per seat, and decodes to expected x. *)
Theorem exec_run_correct :
  [/\ (exec_run x w0 P_idx).1 = nseq (size (exec_procs x w0 P_idx)) Finish,
      size (exec_endpoints x w0 P_idx) = (pi_T' (mp_PI mp)).+1 &
      @exec_decode (exec_endpoints x w0 P_idx) exec_endpoints_size
      = expected x].
Proof.
by split;
  [exact: Hterm | exact: exec_endpoints_size | exact: exec_run_recovers].
Qed.

End run_of_static_observation.

End execution_of_profile.

End PS.

(******************************************************************************)
(*     The observed-execution package                                         *)
(******************************************************************************)

Module OE.

(* FORCED ADJUSTMENT. Set Implicit Arguments demotes every binder that occurs
   in the type of a later one. In this package that is the record argument of
   nearly every declaration: oe_profile occurs in the type of oe_execution, and
   the record oe occurs in the type of the x of every derived declaration. With
   the flag left on, MkObservedExecution, the three proof-field projections and
   all nine derived declarations take their first argument implicitly, and
   oe_endpoints oe x w0 elaborates oe against the type of x:

     The term "oe" has type "ObservedExecution" while it is expected to have
     type "PS.ep_inputT (oe_execution ?oe)".

   Turning the flag off for the module is one line; the alternative is one
   Arguments <name> : clear implicits line per declaration, fourteen in all
   (measured: Arguments ... : clear implicits does fix each site, but three
   lines after the record are not enough — the nine derived declarations demote
   their own record argument in the same way). The five data-field projections
   take no further argument and so are unaffected either way. *)
Unset Implicit Arguments.

(** ObservedExecution — one executed run of a plugged monodromy profile at a
    fixed cut index, together with the static observation it realises and the
    value it recovers.
    Kind: interface.
    The record is self-contained: oe_execution is the execution plug over the
    record's own oe_profile, and the three proof fields quantify over every run
    argument and every cut. Only oe_static_recon carries the group-membership
    hypothesis on the cut. *)
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

(* Set Implicit Arguments demotes every constructor argument that occurs in the
   type of a later one, which here is the first five fields (oe_profile occurs
   in oe_execution's type, oe_execution in oe_content_obs's, oe_P_idx in
   oe_terminates's, oe_content_obs in oe_endpoints's and oe_expected in
   oe_static_recon's). The directive restores all eight. *)
(******************************************************************************)
(*     The generic derivations, each one application of a PS theorem          *)
(******************************************************************************)

(** oe_endpoints_size — the observed run collects one endpoint per seat.
    @composes: oe_run_recovers *)
Definition oe_endpoints_size (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :
  size (@PS.exec_endpoints (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe))
  = (pi_T' (PS.mp_PI (oe_profile oe))).+1
  := PS.exec_endpoints_size (oe_endpoints oe x w0).

(** oe_run_recovers — decoding the observed run's endpoints returns the
    expected value.
    @main correctness: exec_decode (exec_endpoints (oe_execution oe) x w0
    (oe_P_idx oe)) = oe_expected oe x, for any cut w0 in the group. *)
Theorem oe_run_recovers (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :
  w0 \in pgg_G (PS.mp_M (oe_profile oe)) ->
  @PS.exec_decode (oe_profile oe) (oe_execution oe)
    (@PS.exec_endpoints (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe))
    (oe_endpoints_size oe x w0)
  = oe_expected oe x.
Proof.
move=> Hw0.
exact: (@PS.exec_run_recovers (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) (oe_expected oe) x w0 (oe_P_idx oe)
          (oe_endpoints oe x w0) (oe_static_recon oe x w0 Hw0)).
Qed.

(** oe_run_correct — termination, endpoint count and recovery of the observed
    run.
    @main correctness: the run reaches Finish at every process, collects one
    endpoint per seat, and decodes to oe_expected oe x, for any cut w0 in the
    group. *)
Theorem oe_run_correct (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe))) :
  w0 \in pgg_G (PS.mp_M (oe_profile oe)) ->
  [/\ (@PS.exec_run (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe)).1
        = nseq (size (@PS.exec_procs (oe_profile oe) (oe_execution oe)
                        x w0 (oe_P_idx oe))) Finish,
      size (@PS.exec_endpoints (oe_profile oe) (oe_execution oe)
              x w0 (oe_P_idx oe))
        = (pi_T' (PS.mp_PI (oe_profile oe))).+1 &
      @PS.exec_decode (oe_profile oe) (oe_execution oe)
        (@PS.exec_endpoints (oe_profile oe) (oe_execution oe)
           x w0 (oe_P_idx oe))
        (oe_endpoints_size oe x w0)
      = oe_expected oe x].
Proof.
move=> Hw0.
exact: (@PS.exec_run_correct (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) (oe_expected oe) x w0 (oe_P_idx oe)
          (oe_terminates oe x w0) (oe_endpoints oe x w0)
          (oe_static_recon oe x w0 Hw0)).
Qed.

(** oe_seat_endpointE — seat i's endpoint is the static observation at seat i.
    @main correctness: exec_seat_endpoint (oe_execution oe) x w0 (oe_P_idx oe) i
    = oe_content_obs oe x (w0, tnth (pi_starts (mp_PI (oe_profile oe))) i). *)
Lemma oe_seat_endpointE (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe)))
    (i : 'I_(pi_T' (PS.mp_PI (oe_profile oe))).+1) :
  @PS.exec_seat_endpoint (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe) i
  = oe_content_obs oe x (w0, tnth (pi_starts (PS.mp_PI (oe_profile oe))) i).
Proof.
exact: (@PS.exec_seat_endpointE (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) x w0 (oe_P_idx oe) (oe_endpoints oe x w0) i).
Qed.

(** oe_coalition_endpointsE — a coalition's endpoint readings are the static
    observation restricted to its seats.
    @main correctness: exec_coalition_endpoints (oe_execution oe) x w0 (oe_P_idx
    oe) C = [ffun i => if i \in C then oe_content_obs oe x (w0, tnth (pi_starts
    (mp_PI (oe_profile oe))) i) else ord0]. *)
Lemma oe_coalition_endpointsE (oe : ObservedExecution)
    (x : PS.ep_inputT (oe_execution oe))
    (w0 : pgg_gT (PS.mp_M (oe_profile oe)))
    (C : {set 'I_(pi_T' (PS.mp_PI (oe_profile oe))).+1}) :
  @PS.exec_coalition_endpoints (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) C
  = [ffun i => if i \in C
               then oe_content_obs oe x
                      (w0, tnth (pi_starts (PS.mp_PI (oe_profile oe))) i)
               else ord0].
Proof.
exact: (@PS.exec_coalition_endpointsE (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) x w0 (oe_P_idx oe) (oe_endpoints oe x w0) C).
Qed.

(******************************************************************************)
(*     The raw-row extractors, specialised to the package                     *)
(******************************************************************************)

(* These five are definitions only. The package carries no field relating a raw
   trace row to a card content, so no semantic raw-row equation is stated here;
   probe_c_mutation.v shows that such an equation is not derivable from the
   record. *)

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
  @PS.exec_input_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) j.

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

(* Restore the file-level setting for the instance layer below, which is copied
   verbatim from probe_a_profile_split.v and elaborated under the flag. *)
Set Implicit Arguments.

(******************************************************************************)
(*     The two instance profiles over the revised records                     *)
(******************************************************************************)

(** pgl27_profileP — the eight-card orbit profile over the revised record.
    @intent: pgl27_M with secret type bool, starting layout pgl27_PI and
    reconstruction plug pgl27_plug.
    Naming: intentional; the trailing P marks the probe twin of the production
    pgl27_profile, which this file must not shadow. *)
Definition pgl27_profileP : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_plug.

(** five_card_profileP — the five-card profile over the revised record.
    @intent: FiveCardKim_M with secret type bool, starting layout
    FiveCardKim_PI and reconstruction plug five_card_plug.
    Naming: intentional; the trailing P marks the probe twin of the production
    five_card_profile, which this file must not shadow. *)
Definition five_card_profileP : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile FiveCardKim_M bool FiveCardKim_PI five_card_plug.

(** den_boer_profileP — the den Boer profile over the revised record.
    @intent: the five-card profile; with mp_security removed, the bias and the
    word length that distinguished the den Boer member from the Kim family are
    no longer profile data.
    Naming: intentional; the trailing P marks the probe twin of the production
    den_boer_profile, which this file must not shadow. *)
Definition den_boer_profileP : PS.MonodromyProfile := five_card_profileP.

(** den_boer_profileP_core — the den Boer wrapper is the five-card profile.
    @main architecture: den_boer_profileP = five_card_profileP. *)
Lemma den_boer_profileP_core : den_boer_profileP = five_card_profileP.
Proof. by []. Qed.

(******************************************************************************)
(*     The two execution plugs over the revised records                       *)
(******************************************************************************)

(** pgl27_players_enumEP — the eight-element participant list is the seat
    enumeration.
    @composes: pgl27_exec_endpointsP *)
Lemma pgl27_players_enumEP :
  pgl27_players = enum 'I_(pi_T' (PS.mp_PI pgl27_profileP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl27_exec_plugP — the eight-card orbit execution plug.
    @intent: run argument bool, the seat/share bridge erefl at 8 seats and 8
    shares, participant list pgl27_players, content the shares
    ts_encode orbit_scheme s of the dealt orbit secret s and fuel pgl27_fuel. *)
Definition pgl27_exec_plugP : PS.ExecutionPlug pgl27_profileP :=
  @PS.dealer_secret_plug pgl27_profileP bool erefl pgl27_players
    pgl27_players_enumEP (fun s _ => tnth (ts_encode orbit_scheme s))
    pgl27_fuel.

(** five_card_players_enumEP — the five-element participant list is the seat
    enumeration.
    @composes: five_card_exec_endpointsP *)
Lemma five_card_players_enumEP :
  den_boer_players = enum 'I_(pi_T' (PS.mp_PI five_card_profileP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** five_card_exec_plugP — the five-card execution plug.
    @intent: run argument the committed pair (a, b) of bits, the seat/share
    bridge erefl at 5 seats and 5 shares, participant list den_boer_players,
    content the den Boer layout of the decoded committed cards, the two commit
    processes of parties 7 and 8 as input processes and fuel 100. *)
Definition five_card_exec_plugP : PS.ExecutionPlug five_card_profileP :=
  @PS.committed_input_plug five_card_profileP (bool * bool)%type erefl
    den_boer_players five_card_players_enumEP
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(******************************************************************************)
(*     Process-list recovery by definitional equality                         *)
(******************************************************************************)

(** pgl27_exec_procsPE — the derived process list is the instance's process
    list.
    @composes: pgl27_exec_terminatesP, pgl27_exec_endpointsP,
    pgl27_exec_reconP *)
Lemma pgl27_exec_procsPE (s : bool) (w0 : pgg_gT pgl27_M) :
  @PS.exec_procs pgl27_profileP pgl27_exec_plugP s w0 0 = pgl27_procs s w0.
Proof. by []. Qed.

(** five_card_exec_procsPE — the derived process list is the instance's process
    list.
    @composes: five_card_exec_terminatesP, five_card_exec_endpointsP,
    five_card_exec_reconP *)
Lemma five_card_exec_procsPE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  @PS.exec_procs five_card_profileP five_card_exec_plugP (a, b) w0 P_idx
  = den_boer_procs a b w0 P_idx.
Proof. by []. Qed.

(******************************************************************************)
(*     The verifier-trace twin at the five-card carrier                       *)
(******************************************************************************)

(** five_card_exec_verifier_traceEP — the five-card endpoints are the endpoint
    reading of the verifier's executed trace.
    @main architecture: exec_endpoints five_card_exec_plugP (a, b) w0 P_idx =
    endpoints_of_trace (exec_verifier_trace five_card_exec_plugP (a, b) w0
    P_idx).
    Naming: intentional; _verifier_traceE names the equation against the
    verifier's executed trace, and the trailing P marks the probe twin. *)
Lemma five_card_exec_verifier_traceEP (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @PS.exec_endpoints five_card_profileP five_card_exec_plugP (a, b) w0 P_idx
  = endpoints_of_trace (@PS.exec_verifier_trace five_card_profileP
                          five_card_exec_plugP (a, b) w0 P_idx).
Proof. exact: PS.exec_endpoints_verifier_traceE. Qed.

(******************************************************************************)
(*     Correctness transport at the five-card carrier                         *)
(******************************************************************************)

(** five_card_content_obsP — the five-card static observation.
    @intent: tnth (den_boer_layout ab) (pgg_rho w0 p) at a committed pair ab, a
    cut w0 and a position p. *)
Definition five_card_content_obsP (ab : bool * bool)
    (p : pgg_gT FiveCardKim_M * 'I_(pgg_N' FiveCardKim_M).+1)
    : 'I_(pgg_N' FiveCardKim_M).+1 :=
  tnth (den_boer_layout ab) (@pgg_rho FiveCardKim_M p.1 p.2).

(** five_card_exec_playersEP — the plug's participant list is the instance's
    list.
    @composes: five_card_exec_endpointsP *)
Lemma five_card_exec_playersEP :
  PS.ep_players five_card_exec_plugP = den_boer_players.
Proof. by []. Qed.

(** five_card_exec_fuelEP — the plug's fuel is the instance's fuel.
    @composes: five_card_exec_terminatesP, five_card_exec_endpointsP,
    five_card_exec_reconP *)
Lemma five_card_exec_fuelEP : PS.ep_fuel five_card_exec_plugP = 100.
Proof. by []. Qed.

(** five_card_exec_procs_sizeP — the derived run has nine processes.
    @composes: five_card_exec_terminatesP
    Naming: intentional; _size is the repo's suffix for a size _ = _ statement,
    as in exec_endpoints_size, and the trailing P marks the probe twin. *)
Lemma five_card_exec_procs_sizeP (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  size (@PS.exec_procs five_card_profileP five_card_exec_plugP (a, b) w0 P_idx)
  = 9.
Proof. by []. Qed.

(** five_card_exec_terminatesP — every process of the derived run reaches
    Finish.
    @composes: five_card_exec_correctP *)
Lemma five_card_exec_terminatesP (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  (@PS.exec_run five_card_profileP five_card_exec_plugP (a, b) w0 P_idx).1
  = nseq (size (@PS.exec_procs five_card_profileP five_card_exec_plugP
                  (a, b) w0 P_idx)) Finish.
Proof.
rewrite five_card_exec_procs_sizeP /PS.exec_run five_card_exec_fuelEP
        five_card_exec_procsPE.
exact: den_boer_run_terminates.
Qed.

(** five_card_exec_endpointsP — the derived verifier endpoints are the static
    observation over the seats.
    @composes: five_card_exec_reconP, five_card_exec_recoversP,
    five_card_exec_correctP *)
Lemma five_card_exec_endpointsP (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @PS.exec_endpoints five_card_profileP five_card_exec_plugP (a, b) w0 0
  = @PS.exec_static_endpoints five_card_profileP five_card_exec_plugP
      five_card_content_obsP (a, b) w0.
Proof.
rewrite /PS.exec_endpoints /PS.exec_run five_card_exec_fuelEP
        five_card_exec_procsPE.
rewrite /PS.exec_verifier_id.
rewrite /PS.exec_static_endpoints five_card_exec_playersEP
        five_card_players_enumEP.
exact: den_boer_endpoints.
Qed.

(** five_card_exec_decodeEP — the plug's decoder is the instance's
    reconstruction.
    @composes: five_card_exec_decode_seqEP *)
Lemma five_card_exec_decodeEP (ep : seq 'I_(pgg_N' FiveCardKim_M).+1)
    (Hsz : size ep = (pi_T' (PS.mp_PI five_card_profileP)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  @PS.exec_decode five_card_profileP five_card_exec_plugP ep Hsz
  = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /PS.exec_decode /PS.run_recover
   (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** five_card_exec_decode_seqEP — the plug's decoder reads the endpoint list as
    the three-consecutive-cards predicate of the decoded endpoints.
    @composes: five_card_exec_reconP
    Naming: intentional; _seqE names the list form of the decoder equation, as
    in the production five_card_exec_decode_seqE, and the trailing P marks the
    probe twin. *)
Lemma five_card_exec_decode_seqEP (ep : seq 'I_(pgg_N' FiveCardKim_M).+1)
    (Hsz : size ep = (pi_T' (PS.mp_PI five_card_profileP)).+1) :
  @PS.exec_decode five_card_profileP five_card_exec_plugP ep Hsz
  = fc_three_consec [seq decode_bool x | x <- ep].
Proof.
rewrite (five_card_exec_decodeEP Hsz Hsz).
by rewrite /ts_recon /fcI_scheme /fcI_recon val_tcast.
Qed.

(** five_card_exec_reconP — decoding the static observation returns the
    conjunction of the two committed bits.
    @composes: five_card_exec_recoversP, five_card_exec_correctP *)
Lemma five_card_exec_reconP (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@PS.exec_static_endpoints five_card_profileP
                       five_card_exec_plugP five_card_content_obsP (a, b) w0)
               = (pi_T' (PS.mp_PI five_card_profileP)).+1,
  @PS.exec_decode five_card_profileP five_card_exec_plugP
    (@PS.exec_static_endpoints five_card_profileP five_card_exec_plugP
       five_card_content_obsP (a, b) w0) Hsz
  = (a, b).1 && (a, b).2.
Proof.
move=> Hw0 Hsz; rewrite five_card_exec_decode_seqEP -five_card_exec_endpointsP.
rewrite /PS.exec_endpoints /PS.exec_run five_card_exec_fuelEP
        five_card_exec_procsPE.
exact: (den_boer_run_recovers a b w0 Hw0).
Qed.

(** five_card_exec_recoversP — the derived five-card run decodes to the
    conjunction of the two committed bits.
    @main correctness: exec_decode of the executed endpoints of the run of
    five_card_exec_plugP at the committed pair (a, b) and cut w0 is a && b, for
    any cut w0 in the group. *)
Theorem five_card_exec_recoversP (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  @PS.exec_decode five_card_profileP five_card_exec_plugP
    (@PS.exec_endpoints five_card_profileP five_card_exec_plugP (a, b) w0 0)
    (PS.exec_endpoints_size (five_card_exec_endpointsP a b w0)) = a && b.
Proof.
exact: (@PS.exec_run_recovers five_card_profileP five_card_exec_plugP
          five_card_content_obsP (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_endpointsP a b w0) (five_card_exec_reconP Hw0)).
Qed.

(** five_card_exec_correctP — termination, endpoint count and recovery of the
    derived five-card run.
    @main correctness: the run of five_card_exec_plugP reaches Finish at each of
    its nine processes, collects one endpoint per seat, and decodes to the
    conjunction a && b of the two committed bits, for any cut w0 in the
    group. *)
Theorem five_card_exec_correctP (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  [/\ (@PS.exec_run five_card_profileP five_card_exec_plugP (a, b) w0 0).1
        = nseq (size (@PS.exec_procs five_card_profileP five_card_exec_plugP
                        (a, b) w0 0)) Finish,
      size (@PS.exec_endpoints five_card_profileP five_card_exec_plugP
              (a, b) w0 0)
        = (pi_T' (PS.mp_PI five_card_profileP)).+1 &
      @PS.exec_decode five_card_profileP five_card_exec_plugP
        (@PS.exec_endpoints five_card_profileP five_card_exec_plugP
           (a, b) w0 0)
        (PS.exec_endpoints_size (five_card_exec_endpointsP a b w0)) = a && b].
Proof.
exact: (@PS.exec_run_correct five_card_profileP five_card_exec_plugP
          five_card_content_obsP (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_terminatesP a b w0 0)
          (five_card_exec_endpointsP a b w0) (five_card_exec_reconP Hw0)).
Qed.

(******************************************************************************)
(*     Correctness transport at the eight-card orbit carrier                  *)
(******************************************************************************)

(** pgl27_content_obsP — the eight-card orbit static observation.
    @intent: tnth (ts_encode orbit_scheme s) (pgg_rho w0 p) at a dealt secret s,
    a cut w0 and a position p. *)
Definition pgl27_content_obsP (s : bool)
    (p : pgg_gT pgl27_M * 'I_(pgg_N' pgl27_M).+1) : 'I_(pgg_N' pgl27_M).+1 :=
  tnth (ts_encode orbit_scheme s) (@pgg_rho pgl27_M p.1 p.2).

(** pgl27_exec_playersEP — the plug's participant list is the instance's list.
    @composes: pgl27_exec_endpointsP *)
Lemma pgl27_exec_playersEP : PS.ep_players pgl27_exec_plugP = pgl27_players.
Proof. by []. Qed.

(** pgl27_exec_fuelEP — the plug's fuel is the instance's fuel.
    @composes: pgl27_exec_terminatesP, pgl27_exec_endpointsP,
    pgl27_exec_reconP *)
Lemma pgl27_exec_fuelEP : PS.ep_fuel pgl27_exec_plugP = pgl27_fuel.
Proof. by []. Qed.

(** pgl27_exec_procs_sizeP — the derived run has ten processes.
    @composes: pgl27_exec_terminatesP
    Naming: intentional; _size is the repo's suffix for a size _ = _ statement,
    as in exec_endpoints_size, and the trailing P marks the probe twin. *)
Lemma pgl27_exec_procs_sizeP (s : bool) (w0 : pgg_gT pgl27_M) :
  size (@PS.exec_procs pgl27_profileP pgl27_exec_plugP s w0 0) = 10.
Proof. by []. Qed.

(** pgl27_exec_terminatesP — every process of the derived run reaches Finish.
    @composes: pgl27_exec_correctP *)
Lemma pgl27_exec_terminatesP (s : bool) (w0 : pgg_gT pgl27_M) :
  (@PS.exec_run pgl27_profileP pgl27_exec_plugP s w0 0).1
  = nseq (size (@PS.exec_procs pgl27_profileP pgl27_exec_plugP s w0 0)) Finish.
Proof.
rewrite pgl27_exec_procs_sizeP /PS.exec_run pgl27_exec_fuelEP
        pgl27_exec_procsPE.
exact: pgl27_run_terminates.
Qed.

(** pgl27_exec_endpointsP — the derived verifier endpoints are the static
    observation over the seats.
    @composes: pgl27_exec_reconP, pgl27_exec_recoversP, pgl27_exec_correctP *)
Lemma pgl27_exec_endpointsP (s : bool) (w0 : pgg_gT pgl27_M) :
  @PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0
  = @PS.exec_static_endpoints pgl27_profileP pgl27_exec_plugP
      pgl27_content_obsP s w0.
Proof.
rewrite /PS.exec_endpoints /PS.exec_run pgl27_exec_fuelEP pgl27_exec_procsPE.
rewrite /PS.exec_verifier_id.
rewrite /PS.exec_static_endpoints pgl27_exec_playersEP pgl27_players_enumEP.
exact: pgl27_endpoints.
Qed.

(** pgl27_exec_decodeEP — the plug's decoder is the instance's reconstruction.
    @composes: pgl27_exec_reconP *)
Lemma pgl27_exec_decodeEP (ep : seq 'I_(pgg_N' pgl27_M).+1)
    (Hsz : size ep = (pi_T' (PS.mp_PI pgl27_profileP)).+1)
    (Hsz' : size ep = (ts_T' orbit_scheme).+1) :
  @PS.exec_decode pgl27_profileP pgl27_exec_plugP ep Hsz
  = ts_recon orbit_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /PS.exec_decode /PS.run_recover
   (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** pgl27_exec_reconP — decoding the static observation returns the dealt
    secret.
    @composes: pgl27_exec_recoversP, pgl27_exec_correctP *)
Lemma pgl27_exec_reconP (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  forall Hsz : size (@PS.exec_static_endpoints pgl27_profileP pgl27_exec_plugP
                       pgl27_content_obsP s w0)
               = (pi_T' (PS.mp_PI pgl27_profileP)).+1,
  @PS.exec_decode pgl27_profileP pgl27_exec_plugP
    (@PS.exec_static_endpoints pgl27_profileP pgl27_exec_plugP
       pgl27_content_obsP s w0) Hsz = s.
Proof.
move=> Hw0.
rewrite -pgl27_exec_endpointsP /PS.exec_endpoints /PS.exec_run
        pgl27_exec_fuelEP pgl27_exec_procsPE /PS.exec_verifier_id => Hsz.
rewrite (pgl27_exec_decodeEP Hsz (pgl27_endpoints_size s w0)).
exact: (pgl27_run_recovers s Hw0).
Qed.

(** pgl27_exec_recoversP — the derived eight-card orbit run decodes to the
    dealt secret.
    @main correctness: exec_decode of the executed endpoints of the run of
    pgl27_exec_plugP at secret s and cut w0 is s, for any cut w0 in the
    group. *)
Theorem pgl27_exec_recoversP (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  @PS.exec_decode pgl27_profileP pgl27_exec_plugP
    (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
    (PS.exec_endpoints_size (pgl27_exec_endpointsP s w0)) = s.
Proof.
exact: (@PS.exec_run_recovers pgl27_profileP pgl27_exec_plugP
          pgl27_content_obsP (fun b => b) s w0 0 (pgl27_exec_endpointsP s w0)
          (pgl27_exec_reconP Hw0)).
Qed.

(** pgl27_exec_correctP — termination, endpoint count and recovery of the
    derived eight-card orbit run.
    @main correctness: the run of pgl27_exec_plugP reaches Finish at each of its
    ten processes, collects one endpoint per seat, and decodes to the dealt
    secret s, for any cut w0 in the group. *)
Theorem pgl27_exec_correctP (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  [/\ (@PS.exec_run pgl27_profileP pgl27_exec_plugP s w0 0).1
        = nseq (size (@PS.exec_procs pgl27_profileP pgl27_exec_plugP s w0 0))
            Finish,
      size (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
        = (pi_T' (PS.mp_PI pgl27_profileP)).+1 &
      @PS.exec_decode pgl27_profileP pgl27_exec_plugP
        (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
        (PS.exec_endpoints_size (pgl27_exec_endpointsP s w0)) = s].
Proof.
exact: (@PS.exec_run_correct pgl27_profileP pgl27_exec_plugP
          pgl27_content_obsP (fun b => b) s w0 0 (pgl27_exec_terminatesP s w0)
          (pgl27_exec_endpointsP s w0) (pgl27_exec_reconP Hw0)).
Qed.

(******************************************************************************)
(*     The eight-card orbit observed execution                                *)
(******************************************************************************)

(* The three proof fields are the probe A lemmas verbatim:
   pgl27_exec_terminatesP and pgl27_exec_endpointsP already fix the cut index
   at 0, which is exactly the record's own oe_P_idx, and both quantify over the
   dealt secret and the cut, which is exactly the record's forall x w0. *)

(** pgl27_observed — the eight-card orbit observed execution.
    @intent: pgl27_profileP with plug pgl27_exec_plugP at cut index 0, static
    observation pgl27_content_obsP and expected value the dealt secret. *)
Definition pgl27_observed : OE.ObservedExecution :=
  @OE.MkObservedExecution pgl27_profileP pgl27_exec_plugP 0
    pgl27_content_obsP (fun b : bool => b)
    pgl27_exec_terminatesP pgl27_exec_endpointsP pgl27_exec_reconP.

(******************************************************************************)
(*     The five-card observed execution                                       *)
(******************************************************************************)

(* The record quantifies over the committed pair, while the probe A lemmas take
   the pair split into two bits, so each of the three fields needs one case
   split on the pair. Nothing else changes. *)

(** five_card_oe_terminates — every process of the five-card run reaches Finish
    at every committed pair and cut.
    @composes: five_card_observed *)
Lemma five_card_oe_terminates (x : bool * bool) (w0 : pgg_gT FiveCardKim_M) :
  (@PS.exec_run five_card_profileP five_card_exec_plugP x w0 0).1
  = nseq (size (@PS.exec_procs five_card_profileP five_card_exec_plugP
                  x w0 0)) Finish.
Proof. by case: x => a b; exact: five_card_exec_terminatesP. Qed.

(** five_card_oe_endpoints — the five-card verifier endpoints are the static
    observation at every committed pair and cut.
    @composes: five_card_observed *)
Lemma five_card_oe_endpoints (x : bool * bool) (w0 : pgg_gT FiveCardKim_M) :
  @PS.exec_endpoints five_card_profileP five_card_exec_plugP x w0 0
  = @PS.exec_static_endpoints five_card_profileP five_card_exec_plugP
      five_card_content_obsP x w0.
Proof. by case: x => a b; exact: five_card_exec_endpointsP. Qed.

(** five_card_oe_static_recon — decoding the five-card static observation
    returns the conjunction of the committed pair.
    @composes: five_card_observed *)
Lemma five_card_oe_static_recon (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@PS.exec_static_endpoints five_card_profileP
                       five_card_exec_plugP five_card_content_obsP x w0)
               = (pi_T' (PS.mp_PI five_card_profileP)).+1,
  @PS.exec_decode five_card_profileP five_card_exec_plugP
    (@PS.exec_static_endpoints five_card_profileP five_card_exec_plugP
       five_card_content_obsP x w0) Hsz
  = x.1 && x.2.
Proof. by case: x => a b; exact: five_card_exec_reconP. Qed.

(* five_card_observed is the ONE value shared by the den Boer and the Kim
   shuffle models. Neither its type nor its body can vary with the bias or the
   word length: five_card_profileP and five_card_exec_plugP are closed terms
   with no realType, no eps, no hypothesis pack and no L, and the three proof
   fields quantify over the cut w0 rather than over a distribution on cuts. *)

(** five_card_observed — the five-card observed execution.
    @intent: five_card_profileP with plug five_card_exec_plugP at cut index 0,
    static observation five_card_content_obsP and expected value the conjunction
    of the committed pair. *)
Definition five_card_observed : OE.ObservedExecution :=
  @OE.MkObservedExecution five_card_profileP five_card_exec_plugP 0
    five_card_content_obsP (fun ab : bool * bool => ab.1 && ab.2)
    five_card_oe_terminates five_card_oe_endpoints five_card_oe_static_recon.

(** den_boer_observed — the den Boer observed execution.
    @intent: the five-card observed execution; the den Boer member and the Kim
    members of the family share it.
    Naming: intentional; the den Boer prefix names the protocol member, and the
    body records that the member adds no execution data. *)
Definition den_boer_observed : OE.ObservedExecution := five_card_observed.

(** den_boer_observed_core — the den Boer wrapper is the five-card observed
    execution.
    @main architecture: den_boer_observed = five_card_observed. *)
Lemma den_boer_observed_core : den_boer_observed = five_card_observed.
Proof. by []. Qed.

(******************************************************************************)
(*     The generic derivations at the two carriers                            *)
(******************************************************************************)

Check (OE.oe_run_correct pgl27_observed).
Check (OE.oe_run_correct five_card_observed).
Check (OE.oe_seat_endpointE pgl27_observed).
Check (OE.oe_coalition_endpointsE five_card_observed).
Check (OE.oe_participant_trace pgl27_observed).
Check (OE.oe_input_trace five_card_observed).
Check (OE.oe_dealer_trace pgl27_observed).
Check (OE.oe_verifier_trace five_card_observed).
Check (OE.oe_coalition_trace pgl27_observed).

(** pgl27_observed_recovers — the packaged eight-card orbit run decodes to the
    dealt secret.
    @main correctness: exec_decode of the executed endpoints of pgl27_observed
    at secret s and cut w0 is s, for any cut w0 in the group. *)
Theorem pgl27_observed_recovers (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  @PS.exec_decode pgl27_profileP pgl27_exec_plugP
    (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
    (OE.oe_endpoints_size pgl27_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers pgl27_observed s w0 Hw0). Qed.

(** five_card_observed_recovers — the packaged five-card run decodes to the
    conjunction of the committed pair.
    @main correctness: exec_decode of the executed endpoints of
    five_card_observed at the committed pair x and cut w0 is x.1 && x.2, for any
    cut w0 in the group. *)
Theorem five_card_observed_recovers (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  @PS.exec_decode five_card_profileP five_card_exec_plugP
    (@PS.exec_endpoints five_card_profileP five_card_exec_plugP x w0 0)
    (OE.oe_endpoints_size five_card_observed x w0) = x.1 && x.2.
Proof. exact: (OE.oe_run_recovers five_card_observed x w0 Hw0). Qed.

(** pgl27_observed_correct — termination, endpoint count and recovery of the
    packaged eight-card orbit run.
    @main correctness: the run of pgl27_observed reaches Finish at every
    process, collects one endpoint per seat, and decodes to the dealt secret s,
    for any cut w0 in the group. *)
Theorem pgl27_observed_correct (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  [/\ (@PS.exec_run pgl27_profileP pgl27_exec_plugP s w0 0).1
        = nseq (size (@PS.exec_procs pgl27_profileP pgl27_exec_plugP s w0 0))
            Finish,
      size (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
        = (pi_T' (PS.mp_PI pgl27_profileP)).+1 &
      @PS.exec_decode pgl27_profileP pgl27_exec_plugP
        (@PS.exec_endpoints pgl27_profileP pgl27_exec_plugP s w0 0)
        (OE.oe_endpoints_size pgl27_observed s w0) = s].
Proof. exact: (OE.oe_run_correct pgl27_observed s w0 Hw0). Qed.

(** five_card_observed_correct — termination, endpoint count and recovery of
    the packaged five-card run.
    @main correctness: the run of five_card_observed reaches Finish at every
    process, collects one endpoint per seat, and decodes to x.1 && x.2, for any
    cut w0 in the group. *)
Theorem five_card_observed_correct (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  [/\ (@PS.exec_run five_card_profileP five_card_exec_plugP x w0 0).1
        = nseq (size (@PS.exec_procs five_card_profileP five_card_exec_plugP
                        x w0 0)) Finish,
      size (@PS.exec_endpoints five_card_profileP five_card_exec_plugP x w0 0)
        = (pi_T' (PS.mp_PI five_card_profileP)).+1 &
      @PS.exec_decode five_card_profileP five_card_exec_plugP
        (@PS.exec_endpoints five_card_profileP five_card_exec_plugP x w0 0)
        (OE.oe_endpoints_size five_card_observed x w0) = x.1 && x.2].
Proof. exact: (OE.oe_run_correct five_card_observed x w0 Hw0). Qed.

(** pgl27_observed_seat_endpointE — the packaged eight-card orbit run's seat
    endpoint is the static observation at that seat.
    @main correctness: exec_seat_endpoint pgl27_exec_plugP s w0 0 i = tnth
    (ts_encode orbit_scheme s) (pgg_rho w0 (tnth (pi_starts pgl27_PI) i)). *)
Lemma pgl27_observed_seat_endpointE (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (PS.mp_PI pgl27_profileP)).+1) :
  @PS.exec_seat_endpoint pgl27_profileP pgl27_exec_plugP s w0 0 i
  = pgl27_content_obsP s (w0, tnth (pi_starts (PS.mp_PI pgl27_profileP)) i).
Proof. exact: (OE.oe_seat_endpointE pgl27_observed s w0 i). Qed.

(** five_card_observed_coalition_endpointsE — the packaged five-card run's
    coalition endpoints are the static observation over the coalition's seats.
    @main correctness: exec_coalition_endpoints five_card_exec_plugP x w0 0 C =
    [ffun i => if i \in C then five_card_content_obsP x (w0, tnth (pi_starts
    FiveCardKim_PI) i) else ord0]. *)
Lemma five_card_observed_coalition_endpointsE (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M)
    (C : {set 'I_(pi_T' (PS.mp_PI five_card_profileP)).+1}) :
  @PS.exec_coalition_endpoints five_card_profileP five_card_exec_plugP x w0 0 C
  = [ffun i => if i \in C
               then five_card_content_obsP x
                      (w0, tnth (pi_starts (PS.mp_PI five_card_profileP)) i)
               else ord0].
Proof. exact: (OE.oe_coalition_endpointsE five_card_observed x w0 C). Qed.

(******************************************************************************)
(*     Print Assumptions block                                                *)
(******************************************************************************)

Print Assumptions pgl27_observed.
Print Assumptions five_card_observed.
Print Assumptions pgl27_exec_reconP.
Print Assumptions five_card_oe_static_recon.
Print Assumptions pgl27_observed_recovers.
Print Assumptions five_card_observed_recovers.
Print Assumptions pgl27_observed_correct.
Print Assumptions five_card_observed_correct.
