(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* ExecutionPlug: the execution layer over a MonodromyProfile                 *)
(*                                                                            *)
(* An ExecutionPlug over a MonodromyProfile R carries the eight data that     *)
(* turn an algebraic profile into an executable piSMC run: the run argument   *)
(* type, the seat/share and card/share count bridges, the participant list    *)
(* with its enumeration equation, the content readout, the input processes    *)
(* and the interpreter fuel. The profile itself is unchanged: an execution    *)
(* plug is a second value over an existing profile.                           *)
(*                                                                            *)
(* Section execution_of_profile derives from a plug the dealer, the session-  *)
(* typed process list, the interpreter run, the verifier endpoints, the       *)
(* per-seat and per-input-party traces, the coalition readings and the        *)
(* endpoint decoder. Its inner section run_of_static_observation derives,     *)
(* from a termination equation, an endpoint equation and a static recovery    *)
(* equation, that the run reaches Finish at every process, collects one       *)
(* endpoint per seat and decodes to the expected value.                       *)
(*                                                                            *)
(* The two input modes of the framework are the two smart constructors:       *)
(* dealer_secret_plug, whose runs have no committing parties, and             *)
(* committed_input_plug, whose runs carry one commit process per committing   *)
(* party.                                                                     *)
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

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The execution plug                                                     *)
(******************************************************************************)

(** ExecutionPlug — the execution layer over a MonodromyProfile.
    Kind: interface.
    A value of this type carries the run argument type ep_inputT, the seat/share
    bridge ep_players_bridge, the card/share bridge ep_cards_bridge, the
    participant list ep_players with its enumeration equation ep_playersE, the
    content readout ep_content, the input processes ep_input_procs and the
    interpreter fuel ep_fuel. *)
Record ExecutionPlug (R : realType) (mp : MonodromyProfile R) :=
  MkExecutionPlug {
    ep_inputT         : Type ;
    ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
    ep_cards_bridge   : (pgg_N' (mp_M mp)).+1
                          = (ts_T' (rp_scheme (mp_plug mp))).+1 ;
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
    @intent: the plug whose runs have no committing party, its input process
    list being empty at every run argument, so that the dealt secret is the
    only input of the run. *)
Definition dealer_secret_plug (R : realType) (mp : MonodromyProfile R)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (cards_bridge : (pgg_N' (mp_M mp)).+1
                      = (ts_T' (rp_scheme (mp_plug mp))).+1)
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug R mp inputT players_bridge cards_bridge players playersE
    content (fun _ => [::]) fuel.

(** committed_input_plug — the execution plug of a committed input.
    @intent: the plug whose runs carry the committing parties as an argument,
    one commit process per party, so that the run argument is the committed
    value rather than a dealt secret. *)
Definition committed_input_plug (R : realType) (mp : MonodromyProfile R)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (cards_bridge : (pgg_N' (mp_M mp)).+1
                      = (ts_T' (rp_scheme (mp_plug mp))).+1)
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (input_procs : inputT
                     -> seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug R mp inputT players_bridge cards_bridge players playersE
    content input_procs fuel.

(******************************************************************************)
(*     The run, the traces and the decoder derived from the plug              *)
(******************************************************************************)

Section execution_of_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : ExecutionPlug mp.

(** exec_dealer_id — the dealer's process identifier.
    @intent: the dealer occupies process identifier 0, the first entry of the
    process list. *)
Definition exec_dealer_id : nat := 0.

(** exec_verifier_id — the verifier's process identifier.
    @intent: the verifier occupies process identifier 1, the entry following
    the dealer. *)
Definition exec_verifier_id : nat := 1.

(** exec_seat_id — seat i's process identifier.
    @intent: seat i occupies process identifier 2 + i, the seats filling the
    identifiers 2 .. (pi_T' (mp_PI mp)).+2. *)
Definition exec_seat_id (i : 'I_(pi_T' (mp_PI mp)).+1) : nat := 2 + i.

(** exec_input_id — committing party j's process identifier.
    @intent: committing party j occupies process identifier
    (pi_T' (mp_PI mp)).+3 + j, the identifiers following the dealer, the
    verifier and the seats. *)
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
    @intent: the plain-proc image of exec_saprocs, the argument of the
    interpreter. *)
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

(** exec_content_from_plug — the share readout derived from the card/share
    bridge.
    @intent: tnth (ts_encode (rp_scheme (mp_plug mp)) s) at a card position,
    transported along ep_cards_bridge. *)
Definition exec_content_from_plug (s : mp_secretT mp)
    : seq 'I_(pgg_N' (mp_M mp)).+1
      -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1) :=
  fun _ i => tnth (ts_encode (rp_scheme (mp_plug mp)) s)
               (cast_ord e.(ep_cards_bridge) i).

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
