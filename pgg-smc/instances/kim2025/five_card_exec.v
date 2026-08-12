(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_exec: the ExecutionPlug of the five-card instance                *)
(*                                                                            *)
(* The five-card instance carries an execution plug over its own              *)
(* MonodromyProfile five_card_profile at an arbitrary bias, built by the      *)
(* committed-input constructor: the run argument is the committed pair of     *)
(* bits, both count bridges are erefl at 5 seats, 5 shares and 5 cards, the   *)
(* participant list is den_boer_players, the input processes are the two      *)
(* commit processes of the committing parties and the fuel is 100.            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_exec_plug   == the execution plug over five_card_profile       *)
(*   five_card_content_obs == the static observation: the den Boer layout of  *)
(*                            the committed pair at the cut image of a        *)
(*                            starting position                               *)
(*   five_card_exec_player_raw_trace == seat i's raw executed trace           *)
(*   five_card_exec_input_raw_trace  == committing party j's raw executed     *)
(*                                      trace                                 *)
(*   five_card_exec_trace  == seat i's executed trace as a random variable on *)
(*                            the leakage space                               *)
(*   five_card_sample      == the den Boer sample adapter: the leakage space  *)
(*                            Omega under P, the cut being the sampled        *)
(*                            rotation                                        *)
(*   five_card_exec_input_trace == committing party j's executed-row content  *)
(*                                 as a random variable on the leakage space  *)
(*   five_card_exec_dealer_raw_trace == the dealer's raw executed trace       *)
(*   five_card_exec_dealer_readout   == the committed pair decoded from a     *)
(*                                      dealer row                            *)
(*   five_card_exec_dealer_trace     == the dealer's executed row decoded as  *)
(*                                      a random variable on the leakage      *)
(*                                      space                                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_exec_recovers    == the derived run decodes to the conjunction *)
(*                                 of the two committed bits                  *)
(*   five_card_exec_correct     == termination, endpoint count and recovery   *)
(*                                 of the derived run                         *)
(*   five_card_exec_procs_biasE == the derived process list is the same at    *)
(*                                 two biases                                 *)
(*   five_card_exec_seat_endpointE == seat i's endpoint is the layout entry   *)
(*                                    at the cut image of seat i's start      *)
(*   five_card_exec_coalition_endpointsE     == a coalition's endpoint        *)
(*                                              readings are the layout       *)
(*                                              entries at the cut images of  *)
(*                                              its seats                     *)
(*   five_card_exec_coalition_endpoints_seqE == the same reading in seat      *)
(*                                              order                         *)
(*   five_card_exec_seat_countE == the profile's seat index type is 'I_5      *)
(*   five_card_exec_input_positions == the committing parties are read at     *)
(*                                     process identifiers 7 and 8            *)
(*   five_card_exec_raw_traceE == the derived raw trace is the trace of       *)
(*                                den_boer_procs at the seat's process        *)
(*                                identifier                                  *)
(*   five_card_exec_traceE == the execution layer's trace variable is         *)
(*                            denboer_player_trace                            *)
(*   five_card_sample_seat_distE == the executed seat law at the den Boer     *)
(*                                  space is the law of the layout entry at   *)
(*                                  the rotation image of the seat's start    *)
(*   five_card_sample_coalition_distE == the same for a coalition's readings  *)
(*   five_card_exec_trace_secrecy == one seat's executed trace leaves the     *)
(*                                   secret's conditional entropy equal to    *)
(*                                   its plain entropy                        *)
(*   five_card_sample_cut_distE == the sample space's cut distribution is the *)
(*                                 image of the uniform rotation distribution *)
(*                                 under k |-> fc_sigma ^+ k                  *)
(*   five_card_exec_input_trace_secrecy == conditioning the secret on a       *)
(*                                         committing party's executed-row    *)
(*                                         observable leaves its entropy      *)
(*                                         unchanged                          *)
(*   five_card_exec_dealer_pair_centropy0  == the dealer's decoded row        *)
(*                                            determines the committed pair   *)
(*   five_card_exec_dealer_trace_centropy0 == the dealer's decoded row        *)
(*                                            determines the secret           *)
(*   den_boer_sample_cut_witnessE == the sample space's cut distribution is   *)
(*                                   the den Boer member's witness            *)
(*                                   distribution                             *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section five_card_execution.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** five_card_players_enumE — the five-element participant list is the seat
    enumeration.
    @composes: five_card_exec_endpoints *)
Lemma five_card_players_enumE :
  den_boer_players = enum 'I_(pi_T' (mp_PI mpF)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** five_card_exec_plug — the five-card execution plug at bias eps.
    @intent: the execution layer over five_card_profile with run argument the
    committed pair (a, b) of bits, both count bridges erefl at 5 seats, 5
    shares and 5 cards, participant list den_boer_players, content the den Boer
    layout of the decoded committed cards and fuel 100; the committed-input
    constructor takes the two commit processes of the committing parties 7 and
    8 as its input-process list. *)
Definition five_card_exec_plug : ExecutionPlug mpF :=
  @committed_input_plug R mpF (bool * bool)%type erefl erefl den_boer_players
    five_card_players_enumE
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(** five_card_content_obs — the five-card static observation.
    @intent: the den Boer layout of the committed pair ab at the cut image of a
    starting position, namely tnth (den_boer_layout ab) (pgg_rho w0 p) at a cut
    w0 and a position p. *)
Definition five_card_content_obs (ab : bool * bool)
    (p : pgg_gT FiveCardKim_M * 'I_(pgg_N' FiveCardKim_M).+1)
    : 'I_(pgg_N' FiveCardKim_M).+1 :=
  tnth (den_boer_layout ab) (@pgg_rho FiveCardKim_M p.1 p.2).

(** five_card_exec_playersE — the plug's participant list is the instance's
    list.
    @composes: five_card_exec_endpoints *)
Lemma five_card_exec_playersE :
  ep_players five_card_exec_plug = den_boer_players.
Proof. by []. Qed.

(** five_card_exec_fuelE — the plug's fuel is the instance's fuel.
    @composes: five_card_exec_terminates, five_card_exec_endpoints,
    five_card_exec_recon *)
Lemma five_card_exec_fuelE : ep_fuel five_card_exec_plug = 100.
Proof. by []. Qed.

(** five_card_exec_input_idsE — the derived input identifiers are those of the
    two committing parties.
    @composes: five_card_exec_procsE
    The derived identifiers exec_input_id j = (pi_T' (mp_PI mpF)).+3 + j are the
    identifiers 7 and 8 of the instance's own commit processes, which is the
    definitional agreement five_card_exec_procsE rests on. *)
Lemma five_card_exec_input_idsE (ab : bool * bool) :
  @exec_input_ids R mpF five_card_exec_plug ab = [:: 7; 8].
Proof. by []. Qed.

(** five_card_exec_procsE — the derived process list is the instance's process
    list.
    @composes: five_card_exec_terminates, five_card_exec_endpoints,
    five_card_exec_recon *)
Lemma five_card_exec_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  @exec_procs R mpF five_card_exec_plug (a, b) w0 P_idx
  = den_boer_procs a b w0 P_idx.
Proof. by []. Qed.

(** five_card_exec_procs_size — the derived run has nine processes.
    @composes: five_card_exec_terminates
    Naming: intentional; _size is the repo's suffix for a size _ = _ statement,
    as in exec_endpoints_size and pgl27_exec_procs_size. *)
Lemma five_card_exec_procs_size (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  size (@exec_procs R mpF five_card_exec_plug (a, b) w0 P_idx) = 9.
Proof. by []. Qed.

(** five_card_exec_terminates — every process of the derived run reaches
    Finish.
    @composes: five_card_exec_correct *)
Lemma five_card_exec_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  (@exec_run R mpF five_card_exec_plug (a, b) w0 P_idx).1
  = nseq (size (@exec_procs R mpF five_card_exec_plug (a, b) w0 P_idx)) Finish.
Proof.
rewrite five_card_exec_procs_size /exec_run five_card_exec_fuelE
        five_card_exec_procsE.
exact: den_boer_run_terminates.
Qed.

(** five_card_exec_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @composes: five_card_exec_recon, five_card_exec_recovers,
    five_card_exec_correct *)
Lemma five_card_exec_endpoints (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @exec_endpoints R mpF five_card_exec_plug (a, b) w0 0
  = @exec_static_endpoints R mpF five_card_exec_plug five_card_content_obs
      (a, b) w0.
Proof.
rewrite /exec_endpoints /exec_run five_card_exec_fuelE five_card_exec_procsE.
rewrite /exec_verifier_id.
rewrite /exec_static_endpoints five_card_exec_playersE five_card_players_enumE.
exact: den_boer_endpoints.
Qed.

(** five_card_exec_decodeE — the plug's decoder is the instance's
    reconstruction.
    @composes: five_card_exec_decode_seqE *)
Lemma five_card_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  @exec_decode R mpF five_card_exec_plug ep Hsz
  = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** five_card_exec_decode_seqE — the plug's decoder reads the endpoint list as
    the three-consecutive-cards predicate of the decoded endpoints.
    @composes: five_card_exec_recon *)
Lemma five_card_exec_decode_seqE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1) :
  @exec_decode R mpF five_card_exec_plug ep Hsz
  = fc_three_consec [seq decode_bool x | x <- ep].
Proof.
rewrite (five_card_exec_decodeE Hsz Hsz).
by rewrite /ts_recon /fcI_scheme /fcI_recon val_tcast.
Qed.

(** five_card_exec_recon — decoding the static observation returns the
    conjunction of the two committed bits, for any cut in the group and any
    proof of the endpoint count.
    @composes: five_card_exec_recovers, five_card_exec_correct *)
Lemma five_card_exec_recon (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@exec_static_endpoints R mpF five_card_exec_plug
                       five_card_content_obs (a, b) w0)
               = (pi_T' (mp_PI mpF)).+1,
  @exec_decode R mpF five_card_exec_plug
    (@exec_static_endpoints R mpF five_card_exec_plug five_card_content_obs
       (a, b) w0) Hsz
  = (a, b).1 && (a, b).2.
Proof.
move=> Hw0 Hsz; rewrite five_card_exec_decode_seqE -five_card_exec_endpoints.
rewrite /exec_endpoints /exec_run five_card_exec_fuelE five_card_exec_procsE.
exact: (den_boer_run_recovers a b w0 Hw0).
Qed.

(** five_card_exec_recovers — the derived five-card run decodes to the
    conjunction of the two committed bits.
    @main correctness: exec_decode of the executed endpoints of the run of
    five_card_exec_plug at the committed pair (a, b) and cut w0 is a && b, for
    any cut w0 in the group and at every bias eps. *)
Theorem five_card_exec_recovers (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  @exec_decode R mpF five_card_exec_plug
    (@exec_endpoints R mpF five_card_exec_plug (a, b) w0 0)
    (exec_endpoints_size (five_card_exec_endpoints a b w0)) = a && b.
Proof.
exact: (@exec_run_recovers R mpF five_card_exec_plug five_card_content_obs
          (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_endpoints a b w0) (five_card_exec_recon Hw0)).
Qed.

(** five_card_exec_correct — termination, endpoint count and recovery of the
    derived five-card run.
    @main correctness: the run of five_card_exec_plug reaches Finish at each of
    its nine processes, collects one endpoint per seat, and decodes to the
    conjunction a && b of the two committed bits, for any cut w0 in the group
    and at every bias eps. *)
Theorem five_card_exec_correct (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  [/\ (@exec_run R mpF five_card_exec_plug (a, b) w0 0).1
        = nseq (size (@exec_procs R mpF five_card_exec_plug (a, b) w0 0))
            Finish,
      size (@exec_endpoints R mpF five_card_exec_plug (a, b) w0 0)
        = (pi_T' (mp_PI mpF)).+1 &
      @exec_decode R mpF five_card_exec_plug
        (@exec_endpoints R mpF five_card_exec_plug (a, b) w0 0)
        (exec_endpoints_size (five_card_exec_endpoints a b w0)) = a && b].
Proof.
exact: (@exec_run_correct R mpF five_card_exec_plug five_card_content_obs
          (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_terminates a b w0 0)
          (five_card_exec_endpoints a b w0) (five_card_exec_recon Hw0)).
Qed.

(******************************************************************************)
(*     The endpoint and trace read-off at five_card_profile                   *)
(******************************************************************************)

(** five_card_exec_seat_endpointE — seat i's endpoint is the layout entry at
    the cut image of seat i's start.
    @main correctness: exec_seat_endpoint five_card_exec_plug (a, b) w0 0 i =
    five_card_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i). *)
Lemma five_card_exec_seat_endpointE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @exec_seat_endpoint R mpF five_card_exec_plug (a, b) w0 0 i
  = five_card_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i).
Proof. exact: (exec_seat_endpointE (five_card_exec_endpoints a b w0) i). Qed.

(** five_card_exec_coalition_endpointsE — a coalition's endpoint readings are
    the layout entries at the cut images of its seats.
    @main correctness: the finfun sends a seat in C to the layout entry of the
    committed pair at the cut image of that seat's start, and every seat
    outside C to ord0. *)
Lemma five_card_exec_coalition_endpointsE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  @exec_coalition_endpoints R mpF five_card_exec_plug (a, b) w0 0 C
  = [ffun i => if i \in C
               then five_card_content_obs (a, b)
                      (w0, tnth (pi_starts (mp_PI mpF)) i)
               else ord0].
Proof.
exact: (exec_coalition_endpointsE (five_card_exec_endpoints a b w0) C).
Qed.

(** five_card_exec_coalition_endpoints_seqE — the coalition's endpoints in
    seat order are the layout entries at the cut images of its seats.
    @main correctness: mapping the endpoint reading over enum C gives the same
    list as mapping the layout entry at the cut image of the start over
    enum C. *)
Lemma five_card_exec_coalition_endpoints_seqE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  [seq @exec_seat_endpoint R mpF five_card_exec_plug (a, b) w0 0 i
   | i <- enum C]
  = [seq five_card_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i)
     | i <- enum C].
Proof.
exact: (exec_coalition_endpoints_seqE (five_card_exec_endpoints a b w0) C).
Qed.

(** five_card_exec_player_raw_trace — seat i's raw executed trace.
    @intent: the generic participant extractor exec_participant_trace at
    five_card_exec_plug, committed pair ab, cut w0 and process offset 0.
    Naming: intentional; _player_raw_trace names the seat-indexed executed
    trace, matching denboer_player_trace, with which it agrees. *)
Definition five_card_exec_player_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @exec_participant_trace R mpF five_card_exec_plug ab w0 0 i.

(** five_card_exec_coalition_raw_trace — a coalition's raw executed traces.
    @intent: the generic coalition assembly exec_coalition_trace at
    five_card_exec_plug, committed pair ab, cut w0 and process offset 0.
    Naming: intentional; _coalition_raw_trace names the set-indexed executed
    trace family, the coalition twin of five_card_exec_player_raw_trace. *)
Definition five_card_exec_coalition_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @exec_coalition_trace R mpF five_card_exec_plug ab w0 0 C.

(** five_card_exec_input_raw_trace — committing party j's raw executed trace.
    @intent: the generic input extractor exec_input_trace at
    five_card_exec_plug, reading process identifier (pi_T' (mp_PI mpF)).+3 + j
    of the run.
    Naming: intentional; _input_raw_trace names the party-indexed executed
    trace, the committing-party twin of five_card_exec_player_raw_trace. *)
Definition five_card_exec_input_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (j : nat) :=
  @exec_input_trace R mpF five_card_exec_plug ab w0 0 j.

(** five_card_exec_seat_countE — the profile's seat index type is 'I_5.
    @main architecture: (pi_T' (mp_PI mpF)).+1 = 5, the seat index type shared
    by the execution layer and the five-card coalition view. *)
Lemma five_card_exec_seat_countE : (pi_T' (mp_PI mpF)).+1 = 5.
Proof. by []. Qed.

(** five_card_exec_input_positions — the two committing parties are read at
    process identifiers 7 and 8.
    @main architecture: [seq (pi_T' (mp_PI mpF)).+3 + j | j <- iota 0 2] =
    [:: 7; 8], the identifiers of five_card_exec_input_idsE.
    Naming: intentional; _positions distinguishes the unfolded identifier
    arithmetic from the packaged exec_input_ids form of
    five_card_exec_input_idsE. *)
Lemma five_card_exec_input_positions :
  [seq ((pi_T' (mp_PI mpF)).+3 + j)%N | j <- iota 0 2] = [:: 7; 8].
Proof. by []. Qed.

(** five_card_exec_raw_traceE — the derived raw trace is the trace of
    den_boer_procs at the seat's process identifier.
    @main architecture: five_card_exec_player_raw_trace (a, b) w0 i = nth [::]
    (run_interp 100 (den_boer_procs a b w0 0)).2 (2 + i). *)
Lemma five_card_exec_raw_traceE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_exec_player_raw_trace (a, b) w0 i
  = nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 (2 + i).
Proof.
by rewrite /five_card_exec_player_raw_trace /exec_participant_trace
   /exec_seat_id /exec_run five_card_exec_fuelE five_card_exec_procsE.
Qed.

(******************************************************************************)
(*     The den Boer sample space of the five-card instance                    *)
(******************************************************************************)

(** five_card_sample_arg — the committed pair of a den Boer sample point.
    @intent: the first component of a point of bool * bool * 'I_5. *)
Definition five_card_sample_arg (u : five_card_leakage.Omega)
    : (bool * bool)%type := u.1.

(** five_card_sample_cut — the cut of a den Boer sample point.
    @intent: the rotation fc_sigma ^+ k realizing the sampled rotation k, the
    second component of a point of bool * bool * 'I_5. *)
Definition five_card_sample_cut (u : five_card_leakage.Omega)
    : pgg_gT (mp_M mpF) := (five_card_group.fc_sigma ^+ u.2)%g.

(** five_card_sample — the five-card sample adapter at bias eps.
    @intent: the sample layer over five_card_exec_plug whose sample space is
    the den Boer leakage space Omega under its uniform law P, the run argument
    being the committed pair and the cut the realized rotation. *)
Definition five_card_sample : SampleAdapter five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug five_card_leakage.Omega (P R)
    five_card_sample_arg five_card_sample_cut.

(** five_card_sample_run — layer 1 at the den Boer space: the run at a sample
    point.
    @intent: sa_run at five_card_sample and process offset 0, the run at the
    sampled committed pair and the sampled rotation. *)
Definition five_card_sample_run (u : five_card_leakage.Omega) :=
  @sa_run R mpF five_card_exec_plug five_card_sample 0 u.

(** five_card_sample_seat_view — layer 2 at the den Boer space: seat i's
    endpoint.
    @intent: sa_seat_view at five_card_sample, seat i's endpoint reader as a
    random variable on P.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_sample_seat_view (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @sa_seat_view R mpF five_card_exec_plug five_card_sample 0 i.

(** five_card_sample_coalition_view — layer 2 at the den Boer space: a
    coalition's readings.
    @intent: sa_coalition_view at five_card_sample, the coalition endpoint
    reader as a random variable on P.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_sample_coalition_view
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @sa_coalition_view R mpF five_card_exec_plug five_card_sample 0 C.

(** five_card_sample_seat_dist — layer 3 at the den Boer space: the law of
    seat i's endpoint.
    @intent: the pushforward of P along five_card_sample_seat_view i.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_sample_seat_dist (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @sa_seat_dist R mpF five_card_exec_plug five_card_sample 0 i.

(** five_card_sample_coalition_dist — layer 3 at the den Boer space, coalition
    form.
    @intent: the pushforward of P along five_card_sample_coalition_view C.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_sample_coalition_dist
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @sa_coalition_dist R mpF five_card_exec_plug five_card_sample 0 C.

(** five_card_sample_cut_dist — the den Boer sample space's cut law.
    @intent: the pushforward of P along the rotation map five_card_sample_cut.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_sample_cut_dist :=
  @sa_cut_dist R mpF five_card_exec_plug five_card_sample.

(** five_card_witness_cut_dist — the security witness's distribution read as a
    cut law.
    @intent: at the Gen_PGGTypes carrier of the instance the permutation group
    {perm 'I_5} and the group pgg_gT FiveCardKim_M coincide, so sw_rho_dist
    (mp_security mpF) is a law on the carrier the cut is drawn from.
    Naming: intentional; five_card is the two-word instance prefix shared by
    five_card_exec_plug and five_card_content_obs. *)
Definition five_card_witness_cut_dist : R.-fdist (pgg_gT (mp_M mpF)) :=
  sw_rho_dist (mp_security mpF).

(** five_card_sample_seat_distE — the executed seat law at the den Boer space
    is the law of the layout entry at the rotation image of the seat's start.
    @main architecture: five_card_sample_seat_dist i = fdistmap
    (sa_static_seat_view five_card_sample five_card_content_obs i) (P R). *)
Lemma five_card_sample_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_sample_seat_dist i
  = fdistmap (@sa_static_seat_view R mpF five_card_exec_plug five_card_sample
                five_card_content_obs i) (P R).
Proof.
by apply: sa_seat_distE => -[[a b] k]; exact: five_card_exec_endpoints.
Qed.

(** five_card_sample_coalition_distE — the executed coalition law at the den
    Boer space is the law of the layout entries at the rotation images of the
    coalition's starts.
    @main architecture: five_card_sample_coalition_dist C = fdistmap
    (sa_static_coalition_view five_card_sample five_card_content_obs C)
    (P R). *)
Lemma five_card_sample_coalition_distE (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  five_card_sample_coalition_dist C
  = fdistmap (@sa_static_coalition_view R mpF five_card_exec_plug
                five_card_sample five_card_content_obs C) (P R).
Proof.
by apply: sa_coalition_distE => -[[a b] k]; exact: five_card_exec_endpoints.
Qed.

(******************************************************************************)
(*     Single-player executed-trace secrecy through the generic extractor     *)
(******************************************************************************)

Let dbP := P R.

(** five_card_exec_trace — seat i's executed trace as a random variable on the
    leakage space.
    @intent: content_of of five_card_exec_player_raw_trace at the committed
    pair (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2 realizing rotation w.2.
    Naming: intentional; _exec_trace names the executed-trace random variable
    of the execution layer, the plug-side twin of denboer_player_trace. *)
Definition five_card_exec_trace (i : 'I_(pi_T' (mp_PI mpF)).+1)
    : {RV dbP -> 'I_5} :=
  fun w => content_of (five_card_exec_player_raw_trace (w.1.1, w.1.2)
                         (five_card_group.fc_sigma ^+ w.2)%g i).

(** five_card_exec_traceE — the execution layer's trace variable is the den
    Boer trace variable of denboer_trace.v.
    @composes: five_card_exec_trace_secrecy *)
Lemma five_card_exec_traceE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_exec_trace i = denboer_player_trace R i.
Proof.
apply: funext => -[[a b] k].
rewrite /five_card_exec_trace /denboer_player_trace /denboer_rprocs.
by rewrite five_card_exec_raw_traceE.
Qed.

(** five_card_exec_trace_secrecy — one seat's executed trace, read through the
    generic extractor, leaves the secret's conditional entropy equal to its
    plain entropy.
    @main security: conditioning the secret on seat 0's executed trace does not
    lower its entropy, at every bias eps.
    Naming: intentional; _trace_secrecy names the conditional-entropy statement
    about the executed trace, matching denboer_trace_secrecy, which it
    transports. *)
Corollary five_card_exec_trace_secrecy :
  `H( Secret R | five_card_exec_trace ord0 ) = `H `p_ (Secret R).
Proof. by rewrite five_card_exec_traceE; exact: denboer_trace_secrecy. Qed.

(******************************************************************************)
(*     The cut distribution of the den Boer sample space                      *)
(******************************************************************************)

(** five_card_card_bool2 — the pair of committed bits has four values.
    @composes: five_card_sample_uniform_prodE
    Naming: intentional; the identical certificate card_bool2 is declared at
    kim_input_privacy.v:51, and the five_card prefix keeps this local copy from
    colliding with it without adding an import edge to that file. *)
Lemma five_card_card_bool2 : #|{: bool * bool}| = 3.+1.
Proof. by rewrite card_prod card_bool. Qed.

(** five_card_sample_uniform_prodE — the den Boer leakage distribution is the
    product of the uniform distribution on the committed pair with the uniform
    distribution on the rotation.
    @composes: five_card_sample_snd_uniformE *)
Lemma five_card_sample_uniform_prodE :
  P R = ((fdist_uniform five_card_card_bool2)
         `x (fdist_uniform (card_ord 5)))%fdist.
Proof.
apply/fdist_ext => -[ab k].
rewrite fdist_prodE /P !fdist_uniformE.
rewrite card_Omega20 five_card_card_bool2 card_ord.
by rewrite -invfM -natrM.
Qed.

(** five_card_sample_snd_uniformE — the rotation marginal of the den Boer
    leakage distribution is uniform on 'I_5.
    @composes: five_card_sample_cut_distE *)
Lemma five_card_sample_snd_uniformE :
  fdistmap (fun u : five_card_leakage.Omega => u.2) (P R)
  = fdist_uniform (card_ord 5).
Proof.
rewrite five_card_sample_uniform_prodE.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** five_card_sample_cut_distE — the den Boer sample space's cut distribution
    is the image of the uniform rotation distribution under the rotation
    realization k |-> fc_sigma ^+ k.
    @main architecture: five_card_sample_cut_dist = fdistmap
    (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)), at every
    bias eps. *)
Lemma five_card_sample_cut_distE :
  five_card_sample_cut_dist
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /five_card_sample_cut_dist /sa_cut_dist /five_card_sample /=.
rewrite /five_card_sample_cut -five_card_sample_snd_uniformE.
by rewrite fdistmap_comp.
Qed.

(******************************************************************************)
(*     The committing parties' executed rows                                  *)
(******************************************************************************)

(** five_card_exec_traces_size — the den Boer run has nine trace rows.
    @composes: five_card_exec_input_raw_traceE
    Naming: intentional; _size is the repo's suffix for a size _ = _ statement,
    as in five_card_exec_procs_size and exec_endpoints_size. *)
Lemma five_card_exec_traces_size (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  size (run_interp 100 (den_boer_procs a b w0 0)).2 = 9.
Proof. rewrite /den_boer_procs; vm_compute; reflexivity. Qed.

(** five_card_exec_input_raw_traceE — committing party j's executed row is
    empty, at every j.
    @composes: five_card_exec_input_trace_secrecy
    Rows 0 and 1, the rows of the two committing parties, are empty because a
    Send logs nothing to the sender's own row in this interpreter and the
    committing parties are pure senders. Rows j >= 2 are empty by the nth
    default past the nine-process run. *)
Lemma five_card_exec_input_raw_traceE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (j : nat) :
  five_card_exec_input_raw_trace (a, b) w0 j = [::].
Proof.
rewrite /five_card_exec_input_raw_trace /exec_input_trace /exec_input_id
        /exec_run five_card_exec_fuelE five_card_exec_procsE.
case: j => [|[|j]].
- by rewrite /den_boer_procs; vm_compute.
- by rewrite /den_boer_procs; vm_compute.
- by apply: nth_default; rewrite five_card_exec_traces_size.
Qed.

(** five_card_exec_input_trace — committing party j's executed-row content
    as a random variable on the leakage space.
    @intent: content_of of five_card_exec_input_raw_trace at the committed pair
    (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2 realizing rotation w.2.
    Naming: intentional; _input_trace names the party-indexed executed-trace
    random variable, the committing-party twin of five_card_exec_trace. *)
Definition five_card_exec_input_trace (j : nat) : {RV dbP -> 'I_5} :=
  fun w => content_of (five_card_exec_input_raw_trace (w.1.1, w.1.2)
                         (five_card_group.fc_sigma ^+ w.2)%g j).

(** five_card_exec_input_trace_secrecy — conditioning the secret on committing
    party j's executed-row observable leaves its entropy unchanged, at every j.
    @main architecture: `H( Secret | five_card_exec_input_trace j ) =
    `H `p_ Secret, at every bias eps.
    The rows are empty because in this interpreter model a Send logs nothing to
    the sender's own trace, so the identity is a constant-conditioning
    statement, not a commitment-privacy result. A committing party knows its
    own bit, so even a non-empty row would not make this a privacy statement
    about that party. The committed payloads travel to the dealer's row, which
    five_card_exec_dealer_pair_centropy0 and
    five_card_exec_dealer_trace_centropy0 show determines both bits.
    Naming: intentional; _trace_secrecy names the conditional-entropy statement
    about an executed trace, matching five_card_exec_trace_secrecy. *)
Lemma five_card_exec_input_trace_secrecy (j : nat) :
  `H( Secret R | five_card_exec_input_trace j ) = `H `p_ (Secret R).
Proof.
have Hc : five_card_exec_input_trace j
        = (fun _ : unit => ord0) `o (unit_RV dbP).
  apply: funext => w.
  rewrite /five_card_exec_input_trace /comp_RV.
  by rewrite five_card_exec_input_raw_traceE.
rewrite Hc; apply: extra_entropy.inde_cond_entropy.
apply: pgg_trace_secrecy.inde_RV_comp; exact: spp_proba.inde_unit_RV.
Qed.

(******************************************************************************)
(*     The dealer's executed row                                              *)
(******************************************************************************)

(** five_card_exec_dealer_raw_trace — the dealer's raw executed trace.
    @intent: the generic dealer extractor exec_dealer_trace at
    five_card_exec_plug, committed pair ab, cut w0 and process offset 0.
    Naming: intentional; _dealer_raw_trace names the dealer's executed trace,
    the dealer twin of five_card_exec_input_raw_trace. *)
Definition five_card_exec_dealer_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) :=
  @exec_dealer_trace R mpF five_card_exec_plug ab w0 0.

(** five_card_exec_dealer_raw_traceE — the dealer's executed row is the deck
    index followed by the two committed sheets.
    @composes: five_card_exec_dealer_traceE
    The row is anti-chronological: the head PGG_idx 0 is the dealer's own Init
    of the deck index, which happens last, then party 8's sheet
    PGG_sheet (encode_bool b), then party 7's PGG_sheet (encode_bool a). *)
Lemma five_card_exec_dealer_raw_traceE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) :
  five_card_exec_dealer_raw_trace (a, b) w0
  = [:: PGG_idx 0; PGG_sheet (encode_bool b); PGG_sheet (encode_bool a)].
Proof.
rewrite /five_card_exec_dealer_raw_trace /exec_dealer_trace /exec_dealer_id
        /exec_run five_card_exec_fuelE five_card_exec_procsE.
rewrite /den_boer_procs; vm_compute; reflexivity.
Qed.

(** five_card_exec_dealer_readout — the committed pair decoded from a dealer
    row.
    @intent: decode_bool of the two sheets of a three-entry row, the second bit
    at the head, and (false, false) elsewhere.
    The (false, false) value returned on a malformed row coincides with a
    legitimate committed pair, so the readout is meaningful only through
    five_card_exec_dealer_raw_traceE.
    Naming: intentional; _dealer_readout names the decoding function of the
    dealer row, the row-level companion of five_card_exec_dealer_trace. *)
Definition five_card_exec_dealer_readout
    (tr : seq (pgg_data (pgg_N' FiveCardKim_M).+1)) : (bool * bool)%type :=
  if tr is [:: _ ; PGG_sheet y ; PGG_sheet x]
  then (decode_bool x, decode_bool y) else (false, false).

(** five_card_exec_dealer_trace — the dealer's executed row decoded as a
    random variable on the leakage space.
    @intent: five_card_exec_dealer_readout of five_card_exec_dealer_raw_trace
    at the committed pair (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2 realizing
    rotation w.2.
    Naming: intentional; _dealer_trace names the dealer's executed-trace random
    variable, the dealer twin of five_card_exec_trace. *)
Definition five_card_exec_dealer_trace : {RV dbP -> (bool * bool)%type} :=
  fun w => five_card_exec_dealer_readout
             (five_card_exec_dealer_raw_trace (w.1.1, w.1.2)
                (five_card_group.fc_sigma ^+ w.2)%g).

(** five_card_exec_dealer_traceE — the dealer's decoded row is the sampled
    committed pair.
    @composes: five_card_exec_dealer_pair_centropy0 *)
Lemma five_card_exec_dealer_traceE :
  five_card_exec_dealer_trace = fun w => (w.1.1, w.1.2).
Proof.
apply: funext => w.
rewrite /five_card_exec_dealer_trace five_card_exec_dealer_raw_traceE.
by rewrite /five_card_exec_dealer_readout /= !decode_encode_bool.
Qed.

(** five_card_exec_dealer_pair_centropy0 — the dealer's decoded row determines
    the committed pair.
    @main security: `H( (fun w => w.1) | five_card_exec_dealer_trace ) = 0,
    where fun w => w.1 reads the committed pair off a sample point, at every
    bias eps.
    Naming: intentional; _centropy0 names a conditional-entropy-zero
    determination statement, _pair_ marking the committed-pair reader. *)
Lemma five_card_exec_dealer_pair_centropy0 :
  `H( (fun w : five_card_leakage.Omega => w.1)
      | five_card_exec_dealer_trace ) = 0.
Proof.
have -> : (fun w : five_card_leakage.Omega => w.1)
        = idfun `o five_card_exec_dealer_trace.
  apply: funext => w; rewrite /comp_RV five_card_exec_dealer_traceE /=.
  by case: w => -[a b] k.
exact: centropy_RV_comp0.
Qed.

(** five_card_exec_dealer_trace_centropy0 — the dealer's decoded row
    determines the secret.
    @main security: `H( Secret | five_card_exec_dealer_trace ) = 0, at every
    bias eps.
    Naming: intentional; _trace_centropy0 names the conditional-entropy-zero
    determination statement carried by an executed trace. *)
Lemma five_card_exec_dealer_trace_centropy0 :
  `H( Secret R | five_card_exec_dealer_trace ) = 0.
Proof.
have -> : Secret R
        = (fun p : bool * bool => p.1 && p.2) `o five_card_exec_dealer_trace.
  apply: funext => w; rewrite /comp_RV five_card_exec_dealer_traceE /=.
  by case: w => -[a b] k.
exact: centropy_RV_comp0.
Qed.

End five_card_execution.

(** five_card_exec_procs_biasE — the executed program does not depend on the
    bias.
    @main architecture: the process lists of the plugs at two biases eps1 and
    eps2, with their own Kim constraint packs and word lengths, are equal, so
    the security witness of five_card_profile enters no process term. *)
Lemma five_card_exec_procs_biasE (R : realType) (eps1 eps2 : R)
    (Hlt1 : eps1 < 5%:R^-1) (Hgt1 : - (4%:R * 5%:R^-1) < eps1)
    (Hspec1 : `|eps1| < 4%:R / 5%:R)
    (Hlt2 : eps2 < 5%:R^-1) (Hgt2 : - (4%:R * 5%:R^-1) < eps2)
    (Hspec2 : `|eps2| < 4%:R / 5%:R)
    (L1 L2 : nat) (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @exec_procs R (@five_card_profile R eps1 Hlt1 Hgt1 Hspec1 L1)
                (@five_card_exec_plug R eps1 Hlt1 Hgt1 Hspec1 L1)
                (a, b) w0 P_idx
  = @exec_procs R (@five_card_profile R eps2 Hlt2 Hgt2 Hspec2 L2)
                  (@five_card_exec_plug R eps2 Hlt2 Hgt2 Hspec2 L2)
                  (a, b) w0 P_idx.
Proof. by []. Qed.

(******************************************************************************)
(*     The den Boer member's witness distribution                             *)
(******************************************************************************)

Section five_card_one_letter_words.
Local Open Scope vec_ext_scope.

Variable R : realType.
Variables (N'' m : nat).
Variable sigmas : m.+1.-tuple {perm 'I_N''.+2}.
Variable W : R.-fdist 'I_m.+1.

(** fdistmap_head1 — the head letter of a one-letter word is distributed as
    the letter itself.
    @composes: rho_from_words_weighted1 *)
Lemma fdistmap_head1 :
  fdistmap (fun v : 'rV['I_m.+1]_1 => v ``_ ord0) (W `^ 1) = W.
Proof.
apply/fdist_ext => k; rewrite fdistmapE.
rewrite (big_pred1 (\row_(_ < 1) k)); last first.
  move=> v /=; rewrite !inE.
  apply/idP/idP.
    by move/eqP => H; apply/eqP/rowP => i; rewrite (ord1 i) mxE.
  by move/eqP => ->; rewrite mxE.
by rewrite fdist_rV1 mxE.
Qed.

(** rho_from_words_weighted1 — the word shuffle at word length 1 is the image
    of the letter distribution under the alphabet lookup.
    @composes: den_boer_witness_rotationE *)
Lemma rho_from_words_weighted1 :
  @rho_from_words_weighted R N'' m 1 sigmas W = fdistmap (tnth sigmas) W.
Proof.
rewrite /rho_from_words_weighted /word_weighted fdistmap_comp.
have -> : (@word_eval (Gen_PGGTypes sigmas) 1) \o (@tuple_of_row _ 1)
        = (tnth sigmas) \o (fun v : 'rV['I_m.+1]_1 => v ``_ ord0).
  apply: funext => v; rewrite /= /word_eval big_ord1.
  by congr (tnth sigmas _); rewrite tnth_mktuple.
by rewrite -fdistmap_comp fdistmap_head1.
Qed.

End five_card_one_letter_words.

Section den_boer_witness_distribution.

Variable R : realType.

(** kim_weight_uniform_at0 — the Kim weight distribution at bias 0 is uniform
    on 'I_5.
    @composes: den_boer_witness_rotationE *)
Lemma kim_weight_uniform_at0 :
  kim_weight_dist (den_boer_eps0_lt R) (den_boer_eps0_gt R)
  = fdist_uniform (card_ord 5).
Proof.
apply/fdist_ext => k; rewrite kim_weight_distE fdist_uniformE card_ord.
by case: ifP => _; [rewrite subr0 | rewrite mul0r addr0].
Qed.

(** den_boer_witness_rotationE — the den Boer member's witness distribution is
    the image of the uniform rotation distribution under the rotation
    realization k |-> fc_sigma ^+ k.
    @composes: den_boer_sample_cut_witnessE *)
Lemma den_boer_witness_rotationE :
  sw_rho_dist (mp_security (den_boer_profile R))
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /den_boer_profile /= rho_from_words_weighted1 kim_weight_uniform_at0.
by congr fdistmap; apply: funext => k; exact: fc_kim_sigmasE.
Qed.

End den_boer_witness_distribution.

(** den_boer_sample_cut_witnessE — the five-card sample's cut distribution is
    bias-independent and equals the den Boer member's witness distribution.
    @main architecture: five_card_sample_cut_dist Hlt Hgt Hspec L =
    sw_rho_dist (mp_security (den_boer_profile R)), at every bias eps and every
    word length L. *)
Lemma den_boer_sample_cut_witnessE (R : realType) (eps : R)
    (Hlt : eps < 5%:R^-1) (Hgt : - (4%:R * 5%:R^-1) < eps)
    (Hspec : `|eps| < 4%:R / 5%:R) (L : nat) :
  five_card_sample_cut_dist Hlt Hgt Hspec L
  = sw_rho_dist (mp_security (den_boer_profile R)).
Proof. by rewrite five_card_sample_cut_distE den_boer_witness_rotationE. Qed.
