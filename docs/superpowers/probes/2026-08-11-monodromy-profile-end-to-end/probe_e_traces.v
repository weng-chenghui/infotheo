(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-E: the trace layer over the execution adapter                      *)
(*                                                                            *)
(* The EPP record and the generic section execution_of_profile are those of   *)
(* probe_d_fivecard_exec.v, copied verbatim (the probe directory has no -R    *)
(* mapping), including the corrected .+3 input-identifier offset. Four        *)
(* constructions are added to the generic section: the input-party raw trace  *)
(* epp_input_trace, the coalition raw-trace assembly epp_coalition_trace, the *)
(* per-seat endpoint reader epp_seat_endpoint and its coalition assembly      *)
(* epp_coalition_endpoints. Under one hypothesis Hep, naming the executed     *)
(* endpoint list as the map of a static observation content_obs over the      *)
(* seats, three equations relate them to that observation. Both are then      *)
(* instantiated at pgl27_profile and at five_card_profile, Hep discharged     *)
(* from the landed endpoint lemmas.                                           *)
(*                                                                            *)
(* Findings, not statements (design record for P-F and P-H):                  *)
(*                                                                            *)
(*  1. ONE content_obs SHAPE FITS BOTH CARRIERS VERBATIM. pgl27_endpoints and *)
(*     den_boer_endpoints have the same right-hand side up to the readout,    *)
(*     [seq f (pgg_rho w0 (tnth (pi_starts PI) i)) | i <- players]; taking    *)
(*     content_obs UNCURRIED on the pair (cut, start) makes both landed       *)
(*     lemmas close the instance Hep by exact:, no rewriting, since the pair  *)
(*     projections of an explicit pair reduce. Curried content_obs would fit  *)
(*     equally; the pair form is kept because P-F will read a joint sample    *)
(*     (secret, cut) through the same slot.                                   *)
(*                                                                            *)
(*  2. THE COALITION RAW TRACE MIRRORS THE LANDED VIEW SHAPE. pgl27_trace.v's *)
(*     pgl27_coalition_trace is [ffun i => if i \in C then player_trace i u   *)
(*     else ord0], a total finfun on seats with a default outside C. The      *)
(*     executed counterpart epp_coalition_trace keeps the finfun and replaces *)
(*     the value default ord0 by the raw-trace default [::], the same default *)
(*     the nth of epp_participant_trace already uses. The codomain            *)
(*     seq (pgg_data _) is not a finType, which is exactly the gap P-F must   *)
(*     close: the landed coalition RV lands in a finType because content_of   *)
(*     has already been applied.                                              *)
(*                                                                            *)
(*  3. THE RAW PARTICIPANT TRACE IS THE ARGUMENT OF THE LANDED RV.            *)
(*     pgl_player_raw_traceE and fc_player_raw_traceE show the generic        *)
(*     extractor equal to the nth expression under content_of in              *)
(*     pgl27_player_trace and denboer_player_trace. The instance definitions  *)
(*     are therefore content_of \o (generic extractor), and only the sample   *)
(*     space differs between them.                                            *)
(*                                                                            *)
(*  4. INDEX PINNING. Every transport of a landed run fact stages the fuel    *)
(*     (P-C finding 4) and reaches the process indices only through the       *)
(*     process equality, never by conversion between two nth applications.    *)
(*     probe_e_mutation.v is the same discipline applied to the verifier      *)
(*     index: a dealer-for-verifier substitution is refuted by an erefl on    *)
(*     the index, in milliseconds.                                            *)
(*                                                                            *)
(*  5. INPUT PARTIES HAVE NO LANDED EXTRACTOR. Neither pgl27_trace.v nor      *)
(*     denboer_trace.v projects the committing parties' traces; the seats     *)
(*     are read at 2 + i and the verifier at 1. epp_input_trace reads at      *)
(*     (pi_T' PI).+3 + j, which is 7 + j at the five-card carrier             *)
(*     (fc_input_positions) inside a nine-process run (fc_epp_terminates).    *)
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
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The execution adapter (probe_d_fivecard_exec.v)                        *)
(******************************************************************************)

(** EPP — the execution adapter over a MonodromyProfile.
    Kind: interface.
    A value of this type carries the run argument type ep_inputT, the seat/share
    bridge ep_players_bridge, the card/share bridge ep_cards_bridge, the content
    readout ep_content, the input processes ep_input_procs and the interpreter
    fuel ep_fuel. *)
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

(******************************************************************************)
(*     The run and the traces derived from the adapter                        *)
(******************************************************************************)

Section execution_of_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.

(** epp_players — the participant list of the run.
    @intent: the enumeration of the (pi_T' (mp_PI mp)).+1 seats. *)
Definition epp_players : seq 'I_(pi_T' (mp_PI mp)).+1 :=
  enum 'I_(pi_T' (mp_PI mp)).+1.

(** epp_input_ids — the party identifiers of the input processes.
    @intent: iota (pi_T' (mp_PI mp)).+3 (size (ep_input_procs e x)), the
    identifiers following the dealer, the verifier and the seats. *)
Definition epp_input_ids (x : ep_inputT e) : seq nat :=
  iota (pi_T' (mp_PI mp)).+3 (size (e.(ep_input_procs) x)).

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
    @intent: run_interp at ep_fuel e on epp_procs, a pair of the final process
    states and the per-process traces. *)
Definition epp_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (epp_procs x w0 P_idx).

(** epp_endpoints — the verifier's collected endpoints.
    @intent: endpoints_of_trace of entry 1 of epp_run.2. *)
Definition epp_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  endpoints_of_trace (nth [::] (epp_run x w0 P_idx).2 1).

(** epp_participant_trace — the executed trace of the seat-i player.
    @intent: entry 2 + i of epp_run.2. *)
Definition epp_participant_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  nth [::] (epp_run x w0 P_idx).2 (2 + i).

(** epp_seat_share_count — the seat/share bridge in successor form.
    @composes: epp_decode *)
Lemma epp_seat_share_count :
  (pi_T' (mp_PI mp)).+1 = (ts_T' (rp_scheme (mp_plug mp))).+1.
Proof. by rewrite e.(ep_players_bridge). Qed.

(** epp_decode — the endpoint decoder of the adapter.
    @intent: an endpoint list of one card per seat, transported along the
    seat/share bridge into the argument type of run_recover and reconstructed
    there. *)
Definition epp_decode (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mp)).+1) : mp_secretT mp :=
  run_recover (tcast (etrans Hsz epp_seat_share_count) (in_tuple ep)).

(** epp_content_from_plug — the share readout derived from the card/share
    bridge.
    @intent: tnth (ts_encode (rp_scheme (mp_plug mp)) s) at a card position,
    transported along ep_cards_bridge. *)
Definition epp_content_from_plug (s : mp_secretT mp)
    : seq 'I_(pgg_N' (mp_M mp)).+1
      -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1) :=
  fun _ i => tnth (ts_encode (rp_scheme (mp_plug mp)) s)
               (cast_ord e.(ep_cards_bridge) i).

(* The four constructions of P-E. Process identifier j of the input parties is
   (pi_T' (mp_PI mp)).+3 + j, the offset of epp_input_ids: 0 is the dealer, 1
   the verifier, 2 .. (pi_T' _).+2 the seats. *)

(** epp_input_trace — the executed trace of input party j.
    @intent: entry (pi_T' (mp_PI mp)).+3 + j of epp_run.2. *)
Definition epp_input_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (j : nat) :=
  nth [::] (epp_run x w0 P_idx).2 ((pi_T' (mp_PI mp)).+3 + j).

(** epp_coalition_trace — the coalition's executed raw traces.
    @intent: the finfun sending a seat in C to its executed trace and a seat
    outside C to the empty trace. *)
Definition epp_coalition_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> seq (pgg_data (pgg_N' (mp_M mp)).+1)} :=
  [ffun i => if i \in C then epp_participant_trace x w0 P_idx i else [::]].

(** epp_seat_endpoint — the endpoint recorded for seat i.
    @intent: entry i of epp_endpoints. *)
Definition epp_seat_endpoint (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) : 'I_(pgg_N' (mp_M mp)).+1 :=
  nth ord0 (epp_endpoints x w0 P_idx) i.

(** epp_coalition_endpoints — the coalition's endpoint readings.
    @intent: the finfun sending a seat in C to its endpoint and a seat outside
    C to ord0. *)
Definition epp_coalition_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1} :=
  [ffun i => if i \in C then epp_seat_endpoint x w0 P_idx i else ord0].

(******************************************************************************)
(*     Interpreter output against the static group-action observation         *)
(******************************************************************************)

Section trace_of_static_observation.

Variable content_obs :
  pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1.
Variables (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat).

Hypothesis Hep : epp_endpoints x w0 P_idx
  = [seq content_obs (w0, tnth (pi_starts (mp_PI mp)) i) | i <- epp_players].

(** epp_seat_endpointE — seat i's endpoint is the static observation at seat i.
    @main correctness: epp_seat_endpoint x w0 P_idx i = content_obs (w0, tnth
    (pi_starts (mp_PI mp)) i). *)
Lemma epp_seat_endpointE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  epp_seat_endpoint x w0 P_idx i
  = content_obs (w0, tnth (pi_starts (mp_PI mp)) i).
Proof.
rewrite /epp_seat_endpoint Hep (nth_map i) ?/epp_players ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

(** epp_coalition_endpointsE — the coalition's endpoint readings are the static
    observation restricted to its seats.
    @main correctness: epp_coalition_endpoints x w0 P_idx C = [ffun i => if i
    \in C then content_obs (w0, tnth (pi_starts (mp_PI mp)) i) else ord0]. *)
Lemma epp_coalition_endpointsE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  epp_coalition_endpoints x w0 P_idx C
  = [ffun i => if i \in C
               then content_obs (w0, tnth (pi_starts (mp_PI mp)) i) else ord0].
Proof.
apply/ffunP => i; rewrite /epp_coalition_endpoints !ffunE.
by case: ifP => // _; exact: epp_seat_endpointE.
Qed.

(** epp_coalition_endpoints_seqE — the coalition's endpoint readings in seat
    order are the map of the static observation over its seats.
    @composes: epp_coalition_endpointsE *)
Lemma epp_coalition_endpoints_seqE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  [seq epp_seat_endpoint x w0 P_idx i | i <- enum C]
  = [seq content_obs (w0, tnth (pi_starts (mp_PI mp)) i) | i <- enum C].
Proof. by apply: eq_map => i; exact: epp_seat_endpointE. Qed.

End trace_of_static_observation.

End execution_of_profile.

(******************************************************************************)
(*     The trace layer at pgl27_profile                                       *)
(******************************************************************************)

Section pgl27_trace_readoff.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_epp — the PGL(2,7) execution adapter.
    @intent: run argument bool, both bridges erefl at 8 seats, 8 shares and 8
    cards, content the shares ts_encode orbit_scheme s of the dealt orbit
    secret, no input processes, fuel pgl27_fuel. *)
Definition pgl_epp : EPP mpP :=
  @MkEPP R mpP bool erefl erefl
    (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) pgl27_fuel.

(** pgl_epp_playersE — the derived participant list is the instance's list.
    @composes: pgl_epp_procsE *)
Lemma pgl_epp_playersE : @epp_players R mpP = pgl27_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** pgl_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: pgl_epp_endpoints *)
Lemma pgl_epp_fuelE : @ep_fuel R mpP pgl_epp = pgl27_fuel.
Proof. by []. Qed.

(** pgl_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs pgl_epp s w0 0 = pgl27_procs s w0. *)
Lemma pgl_epp_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_procs R mpP pgl_epp s w0 0 = pgl27_procs s w0.
Proof.
rewrite /epp_procs /pgl27_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /pgl27_saprocs /pgl27_dealer_run.
by rewrite pgl_epp_playersE.
Qed.

(** pgl_content_obs — the PGL(2,7) static observation.
    @intent: the share of s at the cut image of a starting position. *)
Definition pgl_content_obs (s : bool)
    (p : pgg_gT (mp_M mpP) * 'I_(pgg_N' (mp_M mpP)).+1)
    : 'I_(pgg_N' (mp_M mpP)).+1 :=
  tnth (ts_encode orbit_scheme s) (@pgg_rho (mp_M mpP) p.1 p.2).

(** pgl_epp_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @main correctness: epp_endpoints pgl_epp s w0 0 = [seq pgl_content_obs s
    (w0, tnth (pi_starts (mp_PI mpP)) i) | i <- epp_players]. *)
Lemma pgl_epp_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_endpoints R mpP pgl_epp s w0 0
  = [seq pgl_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i)
     | i <- @epp_players R mpP].
Proof.
rewrite /epp_endpoints /epp_run pgl_epp_fuelE pgl_epp_procsE.
exact: pgl27_endpoints.
Qed.

(** pgl_seat_endpointE — seat i's PGL(2,7) endpoint is the share at the cut
    image of seat i's start.
    @main correctness: the per-seat generic equation at pgl27_profile. *)
Lemma pgl_seat_endpointE (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  @epp_seat_endpoint R mpP pgl_epp s w0 0 i
  = pgl_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i).
Proof. exact: (epp_seat_endpointE (pgl_epp_endpoints s w0) i). Qed.

(** pgl_coalition_endpointsE — a PGL(2,7) coalition's endpoint readings are the
    shares at the cut images of its seats.
    @main correctness: the coalition generic equation at pgl27_profile. *)
Lemma pgl_coalition_endpointsE (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  @epp_coalition_endpoints R mpP pgl_epp s w0 0 C
  = [ffun i => if i \in C
               then pgl_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i)
               else ord0].
Proof. exact: (epp_coalition_endpointsE (pgl_epp_endpoints s w0) C). Qed.

(** pgl_coalition_endpoints_seqE — the same reading in seat order.
    @composes: pgl_coalition_endpointsE *)
Lemma pgl_coalition_endpoints_seqE (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  [seq @epp_seat_endpoint R mpP pgl_epp s w0 0 i | i <- enum C]
  = [seq pgl_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i) | i <- enum C].
Proof. exact: (epp_coalition_endpoints_seqE (pgl_epp_endpoints s w0) C). Qed.

(** pgl_player_raw_trace — seat i's raw PGL(2,7) trace.
    @intent: the generic participant extractor at pgl_epp. *)
Definition pgl_player_raw_trace (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @epp_participant_trace R mpP pgl_epp s w0 0 i.

(** pgl_coalition_raw_trace — a PGL(2,7) coalition's raw traces.
    @intent: the generic coalition assembly at pgl_epp. *)
Definition pgl_coalition_raw_trace (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @epp_coalition_trace R mpP pgl_epp s w0 0 C.

(** pgl_seat_countE — the seat index type of the trace layer is the seat index
    type of the landed coalition view.
    @composes: pgl_coalition_raw_trace *)
Lemma pgl_seat_countE : (pi_T' (mp_PI mpP)).+1 = 8.
Proof. by []. Qed.

(** pgl_player_raw_traceE — the generic raw trace is the trace under content_of
    in pgl27_player_trace.
    @main architecture: pgl_player_raw_trace s w0 i = nth [::] (run_interp
    pgl27_fuel (pgl27_procs s w0)).2 (2 + i). *)
Lemma pgl_player_raw_traceE (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pgl_player_raw_trace s w0 i
  = nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 (2 + i).
Proof.
by rewrite /pgl_player_raw_trace /epp_participant_trace /epp_run
   pgl_epp_fuelE pgl_epp_procsE.
Qed.

End pgl27_trace_readoff.

(******************************************************************************)
(*     The trace layer at five_card_profile, arbitrary bias                   *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_trace_readoff.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** fc_epp — the five-card execution adapter at bias eps.
    @intent: run argument the committed pair (a, b) : bool * bool, both bridges
    erefl at 5 seats, 5 shares and 5 cards, content the den Boer layout of the
    decoded committed cards, input processes the two committing parties 7 and 8,
    fuel 100. *)
Definition fc_epp : EPP mpF :=
  @MkEPP R mpF (bool * bool)%type erefl erefl
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(** fc_epp_playersE — the derived participant list is the instance's list.
    @composes: fc_epp_procsE *)
Lemma fc_epp_playersE : @epp_players R mpF = den_boer_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** fc_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: fc_epp_endpoints *)
Lemma fc_epp_fuelE : @ep_fuel R mpF fc_epp = 100.
Proof. by []. Qed.

(** fc_epp_input_idsE — the derived input identifiers are the instance's.
    @composes: fc_input_positions *)
Lemma fc_epp_input_idsE (ab : bool * bool) :
  @epp_input_ids R mpF fc_epp ab = [:: 7; 8].
Proof. by []. Qed.

(** fc_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs fc_epp (a, b) w0 P_idx = den_boer_procs a b w0
    P_idx, at every bias eps. *)
Lemma fc_epp_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @epp_procs R mpF fc_epp (a, b) w0 P_idx = den_boer_procs a b w0 P_idx.
Proof.
rewrite /epp_procs /den_boer_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /den_boer_saprocs /den_boer_dealer_run.
by rewrite fc_epp_playersE.
Qed.

(** fc_content_obs — the five-card static observation.
    @intent: the den Boer layout of the committed pair at the cut image of a
    starting position. *)
Definition fc_content_obs (ab : bool * bool)
    (p : pgg_gT (mp_M mpF) * 'I_(pgg_N' (mp_M mpF)).+1)
    : 'I_(pgg_N' (mp_M mpF)).+1 :=
  tnth (den_boer_layout ab) (@pgg_rho (mp_M mpF) p.1 p.2).

(** fc_epp_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @main correctness: epp_endpoints fc_epp (a, b) w0 0 = [seq fc_content_obs
    (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i) | i <- epp_players]. *)
Lemma fc_epp_endpoints (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @epp_endpoints R mpF fc_epp (a, b) w0 0
  = [seq fc_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i)
     | i <- @epp_players R mpF].
Proof.
rewrite /epp_endpoints /epp_run fc_epp_fuelE fc_epp_procsE.
exact: den_boer_endpoints.
Qed.

(** fc_seat_endpointE — seat i's five-card endpoint is the layout entry at the
    cut image of seat i's start.
    @main correctness: the per-seat generic equation at five_card_profile. *)
Lemma fc_seat_endpointE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @epp_seat_endpoint R mpF fc_epp (a, b) w0 0 i
  = fc_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i).
Proof. exact: (epp_seat_endpointE (fc_epp_endpoints a b w0) i). Qed.

(** fc_coalition_endpointsE — a five-card coalition's endpoint readings are the
    layout entries at the cut images of its seats.
    @main correctness: the coalition generic equation at five_card_profile. *)
Lemma fc_coalition_endpointsE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  @epp_coalition_endpoints R mpF fc_epp (a, b) w0 0 C
  = [ffun i => if i \in C
               then fc_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i)
               else ord0].
Proof. exact: (epp_coalition_endpointsE (fc_epp_endpoints a b w0) C). Qed.

(** fc_coalition_endpoints_seqE — the same reading in seat order.
    @composes: fc_coalition_endpointsE *)
Lemma fc_coalition_endpoints_seqE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  [seq @epp_seat_endpoint R mpF fc_epp (a, b) w0 0 i | i <- enum C]
  = [seq fc_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i)
     | i <- enum C].
Proof. exact: (epp_coalition_endpoints_seqE (fc_epp_endpoints a b w0) C). Qed.

(** fc_player_raw_trace — seat i's raw five-card trace.
    @intent: the generic participant extractor at fc_epp. *)
Definition fc_player_raw_trace (ab : bool * bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @epp_participant_trace R mpF fc_epp ab w0 0 i.

(** fc_coalition_raw_trace — a five-card coalition's raw traces.
    @intent: the generic coalition assembly at fc_epp. *)
Definition fc_coalition_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @epp_coalition_trace R mpF fc_epp ab w0 0 C.

(** fc_input_raw_trace — input party j's raw five-card trace.
    @intent: the generic input extractor at fc_epp, reading position
    (pi_T' (mp_PI mpF)).+3 + j of the run. *)
Definition fc_input_raw_trace (ab : bool * bool) (w0 : pgg_gT FiveCardKim_M)
    (j : nat) := @epp_input_trace R mpF fc_epp ab w0 0 j.

(** fc_seat_countE — the seat index type of the trace layer is the seat index
    type of the landed five-card view.
    @composes: fc_coalition_raw_trace *)
Lemma fc_seat_countE : (pi_T' (mp_PI mpF)).+1 = 5.
Proof. by []. Qed.

(** fc_input_positions — the two input parties are read at positions 7 and 8.
    @main architecture: [seq (pi_T' (mp_PI mpF)).+3 + j | j <- iota 0 2] =
    [:: 7; 8], the identifiers of fc_epp_input_idsE. *)
Lemma fc_input_positions :
  [seq ((pi_T' (mp_PI mpF)).+3 + j)%N | j <- iota 0 2] = [:: 7; 8].
Proof. by []. Qed.

(** fc_epp_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run fc_epp (a, b) w0 0).1 = nseq 9 Finish, so
    positions 7 and 8 of fc_input_positions lie inside the run. *)
Lemma fc_epp_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  (@epp_run R mpF fc_epp (a, b) w0 0).1 = nseq 9 Finish.
Proof.
rewrite /epp_run fc_epp_fuelE fc_epp_procsE; exact: den_boer_run_terminates.
Qed.

(** fc_player_raw_traceE — the generic raw trace is the trace under content_of
    in denboer_player_trace.
    @main architecture: fc_player_raw_trace (a, b) w0 i = nth [::] (run_interp
    100 (den_boer_procs a b w0 0)).2 (2 + i). *)
Lemma fc_player_raw_traceE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  fc_player_raw_trace (a, b) w0 i
  = nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 (2 + i).
Proof.
by rewrite /fc_player_raw_trace /epp_participant_trace /epp_run
   fc_epp_fuelE fc_epp_procsE.
Qed.

End fivecard_trace_readoff.

Print Assumptions epp_seat_endpointE.
Print Assumptions epp_coalition_endpointsE.
Print Assumptions epp_coalition_endpoints_seqE.
Print Assumptions pgl_seat_endpointE.
Print Assumptions pgl_coalition_endpointsE.
Print Assumptions fc_seat_endpointE.
Print Assumptions fc_coalition_endpointsE.
Print Assumptions fc_player_raw_traceE.
