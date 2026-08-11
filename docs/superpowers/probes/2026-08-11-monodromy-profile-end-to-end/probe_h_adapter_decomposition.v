(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-H: the decomposition probe                                         *)
(*                                                                            *)
(* The final execution adapter EPP, with every field justified by a landed    *)
(* probe: the two count bridges of probe_b_count_bridge.v, the uncast content *)
(* readout of probe_c_pgl27_exec.v, the input processes of                    *)
(* probe_d_fivecard_exec.v, the concrete participant list and its enum        *)
(* equation of probe_g_vmcompute.v. Section run_of_static_observation        *)
(* derives the headline from three section hypotheses; the two instantiation *)
(* sections discharge all three at pgl27_profile and at five_card_profile    *)
(* from the landed instance lemmas. There is no Admitted, Axiom, Parameter   *)
(* or Abort in this file: every hypothesis of the generic layer is closed at *)
(* both carriers.                                                            *)
(*                                                                            *)
(* The sample adapter of probe_f_distributions.v is restated as a four-field  *)
(* record with its three layers over it. The observation map content_obs and  *)
(* the endpoint equation Hep stay theorem parameters, never fields.           *)
(*                                                                            *)
(* MonodromyProfileX is the one-record packaging of request alternative 6.1,  *)
(* instantiated at both carriers; the field-count and migration comparison is *)
(* the comment block at the end of the file.                                  *)
(*                                                                            *)
(* Findings, not statements (design record for the response):                 *)
(*                                                                            *)
(*  1. THE CONCRETE PARTICIPANT LIST TURNS TWO TRANSPORTS INTO CONVERSIONS.   *)
(*     With ep_players a field holding the instance's own list, the process   *)
(*     equalities pgl_epp_procsE and fc_epp_procsE close by [] where          *)
(*     probe_c_pgl27_exec.v and probe_d_fivecard_exec.v needed one rewrite   *)
(*     of the participant list under congr erase_aprocs. The process COUNT is *)
(*     then also a conversion (pgl_epp_proc_count, fc_epp_proc_count), which  *)
(*     is what lets Hterm be stated in the count-free form                    *)
(*     nseq (size (epp_procs x w0 P_idx)) Finish and still be discharged      *)
(*     from the landed nseq 10 / nseq 9 lemmas.                               *)
(*                                                                            *)
(*  2. THE ENUM EQUATION IS NEEDED IN BOTH DIRECTIONS. ep_playersE feeds      *)
(*     epp_players_size and epp_seat_endpointE (which read the list as an     *)
(*     enumeration) and, run backwards, converts the landed endpoint lemmas   *)
(*     (stated over enum 'I_T.+1) into the adapter's form over ep_players.    *)
(*     A concrete list without the equation would not support either.         *)
(*                                                                            *)
(*  3. Hrecon's LEAST COMMON FORM IS THE STATIC DECODE EQUATION, QUANTIFIED   *)
(*     OVER THE SIZE PROOF. Both carriers' landed recovery lemmas are about   *)
(*     an executed endpoint list; both discharge the static form after the    *)
(*     endpoint equation is run backwards. Quantifying over the size proof    *)
(*     rather than fixing one canonical proof is what makes the generic       *)
(*     derivation a two-line rewrite: the transport of the goal along Hep     *)
(*     changes the size proof's type, and any proof of the new type is        *)
(*     accepted. Fixing the proof would force an eq_irrelevance step at       *)
(*     every use.                                                             *)
(*                                                                            *)
(*  4. TERMINATION IS NOT A PREMISE OF RECOVERY. epp_run_recovers uses Hep    *)
(*     and Hrecon only; the endpoint equation already names the interpreter   *)
(*     output. Hterm is therefore carried as a separate conjunct of           *)
(*     epp_end_to_end rather than as a premise, and the two theorems are      *)
(*     stated separately so that the unused-hypothesis reading is visible.    *)
(*                                                                            *)
(*  5. THE FIVE-CARD DECODER SIDESTEPS THE DEPENDENT REWRITE.                 *)
(*     fc_epp_decode_seqE turns the tuple cast into a map over the underlying *)
(*     sequence, so the five-card Hrecon is a rewrite chain with no           *)
(*     generalization step, while PGL still needs the Hgen dance of           *)
(*     probe_c_pgl27_exec.v because ts_recon orbit_scheme is applied to the   *)
(*     cast tuple itself.                                                     *)
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

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The execution adapter                                                  *)
(******************************************************************************)

(** EPP — the execution adapter over a MonodromyProfile.
    Kind: interface.
    A value of this type carries the run argument type ep_inputT, the seat/share
    bridge ep_players_bridge, the card/share bridge ep_cards_bridge, the
    participant list ep_players with its enumeration equation ep_playersE, the
    content readout ep_content, the input processes ep_input_procs and the
    interpreter fuel ep_fuel. *)
Record EPP (R : realType) (mp : MonodromyProfile R) := MkEPP {
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

(******************************************************************************)
(*     The run, the traces and the decoder derived from the adapter           *)
(******************************************************************************)

Section execution_of_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.

(** epp_dealer_id — the dealer's process identifier.
    @intent: 0. *)
Definition epp_dealer_id : nat := 0.

(** epp_verifier_id — the verifier's process identifier.
    @intent: 1. *)
Definition epp_verifier_id : nat := 1.

(** epp_seat_id — seat i's process identifier.
    @intent: 2 + i, the seats occupying 2 .. (pi_T' (mp_PI mp)).+2. *)
Definition epp_seat_id (i : 'I_(pi_T' (mp_PI mp)).+1) : nat := 2 + i.

(** epp_input_id — input party j's process identifier.
    @intent: (pi_T' (mp_PI mp)).+3 + j, the identifiers following the dealer,
    the verifier and the seats. *)
Definition epp_input_id (j : nat) : nat := (pi_T' (mp_PI mp)).+3 + j.

(** epp_input_ids — the party identifiers of the input processes.
    @intent: epp_input_id read at each position of ep_input_procs e x. *)
Definition epp_input_ids (x : ep_inputT e) : seq nat :=
  [seq epp_input_id j | j <- iota 0 (size (e.(ep_input_procs) x))].

(** epp_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI mp with the adapter's content
    readout, the singleton deck [:: w0], the input identifiers and the
    participant list. *)
Definition epp_dealer (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
    (epp_input_ids x) e.(ep_players) P_idx.

(** epp_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per participant, then the input
    processes, in process-identifier order. *)
Definition epp_saprocs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (epp_dealer x w0 P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) e.(ep_players))
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- e.(ep_players)]
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
    @intent: endpoints_of_trace of entry epp_verifier_id of epp_run.2. *)
Definition epp_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  endpoints_of_trace (nth [::] (epp_run x w0 P_idx).2 epp_verifier_id).

(** epp_participant_trace — the executed trace of the seat-i player.
    @intent: entry epp_seat_id i of epp_run.2. *)
Definition epp_participant_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  nth [::] (epp_run x w0 P_idx).2 (epp_seat_id i).

(** epp_input_trace — the executed trace of input party j.
    @intent: entry epp_input_id j of epp_run.2. *)
Definition epp_input_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (j : nat) :=
  nth [::] (epp_run x w0 P_idx).2 (epp_input_id j).

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

(** epp_players_size — the participant list has one entry per seat.
    @composes: epp_static_endpoints_size *)
Lemma epp_players_size : size e.(ep_players) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite e.(ep_playersE) size_enum_ord. Qed.

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

(** epp_static_endpoints — the static group-action observation over the seats.
    @intent: content_obs x read at the cut w0 and each participant's starting
    position. *)
Definition epp_static_endpoints
    (content_obs : ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
                     -> 'I_(pgg_N' (mp_M mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) :=
  [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- e.(ep_players)].

(** epp_static_endpoints_size — the static observation has one entry per seat.
    @composes: epp_endpoints_size *)
Lemma epp_static_endpoints_size content_obs x w0 :
  size (epp_static_endpoints content_obs x w0) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite size_map epp_players_size. Qed.

(******************************************************************************)
(*     The headline: interpreter output against the static observation        *)
(******************************************************************************)

Section run_of_static_observation.

Variable content_obs :
  ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
    -> 'I_(pgg_N' (mp_M mp)).+1.
Variable expected : ep_inputT e -> mp_secretT mp.
Variables (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat).

(* Termination: every process of the run reaches Finish. *)
Hypothesis Hterm : (epp_run x w0 P_idx).1
  = nseq (size (epp_procs x w0 P_idx)) Finish.

(* Endpoint equation: the executed endpoints are the static observation. *)
Hypothesis Hep : epp_endpoints x w0 P_idx
  = epp_static_endpoints content_obs x w0.

(* Static recovery: decoding the static observation returns the expected
   value. *)
Hypothesis Hrecon : forall Hsz : size (epp_static_endpoints content_obs x w0)
    = (pi_T' (mp_PI mp)).+1,
  @epp_decode (epp_static_endpoints content_obs x w0) Hsz = expected x.

(** epp_endpoints_size — the run collects one endpoint per seat.
    @composes: epp_run_recovers *)
Lemma epp_endpoints_size : size (epp_endpoints x w0 P_idx)
  = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite Hep epp_static_endpoints_size. Qed.

(** epp_run_recovers — decoding the executed endpoints returns the expected
    value.
    @main correctness: epp_decode (epp_endpoints x w0 P_idx) = expected x, for
    an adapter whose endpoints are the static observation and whose static
    observation decodes to expected x. *)
Theorem epp_run_recovers :
  @epp_decode (epp_endpoints x w0 P_idx) epp_endpoints_size = expected x.
Proof.
have Hgen : forall (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (H1 : size ep = (pi_T' (mp_PI mp)).+1),
    ep = epp_static_endpoints content_obs x w0 ->
    @epp_decode ep H1 = expected x.
  by move=> ep H1 Heq; move: H1; rewrite Heq => H1; exact: Hrecon.
by apply: Hgen.
Qed.

(** epp_seat_endpointE — seat i's endpoint is the static observation at seat i.
    @main correctness: epp_seat_endpoint x w0 P_idx i = content_obs x (w0, tnth
    (pi_starts (mp_PI mp)) i). *)
Lemma epp_seat_endpointE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  epp_seat_endpoint x w0 P_idx i
  = content_obs x (w0, tnth (pi_starts (mp_PI mp)) i).
Proof.
rewrite /epp_seat_endpoint Hep /epp_static_endpoints e.(ep_playersE).
by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
Qed.

(** epp_coalition_endpointsE — a coalition's endpoint readings are the static
    observation restricted to its seats.
    @main correctness: epp_coalition_endpoints x w0 P_idx C = [ffun i => if i
    \in C then content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) else ord0]. *)
Lemma epp_coalition_endpointsE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  epp_coalition_endpoints x w0 P_idx C
  = [ffun i => if i \in C
               then content_obs x (w0, tnth (pi_starts (mp_PI mp)) i)
               else ord0].
Proof.
apply/ffunP => i; rewrite /epp_coalition_endpoints !ffunE.
by case: ifP => // _; exact: epp_seat_endpointE.
Qed.

(** epp_end_to_end — termination, endpoint count and recovery of one run.
    @main correctness: the run reaches Finish at every process, collects one
    endpoint per seat, and decodes to expected x. *)
Theorem epp_end_to_end :
  [/\ (epp_run x w0 P_idx).1 = nseq (size (epp_procs x w0 P_idx)) Finish,
      size (epp_endpoints x w0 P_idx) = (pi_T' (mp_PI mp)).+1 &
      @epp_decode (epp_endpoints x w0 P_idx) epp_endpoints_size = expected x].
Proof.
by split; [exact: Hterm | exact: epp_endpoints_size | exact: epp_run_recovers].
Qed.

End run_of_static_observation.

End execution_of_profile.

(******************************************************************************)
(*     The sample adapter and its three layers                                *)
(******************************************************************************)

(** SampleAdapter — the probabilistic layer over an execution adapter.
    Kind: interface.
    A value of this type carries a finite sample space sa_sampleT with a law
    sa_sampleP, the run argument map sa_arg and the cut map sa_cut. *)
Record SampleAdapter (R : realType) (mp : MonodromyProfile R) (e : EPP mp) :=
  MkSampleAdapter {
    sa_sampleT : finType ;
    sa_sampleP : R.-fdist sa_sampleT ;
    sa_arg     : sa_sampleT -> ep_inputT e ;
    sa_cut     : sa_sampleT -> pgg_gT (mp_M mp) ;
  }.

Section sample_layers.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.
Variable sa : SampleAdapter e.
Variable P_idx : nat.

(* LAYER 1: raw execution. One interpreter result per sample point. *)

(** sa_run — the run at a sample point.
    @intent: epp_run at the sample's argument and cut, a pair of final process
    states and per-process traces. *)
Definition sa_run (u : sa_sampleT sa) :=
  @epp_run R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx.

(* LAYER 2: trace functions on sample points, typed as random variables. *)

(** sa_seat_view — seat i's endpoint as a random variable.
    @intent: the sample point mapped to epp_seat_endpoint at its argument and
    cut. *)
Definition sa_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sa.(sa_sampleP) -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => @epp_seat_endpoint R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx i.

(** sa_coalition_view — a coalition's endpoint readings as a random variable.
    @intent: the sample point mapped to epp_coalition_endpoints at its argument
    and cut. *)
Definition sa_coalition_view (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {RV sa.(sa_sampleP) -> {ffun 'I_(pi_T' (mp_PI mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1}} :=
  fun u => @epp_coalition_endpoints R mp e (sa.(sa_arg) u) (sa.(sa_cut) u)
             P_idx C.

(* LAYER 3: pushforwards of the sample law along the layer-2 functions. *)

(** sa_seat_dist — the law of seat i's endpoint.
    @intent: the pushforward of sa_sampleP along sa_seat_view i. *)
Definition sa_seat_dist (i : 'I_(pi_T' (mp_PI mp)).+1)
    : R.-fdist 'I_(pgg_N' (mp_M mp)).+1 :=
  fdistmap (sa_seat_view i) sa.(sa_sampleP).

(** sa_coalition_dist — the law of a coalition's endpoint readings.
    @intent: the pushforward of sa_sampleP along sa_coalition_view C. *)
Definition sa_coalition_dist (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :=
  fdistmap (sa_coalition_view C) sa.(sa_sampleP).

(** sa_cut_dist — the law of the cut.
    @intent: the pushforward of sa_sampleP along sa_cut. *)
Definition sa_cut_dist : R.-fdist (pgg_gT (mp_M mp)) :=
  fdistmap sa.(sa_cut) sa.(sa_sampleP).

Section sample_of_static_observation.

Variable content_obs :
  ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
    -> 'I_(pgg_N' (mp_M mp)).+1.

Hypothesis Hep : forall u : sa_sampleT sa,
  @epp_endpoints R mp e (sa.(sa_arg) u) (sa.(sa_cut) u) P_idx
  = @epp_static_endpoints R mp e content_obs (sa.(sa_arg) u) (sa.(sa_cut) u).

(** sa_static_seat_view — the static observation at seat i as a random
    variable.
    @intent: the sample point mapped to content_obs of its argument at its cut
    and seat i's start. *)
Definition sa_static_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sa.(sa_sampleP) -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => content_obs (sa.(sa_arg) u)
             (sa.(sa_cut) u, tnth (pi_starts (mp_PI mp)) i).

(** sa_seat_viewE — the executed seat view is the static observation.
    @main correctness: sa_seat_view i = sa_static_seat_view i. *)
Lemma sa_seat_viewE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_view i = sa_static_seat_view i.
Proof. by apply: boolp.funext => u; exact: (epp_seat_endpointE (Hep u) i). Qed.

(** sa_seat_distE — the executed seat law is the static observation's law.
    @main correctness: sa_seat_dist i = fdistmap (sa_static_seat_view i)
    sa_sampleP. *)
Lemma sa_seat_distE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  sa_seat_dist i = fdistmap (sa_static_seat_view i) sa.(sa_sampleP).
Proof. by rewrite /sa_seat_dist sa_seat_viewE. Qed.

End sample_of_static_observation.

End sample_layers.

(******************************************************************************)
(*     The adapter filled at pgl27_profile                                    *)
(******************************************************************************)

Section pgl27_execution.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_playersE — the PGL(2,7) participant list is the seat enumeration.
    @composes: pgl_epp *)
Lemma pgl_playersE : pgl27_players = enum 'I_(pi_T' (mp_PI mpP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl_epp — the PGL(2,7) execution adapter.
    @intent: run argument bool, both bridges erefl at 7 seats, 7 shares and 8
    cards, participant list pgl27_players, content the shares ts_encode
    orbit_scheme s of the dealt orbit secret, no input processes, fuel
    pgl27_fuel. *)
Definition pgl_epp : EPP mpP :=
  @MkEPP R mpP bool erefl erefl pgl27_players pgl_playersE
    (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) pgl27_fuel.

(** pgl_content_obs — the PGL(2,7) static observation.
    @intent: the share of s at the cut image of a starting position. *)
Definition pgl_content_obs (s : bool)
    (p : pgg_gT (mp_M mpP) * 'I_(pgg_N' (mp_M mpP)).+1)
    : 'I_(pgg_N' (mp_M mpP)).+1 :=
  tnth (ts_encode orbit_scheme s) (@pgg_rho (mp_M mpP) p.1 p.2).

(** pgl_epp_playersE — the adapter's participant list is the instance's list.
    @composes: pgl_epp_endpoints *)
Lemma pgl_epp_playersE : @ep_players R mpP pgl_epp = pgl27_players.
Proof. by []. Qed.

(** pgl_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs pgl_epp s w0 0 = pgl27_procs s w0, by
    conversion. *)
Lemma pgl_epp_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_procs R mpP pgl_epp s w0 0 = pgl27_procs s w0.
Proof. by []. Qed.

(** pgl_epp_proc_count — the derived run has ten processes.
    @composes: pgl_epp_terminates *)
Lemma pgl_epp_proc_count (s : bool) (w0 : pgg_gT pgl27_M) :
  size (@epp_procs R mpP pgl_epp s w0 0) = 10.
Proof. by []. Qed.

(** pgl_epp_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run pgl_epp s w0 0).1 is Finish at each of the ten
    processes, for any cut w0. *)
Lemma pgl_epp_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@epp_run R mpP pgl_epp s w0 0).1
  = nseq (size (@epp_procs R mpP pgl_epp s w0 0)) Finish.
Proof.
rewrite pgl_epp_proc_count /epp_run pgl_epp_procsE; exact: pgl27_run_terminates.
Qed.

(** pgl_epp_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @main correctness: epp_endpoints pgl_epp s w0 0 = epp_static_endpoints
    pgl_content_obs s w0. *)
Lemma pgl_epp_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_endpoints R mpP pgl_epp s w0 0
  = @epp_static_endpoints R mpP pgl_epp pgl_content_obs s w0.
Proof.
rewrite /epp_endpoints /epp_run pgl_epp_procsE /epp_static_endpoints.
rewrite pgl_epp_playersE pgl_playersE; exact: pgl27_endpoints.
Qed.

(** pgl_epp_decodeE — the adapter's decoder is the instance's reconstruction.
    @composes: pgl_epp_recon *)
Lemma pgl_epp_decodeE (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpP)).+1)
    (Hsz' : size ep = (ts_T' orbit_scheme).+1) :
  @epp_decode R mpP pgl_epp ep Hsz
  = ts_recon orbit_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /epp_decode /run_recover.
by rewrite (eq_irrelevance (etrans Hsz (@epp_seat_share_count R mpP pgl_epp))
                          Hsz').
Qed.

(** pgl_epp_recon — decoding the PGL(2,7) static observation returns the dealt
    secret.
    @main correctness: the static recovery hypothesis of the headline, at
    pgl27_profile, for any cut w0 in the group and any proof of the endpoint
    count. *)
Lemma pgl_epp_recon (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  forall Hsz : size (@epp_static_endpoints R mpP pgl_epp pgl_content_obs s w0)
                 = (pi_T' (mp_PI mpP)).+1,
  @epp_decode R mpP pgl_epp
    (@epp_static_endpoints R mpP pgl_epp pgl_content_obs s w0) Hsz = s.
Proof.
move=> Hw0.
have Hgen : forall (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (H1 : size ep = (pi_T' (mp_PI mpP)).+1),
    ep = endpoints_of_trace
           (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1) ->
    @epp_decode R mpP pgl_epp ep H1 = s.
  move=> ep H1 Hq; move: H1; rewrite Hq => H1.
  rewrite (pgl_epp_decodeE H1 (pgl27_endpoints_size s w0)).
  exact: (pgl27_run_recovers s Hw0).
move=> Hsz; apply: Hgen.
by rewrite -pgl_epp_endpoints /epp_endpoints /epp_run pgl_epp_procsE.
Qed.

(** pgl_run_recovers — the headline at pgl27_profile.
    @main correctness: decoding the executed endpoints of the derived PGL(2,7)
    run returns the dealt orbit secret s, for any cut w0 in the group. *)
Theorem pgl_run_recovers (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  @epp_decode R mpP pgl_epp (@epp_endpoints R mpP pgl_epp s w0 0)
    (@epp_endpoints_size R mpP pgl_epp pgl_content_obs s w0 0
       (pgl_epp_endpoints s w0)) = s.
Proof.
exact: (@epp_run_recovers R mpP pgl_epp pgl_content_obs (fun s => s) s w0 0
          (pgl_epp_endpoints s w0) (pgl_epp_recon Hw0)).
Qed.

(** pgl_end_to_end — termination, endpoint count and recovery at
    pgl27_profile.
    @main correctness: the three-part end-to-end statement of the derived
    PGL(2,7) run, for any cut w0 in the group. *)
Theorem pgl_end_to_end (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  [/\ (@epp_run R mpP pgl_epp s w0 0).1
        = nseq (size (@epp_procs R mpP pgl_epp s w0 0)) Finish,
      size (@epp_endpoints R mpP pgl_epp s w0 0) = (pi_T' (mp_PI mpP)).+1 &
      @epp_decode R mpP pgl_epp (@epp_endpoints R mpP pgl_epp s w0 0)
        (@epp_endpoints_size R mpP pgl_epp pgl_content_obs s w0 0
           (pgl_epp_endpoints s w0)) = s].
Proof.
exact: (@epp_end_to_end R mpP pgl_epp pgl_content_obs (fun s => s) s w0 0
          (pgl_epp_terminates s w0) (pgl_epp_endpoints s w0)
          (pgl_epp_recon Hw0)).
Qed.

End pgl27_execution.

(******************************************************************************)
(*     The adapter filled at five_card_profile, arbitrary bias                *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_execution.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** fc_playersE — the five-card participant list is the seat enumeration.
    @composes: fc_epp *)
Lemma fc_playersE : den_boer_players = enum 'I_(pi_T' (mp_PI mpF)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** fc_epp — the five-card execution adapter at bias eps.
    @intent: run argument the committed pair (a, b) : bool * bool, both bridges
    erefl at 5 seats, 5 shares and 5 cards, participant list den_boer_players,
    content the den Boer layout of the decoded committed cards, input processes
    the two committing parties 7 and 8, fuel 100. *)
Definition fc_epp : EPP mpF :=
  @MkEPP R mpF (bool * bool)%type erefl erefl den_boer_players fc_playersE
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(** fc_content_obs — the five-card static observation.
    @intent: the den Boer layout of the committed pair at the cut image of a
    starting position. *)
Definition fc_content_obs (ab : bool * bool)
    (p : pgg_gT (mp_M mpF) * 'I_(pgg_N' (mp_M mpF)).+1)
    : 'I_(pgg_N' (mp_M mpF)).+1 :=
  tnth (den_boer_layout ab) (@pgg_rho (mp_M mpF) p.1 p.2).

(** fc_epp_playersE — the adapter's participant list is the instance's list.
    @composes: fc_epp_endpoints *)
Lemma fc_epp_playersE : @ep_players R mpF fc_epp = den_boer_players.
Proof. by []. Qed.

(** fc_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: fc_epp_terminates *)
Lemma fc_epp_fuelE : @ep_fuel R mpF fc_epp = 100.
Proof. by []. Qed.

(** fc_epp_input_idsE — the derived input identifiers are the instance's.
    @composes: fc_epp_procsE *)
Lemma fc_epp_input_idsE (ab : bool * bool) :
  @epp_input_ids R mpF fc_epp ab = [:: 7; 8].
Proof. by []. Qed.

(** fc_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs fc_epp (a, b) w0 P_idx = den_boer_procs a b w0
    P_idx, by conversion, at every bias eps. *)
Lemma fc_epp_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @epp_procs R mpF fc_epp (a, b) w0 P_idx = den_boer_procs a b w0 P_idx.
Proof. by []. Qed.

(** fc_epp_proc_count — the derived run has nine processes.
    @composes: fc_epp_terminates *)
Lemma fc_epp_proc_count (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  size (@epp_procs R mpF fc_epp (a, b) w0 P_idx) = 9.
Proof. by []. Qed.

(** fc_epp_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run fc_epp (a, b) w0 P_idx).1 is Finish at each of
    the nine processes, for any cut w0. *)
Lemma fc_epp_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  (@epp_run R mpF fc_epp (a, b) w0 P_idx).1
  = nseq (size (@epp_procs R mpF fc_epp (a, b) w0 P_idx)) Finish.
Proof.
rewrite fc_epp_proc_count /epp_run fc_epp_fuelE fc_epp_procsE.
exact: den_boer_run_terminates.
Qed.

(** fc_epp_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @main correctness: epp_endpoints fc_epp (a, b) w0 0 = epp_static_endpoints
    fc_content_obs (a, b) w0. *)
Lemma fc_epp_endpoints (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @epp_endpoints R mpF fc_epp (a, b) w0 0
  = @epp_static_endpoints R mpF fc_epp fc_content_obs (a, b) w0.
Proof.
rewrite /epp_endpoints /epp_run fc_epp_fuelE fc_epp_procsE.
rewrite /epp_static_endpoints fc_epp_playersE fc_playersE.
exact: den_boer_endpoints.
Qed.

(** fc_epp_decodeE — the adapter's decoder is the instance's reconstruction.
    @composes: fc_epp_decode_seqE *)
Lemma fc_epp_decodeE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  @epp_decode R mpF fc_epp ep Hsz
  = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /epp_decode /run_recover.
by rewrite (eq_irrelevance (etrans Hsz (@epp_seat_share_count R mpF fc_epp))
                          Hsz').
Qed.

(** fc_epp_decode_seqE — the adapter's decoder at the sequence level.
    @composes: fc_epp_recon
    epp_decode fc_epp ep Hsz = fc_three_consec [seq decode_bool x | x <- ep],
    the reconstruction shape of den_boer_run_recovers. *)
Lemma fc_epp_decode_seqE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1) :
  @epp_decode R mpF fc_epp ep Hsz
  = fc_three_consec [seq decode_bool x | x <- ep].
Proof.
rewrite (fc_epp_decodeE Hsz Hsz).
by rewrite /ts_recon /fcI_scheme /fcI_recon val_tcast.
Qed.

(** fc_epp_recon — decoding the five-card static observation returns the
    committed conjunction.
    @main correctness: the static recovery hypothesis of the headline, at
    five_card_profile, for any cut w0 in the group and any proof of the
    endpoint count. *)
Lemma fc_epp_recon (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@epp_static_endpoints R mpF fc_epp fc_content_obs
                       (a, b) w0) = (pi_T' (mp_PI mpF)).+1,
  @epp_decode R mpF fc_epp
    (@epp_static_endpoints R mpF fc_epp fc_content_obs (a, b) w0) Hsz
  = (a, b).1 && (a, b).2.
Proof.
move=> Hw0 Hsz; rewrite fc_epp_decode_seqE -fc_epp_endpoints.
rewrite /epp_endpoints /epp_run fc_epp_fuelE fc_epp_procsE.
exact: den_boer_run_recovers.
Qed.

(** fc_run_recovers — the headline at five_card_profile.
    @main correctness: decoding the executed endpoints of the derived five-card
    run returns a && b, the conjunction of the two committed bits, for any cut
    w0 in the group and at every bias eps. *)
Theorem fc_run_recovers (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  @epp_decode R mpF fc_epp (@epp_endpoints R mpF fc_epp (a, b) w0 0)
    (@epp_endpoints_size R mpF fc_epp fc_content_obs (a, b) w0 0
       (fc_epp_endpoints a b w0)) = a && b.
Proof.
exact: (@epp_run_recovers R mpF fc_epp fc_content_obs (fun ab => ab.1 && ab.2)
          (a, b) w0 0 (fc_epp_endpoints a b w0) (fc_epp_recon Hw0)).
Qed.

(** fc_end_to_end — termination, endpoint count and recovery at
    five_card_profile.
    @main correctness: the three-part end-to-end statement of the derived
    five-card run, for any cut w0 in the group and at every bias eps. *)
Theorem fc_end_to_end (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Hw0 : w0 \in pgg_G FiveCardKim_M) :
  [/\ (@epp_run R mpF fc_epp (a, b) w0 0).1
        = nseq (size (@epp_procs R mpF fc_epp (a, b) w0 0)) Finish,
      size (@epp_endpoints R mpF fc_epp (a, b) w0 0) = (pi_T' (mp_PI mpF)).+1 &
      @epp_decode R mpF fc_epp (@epp_endpoints R mpF fc_epp (a, b) w0 0)
        (@epp_endpoints_size R mpF fc_epp fc_content_obs (a, b) w0 0
           (fc_epp_endpoints a b w0)) = a && b].
Proof.
exact: (@epp_end_to_end R mpF fc_epp fc_content_obs (fun ab => ab.1 && ab.2)
          (a, b) w0 0 (fc_epp_terminates a b w0 0) (fc_epp_endpoints a b w0)
          (fc_epp_recon Hw0)).
Qed.

End fivecard_execution.

(******************************************************************************)
(*     Alternative 6.1: the one-record packaging                              *)
(******************************************************************************)

(** MonodromyProfileX — the profile and its execution adapter in one record.
    Kind: interface.
    A value of this type carries an algebraic profile mpx_core and an execution
    adapter mpx_exec over it. *)
Record MonodromyProfileX (R : realType) := MkMonodromyProfileX {
  mpx_core : MonodromyProfile R ;
  mpx_exec : EPP mpx_core ;
}.

(** pgl_mpx — the one-record packaging at pgl27_profile.
    @intent: pgl27_profile R with pgl_epp. *)
Definition pgl_mpx (R : realType) : MonodromyProfileX R :=
  @MkMonodromyProfileX R (pgl27_profile R) (pgl_epp R).

(** fc_mpx — the one-record packaging at five_card_profile.
    @intent: five_card_profile at bias eps and word length L with fc_epp. *)
Definition fc_mpx (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R)
    (L : nat) : MonodromyProfileX R :=
  @MkMonodromyProfileX R (@five_card_profile R eps Hlt Hgt Hspec L)
    (@fc_epp R eps Hlt Hgt Hspec L).

(** pgl_mpx_coreE — the packaging reuses the landed PGL(2,7) profile value.
    @main architecture: mpx_core (pgl_mpx R) = pgl27_profile R, by conversion;
    the existing profile is a component, not a rebuild. *)
Lemma pgl_mpx_coreE (R : realType) : mpx_core (pgl_mpx R) = pgl27_profile R.
Proof. by []. Qed.

(** fc_mpx_coreE — the packaging reuses the landed five-card profile value.
    @main architecture: mpx_core (fc_mpx Hlt Hgt Hspec L) = five_card_profile at
    the same bias and word length, by conversion. *)
Lemma fc_mpx_coreE (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat) :
  mpx_core (fc_mpx Hlt Hgt Hspec L) = @five_card_profile R eps Hlt Hgt Hspec L.
Proof. by []. Qed.

Print Assumptions epp_run_recovers.
Print Assumptions epp_end_to_end.
Print Assumptions pgl_run_recovers.
Print Assumptions pgl_end_to_end.
Print Assumptions fc_run_recovers.
Print Assumptions fc_end_to_end.
Print Assumptions sa_seat_distE.

(******************************************************************************)
(*     Request 6.1 against request 6.2: field counts and migration            *)
(*                                                                            *)
(* FIELD COUNT SEEN BY AN INSTANCE AUTHOR                                     *)
(*                                                                            *)
(*   6.2, two records (this file)   5 profile fields + 8 adapter fields = 13, *)
(*                                  filled in two separate constructor calls; *)
(*                                  a profile with no execution adapter stays *)
(*                                  a legal, complete value.                  *)
(*   6.1, one flat record           13 fields in one constructor call; there  *)
(*                                  is no legal value carrying only the       *)
(*                                  algebraic five.                           *)
(*   6.1 as packaged here           MonodromyProfileX has 2 fields, and the   *)
(*   (MonodromyProfileX)            author still fills 13 across the two      *)
(*                                  nested constructors; the profile value is *)
(*                                  reused rather than rebuilt                *)
(*                                  (pgl_mpx_coreE, fc_mpx_coreE).            *)
(*                                                                            *)
(* The 8 adapter fields and their probe evidence: ep_inputT (P-A register),   *)
(* ep_players_bridge and ep_cards_bridge (P-B), ep_players and ep_playersE    *)
(* (P-G: the enum-direct run does not reduce under vm_compute at either       *)
(* carrier), ep_content (P-C finding 3: the uncast share readout, not the     *)
(* bridge-2 transported one), ep_input_procs (P-D), ep_fuel (P-C finding 4).  *)
(*                                                                            *)
(* MIGRATION IMPACT: every landed MonodromyProfile constructor                *)
(*                                                                            *)
(*   file:line                                            form               *)
(*   ---------                                            ----               *)
(*   pgg-smc/instances/pgl27/pgl27_profile.v:105          MkMonodromyProfile *)
(*   pgg-smc/instances/kim2025/five_card_family.v:164      MkMonodromyProfile *)
(*   pgg-smc/instances/s5/s5_profile.v:51                  MkMonodromyProfile *)
(*   pgg-smc/instances/s5x5/s5x5_profile.v:42              MkMonodromyProfile *)
(*   pgg-smc/instances/abelian/abel_profile.v:69           MkMonodromyProfile *)
(*   pgg-smc/instances/denboer1989/den_boer_profile.v:76   five_card_profile  *)
(*   pgg-smc/instances/kim2025/rigidity_kim_instance.v:66  five_card_profile  *)
(*                                                                           *)
(*   Under 6.2 all seven are untouched: the adapter is a second value over an *)
(*   existing profile, and only the two carriers that own a run (PGL and the  *)
(*   five-card family) gain one. Under a flat 6.1 record all five direct      *)
(*   constructor calls change arity, and the two wrappers change with the     *)
(*   function they wrap; the three instances with no interpreter run (s5,     *)
(*   s5x5, abelian) would have to invent a participant list, a content        *)
(*   readout, an input-process list and a fuel value, or the record would     *)
(*   need option-typed fields.                                               *)
(*                                                                           *)
(* PAPER CLAIM SUPPORTED                                                     *)
(*                                                                           *)
(*   Under 6.2, and compiled here: an algebraic profile plus one execution    *)
(*   adapter yields the piSMC process list, the interpreter run, the          *)
(*   per-participant and per-input-party traces, the verifier endpoints and   *)
(*   the endpoint decoder, and one generic theorem gives termination,         *)
(*   endpoint count and recovery at both protocol families from three         *)
(*   per-carrier facts.                                                      *)
(*                                                                           *)
(*   Under a flat 6.1 record the same sentence would be available with one    *)
(*   filled record in place of a profile plus an adapter, at the cost of      *)
(*   rebuilding every profile value above and of admitting instances that     *)
(*   carry execution data they never run.                                    *)
(******************************************************************************)
