(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-F: the distribution layer over the trace layer                     *)
(*                                                                            *)
(* SCOPE. This file states TYPED DEFINITIONS and equations between them. It   *)
(* contains no variation-distance, entropy or mutual-information claim, and   *)
(* no privacy statement: a per-position endpoint law is neither coalition     *)
(* privacy nor trace privacy, and nothing here should be read as either.      *)
(*                                                                            *)
(* The EPP record and the generic execution section are those of              *)
(* probe_e_traces.v, copied (the probe directory has no -R mapping) and       *)
(* trimmed to the endpoint readers, with the corrected .+3 input-identifier   *)
(* offset kept in epp_input_ids. Three layers are then stacked over a sample  *)
(* space, and kept apart by their types:                                      *)
(*                                                                            *)
(*   LAYER 1  samp_run u          : a concrete interpreter result per sample  *)
(*                                  point, a pair of process states and raw   *)
(*                                  traces; not a distribution;               *)
(*   LAYER 2  samp_seat_view i    : {RV sampleP -> 'I_N.+1}, a function on    *)
(*            samp_coalition_view  sample points; not a distribution;         *)
(*   LAYER 3  samp_seat_dist i    : R.-fdist 'I_N.+1, the pushforward of      *)
(*            samp_coalition_dist  sampleP along the layer-2 function.        *)
(*                                                                            *)
(* Findings, not statements (design record for P-H):                          *)
(*                                                                            *)
(*  1. THE SAMPLE ADAPTER NEEDS AN ARG MAP AND A CUT MAP, NOT A PRODUCT.      *)
(*     pgl27P is a product of a secret law and a shuffle law, so its arg and  *)
(*     cut maps are fst and snd; the den Boer space P (five_card_leakage.v)   *)
(*     samples bool * bool * 'I_5 and reconstructs the cut as fc_sigma ^+ k,  *)
(*     a map that is not a projection. Both instantiate the same section.     *)
(*                                                                            *)
(*  2. RAW TRACES DO NOT LIFT. samp_raw_trace_dist is a Fail Definition: the  *)
(*     codomain seq (pgg_data _) of epp_participant_trace is not a finType,   *)
(*     so fdistmap does not accept it. Layer 3 exists only for the finType-   *)
(*     valued readers, which is why P-E stopped at the endpoint observables.  *)
(*                                                                            *)
(*  3. THE WITNESS DISTRIBUTION IS NOT A CUT DISTRIBUTION IN GENERAL.         *)
(*     sw_rho_dist (mp_security mp) : R.-fdist {perm 'I_(pgg_N' (mp_M mp)).+1}*)
(*     while a cut is drawn in pgg_gT (mp_M mp), an abstract finGroupType.    *)
(*     samp_cut_dist_from_witness records the mismatch; samp_cut_dist_image   *)
(*     is the connecting map, the pushforward along the representation        *)
(*     pgg_rho. At the two Gen_PGGTypes instances of this file the two        *)
(*     carriers coincide by conversion (pgl_witness_is_cut_dist,              *)
(*     fc_witness_is_cut_dist), and at PGL(2,7) the sample space's cut factor *)
(*     is the witness distribution itself (pgl_sample_is_witness_prod).       *)
(*                                                                            *)
(*  4. THE FINITE-WORD SPACE FITS THE ADAPTER UNCHANGED. Taking the sample    *)
(*     space to be a secret prior times the two-hundred-letter word law and   *)
(*     the cut map to be word_eval reproduces the landed word shuffle law     *)
(*     rho_word as the adapter's cut pushforward (pglw_cut_dist_word). The    *)
(*     word length, the letter law and the secret prior are all parameters    *)
(*     of the model, none of them read off the profile.                       *)
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
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The execution adapter (probe_d_fivecard_exec.v, probe_e_traces.v)      *)
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

End trace_of_static_observation.

End execution_of_profile.

(******************************************************************************)
(*     The sample adapter and the three layers                                *)
(******************************************************************************)

Section sample_adapter.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.
Variables (sampleT : finType) (sampleP : R.-fdist sampleT).
Variables (samp_arg : sampleT -> ep_inputT e)
          (samp_cut : sampleT -> pgg_gT (mp_M mp)).
Variable P_idx : nat.

(* LAYER 1: raw execution. One interpreter result per sample point. *)

(** samp_run — the run at a sample point.
    @intent: epp_run at the sample's argument and cut, a pair of final process
    states and per-process traces. *)
Definition samp_run (u : sampleT) :=
  @epp_run R mp e (samp_arg u) (samp_cut u) P_idx.

(* LAYER 2: trace functions on sample points, typed as random variables. *)

(** samp_seat_view — seat i's endpoint as a random variable.
    @intent: the sample point mapped to epp_seat_endpoint at its argument and
    cut. *)
Definition samp_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sampleP -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => @epp_seat_endpoint R mp e (samp_arg u) (samp_cut u) P_idx i.

(** samp_coalition_view — a coalition's endpoint readings as a random variable.
    @intent: the sample point mapped to epp_coalition_endpoints at its argument
    and cut. *)
Definition samp_coalition_view (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {RV sampleP -> {ffun 'I_(pi_T' (mp_PI mp)).+1
                      -> 'I_(pgg_N' (mp_M mp)).+1}} :=
  fun u => @epp_coalition_endpoints R mp e (samp_arg u) (samp_cut u) P_idx C.

(** samp_seat_view_of_run — the layer-2 reader reads the layer-1 run.
    @composes: samp_seat_dist *)
Lemma samp_seat_view_of_run (u : sampleT) (i : 'I_(pi_T' (mp_PI mp)).+1) :
  samp_seat_view i u
  = nth ord0 (endpoints_of_trace (nth [::] (samp_run u).2 1)) i.
Proof. by []. Qed.

(* The raw trace has no layer 3: seq (pgg_data _) is not a finType.
   The Fail below is the type evidence, verbatim:
     The term "f" has type "forall _ : Finite.sort sT,
       list (pgg_data (S (pgg_N' (MonodromyReprWithGenerator.sort (mp_M mp)))))"
     while it is expected to have type
       "forall _ : Finite.sort sT, Finite.sort ?B". *)
Fail Definition samp_raw_trace_dist (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  fdistmap (fun u : sampleT =>
    @epp_participant_trace R mp e (samp_arg u) (samp_cut u) P_idx i) sampleP.

(* LAYER 3: pushforward distributions. fdistmap X sampleP is the landed
   pushforward idiom (fdist.v), the one pgl27_word_privacy.v uses for view laws
   and the one proba.v's `p_ X abbreviates. *)

(** samp_seat_dist — the law of seat i's endpoint.
    @intent: the pushforward of sampleP along samp_seat_view i. *)
Definition samp_seat_dist (i : 'I_(pi_T' (mp_PI mp)).+1)
    : R.-fdist 'I_(pgg_N' (mp_M mp)).+1 :=
  fdistmap (samp_seat_view i) sampleP.

(** samp_coalition_dist — the law of a coalition's endpoint readings.
    @intent: the pushforward of sampleP along samp_coalition_view C. *)
Definition samp_coalition_dist (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :=
  fdistmap (samp_coalition_view C) sampleP.

(** samp_seat_dist_law — the pushforward is the law of the random variable.
    @composes: samp_seat_distE *)
Lemma samp_seat_dist_law (i : 'I_(pi_T' (mp_PI mp)).+1) :
  samp_seat_dist i = `p_ (samp_seat_view i).
Proof. by []. Qed.

(** samp_cut_dist — the law of the cut.
    @intent: the pushforward of sampleP along the cut map. *)
Definition samp_cut_dist : R.-fdist (pgg_gT (mp_M mp)) :=
  fdistmap samp_cut sampleP.

(** samp_cut_dist_image — the law of the cut's permutation image.
    @intent: the pushforward of samp_cut_dist along the representation pgg_rho,
    the carrier in which a SecurityWitness states its bound. *)
Definition samp_cut_dist_image : R.-fdist {perm 'I_(pgg_N' (mp_M mp)).+1} :=
  fdistmap (@pgg_rho (mp_M mp)) samp_cut_dist.

(* The witness's distribution is not a cut law: it lives in the permutation
   image, not in the abstract group the cut is drawn from. Verbatim:
     The term "sw_rho_dist (mp_security mp)" has type
      "{fdist {perm 'I_(pgg_N' (mp_M mp)).+1}}%fdist"
     while it is expected to have type "{fdist pgg_gT (mp_M mp)}%fdist". *)
Fail Definition samp_cut_dist_from_witness : R.-fdist (pgg_gT (mp_M mp)) :=
  sw_rho_dist (mp_security mp).

Section sample_of_static_observation.

Variable content_obs : ep_inputT e
  -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1.

(** samp_static_seat_view — the static observation at seat i as a random
    variable.
    @intent: the sample point mapped to content_obs of its argument at its cut
    and seat i's start. *)
Definition samp_static_seat_view (i : 'I_(pi_T' (mp_PI mp)).+1)
    : {RV sampleP -> 'I_(pgg_N' (mp_M mp)).+1} :=
  fun u => content_obs (samp_arg u) (samp_cut u, tnth (pi_starts (mp_PI mp)) i).

(** samp_static_coalition_view — the static observation restricted to a
    coalition as a random variable.
    @intent: the finfun of static observations on C, ord0 outside C. *)
Definition samp_static_coalition_view (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {RV sampleP -> {ffun 'I_(pi_T' (mp_PI mp)).+1
                      -> 'I_(pgg_N' (mp_M mp)).+1}} :=
  fun u => [ffun i => if i \in C
            then content_obs (samp_arg u)
                   (samp_cut u, tnth (pi_starts (mp_PI mp)) i)
            else ord0].

Hypothesis Hep : forall u : sampleT,
  @epp_endpoints R mp e (samp_arg u) (samp_cut u) P_idx
  = [seq content_obs (samp_arg u) (samp_cut u, tnth (pi_starts (mp_PI mp)) i)
     | i <- epp_players mp].

(** samp_seat_viewE — the executed seat view is the static observation,
    pointwise on the sample space.
    @main correctness: samp_seat_view i = samp_static_seat_view i. *)
Lemma samp_seat_viewE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  samp_seat_view i = samp_static_seat_view i.
Proof. by apply: boolp.funext => u; exact: (epp_seat_endpointE (Hep u) i). Qed.

(** samp_seat_distE — the executed seat law is the static observation's law.
    @main correctness: samp_seat_dist i = fdistmap (samp_static_seat_view i)
    sampleP. *)
Lemma samp_seat_distE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  samp_seat_dist i = fdistmap (samp_static_seat_view i) sampleP.
Proof. by rewrite /samp_seat_dist samp_seat_viewE. Qed.

(** samp_coalition_viewE — the executed coalition view is the static
    observation on C, pointwise on the sample space.
    @main correctness: samp_coalition_view C = samp_static_coalition_view C. *)
Lemma samp_coalition_viewE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  samp_coalition_view C = samp_static_coalition_view C.
Proof.
by apply: boolp.funext => u; exact: (epp_coalition_endpointsE (Hep u) C).
Qed.

(** samp_coalition_distE — the executed coalition law is the static
    observation's law.
    @main correctness: samp_coalition_dist C = fdistmap
    (samp_static_coalition_view C) sampleP. *)
Lemma samp_coalition_distE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  samp_coalition_dist C = fdistmap (samp_static_coalition_view C) sampleP.
Proof. by rewrite /samp_coalition_dist samp_coalition_viewE. Qed.

End sample_of_static_observation.

End sample_adapter.

(******************************************************************************)
(*     PGL(2,7): the exact instance and the finite-word instance              *)
(******************************************************************************)

Section pgl27_distributions.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.
Let sTp : finType := [the finType of (bool * pgg_gT pgl27_M)%type].

(** pgl_epp — the PGL(2,7) execution adapter.
    @intent: run argument bool, both bridges erefl at 7 seats, 7 shares and 8
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

(****************************************************************************)
(*   Exact instance: the landed pgl27P                                      *)
(****************************************************************************)

(* pgl27P R (pgl27_secrecy.v:60) is imported and used as it stands: it is a
   plain Definition in a section over R only, so no local twin is needed. *)

(** pgl_samp_run — layer 1 at pgl27P: the run at a sample point.
    @intent: the PGL(2,7) run whose secret is the sample's first component and
    whose cut is its second. *)
Definition pgl_samp_run (u : sTp) := @samp_run R mpP pgl_epp sTp fst snd 0 u.

(** pgl_samp_seat_view — layer 2 at pgl27P: seat i's endpoint.
    @intent: the endpoint reader of seat i as a random variable over pgl27P. *)
Definition pgl_samp_seat_view (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @samp_seat_view R mpP pgl_epp sTp (pgl27P R) fst snd 0 i.

(** pgl_samp_coalition_view — layer 2 at pgl27P: a coalition's readings.
    @intent: the coalition endpoint reader as a random variable over pgl27P. *)
Definition pgl_samp_coalition_view (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @samp_coalition_view R mpP pgl_epp sTp (pgl27P R) fst snd 0 C.

(** pgl_samp_seat_dist — layer 3 at pgl27P: the law of seat i's endpoint.
    @intent: the pushforward of pgl27P along pgl_samp_seat_view i. *)
Definition pgl_samp_seat_dist (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @samp_seat_dist R mpP pgl_epp sTp (pgl27P R) fst snd 0 i.

(** pgl_samp_coalition_dist — layer 3 at pgl27P: the law of a coalition's
    readings.
    @intent: the pushforward of pgl27P along pgl_samp_coalition_view C. *)
Definition pgl_samp_coalition_dist (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @samp_coalition_dist R mpP pgl_epp sTp (pgl27P R) fst snd 0 C.

(** pgl_samp_seat_distE — the executed seat law at pgl27P is the law of the
    orbit share at the cut image of the seat's start.
    @main correctness: the generic equation at the PGL(2,7) exact instance. *)
Lemma pgl_samp_seat_distE (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pgl_samp_seat_dist i
  = fdistmap (@samp_static_seat_view R mpP pgl_epp sTp (pgl27P R) fst snd
                pgl_content_obs i) (pgl27P R).
Proof. by apply: samp_seat_distE => u; exact: pgl_epp_endpoints. Qed.

(** pgl_samp_coalition_distE — the executed coalition law at pgl27P is the law
    of the orbit shares at the cut images of the coalition's starts.
    @main correctness: the generic coalition equation at the PGL(2,7) exact
    instance. *)
Lemma pgl_samp_coalition_distE (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  pgl_samp_coalition_dist C
  = fdistmap (@samp_static_coalition_view R mpP pgl_epp sTp (pgl27P R) fst snd
                pgl_content_obs C) (pgl27P R).
Proof. by apply: samp_coalition_distE => u; exact: pgl_epp_endpoints. Qed.

(** pgl_witness_is_cut_dist — at a Gen_PGGTypes carrier the witness's
    distribution is a cut law.
    @intent: the type-level coincidence of {perm 'I_8} with pgg_gT pgl27_M. *)
Definition pgl_witness_is_cut_dist : R.-fdist (pgg_gT (mp_M mpP)) :=
  sw_rho_dist (mp_security mpP).

(** pgl_sample_is_witness_prod — the exact sample space is the product of the
    uniform secret prior with the profile's own shuffle distribution.
    @main architecture: pgl27P R = fdist_uniform card_bool `x sw_rho_dist
    (mp_security mpP). *)
Lemma pgl_sample_is_witness_prod :
  pgl27P R
  = ((fdist_uniform card_bool) `x (sw_rho_dist (mp_security mpP)))%fdist.
Proof. by []. Qed.

(****************************************************************************)
(*   Finite-word instance: a secret prior times the word law                *)
(****************************************************************************)

Variable secretP : R.-fdist bool.

(** pglw_wordP — the two-hundred-letter word law over the symmetrized
    generator alphabet.
    @intent: the word_weighted law at length 200 and uniform letters, the
    space rho_word (pgl27_word_privacy.v) is the image of. *)
Definition pglw_wordP : R.-fdist (200.-tuple 'I_5) :=
  @word_weighted R 4 200 (Wuni R).

(** pglw_sampleT — the finite-word sample space.
    @intent: pairs of a secret and a two-hundred-letter word. *)
Definition pglw_sampleT : finType :=
  [the finType of (bool * 200.-tuple 'I_5)%type].

(** pglw_sampleP — the finite-word sample law.
    @intent: the product of the secret prior with the word law. *)
Definition pglw_sampleP : R.-fdist pglw_sampleT :=
  (secretP `x pglw_wordP)%fdist.

(** pglw_cut — the finite-word cut map.
    @intent: the evaluation of the sampled word in PGL(2,7). *)
Definition pglw_cut (u : pglw_sampleT) : pgg_gT (mp_M mpP) :=
  @word_eval pgl27_Msym 200 u.2.

(** pglw_samp_run — layer 1 at the word space.
    @intent: the PGL(2,7) run whose cut is the evaluated word. *)
Definition pglw_samp_run (u : pglw_sampleT) :=
  @samp_run R mpP pgl_epp pglw_sampleT fst pglw_cut 0 u.

(** pglw_samp_seat_view — layer 2 at the word space.
    @intent: seat i's endpoint as a random variable over pglw_sampleP. *)
Definition pglw_samp_seat_view (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @samp_seat_view R mpP pgl_epp pglw_sampleT pglw_sampleP fst pglw_cut 0 i.

(** pglw_samp_seat_dist — layer 3 at the word space.
    @intent: the pushforward of pglw_sampleP along pglw_samp_seat_view i. *)
Definition pglw_samp_seat_dist (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @samp_seat_dist R mpP pgl_epp pglw_sampleT pglw_sampleP fst pglw_cut 0 i.

(** pglw_samp_coalition_dist — layer 3 at the word space, coalition form.
    @intent: the pushforward of pglw_sampleP along the coalition reader. *)
Definition pglw_samp_coalition_dist (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @samp_coalition_dist R mpP pgl_epp pglw_sampleT pglw_sampleP fst pglw_cut 0 C.

(** pglw_samp_seat_distE — the executed seat law under the word shuffle is the
    law of the orbit share at the evaluated word's image of the seat's start.
    @main correctness: the generic equation at the PGL(2,7) finite-word
    instance. *)
Lemma pglw_samp_seat_distE (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pglw_samp_seat_dist i
  = fdistmap (@samp_static_seat_view R mpP pgl_epp pglw_sampleT pglw_sampleP
                fst pglw_cut pgl_content_obs i) pglw_sampleP.
Proof. by apply: samp_seat_distE => u; exact: pgl_epp_endpoints. Qed.

(** pglw_cut_dist_word — the word instance's cut law is the landed word
    shuffle law.
    @main architecture: fdistmap pglw_cut pglw_sampleP = rho_word R. *)
Lemma pglw_cut_dist_word :
  @samp_cut_dist R mpP pglw_sampleT pglw_sampleP pglw_cut = rho_word R.
Proof.
rewrite /samp_cut_dist /pglw_cut /pglw_sampleP.
rewrite -(fdistmap_comp (@word_eval pgl27_Msym 200) snd).
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

End pgl27_distributions.

(******************************************************************************)
(*     Five card: the exact instance over the den Boer sample space           *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_distributions.

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

(****************************************************************************)
(*   Exact instance: the landed den Boer sample space                       *)
(****************************************************************************)

(* five_card_leakage.P R over five_card_leakage.Omega = bool * bool * 'I_5 is
   imported and used as it stands (denboer_trace.v:100 abbreviates it dbP).
   The argument map is the projection to the committed pair; the cut map is the
   rotation power fc_sigma ^+ k, which is NOT a projection. *)

(** fc_samp_arg — the committed pair of a den Boer sample point.
    @intent: the first component of bool * bool * 'I_5. *)
Definition fc_samp_arg (u : five_card_leakage.Omega) : (bool * bool)%type :=
  u.1.

(** fc_samp_cut — the cut of a den Boer sample point.
    @intent: the rotation fc_sigma ^+ k realizing the sampled rotation k. *)
Definition fc_samp_cut (u : five_card_leakage.Omega) : pgg_gT (mp_M mpF) :=
  (five_card_group.fc_sigma ^+ u.2)%g.

(** fc_samp_run — layer 1 at the den Boer space: the run at a sample point.
    @intent: the five-card run at the sampled committed pair and rotation. *)
Definition fc_samp_run (u : five_card_leakage.Omega) :=
  @samp_run R mpF fc_epp five_card_leakage.Omega fc_samp_arg fc_samp_cut 0 u.

(** fc_samp_seat_view — layer 2 at the den Boer space: seat i's endpoint.
    @intent: the endpoint reader of seat i as a random variable over P. *)
Definition fc_samp_seat_view (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @samp_seat_view R mpF fc_epp five_card_leakage.Omega (five_card_leakage.P R)
    fc_samp_arg fc_samp_cut 0 i.

(** fc_samp_coalition_view — layer 2 at the den Boer space: a coalition's
    readings.
    @intent: the coalition endpoint reader as a random variable over P. *)
Definition fc_samp_coalition_view (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @samp_coalition_view R mpF fc_epp five_card_leakage.Omega
    (five_card_leakage.P R) fc_samp_arg fc_samp_cut 0 C.

(** fc_samp_seat_dist — layer 3 at the den Boer space: the law of seat i's
    endpoint.
    @intent: the pushforward of P along fc_samp_seat_view i. *)
Definition fc_samp_seat_dist (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @samp_seat_dist R mpF fc_epp five_card_leakage.Omega (five_card_leakage.P R)
    fc_samp_arg fc_samp_cut 0 i.

(** fc_samp_coalition_dist — layer 3 at the den Boer space, coalition form.
    @intent: the pushforward of P along fc_samp_coalition_view C. *)
Definition fc_samp_coalition_dist (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @samp_coalition_dist R mpF fc_epp five_card_leakage.Omega
    (five_card_leakage.P R) fc_samp_arg fc_samp_cut 0 C.

(** fc_samp_seat_distE — the executed seat law at the den Boer space is the law
    of the layout entry at the rotation image of the seat's start.
    @main correctness: the generic equation at the five-card exact instance. *)
Lemma fc_samp_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  fc_samp_seat_dist i
  = fdistmap (@samp_static_seat_view R mpF fc_epp five_card_leakage.Omega
       (five_card_leakage.P R) fc_samp_arg fc_samp_cut fc_content_obs i)
      (five_card_leakage.P R).
Proof.
apply: samp_seat_distE => -[[a b] k]; exact: fc_epp_endpoints.
Qed.

(** fc_samp_coalition_distE — the executed coalition law at the den Boer space
    is the law of the layout entries at the rotation images of its starts.
    @main correctness: the generic coalition equation at the five-card exact
    instance. *)
Lemma fc_samp_coalition_distE (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  fc_samp_coalition_dist C
  = fdistmap (@samp_static_coalition_view R mpF fc_epp five_card_leakage.Omega
       (five_card_leakage.P R) fc_samp_arg fc_samp_cut fc_content_obs C)
      (five_card_leakage.P R).
Proof.
apply: samp_coalition_distE => -[[a b] k]; exact: fc_epp_endpoints.
Qed.

(** fc_witness_is_cut_dist — at the five-card Gen_PGGTypes carrier the
    witness's distribution is a cut law.
    @intent: the type-level coincidence of {perm 'I_5} with pgg_gT
    FiveCardKim_M. The sample space's own cut law fc_samp_cut_dist is a
    separate object; no equality between them is claimed. *)
Definition fc_witness_is_cut_dist : R.-fdist (pgg_gT (mp_M mpF)) :=
  sw_rho_dist (mp_security mpF).

(** fc_samp_cut_dist — the den Boer sample space's cut law.
    @intent: the pushforward of P along the rotation power map. *)
Definition fc_samp_cut_dist :=
  @samp_cut_dist R mpF five_card_leakage.Omega (five_card_leakage.P R)
    fc_samp_cut.

End fivecard_distributions.

Print Assumptions samp_seat_distE.
Print Assumptions samp_coalition_distE.
Print Assumptions pgl_samp_seat_distE.
Print Assumptions pgl_samp_coalition_distE.
Print Assumptions pglw_samp_seat_distE.
Print Assumptions pglw_cut_dist_word.
Print Assumptions fc_samp_seat_distE.
Print Assumptions fc_samp_coalition_distE.
Print Assumptions pgl_sample_is_witness_prod.

(******************************************************************************)
(*     Profile, adapter, model parameter: where each input comes from         *)
(*                                                                            *)
(*  sample space (sampleT)     ADAPTER (sample adapter, Variable sampleT).    *)
(*    Neither the profile nor the EPP names it. At PGL it is bool * pgg_gT    *)
(*    pgl27_M; at five card it is five_card_leakage.Omega = bool * bool *     *)
(*    'I_5; at the word instance bool * 200.-tuple 'I_5.                      *)
(*                                                                            *)
(*  secret / input prior       MODEL PARAMETER. At PGL the exact instance     *)
(*    fixes fdist_uniform card_bool inside pgl27P; the word instance takes it *)
(*    as the Variable secretP. mp_secretT gives only the TYPE of the secret,  *)
(*    never a law on it.                                                      *)
(*                                                                            *)
(*  cut / shuffle distribution PROFILE at PGL, MODEL PARAMETER elsewhere.     *)
(*    mp_security carries sw_rho_dist, and pgl_sample_is_witness_prod shows   *)
(*    pgl27P's second factor IS that field. The word law rho_word and the den *)
(*    Boer rotation law are not read off the profile: sw_asymptotic is the    *)
(*    only slot that mentions word length, and it carries sa_rho_L : nat ->   *)
(*    R.-fdist {perm _}, again in the permutation carrier.                    *)
(*                                                                            *)
(*  arg map (samp_arg)         ADAPTER (sample adapter). fst at PGL and at    *)
(*    the word space, u.1 at five card.                                       *)
(*                                                                            *)
(*  cut map (samp_cut)         ADAPTER (sample adapter). snd at PGL,          *)
(*    fc_sigma ^+ u.2 at five card, word_eval u.2 at the word space. It is    *)
(*    not a projection in two of the three, so no product shape can replace   *)
(*    it.                                                                     *)
(*                                                                            *)
(*  fuel                       ADAPTER (EPP, ep_fuel). pgl27_fuel and 100.    *)
(*                                                                            *)
(*  process index (P_idx)      ADAPTER (sample adapter, Variable P_idx).      *)
(*                                                                            *)
(*  content readout            ADAPTER (EPP, ep_content), with the static     *)
(*    twin content_obs a Variable of the observation subsection; both are     *)
(*    derived from the profile's plug at the two instances (ts_encode         *)
(*    orbit_scheme, den_boer_layout).                                         *)
(*                                                                            *)
(*  trace functions            ADAPTER (sample adapter, layer 2). Determined  *)
(*    by e, samp_arg, samp_cut, P_idx; no profile field names them.           *)
(*                                                                            *)
(*  pushforward                ADAPTER (sample adapter, layer 3), fdistmap    *)
(*    of a layer-2 function along sampleP, which is proba.v's `p_ (see        *)
(*    samp_seat_dist_law).                                                    *)
(*                                                                            *)
(*  sw_rho_dist verdict        The witness's distribution CANNOT serve as a   *)
(*    cut law at a general profile: samp_cut_dist_from_witness is a Fail      *)
(*    Definition, {fdist {perm 'I_(pgg_N' (mp_M mp)).+1}} against {fdist      *)
(*    pgg_gT (mp_M mp)}. The connecting map is the representation:            *)
(*    samp_cut_dist_image = fdistmap (pgg_rho (mp_M mp)) samp_cut_dist sends  *)
(*    a cut law to the witness's carrier. At every Gen_PGGTypes instance the  *)
(*    group IS the permutation group and the two carriers coincide by         *)
(*    conversion (pgl_witness_is_cut_dist, fc_witness_is_cut_dist), so the    *)
(*    mismatch bites only for a profile whose monodromy is a proper           *)
(*    representation of an abstract group.                                    *)
(******************************************************************************)
