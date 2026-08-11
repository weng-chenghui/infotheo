(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-C: the execution adapter at pgl27_profile                          *)
(*                                                                            *)
(* EPP is the probe-local execution adapter over a MonodromyProfile: the run  *)
(* argument type, the two count bridges of probe_b_count_bridge.v, the        *)
(* content readout, the input processes and the fuel. Section                 *)
(* execution_of_profile derives, from the record alone, the six register      *)
(* entries probe_a_sufficiency.v had to assume (players, input identifiers,   *)
(* dealer, process lists, run, endpoints) plus the endpoint decoder.          *)
(*                                                                            *)
(* Section pgl27_execution fills the record at pgl27_profile R and proves the *)
(* derived process list equal to the landed pgl27_procs, then transports the  *)
(* three landed end-to-end facts (termination, endpoints, executed recovery)  *)
(* along that equality.                                                       *)
(*                                                                            *)
(* Notes carried to P-D and P-H (not statements, design record):              *)
(*                                                                            *)
(*  1. ep_content and ep_input_procs take the record argument IMPLICITLY:     *)
(*     their declared types mention ep_inputT e, and Unset Strict Implicit    *)
(*     makes e inferable, so call sites read e.(ep_content) / @ep_content _ _ *)
(*     e, never ep_content e.                                                 *)
(*  2. epp_players discharges with mp EXPLICIT (mp occurs only in the return  *)
(*     type) while every construction depending on e discharges with R, mp    *)
(*     and e implicit; the instantiations below spell @ everywhere.           *)
(*  3. The two candidate content readouts (the scheme's share readout and the *)
(*     bridge-2 transported readout epp_content_from_plug) are NOT            *)
(*     convertible: they differ by cast_ord (ep_cards_bridge e), which is a   *)
(*     constructor application, not the identity. pgl_epp_contentE proves     *)
(*     them propositionally equal, at the cost of functional extensionality.  *)
(*     ep_content must therefore hold the share readout, since the process    *)
(*     equality against the landed dealer is a conversion.                    *)
(*  4. Transporting a landed run fact along a fuel MISMATCH does not fail, it *)
(*     diverges: conversion unfolds both run_interp applications. The fuel    *)
(*     must be identified by a statement-level equation before the landed     *)
(*     lemma is applied (see probe_c_mutation.v).                             *)
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
(*     The execution adapter                                                  *)
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
(*     The run derived from the adapter                                       *)
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
(* As-built correction (probe P-D): offset .+2 -> .+3. Seats occupy ids 2
   through (pi_T' _).+2, so the first free id is (pi_T' _).+3; at the
   five-card carrier .+2 yields [:: 6; 7] where the landed dealer passes
   [:: 7; 8], making the process equality false. PGL is insensitive: its
   input list is empty and iota _ 0 = [::] at every offset. *)
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
    @composes: pgl_epp_run_recovers *)
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

End execution_of_profile.

(******************************************************************************)
(*     The adapter filled at pgl27_profile                                    *)
(******************************************************************************)

Section pgl27_execution.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_epp — the PGL(2,7) execution adapter.
    @intent: run argument bool, both bridges erefl at 7 seats, 7 shares and 8
    cards, content the shares ts_encode orbit_scheme s of the dealt orbit
    secret, no input processes, fuel pgl27_fuel. *)
Definition pgl_epp : EPP mpP :=
  @MkEPP R mpP bool erefl erefl
    (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) pgl27_fuel.

(** pgl_epp_contentE — the two PGL(2,7) content readouts agree.
    @main architecture: the share readout ep_content pgl_epp s and the
    bridge-2 transported readout epp_content_from_plug pgl_epp s are equal as
    functions. *)
Lemma pgl_epp_contentE (s : bool) :
  pgl_epp.(ep_content) s = @epp_content_from_plug R mpP pgl_epp s.
Proof.
rewrite /epp_content_from_plug.
by apply: funext => c; apply: funext => i; rewrite cast_ord_id.
Qed.

(** pgl_epp_playersE — the derived participant list is the instance's list.
    @composes: pgl_epp_procsE *)
Lemma pgl_epp_playersE : @epp_players R mpP = pgl27_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(* The only difference between the two dealers is the participant list, since
   the adapter's input identifiers iota 9 0 and its empty input-process list
   both reduce to [::]. Hence one rewrite of the participant list, then
   conversion. No vm_compute: the goal carries process terms only. *)

(** pgl_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs pgl_epp s w0 0 = pgl27_procs s w0. *)
Lemma pgl_epp_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_procs R mpP pgl_epp s w0 0 = pgl27_procs s w0.
Proof.
rewrite /epp_procs /pgl27_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /pgl27_saprocs /pgl27_dealer_run.
by rewrite pgl_epp_playersE.
Qed.

(** pgl_epp_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run pgl_epp s w0 0).1 = nseq 10 Finish, for any
    cut w0. *)
Lemma pgl_epp_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@epp_run R mpP pgl_epp s w0 0).1 = nseq 10 Finish.
Proof. by rewrite /epp_run pgl_epp_procsE; exact: pgl27_run_terminates. Qed.

(** pgl_epp_endpoints — the derived verifier endpoints are the dealt shares at
    the cut.
    @main correctness: epp_endpoints pgl_epp s w0 0 is the shares of s read at
    the cut image of each starting position, one per seat. *)
Lemma pgl_epp_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_endpoints R mpP pgl_epp s w0 0
  = [seq tnth (ts_encode orbit_scheme s)
        (@pgg_rho (mp_M mpP) w0 (tnth (pi_starts (mp_PI mpP)) i))
     | i <- @epp_players R mpP].
Proof.
rewrite /epp_endpoints /epp_run pgl_epp_procsE; exact: pgl27_endpoints.
Qed.

(** pgl_epp_endpoints_size — the derived run collects one endpoint per seat.
    @composes: pgl_epp_run_recovers *)
Lemma pgl_epp_endpoints_size (s : bool) (w0 : pgg_gT pgl27_M) :
  size (@epp_endpoints R mpP pgl_epp s w0 0) = (pi_T' (mp_PI mpP)).+1.
Proof.
rewrite /epp_endpoints /epp_run pgl_epp_procsE; exact: pgl27_endpoints_size.
Qed.

(** pgl_epp_decodeE — the adapter's decoder is the instance's reconstruction.
    @composes: pgl_epp_run_recovers *)
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

(** pgl_epp_run_recovers — the derived run reconstructs the dealt secret.
    @main correctness: decoding the executed endpoints of epp_run pgl_epp
    through epp_decode returns the dealt orbit secret s, for any cut w0 in the
    group. *)
Lemma pgl_epp_run_recovers (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  @epp_decode R mpP pgl_epp (@epp_endpoints R mpP pgl_epp s w0 0)
    (pgl_epp_endpoints_size s w0) = s.
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (H1 : size ep = (pi_T' (mp_PI mpP)).+1),
    ep = endpoints_of_trace
           (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1) ->
    @epp_decode R mpP pgl_epp ep H1 = s.
  move=> ep H1 Hep.
  move: H1; rewrite Hep => H1.
  rewrite (pgl_epp_decodeE H1 (pgl27_endpoints_size s w0)).
  exact: (pgl27_run_recovers s Hw0).
apply: Hgoal.
by rewrite /epp_endpoints /epp_run pgl_epp_procsE.
Qed.

End pgl27_execution.

Print Assumptions pgl_epp_procsE.
Print Assumptions pgl_epp_run_recovers.
