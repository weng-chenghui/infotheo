(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_exec: the two ExecutionPlug values of the S_5 instance                  *)
(*                                                                            *)
(* The five-seat adjacent-transposition instance carries two execution plugs  *)
(* over the same profile s5_profile. The deterministic plug takes the dealt   *)
(* position 'I_5 as its run argument and reads the canonical shares           *)
(* ts_encode s5_scheme; the randomized plug takes the sampler tape            *)
(* 'rV['Z_5]_5 and reads the probability-free additive layout of that tape.   *)
(* Both use the participant list s5_run.s5_players and fuel 150. The two      *)
(* process lists are not equal: they share the profile and the seven-process  *)
(* session skeleton, and their dealt contents differ.                         *)
(*                                                                            *)
(* The run skeleton s5_aprocs_cut generalizes s5_trace.s5_aprocs_abs to an    *)
(* arbitrary cut, its identity cut giving s5_trace.s5_aprocs_abs back. Fed    *)
(* the layout of a tape it is s5_rprocs_cut, whose identity cut is            *)
(* s5_trace.s5_rprocs.                                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_exec_plug        == the deterministic execution plug over s5_profile  *)
(*   s5_content_obs      == the deterministic static observation: the share   *)
(*                          of the dealt position at the cut image of a       *)
(*                          starting position                                 *)
(*   s5_observed         == the ObservedExecution packing the deterministic   *)
(*                          plug, its static observation and its three run    *)
(*                          facts at process offset 0                         *)
(*   s5_rfree_share      == the j-th additive share of a tape, stated without *)
(*                          a realType                                        *)
(*   s5_rfree_layout     == the dealt layout of a tape                        *)
(*   s5_codec, s5_decodec == the identity codec between the 'Z_5 tape secret  *)
(*                          and the profile secret carrier 'I_5               *)
(*   s5_tape_secret      == coordinate 0 of a tape                            *)
(*   s5_aprocs_cut       == the seven-process skeleton at an abstract content *)
(*                          readout and an arbitrary cut                      *)
(*   s5_rprocs_cut       == that skeleton at the layout of a tape             *)
(*   s5_rand_exec_plug   == the randomized execution plug over s5_profile     *)
(*   s5_rcontent_obs     == the randomized static observation                 *)
(*   s5_rand_observed    == the ObservedExecution of the randomized plug      *)
(*                                                                            *)
(* Key results, one entry per @main declaration:                              *)
(*   s5_exec_endpoint_count == the deterministic run collects five endpoints  *)
(*   s5_exec_recovers    == the deterministic run decodes to the dealt        *)
(*                          position                                          *)
(*   s5_exec_correct     == termination, endpoint count and recovery of the   *)
(*                          deterministic run                                 *)
(*   s5_observed_recovers == the same recovery through the packaged           *)
(*                          observed execution                                *)
(*   s5_exec_seat_endpointE == seat i's endpoint is the share at the cut      *)
(*                          image of seat i's start                           *)
(*   s5_exec_coalition_endpointsE == a coalition's endpoint readings are the  *)
(*                          shares at the cut images of its seats             *)
(*   s5_exec_verifier_traceE == the derived verifier row is the verifier row  *)
(*                          of s5_procs                                       *)
(*   s5_exec_raw_traceE  == the derived raw seat trace is the trace of        *)
(*                          s5_procs at the seat's process identifier         *)
(*   s5_exec_seat_countE == the profile's seat index type is 'I_5             *)
(*   s5_codecK, s5_decodecK == the two carriers of the secret are identified  *)
(*                          by the codec                                      *)
(*   s5_tape_secretE     == the tape secret is the randomized sharing's       *)
(*                          secret                                            *)
(*   s5_rprocs_cut1      == the identity cut specializes to s5_rprocs         *)
(*   s5_rand_run_recovers == reconstruction returns the tape secret           *)
(*   s5_rand_endpoint_count == the randomized run collects five endpoints     *)
(*   s5_rand_exec_recovers == the randomized run decodes to the encoded tape  *)
(*                          secret                                            *)
(*   s5_rand_correct     == termination, endpoint count and recovery of the   *)
(*                          randomized run                                    *)
(*   s5_rand_observed_recovers == the same recovery through the packaged      *)
(*                          observed execution                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_raag_s5 pgg_raag_path s5_profile s5_run.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy s5_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(* Both s5_run and s5_trace declare a participant list named s5_players, so
   every occurrence below is written qualified. *)

Section s5_execution.

(** s5_M — the S_5 adjacent-transposition monodromy template at N = 5.
    @intent: the Gen_PGGTypes form s5_PI and s5_plug carry, spelled out here
    because the instance files keep it section-local. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

Let mpS : MonodromyProfile := s5_profile.

(* The participant list s5_run.s5_players is the five seats written as
   explicit ordinals. It is a reduction cache: the interpreter facts below are
   closed by vm_compute on the process list this literal builds, and enum
   'I_5 in its place leaves an unreduced enumeration inside the run. The fuel
   150 is pinned for the same reason, the termination and endpoint facts being
   computed at that fuel. *)

(** s5_players_enumE — the five-element participant list is the seat
    enumeration.
    @composes: s5_exec_endpoints, s5_rand_run_recovers *)
Lemma s5_players_enumE :
  s5_run.s5_players = enum 'I_(pi_T' (mp_PI mpS)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(******************************************************************************)
(*     The deterministic correctness plug                                     *)
(******************************************************************************)

(** s5_exec_plug — the S_5 deterministic execution plug.
    @intent: the execution layer over s5_profile with run argument the dealt
    position 'I_5, the seat/share bridge erefl at 5 seats and 5 shares,
    participant list s5_run.s5_players, content the shares
    ts_encode s5_scheme s of the dealt position s and fuel 150; the
    dealer-secret constructor fixes the input-process list to the empty
    list. *)
Definition s5_exec_plug : ExecutionPlug mpS :=
  @dealer_secret_plug mpS 'I_5 erefl s5_run.s5_players s5_players_enumE
    (fun s _ => tnth (ts_encode s5_scheme s)) 150.

(** s5_content_obs — the S_5 deterministic static observation.
    @intent: the share of the position s at the cut image of a starting
    position, namely tnth (ts_encode s5_scheme s) (pgg_rho w0 p). *)
Definition s5_content_obs (s : 'I_5)
    (p : pgg_gT (mp_M mpS) * 'I_(pgg_N' (mp_M mpS)).+1)
    : 'I_(pgg_N' (mp_M mpS)).+1 :=
  tnth (ts_encode s5_scheme s) (@pgg_rho (mp_M mpS) p.1 p.2).

(** s5_exec_procsE — the derived process list is the instance's process list.
    @composes: s5_exec_terminates, s5_exec_endpoints, s5_exec_recon *)
Lemma s5_exec_procsE (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_procs mpS s5_exec_plug s w0 0 = s5_procs s w0.
Proof. by []. Qed.

(** s5_exec_fuelE — the plug's fuel is the fuel of the instance's run facts.
    @composes: s5_exec_terminates, s5_exec_endpoints, s5_exec_recon *)
Lemma s5_exec_fuelE : ep_fuel s5_exec_plug = 150.
Proof. by []. Qed.

(** s5_exec_playersE — the plug's participant list is the instance's list.
    @composes: s5_exec_endpoints *)
Lemma s5_exec_playersE : ep_players s5_exec_plug = s5_run.s5_players.
Proof. by []. Qed.

(** s5_exec_procs_size — the derived run has seven processes.
    @composes: s5_exec_terminates *)
Lemma s5_exec_procs_size (s : 'I_5) (w0 : pgg_gT s5_M) :
  size (@exec_procs mpS s5_exec_plug s w0 0) = 7.
Proof. by []. Qed.

(** s5_exec_terminates — every process of the deterministic run reaches
    Finish.
    @composes: s5_observed, s5_exec_correct *)
Lemma s5_exec_terminates (s : 'I_5) (w0 : pgg_gT s5_M) :
  (@exec_run mpS s5_exec_plug s w0 0).1
  = nseq (size (@exec_procs mpS s5_exec_plug s w0 0)) Finish.
Proof.
rewrite s5_exec_procs_size /exec_run s5_exec_fuelE s5_exec_procsE.
exact: s5_run_terminates.
Qed.

(** s5_exec_endpoints — the deterministic verifier endpoints are the static
    observation over the seats.
    @composes: s5_exec_recon, s5_observed, s5_exec_correct *)
Lemma s5_exec_endpoints (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_endpoints mpS s5_exec_plug s w0 0
  = @exec_static_endpoints mpS s5_exec_plug s5_content_obs s w0.
Proof.
rewrite /exec_endpoints /exec_run s5_exec_fuelE s5_exec_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5_exec_playersE s5_players_enumE.
exact: s5_endpoints.
Qed.

(** s5_exec_endpoint_count — the deterministic run collects five endpoints.
    @main correctness: size (exec_endpoints s5_exec_plug s w0 0) = 5. *)
Lemma s5_exec_endpoint_count (s : 'I_5) (w0 : pgg_gT s5_M) :
  size (@exec_endpoints mpS s5_exec_plug s w0 0) = 5.
Proof. by rewrite (exec_endpoints_size (s5_exec_endpoints s w0)). Qed.

(** s5_exec_decodeE — the plug's decoder is the instance's reconstruction.
    @composes: s5_exec_recon *)
Lemma s5_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpS)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpS)).+1)
    (Hsz' : size ep = (ts_T' s5_scheme).+1) :
  @exec_decode mpS s5_exec_plug ep Hsz
  = ts_recon s5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5_exec_recon — decoding the static observation returns the dealt position,
    for any cut in the group and any proof of the endpoint count.
    @composes: s5_observed, s5_exec_recovers *)
Lemma s5_exec_recon (s : 'I_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  forall Hsz : size (@exec_static_endpoints mpS s5_exec_plug
                       s5_content_obs s w0)
               = (pi_T' (mp_PI mpS)).+1,
  @exec_decode mpS s5_exec_plug
    (@exec_static_endpoints mpS s5_exec_plug s5_content_obs s w0) Hsz = s.
Proof.
move=> Hw0.
rewrite -s5_exec_endpoints /exec_endpoints /exec_run s5_exec_fuelE
        s5_exec_procsE /exec_verifier_id => Hsz.
rewrite (s5_exec_decodeE Hsz (s5_endpoints_size s w0)).
exact: (s5_run_recovers s Hw0).
Qed.

(* Recovery is exported in three forms per plug, as at the other instances:
   the standalone equation below, the third conjunct of the combined statement
   s5_exec_correct, and the same equation with the size proof taken from the
   observed-execution record in s5_observed_recovers. The three are convertible
   and each is the form one client layer expects. *)

(** s5_exec_recovers — the deterministic run decodes to the dealt position.
    @main correctness: exec_decode of the executed endpoints of the run of
    s5_exec_plug at position s and cut w0 is s, for any cut w0 in the
    group. *)
Theorem s5_exec_recovers (s : 'I_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_exec_plug
    (@exec_endpoints mpS s5_exec_plug s w0 0)
    (exec_endpoints_size (s5_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers mpS s5_exec_plug s5_content_obs (fun s : 'I_5 => s)
          s w0 0 (s5_exec_endpoints s w0) (s5_exec_recon Hw0)).
Qed.

(** s5_exec_correct — termination, endpoint count and recovery of the
    deterministic run.
    @main correctness: the run of s5_exec_plug reaches Finish at each of its
    seven processes, collects one endpoint per seat, and decodes to the dealt
    position s, for any cut w0 in the group. *)
Theorem s5_exec_correct (s : 'I_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  [/\ (@exec_run mpS s5_exec_plug s w0 0).1
        = nseq (size (@exec_procs mpS s5_exec_plug s w0 0)) Finish,
      size (@exec_endpoints mpS s5_exec_plug s w0 0)
        = (pi_T' (mp_PI mpS)).+1 &
      @exec_decode mpS s5_exec_plug
        (@exec_endpoints mpS s5_exec_plug s w0 0)
        (exec_endpoints_size (s5_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct mpS s5_exec_plug s5_content_obs (fun s : 'I_5 => s)
          s w0 0 (s5_exec_terminates s w0) (s5_exec_endpoints s w0)
          (s5_exec_recon Hw0)).
Qed.

(** s5_observed — the S_5 deterministic observed execution.
    @intent: s5_profile with plug s5_exec_plug at process offset 0, static
    observation s5_content_obs and expected value the dealt position; the
    three run facts are s5_exec_terminates, s5_exec_endpoints and
    s5_exec_recon. *)
Definition s5_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpS s5_exec_plug 0
    s5_content_obs (fun s : 'I_5 => s)
    s5_exec_terminates s5_exec_endpoints (@s5_exec_recon).

(** s5_observed_recovers — the packaged deterministic run decodes to the dealt
    position.
    @main correctness: exec_decode of the executed endpoints of s5_observed at
    position s and cut w0 is s, for any cut w0 in the group. *)
Theorem s5_observed_recovers (s : 'I_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_exec_plug
    (@exec_endpoints mpS s5_exec_plug s w0 0)
    (OE.oe_endpoints_size s5_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers s5_observed s w0 Hw0). Qed.

(******************************************************************************)
(*     The observer types read off the deterministic plug                     *)
(******************************************************************************)

(** s5_exec_seat_endpointE — seat i's endpoint is the share at the cut image of
    seat i's start.
    @main correctness: exec_seat_endpoint s5_exec_plug s w0 0 i =
    s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i). *)
Lemma s5_exec_seat_endpointE (s : 'I_5) (w0 : pgg_gT s5_M)
    (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @exec_seat_endpoint mpS s5_exec_plug s w0 0 i
  = s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i).
Proof. exact: (exec_seat_endpointE (s5_exec_endpoints s w0) i). Qed.

(** s5_exec_coalition_endpointsE — a coalition's endpoint readings are the
    shares at the cut images of its seats.
    @main correctness: the finfun sends a seat in C to the share of s at the
    cut image of that seat's start, and every seat outside C to ord0. *)
Lemma s5_exec_coalition_endpointsE (s : 'I_5) (w0 : pgg_gT s5_M)
    (C : {set 'I_(pi_T' (mp_PI mpS)).+1}) :
  @exec_coalition_endpoints mpS s5_exec_plug s w0 0 C
  = [ffun i => if i \in C
               then s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (s5_exec_endpoints s w0) C). Qed.

(** s5_exec_verifier_traceE — the derived verifier row is the verifier row of
    s5_procs.
    @main architecture: exec_verifier_trace s5_exec_plug s w0 0 = nth [::]
    (run_interp 150 (s5_procs s w0)).2 1. *)
Lemma s5_exec_verifier_traceE (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_verifier_trace mpS s5_exec_plug s w0 0
  = nth [::] (run_interp 150 (s5_procs s w0)).2 1.
Proof.
by rewrite /exec_verifier_trace /exec_run s5_exec_fuelE s5_exec_procsE.
Qed.

(** s5_exec_raw_traceE — the derived raw seat trace is the trace of s5_procs at
    the seat's process identifier.
    @main architecture: exec_participant_trace s5_exec_plug s w0 0 i = nth [::]
    (run_interp 150 (s5_procs s w0)).2 (2 + i). *)
Lemma s5_exec_raw_traceE (s : 'I_5) (w0 : pgg_gT s5_M)
    (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @exec_participant_trace mpS s5_exec_plug s w0 0 i
  = nth [::] (run_interp 150 (s5_procs s w0)).2 (2 + i).
Proof.
by rewrite /exec_participant_trace /exec_seat_id /exec_run s5_exec_fuelE
   s5_exec_procsE.
Qed.

(** s5_exec_seat_countE — the profile's seat index type is 'I_5.
    @main architecture: (pi_T' (mp_PI mpS)).+1 = 5, the seat index type shared
    by the execution layer and the five-seat coalition view. *)
Lemma s5_exec_seat_countE : (pi_T' (mp_PI mpS)).+1 = 5.
Proof. by []. Qed.

(******************************************************************************)
(*     The probability-free additive layout                                   *)
(******************************************************************************)

(** s5_rfree_share — the j-th additive share of a sampler tape, stated without
    a realType.
    @intent: coordinate j+1 of the tape for j below the last index, and the
    residue of coordinate 0 against the first four coordinates at the last
    index. *)
Definition s5_rfree_share (j : 'I_5) (u : 'rV['Z_5]_5) : 'Z_5 :=
  if unlift ord_max j is Some j' then u ord0 (lift ord0 j')
  else (u ord0 ord0 - \sum_(i < 4) u ord0 (lift ord0 i))%R.

(** s5_rfree_shareE — the probability-free share is the randomized sharing's
    share, at every realType.
    @composes: s5_rfree_layoutE *)
Lemma s5_rfree_shareE (R : realType) (j : 'I_5) :
  rsh_share (@unif_randomized_sharing R 3 4) j = s5_rfree_share j.
Proof.
apply: boolp.funext => u; rewrite /s5_rfree_share /rsh_share.
by case: (unlift ord_max j) => [k|] //=; rewrite sumrRVE.
Qed.

(** s5_rfree_layout — the dealt layout at a tape: position i carries share i.
    @intent: the probability-free twin of s5_trace.s5_rlayout. *)
Definition s5_rfree_layout (u : 'rV['Z_5]_5) : 5.-tuple 'I_5 :=
  [tuple s5_rfree_share i u | i < 5].

(** s5_rfree_layoutE — the probability-free layout is the randomized layout.
    @composes: s5_rprocs_cut1 *)
Lemma s5_rfree_layoutE (R : realType) (u : 'rV['Z_5]_5) :
  s5_rlayout R u = s5_rfree_layout u.
Proof.
apply: eq_from_tnth => i; rewrite /s5_rlayout /s5_rfree_layout !tnth_mktuple.
by rewrite /s5_rs s5_rfree_shareE.
Qed.

(** s5_rfree_sum — the five shares of a tape sum to the tape's secret
    coordinate.
    @composes: s5_rfree_valid *)
Lemma s5_rfree_sum (u : 'rV['Z_5]_5) :
  (\sum_(i < 5) s5_rfree_share i u)%R = u ord0 ord0.
Proof.
have Hw : forall i : 'I_4, widen_ord (leqnSn 4) i = lift ord_max i.
  by move=> i; apply: val_inj; symmetry; exact: lift_max.
rewrite big_ord_recr /=.
under eq_bigr do rewrite Hw /s5_rfree_share liftK.
rewrite /s5_rfree_share unlift_none /=.
by rewrite GRing.addrC GRing.subrK.
Qed.

(** zp5_sum_val — the residue of a natural sum of Z/5 values is the value of
    their ring sum.
    @composes: s5_rfree_valid *)
Lemma zp5_sum_val (n : nat) (f : 'I_n -> 'Z_5) :
  (\sum_(i < n) (f i : nat)) %% 5 = ((\sum_(i < n) f i)%R : 'Z_5) :> nat.
Proof.
rewrite -(@val_Zp_nat 5 isT) GRing.natr_sum.
by under eq_bigr do rewrite natr_Zp.
Qed.

(** s5_rfree_valid — the probability-free layout is a valid sum-mod sharing of
    the tape's secret coordinate.
    @composes: s5_rand_run_recovers *)
Lemma s5_rfree_valid (u : 'rV['Z_5]_5) :
  ts_valid s5_scheme (u ord0 ord0) (s5_rfree_layout u).
Proof.
rewrite /s5_scheme /sum_mod_scheme /ts_valid /sum_mod_valid_pred.
under eq_bigr do rewrite tnth_mktuple.
by rewrite zp5_sum_val s5_rfree_sum.
Qed.

(******************************************************************************)
(*     The ordinal codec between the randomized secret and the profile secret *)
(******************************************************************************)

(** s5_codec — the codec from the Z/5 tape secret to the profile secret
    carrier 'I_5.
    @intent: the identity, the two carriers being the same ordinal type
    ('Z_5 = 'I_(Zp_trunc 5).+2 = 'I_5). *)
Definition s5_codec (z : 'Z_5) : 'I_5 := z.

(** s5_decodec — the codec from the profile secret carrier back to Z/5.
    @intent: the identity in the other direction. *)
Definition s5_decodec (i : 'I_5) : 'Z_5 := i.

(** s5_codecK — decoding cancels encoding.
    @main architecture: cancel s5_codec s5_decodec, one half of the identity
    of the randomized secret carrier with the profile secret carrier. *)
Lemma s5_codecK : cancel s5_codec s5_decodec.
Proof. by []. Qed.

(** s5_decodecK — encoding cancels decoding.
    @main architecture: cancel s5_decodec s5_codec, the other half of that
    identity. *)
Lemma s5_decodecK : cancel s5_decodec s5_codec.
Proof. by []. Qed.

(** s5_tape_secret — the secret coordinate of a sampler tape.
    @intent: coordinate 0 of the tape, the value the additive sharing
    shares. *)
Definition s5_tape_secret (u : 'rV['Z_5]_5) : 'Z_5 := u ord0 ord0.

(** s5_tape_secretE — the tape secret is the randomized sharing's secret, at
    every realType.
    @main architecture: rsh_secret (unif_randomized_sharing R 3 4) =
    s5_tape_secret, the equation identifying the run argument's secret
    coordinate with the secret of the randomized sharing. *)
Lemma s5_tape_secretE (R : realType) :
  rsh_secret (@unif_randomized_sharing R 3 4) = s5_tape_secret.
Proof. by []. Qed.

(******************************************************************************)
(*     The cut-generalized run skeleton                                       *)
(******************************************************************************)

(** s5_aprocs_cut — the seven-process S_5 run skeleton at an abstract content
    readout and an arbitrary cut.
    @intent: s5_trace.s5_aprocs_abs with the dealer's singleton deck [:: w0]
    in place of the identity cut. *)
Definition s5_aprocs_cut (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding s5_PI
                  (fun _ => g) [:: w0] [::] s5_run.s5_players 0)
    ; mk_aproc (exchange_verifier s5_PI s5_run.s5_players)
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 0 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 1 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 2 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 3 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 4 isT))].

(** s5_aprocs_cut1 — the identity cut gives the landed abstract skeleton.
    @composes: s5_rprocs_cut1 *)
Lemma s5_aprocs_cut1 (g : 'I_5 -> 'I_5) :
  s5_aprocs_cut g 1%g = s5_aprocs_abs g.
Proof. by []. Qed.

(** s5_rprocs_cut — the randomized run at a tape and an arbitrary cut.
    @intent: s5_aprocs_cut fed the probability-free layout of the tape. *)
Definition s5_rprocs_cut (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :=
  s5_aprocs_cut (tnth (s5_rfree_layout u)) w0.

(** s5_rprocs_cut1 — the identity-cut specialization is the landed randomized
    process list.
    @main architecture: s5_rprocs_cut u 1 = s5_rprocs R u, at every
    realType. *)
Lemma s5_rprocs_cut1 (R : realType) (u : 'rV['Z_5]_5) :
  s5_rprocs_cut u 1%g = s5_rprocs R u.
Proof.
by rewrite /s5_rprocs_cut s5_aprocs_cut1 /s5_rprocs s5_rfree_layoutE.
Qed.

(** s5_aprocs_cut_terminates — every process of the cut-generalized run reaches
    Finish.
    @composes: s5_rand_terminates *)
Lemma s5_aprocs_cut_terminates (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :
  (run_interp 150 (s5_aprocs_cut g w0)).1 = nseq 7 Finish.
Proof. by vm_compute. Qed.

(** s5_aprocs_cut_endpoints — the cut-generalized verifier endpoints are the
    abstract readout at the cut images of the starts.
    @composes: s5_rand_endpoints, s5_rand_run_recovers *)
Lemma s5_aprocs_cut_endpoints (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :
  endpoints_of_trace (nth [::] (run_interp 150 (s5_aprocs_cut g w0)).2 1)
  = [seq g (@pgg_rho s5_M w0 (tnth (pi_starts s5_PI) i))
     | i <- s5_run.s5_players].
Proof.
rewrite /s5_aprocs_cut /dealer_with_input_encoding.
exact: (@s5_verifier_endpoints (fun=> g) w0 (ord_tuple 5) s5_starts_uniq).
Qed.

(******************************************************************************)
(*     The randomized security plug                                           *)
(******************************************************************************)

(** s5_recon_perm_invariant — sum-mod reconstruction is invariant under the S_5
    monodromy's coordinate permutation.
    @composes: s5_rand_run_recovers *)
Lemma s5_recon_perm_invariant :
  @ts_recon_perm_invariant _ (pgg_G s5_M) _ _ s5_scheme (@pgg_rho s5_M).
Proof.
move=> g s' shares Hg Hvalid.
rewrite /s5_scheme.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry; rewrite (reindex_inj (@perm_inj _ (@pgg_rho s5_M g))).
by apply: eq_bigr.
Qed.

(** s5_rand_endpoints_size — the randomized run collects one endpoint per
    share.
    @composes: s5_rand_run_recovers, s5_rand_recon *)
Lemma s5_rand_endpoints_size (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (endpoints_of_trace (nth [::] (run_interp 150 (s5_rprocs_cut u w0)).2 1))
  = (ts_T' s5_scheme).+1.
Proof. by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints size_map. Qed.

(** s5_rand_run_recovers — reconstructing the randomized run's endpoints
    returns the tape's secret coordinate, for any cut in the group.
    @main correctness: ts_recon s5_scheme of the cut-permuted endpoints of
    s5_rprocs_cut u w0 is u ord0 ord0, for any cut w0 in the group. *)
Lemma s5_rand_run_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  ts_recon s5_scheme
    (tcast (s5_rand_endpoints_size u w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp 150 (s5_rprocs_cut u w0)).2 1))))
  = u ord0 ord0.
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' s5_M).+1)
    (Hsz : size ep = (ts_T' s5_scheme).+1),
    ep = [seq tnth (s5_rfree_layout u)
                (pgg_rho w0 (tnth (pi_starts s5_PI) i))
          | i <- enum 'I_(pi_T' s5_PI).+1] ->
    ts_recon s5_scheme (tcast Hsz (in_tuple ep)) = u ord0 ord0.
  move=> ep Hsz Hep.
  rewrite -[u ord0 ord0](s5_recon_perm_invariant Hw0 (s5_rfree_valid u)).
  congr (ts_recon _ _).
  apply: eq_from_tnth => i.
  rewrite tcastE tnth_mktuple.
  rewrite (tnth_nth ord0) /= Hep.
  rewrite (nth_map i) ?nth_ord_enum ?tnth_ord_tuple;
    last by rewrite size_enum_ord ltn_ord.
  by [].
apply: Hgoal.
by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints s5_players_enumE.
Qed.

(** s5_rand_exec_plug — the S_5 randomized execution plug.
    @intent: the execution layer over s5_profile with run argument the sampler
    tape 'rV['Z_5]_5, the seat/share bridge erefl at 5 seats and 5 shares,
    participant list s5_run.s5_players, content the probability-free additive
    layout of the tape and fuel 150. *)
Definition s5_rand_exec_plug : ExecutionPlug mpS :=
  @dealer_secret_plug mpS 'rV['Z_5]_5 erefl s5_run.s5_players s5_players_enumE
    (fun u _ => tnth (s5_rfree_layout u)) 150.

(** s5_rcontent_obs — the S_5 randomized static observation.
    @intent: the additive share at the cut image of a starting position,
    namely tnth (s5_rfree_layout u) (pgg_rho w0 p). *)
Definition s5_rcontent_obs (u : 'rV['Z_5]_5)
    (p : pgg_gT (mp_M mpS) * 'I_(pgg_N' (mp_M mpS)).+1)
    : 'I_(pgg_N' (mp_M mpS)).+1 :=
  tnth (s5_rfree_layout u) (@pgg_rho (mp_M mpS) p.1 p.2).

(** s5_rand_procsE — the derived process list is the cut-generalized
    randomized list.
    @composes: s5_rand_terminates, s5_rand_endpoints, s5_rand_recon *)
Lemma s5_rand_procsE (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  @exec_procs mpS s5_rand_exec_plug u w0 0 = s5_rprocs_cut u w0.
Proof. by []. Qed.

(** s5_rand_fuelE — the randomized plug's fuel is 150.
    @composes: s5_rand_terminates, s5_rand_endpoints, s5_rand_recon *)
Lemma s5_rand_fuelE : ep_fuel s5_rand_exec_plug = 150.
Proof. by []. Qed.

(** s5_rand_playersE — the randomized plug's participant list is the
    instance's list.
    @composes: s5_rand_endpoints *)
Lemma s5_rand_playersE : ep_players s5_rand_exec_plug = s5_run.s5_players.
Proof. by []. Qed.

(** s5_rand_procs_size — the randomized run has seven processes.
    @composes: s5_rand_terminates *)
Lemma s5_rand_procs_size (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (@exec_procs mpS s5_rand_exec_plug u w0 0) = 7.
Proof. by []. Qed.

(** s5_rand_terminates — every process of the randomized run reaches Finish.
    @composes: s5_rand_observed, s5_rand_correct *)
Lemma s5_rand_terminates (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  (@exec_run mpS s5_rand_exec_plug u w0 0).1
  = nseq (size (@exec_procs mpS s5_rand_exec_plug u w0 0)) Finish.
Proof.
rewrite s5_rand_procs_size /exec_run s5_rand_fuelE s5_rand_procsE.
exact: s5_aprocs_cut_terminates.
Qed.

(** s5_rand_endpoints — the randomized verifier endpoints are the static
    observation over the seats.
    @composes: s5_rand_recon, s5_rand_observed, s5_rand_correct *)
Lemma s5_rand_endpoints (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  @exec_endpoints mpS s5_rand_exec_plug u w0 0
  = @exec_static_endpoints mpS s5_rand_exec_plug s5_rcontent_obs u w0.
Proof.
rewrite /exec_endpoints /exec_run s5_rand_fuelE s5_rand_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5_rand_playersE.
by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints.
Qed.

(** s5_rand_endpoint_count — the randomized run collects five endpoints.
    @main correctness: size (exec_endpoints s5_rand_exec_plug u w0 0) = 5. *)
Lemma s5_rand_endpoint_count (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (@exec_endpoints mpS s5_rand_exec_plug u w0 0) = 5.
Proof. by rewrite (exec_endpoints_size (s5_rand_endpoints u w0)). Qed.

(** s5_rand_decodeE — the randomized plug's decoder is the instance's
    reconstruction.
    @composes: s5_rand_recon *)
Lemma s5_rand_decodeE (ep : seq 'I_(pgg_N' (mp_M mpS)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpS)).+1)
    (Hsz' : size ep = (ts_T' s5_scheme).+1) :
  @exec_decode mpS s5_rand_exec_plug ep Hsz
  = ts_recon s5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5_rand_recon — decoding the randomized static observation returns the
    encoded tape secret.
    @composes: s5_rand_observed, s5_rand_exec_recovers *)
Lemma s5_rand_recon (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  forall Hsz : size (@exec_static_endpoints mpS s5_rand_exec_plug
                       s5_rcontent_obs u w0)
               = (pi_T' (mp_PI mpS)).+1,
  @exec_decode mpS s5_rand_exec_plug
    (@exec_static_endpoints mpS s5_rand_exec_plug s5_rcontent_obs u w0) Hsz
  = s5_codec (s5_tape_secret u).
Proof.
move=> Hw0.
rewrite -s5_rand_endpoints /exec_endpoints /exec_run s5_rand_fuelE
        s5_rand_procsE /exec_verifier_id => Hsz.
rewrite (s5_rand_decodeE Hsz (s5_rand_endpoints_size u w0)).
exact: (@s5_rand_run_recovers u w0 Hw0).
Qed.

(** s5_rand_exec_recovers — the randomized run decodes to the encoded tape
    secret.
    @main correctness: exec_decode of the executed endpoints of the run of
    s5_rand_exec_plug at tape u and cut w0 is s5_codec (s5_tape_secret u), for
    any cut w0 in the group. *)
Theorem s5_rand_exec_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_rand_exec_plug
    (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
    (exec_endpoints_size (s5_rand_endpoints u w0))
  = s5_codec (s5_tape_secret u).
Proof.
exact: (@exec_run_recovers mpS s5_rand_exec_plug s5_rcontent_obs
          (fun u => s5_codec (s5_tape_secret u)) u w0 0
          (s5_rand_endpoints u w0) (s5_rand_recon Hw0)).
Qed.

(** s5_rand_correct — termination, endpoint count and recovery of the
    randomized run.
    @main correctness: the run of s5_rand_exec_plug reaches Finish at each of
    its seven processes, collects one endpoint per seat, and decodes to the
    encoded tape secret, for any cut w0 in the group. *)
Theorem s5_rand_correct (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  [/\ (@exec_run mpS s5_rand_exec_plug u w0 0).1
        = nseq (size (@exec_procs mpS s5_rand_exec_plug u w0 0)) Finish,
      size (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
        = (pi_T' (mp_PI mpS)).+1 &
      @exec_decode mpS s5_rand_exec_plug
        (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
        (exec_endpoints_size (s5_rand_endpoints u w0))
      = s5_codec (s5_tape_secret u)].
Proof.
exact: (@exec_run_correct mpS s5_rand_exec_plug s5_rcontent_obs
          (fun u => s5_codec (s5_tape_secret u)) u w0 0
          (s5_rand_terminates u w0) (s5_rand_endpoints u w0)
          (s5_rand_recon Hw0)).
Qed.

(** s5_rand_observed — the S_5 randomized observed execution.
    @intent: s5_profile with plug s5_rand_exec_plug at process offset 0, static
    observation s5_rcontent_obs and expected value the encoded tape secret;
    the three run facts are s5_rand_terminates, s5_rand_endpoints and
    s5_rand_recon. *)
Definition s5_rand_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpS s5_rand_exec_plug 0
    s5_rcontent_obs (fun u => s5_codec (s5_tape_secret u))
    s5_rand_terminates s5_rand_endpoints (@s5_rand_recon).

(** s5_rand_observed_recovers — the packaged randomized run decodes to the
    encoded tape secret.
    @main correctness: exec_decode of the executed endpoints of
    s5_rand_observed at tape u and cut w0 is s5_codec (s5_tape_secret u), for
    any cut w0 in the group. *)
Theorem s5_rand_observed_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Hw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_rand_exec_plug
    (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
    (OE.oe_endpoints_size s5_rand_observed u w0)
  = s5_codec (s5_tape_secret u).
Proof. exact: (OE.oe_run_recovers s5_rand_observed u w0 Hw0). Qed.

End s5_execution.
