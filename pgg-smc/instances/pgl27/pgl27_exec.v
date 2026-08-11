(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_exec: the ExecutionPlug of the PGL(2,7) instance                     *)
(*                                                                            *)
(* The eight-card orbit instance carries an execution plug over its own       *)
(* MonodromyProfile pgl27_profile, built by the dealer-secret constructor:    *)
(* the run argument is the dealt orbit secret, both count bridges are erefl   *)
(* at 8 seats, 8 shares and 8 cards, the participant list is pgl27_players    *)
(* and the fuel is pgl27_fuel.                                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exec_plug   == the execution plug over pgl27_profile               *)
(*   pgl27_content_obs == the static observation: the share of the secret at  *)
(*                        the cut image of a starting position                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_exec_recovers == the derived run decodes to the dealt secret       *)
(*   pgl27_exec_correct  == termination, endpoint count and recovery of the   *)
(*                          derived run                                       *)
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
From pgg_smc Require Import pgg_execution_plug.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section pgl27_execution.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl27_players_enumE — the eight-element participant list is the seat
    enumeration.
    @composes: pgl27_exec_endpoints *)
Lemma pgl27_players_enumE : pgl27_players = enum 'I_(pi_T' (mp_PI mpP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl27_exec_plug — the PGL(2,7) execution plug.
    @intent: the execution layer over pgl27_profile with run argument bool,
    both count bridges erefl at 8 seats, 8 shares and 8 cards, participant
    list pgl27_players, content the shares ts_encode orbit_scheme s of the
    dealt orbit secret s and fuel pgl27_fuel; the dealer-secret constructor
    fixes the input-process list to the empty list. *)
Definition pgl27_exec_plug : ExecutionPlug mpP :=
  @dealer_secret_plug R mpP bool erefl erefl pgl27_players pgl27_players_enumE
    (fun s _ => tnth (ts_encode orbit_scheme s)) pgl27_fuel.

(** pgl27_content_obs — the PGL(2,7) static observation.
    @intent: the share of the secret s at the cut image of a starting
    position, namely tnth (ts_encode orbit_scheme s) (pgg_rho w0 p) at a cut w0
    and a position p. *)
Definition pgl27_content_obs (s : bool)
    (p : pgg_gT (mp_M mpP) * 'I_(pgg_N' (mp_M mpP)).+1)
    : 'I_(pgg_N' (mp_M mpP)).+1 :=
  tnth (ts_encode orbit_scheme s) (@pgg_rho (mp_M mpP) p.1 p.2).

(** pgl27_exec_playersE — the plug's participant list is the instance's list.
    @composes: pgl27_exec_endpoints *)
Lemma pgl27_exec_playersE : ep_players pgl27_exec_plug = pgl27_players.
Proof. by []. Qed.

(** pgl27_exec_fuelE — the plug's fuel is the instance's fuel.
    @composes: pgl27_exec_terminates, pgl27_exec_endpoints, pgl27_exec_recon *)
Lemma pgl27_exec_fuelE : ep_fuel pgl27_exec_plug = pgl27_fuel.
Proof. by []. Qed.

(** pgl27_exec_procsE — the derived process list is the instance's process
    list.
    @composes: pgl27_exec_terminates, pgl27_exec_endpoints, pgl27_exec_recon *)
Lemma pgl27_exec_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @exec_procs R mpP pgl27_exec_plug s w0 0 = pgl27_procs s w0.
Proof. by []. Qed.

(** pgl27_exec_procs_size — the derived run has ten processes.
    @composes: pgl27_exec_terminates *)
Lemma pgl27_exec_procs_size (s : bool) (w0 : pgg_gT pgl27_M) :
  size (@exec_procs R mpP pgl27_exec_plug s w0 0) = 10.
Proof. by []. Qed.

(** pgl27_exec_terminates — every process of the derived run reaches Finish.
    @composes: pgl27_exec_correct *)
Lemma pgl27_exec_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@exec_run R mpP pgl27_exec_plug s w0 0).1
  = nseq (size (@exec_procs R mpP pgl27_exec_plug s w0 0)) Finish.
Proof.
rewrite pgl27_exec_procs_size /exec_run pgl27_exec_fuelE pgl27_exec_procsE.
exact: pgl27_run_terminates.
Qed.

(** pgl27_exec_endpoints — the derived verifier endpoints are the static
    observation over the seats.
    @composes: pgl27_exec_recon, pgl27_exec_recovers, pgl27_exec_correct *)
Lemma pgl27_exec_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  @exec_endpoints R mpP pgl27_exec_plug s w0 0
  = @exec_static_endpoints R mpP pgl27_exec_plug pgl27_content_obs s w0.
Proof.
rewrite /exec_endpoints /exec_run pgl27_exec_fuelE pgl27_exec_procsE.
rewrite /exec_verifier_id.
rewrite /exec_static_endpoints pgl27_exec_playersE pgl27_players_enumE.
exact: pgl27_endpoints.
Qed.

(** pgl27_exec_decodeE — the plug's decoder is the instance's reconstruction.
    @composes: pgl27_exec_recon *)
Lemma pgl27_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpP)).+1)
    (Hsz' : size ep = (ts_T' orbit_scheme).+1) :
  @exec_decode R mpP pgl27_exec_plug ep Hsz
  = ts_recon orbit_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /exec_decode /run_recover.
by rewrite (eq_irrelevance
              (etrans Hsz (@exec_seat_share_count R mpP pgl27_exec_plug)) Hsz').
Qed.

(** pgl27_exec_recon — decoding the static observation returns the dealt
    secret, for any cut in the group and any proof of the endpoint count.
    @composes: pgl27_exec_recovers, pgl27_exec_correct *)
Lemma pgl27_exec_recon (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  forall Hsz : size (@exec_static_endpoints R mpP pgl27_exec_plug
                       pgl27_content_obs s w0) = (pi_T' (mp_PI mpP)).+1,
  @exec_decode R mpP pgl27_exec_plug
    (@exec_static_endpoints R mpP pgl27_exec_plug pgl27_content_obs s w0)
    Hsz = s.
Proof.
move=> Hw0.
have Hgen : forall (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (H1 : size ep = (pi_T' (mp_PI mpP)).+1),
    ep = endpoints_of_trace
           (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1) ->
    @exec_decode R mpP pgl27_exec_plug ep H1 = s.
  move=> ep H1 Hq; move: H1; rewrite Hq => H1.
  rewrite (pgl27_exec_decodeE H1 (pgl27_endpoints_size s w0)).
  exact: (pgl27_run_recovers s Hw0).
move=> Hsz; apply: Hgen.
by rewrite -pgl27_exec_endpoints /exec_endpoints /exec_run pgl27_exec_fuelE
           pgl27_exec_procsE /exec_verifier_id.
Qed.

(** pgl27_exec_recovers — the derived PGL(2,7) run decodes to the dealt
    secret.
    @main correctness: exec_decode of the executed endpoints of the run of
    pgl27_exec_plug at secret s and cut w0 is s, for any cut w0 in the
    group. *)
Theorem pgl27_exec_recovers (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  @exec_decode R mpP pgl27_exec_plug
    (@exec_endpoints R mpP pgl27_exec_plug s w0 0)
    (exec_endpoints_size (pgl27_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers R mpP pgl27_exec_plug pgl27_content_obs (fun b => b)
          s w0 0 (pgl27_exec_endpoints s w0) (pgl27_exec_recon Hw0)).
Qed.

(** pgl27_exec_correct — termination, endpoint count and recovery of the
    derived PGL(2,7) run.
    @main correctness: the run of pgl27_exec_plug reaches Finish at each of its
    ten processes, collects one endpoint per seat, and decodes to the dealt
    secret s, for any cut w0 in the group. *)
Theorem pgl27_exec_correct (s : bool) (w0 : pgg_gT pgl27_M)
    (Hw0 : w0 \in pgg_G pgl27_M) :
  [/\ (@exec_run R mpP pgl27_exec_plug s w0 0).1
        = nseq (size (@exec_procs R mpP pgl27_exec_plug s w0 0)) Finish,
      size (@exec_endpoints R mpP pgl27_exec_plug s w0 0)
        = (pi_T' (mp_PI mpP)).+1 &
      @exec_decode R mpP pgl27_exec_plug
        (@exec_endpoints R mpP pgl27_exec_plug s w0 0)
        (exec_endpoints_size (pgl27_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct R mpP pgl27_exec_plug pgl27_content_obs (fun b => b)
          s w0 0 (pgl27_exec_terminates s w0) (pgl27_exec_endpoints s w0)
          (pgl27_exec_recon Hw0)).
Qed.

End pgl27_execution.
