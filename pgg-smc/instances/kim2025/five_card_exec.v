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
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_exec_recovers    == the derived run decodes to the conjunction *)
(*                                 of the two committed bits                  *)
(*   five_card_exec_correct     == termination, endpoint count and recovery   *)
(*                                 of the derived run                         *)
(*   five_card_exec_procs_biasE == the derived process list is the same at    *)
(*                                 two biases                                 *)
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
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

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
rewrite /exec_decode /run_recover.
by rewrite (eq_irrelevance
              (etrans Hsz (@exec_seat_share_count R mpF five_card_exec_plug))
              Hsz').
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
