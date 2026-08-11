(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-D counter-probe: THIS FILE MUST FAIL TO COMPILE                    *)
(*                                                                            *)
(* Mutation landed: the PRIMARY one. fc_epp_bad is probe_d_fivecard_exec.v's  *)
(* fc_epp with ep_input_procs := fun _ => [::]; every other field, and the    *)
(* whole proof script of fc_epp_procsE, is unchanged. The fallback mutation   *)
(* (ep_inputT := unit) was not needed: the closing conversion fails in tens   *)
(* of milliseconds, so there is no divergence risk to avoid.                  *)
(*                                                                            *)
(* Dropping the input parties changes the run in two places at once. The      *)
(* process list loses its two-element tail, seven processes against the       *)
(* landed nine, and the dealer's prologue receives from epp_input_ids = iota  *)
(* 7 0 = [::] instead of [:: 7; 8]. Both are structural mismatches under the  *)
(* cons/nil constructors, so the check fails without evaluating any process   *)
(* body and without touching run_interp.                                      *)
(*                                                                            *)
(* Expected error at fc_epp_bad_procsE:                                       *)
(*   Error: No applicable tactic.                                             *)
(* the ssreflect closing failure of "by rewrite fc_epp_bad_playersE.", the    *)
(* step that closes in the green file. The goal at failure is the seven-      *)
(* process derived list against the nine-process den_boer_saprocs, with       *)
(* [:: w0] (epp_input_ids (a, b)) against [:: w0] [:: 7; 8] inside the two    *)
(* dealers.                                                                   *)
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
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** EPP — the execution adapter over a MonodromyProfile.
    Kind: interface.
    The record of probe_d_fivecard_exec.v, unchanged. *)
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

End execution_of_profile.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_mutation.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpB : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** fc_epp_bad — the five-card adapter with the input parties dropped.
    @intent: fc_epp with ep_input_procs := fun _ => [::]; the two bits are
    committed by no process, so the run has seven processes and the dealer's
    prologue receives from nobody. *)
Definition fc_epp_bad : EPP mpB :=
  @MkEPP R mpB (bool * bool)%type erefl erefl
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun _ => [::])
    100.

(** fc_epp_bad_playersE — the derived participant list is the instance's list.
    @composes: fc_epp_bad_procsE *)
Lemma fc_epp_bad_playersE : @epp_players R mpB = den_boer_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** fc_epp_bad_procsE — the derived process list is the instance's process
    list.
    @main architecture: epp_procs fc_epp_bad (a, b) w0 P_idx = den_boer_procs a
    b w0 P_idx; false, since the left side has seven processes and the right
    side nine. *)
Lemma fc_epp_bad_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  @epp_procs R mpB fc_epp_bad (a, b) w0 P_idx = den_boer_procs a b w0 P_idx.
Proof.
rewrite /epp_procs /den_boer_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /den_boer_saprocs /den_boer_dealer_run.
by rewrite fc_epp_bad_playersE.
Qed.

End fivecard_mutation.
