(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-A mutation: the content readout is carrier-bound                   *)
(*                                                                            *)
(* The PGL(2,7) register of probe_a_sufficiency.v with the den Boer content   *)
(* readout in place of the PGL(2,7) one. This file must not compile: the      *)
(* readout den_boer_layout o den_boer_decode reads five card positions, the   *)
(* carrier pgl27_profile has eight.                                           *)
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

Section generic_sufficiency.

Variable R : realType.
Variable mp : MonodromyProfile R.

Let M  := mp_M mp.
Let PI := mp_PI mp.
Let N  := (pgg_N' M).+1.
Let T  := (pi_T' PI).+1.

Variable content_of : seq 'I_N -> ('I_N -> 'I_N).
Variable W : seq (pgg_gT M).
Variable input_procs : seq (aproc pgg_dtype (pgg_data N)).
Variable inputs : seq nat.
Variable P_idx : nat.
Variable fuel : nat.

(** gen_players — the participant list of the run.
    @intent: the enumeration of the pi_T'.+1 seats of mp_PI. *)
Definition gen_players : seq 'I_T := enum 'I_T.

(** gen_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI with the register's content
    readout, deck, input identifiers and announced index. *)
Definition gen_dealer :=
  dealer_with_input_encoding PI content_of W inputs gen_players P_idx.

(** gen_verifier — the verifier of the run.
    @intent: exchange_verifier at mp_PI over gen_players. *)
Definition gen_verifier := exchange_verifier PI gen_players.

(** gen_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per seat, then the input parties. *)
Definition gen_saprocs : seq (aproc pgg_dtype (pgg_data N)) :=
  mk_aproc gen_dealer :: mk_aproc gen_verifier
    :: [seq mk_aproc (exchange_player PI i) | i <- gen_players] ++ input_procs.

(** gen_procs — the erased process list.
    @intent: the plain-proc image of gen_saprocs. *)
Definition gen_procs := erase_aprocs gen_saprocs.

(** gen_run — the interpreter result.
    @intent: run_interp at the register's fuel on gen_procs. *)
Definition gen_run := run_interp fuel gen_procs.

(** gen_endpoints — the verifier's collected endpoints.
    @intent: endpoints_of_trace of entry 1 of gen_run.2. *)
Definition gen_endpoints := endpoints_of_trace (nth [::] gen_run.2 1).

End generic_sufficiency.

Section pgl27_register_mutated.

Variable R : realType.
Variable w0 : pgg_gT pgl27_M.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** mut_content — the den Boer content readout at the PGL(2,7) carrier.
    @intent: tnth (den_boer_layout (den_boer_decode committed)), a readout on
    the five card positions of FiveCardKim_M. *)
Definition mut_content : seq 'I_(pgg_N' (mp_M mpP)).+1 ->
    ('I_(pgg_N' (mp_M mpP)).+1 -> 'I_(pgg_N' (mp_M mpP)).+1) :=
  fun committed => tnth (den_boer_layout (den_boer_decode committed)).

(** mut_input_procs — no input parties. @intent: the empty prologue. *)
Definition mut_input_procs
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mpP)).+1)) := [::].

(** mut_procs — the erased process list at the mutated readout.
    @intent: gen_procs at mpP with mut_content. *)
Definition mut_procs :=
  @gen_procs R mpP mut_content [:: w0] mut_input_procs [::] 0.

(** mut_endpoints — the verifier endpoints at the mutated readout.
    @intent: gen_endpoints at mpP with mut_content. *)
Definition mut_endpoints :=
  @gen_endpoints R mpP mut_content [:: w0] mut_input_procs [::] 0 pgl27_fuel.

End pgl27_register_mutated.
