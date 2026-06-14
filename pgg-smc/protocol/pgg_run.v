(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG piSMC trace bridge: execute the shared program and read correctness    *)
(* off the executed trace (DSDP-style). The cut stays the identity; endpoint  *)
(* values stay symbolic.                                                       *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** evens — every other element from the front ([a0; a2; a4; ...]). The verifier
    records each endpoint twice (Recv of the revealed card, then Init into its
    buffer), so the two copies are extracted by taking alternates. *)
Fixpoint evens {T : Type} (s : seq T) : seq T :=
  match s with
  | x :: _ :: s' => x :: evens s'
  | [:: x] => [:: x]
  | [::] => [::]
  end.

Section pgg_run.
Variable M : MonodromyReprWithGeneratorType.
Variable PI : PGGInterface M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let data := pgg_data N.

(** identity_deck — the singleton deck carrying the identity cut. *)
Definition identity_deck : seq (pgg_gT M) := [:: 1%g].

(** dealer_with_input_encoding — generic input-derived-content dealer: a commit
    prologue collecting [inputs], then [exchange_dealer] with the committed
    content readout and the identity cut. Generalizes den_boer_dealer_layout. *)
Definition dealer_with_input_encoding
    (content_of : seq 'I_N -> ('I_N -> 'I_N))
    (inputs : seq nat) (players : seq 'I_T) (P_idx : nat) :=
  pgg_commit_prologue
    (fun committed =>
       exchange_dealer PI (content_of committed) players identity_deck P_idx)
    [::] inputs.

(** sheets_of — the PGG_sheet payloads of a trace, in trace order. *)
Definition sheets_of (tr : seq data) : seq 'I_N :=
  pmap (fun d => if d is PGG_sheet x then Some x else None) tr.

(** endpoints_of_trace — the endpoints the verifier collected, in player order.
    Each endpoint is recorded twice (Recv then Init); [evens] keeps one copy.
    The verifier pushes player T-1 first, so [rev] restores player order. *)
Definition endpoints_of_trace (verifier_trace : seq data) : seq 'I_N :=
  rev (evens (sheets_of verifier_trace)).

End pgg_run.

Arguments identity_deck {M}.
Arguments dealer_with_input_encoding {M} PI.
Arguments sheets_of {M}.
Arguments endpoints_of_trace {M}.
