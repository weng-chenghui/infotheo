(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From mathcomp Require Import bigop.

(******************************************************************************)
(* PGG: Protocol Specification                                                *)
(*                                                                            *)
(* Defines the three phases of the card protocol:                             *)
(*   split rho W starts == for each shuffle w in W, compute permutation       *)
(*                         table columns: player i gets {rho(w)(s_i)|w in W}  *)
(*   compute dealt_hand P == player looks up rho(P)(s_i) in their hand        *)
(*   outcome recon P      == apply reconstruction to T card positions          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_protocol.

Variable gT : finGroupType.
Variable N' : nat.
Let N := N'.+1.
Variable G : {group gT}.
Variable rho : {morphism G >-> {perm 'I_N}}.

Variable T' : nat.
Let T := T'.+1.

Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* A dealt hand for player i is a function from shuffles to card positions.
   Given a set of shuffles W (represented as a sequence), the hand maps
   each shuffle index to the endpoint evaluation at player i's starting sheet. *)

(* The permutation table: for a sequence of group elements (words),
   compute the full N x |W| table of permutation evaluations *)
Definition perm_table (W : seq gT) : seq {perm 'I_N} :=
  [seq rho w | w <- W].

(* Player i's dealt hand: column of the permutation table at starting sheet s_i *)
Definition dealt_hand (W : seq gT) (i : 'I_T) : seq ('I_N) :=
  [seq rho w (tnth starts i) | w <- W].

(* Compute phase: player i evaluates rho(P)(s_i) using the selected shuffle P.
   This is just endpoint evaluation. *)
Definition compute (P : gT) (i : 'I_T) : 'I_N :=
  rho P (tnth starts i).

(* The T-tuple of all player card positions for shuffle P *)
Definition endpoints (P : gT) : T.-tuple 'I_N :=
  [tuple compute P i | i < T].

(* Key property: player i's computation result equals looking up P in hand *)
Lemma compute_in_dealt_hand (W : seq gT) (P : gT) (i : 'I_T) :
  P \in W -> compute P i \in dealt_hand W i.
Proof.
move=> PW; rewrite /dealt_hand /compute.
by apply/mapP; exists P.
Qed.

(* The card positions are just rho(P) applied to each starting sheet *)
Lemma endpointsE (P : gT) (i : 'I_T) :
  tnth (endpoints P) i = rho P (tnth starts i).
Proof. by rewrite tnth_mktuple. Qed.

(* Reconstruction: parametric over an arbitrary reconstruction function.
   In card protocol terms: determines the outcome from T observed card positions. *)
Variable recon : T.-tuple 'I_N -> 'I_N.

(* The outcome: apply reconstruction to card positions *)
Definition outcome (P : gT) : 'I_N :=
  recon (endpoints P).

End pgg_protocol.
