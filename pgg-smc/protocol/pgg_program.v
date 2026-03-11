(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From mathcomp Require Import bigop.

(******************************************************************************)
(* PGG-SMC: Protocol Specification                                            *)
(*                                                                            *)
(* Defines the three phases of the covering-space MPC protocol:               *)
(*   split rho W starts == for each word w in W, compute permutation table    *)
(*                         columns: party i gets {rho(w)(s_i) | w in W}       *)
(*   compute share P    == party looks up rho(P)(s_i) in their share          *)
(*   secret recon P     == apply reconstruction function to T endpoints       *)
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

(* A share for party i is a function from words to sheet values.
   Given a set of words W (represented as a sequence), the share maps
   each word index to the endpoint evaluation at party i's starting sheet. *)

(* The permutation table: for a sequence of group elements (words),
   compute the full N x |W| table of permutation evaluations *)
Definition perm_table (W : seq gT) : seq {perm 'I_N} :=
  [seq rho w | w <- W].

(* Party i's share: column of the permutation table at starting sheet s_i *)
Definition share (W : seq gT) (i : 'I_T) : seq ('I_N) :=
  [seq rho w (tnth starts i) | w <- W].

(* Compute phase: party i evaluates rho(P)(s_i) using the public word P.
   This is just endpoint evaluation. *)
Definition compute (P : gT) (i : 'I_T) : 'I_N :=
  rho P (tnth starts i).

(* The T-tuple of all party endpoints for word P *)
Definition endpoints (P : gT) : T.-tuple 'I_N :=
  [tuple compute P i | i < T].

(* Key property: party i's computation result equals looking up P in share *)
Lemma compute_in_share (W : seq gT) (P : gT) (i : 'I_T) :
  P \in W -> compute P i \in share W i.
Proof.
move=> PW; rewrite /share /compute.
by apply/mapP; exists P.
Qed.

(* The endpoints are just rho(P) applied to each starting sheet *)
Lemma endpointsE (P : gT) (i : 'I_T) :
  tnth (endpoints P) i = rho P (tnth starts i).
Proof. by rewrite tnth_mktuple. Qed.

(* Reconstruction: parametric over an arbitrary reconstruction function *)
Variable recon : T.-tuple 'I_N -> 'I_N.

(* The secret: apply reconstruction to endpoints *)
Definition secret (P : gT) : 'I_N :=
  recon (endpoints P).

End pgg_protocol.
