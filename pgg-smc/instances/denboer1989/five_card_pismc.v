(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick: piSMC Protocol Programs and ThresholdScheme    *)
(*                                                                            *)
(* Part A: Session-typed protocol programs for the five-card trick,           *)
(*   using the piSMC framework (pismc.v) and session-type wrappers            *)
(*   from five_card_session_types.v.                                          *)
(*                                                                            *)
(* Part B: ThresholdScheme instantiation for the five-card trick.             *)
(*                                                                            *)
(* Party indices:                                                             *)
(*   dealer_idx   = 0 : arranges cards and reveals to verifier                *)
(*   verifier_idx = 1 : observes revealed cards                               *)
(*   alice_idx    = 2 : commits her input bit                                 *)
(*   bob_idx      = 3 : commits his input bit                                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
Require Import smc_session_types pismc.
From pgg_smc Require Import five_card_group five_card_session_types
  five_card_program.
From pgg_reconstruct Require Import pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope pismc_scope.

(******************************************************************************)
(** * Part A: piSMC Protocol Programs                                        *)
(******************************************************************************)

(* Party indices *)
Definition dealer_idx : nat := 0.
Definition verifier_idx : nat := 1.
Definition alice_idx : nat := 2.
Definition bob_idx : nat := 3.

(* Make sproc type annotations concise *)
Arguments sproc dtype data party {_} {_}.

(** * Custom pismc notations for five-card actions *)

Notation "'Reveal<' p '>' v ; P" := (FCReveal p v P)
  (in custom pismc at level 85, p constr at level 0, v constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Commit<' p '>' cs ; P" := (FCCommit p cs P)
  (in custom pismc at level 85, p constr at level 0, cs constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Observe<' p '>' v '=>' P" := (FCObserve p (fun v => P))
  (in custom pismc at level 85, p constr at level 0, v name,
   P custom pismc at level 85, right associativity).

Notation "'RecvCommit<' p '>' cs '=>' P" := (FCRecvCommit p (fun cs => P))
  (in custom pismc at level 85, p constr at level 0, cs name,
   P custom pismc at level 85, right associativity).

(** * Protocol programs *)

Definition fc_alice (a : bool) : sproc fc_dtype fc_data alice_idx :=
  \pi{ Commit<dealer_idx> (fc_encode a) ; Finish }.

Definition fc_bob (b : bool) : sproc fc_dtype fc_data bob_idx :=
  \pi{ Commit<dealer_idx> (fc_encode b) ; Finish }.

Definition fc_dealer (a b : bool) (k : nat) (Hk : k < 5)
    : sproc fc_dtype fc_data dealer_idx :=
  let shuffled := fc_shuffle k (fc_arrange a b) in
  \pi{ RecvCommit<alice_idx> _ca =>
       RecvCommit<bob_idx> _cb =>
       Reveal<verifier_idx> (nth false shuffled 0) ;
       Reveal<verifier_idx> (nth false shuffled 1) ;
       Reveal<verifier_idx> (nth false shuffled 2) ;
       Reveal<verifier_idx> (nth false shuffled 3) ;
       Reveal<verifier_idx> (nth false shuffled 4) ;
       Finish }.

Definition fc_verifier : sproc fc_dtype fc_data verifier_idx :=
  \pi{ Observe<dealer_idx> c0 =>
       Observe<dealer_idx> c1 =>
       Observe<dealer_idx> c2 =>
       Observe<dealer_idx> c3 =>
       Observe<dealer_idx> c4 =>
       Finish }.

(******************************************************************************)
(** * Part B: ThresholdScheme Instantiation                                   *)
(******************************************************************************)

(** Validity: shares encode secret s iff three consecutive hearts
    in the cyclic arrangement equal s. *)
Definition fc_ts_valid (s : bool) (shares : 5.-tuple bool) : Prop :=
  fc_three_consec (val shares) = s.

(** Reconstruction: extract the AND result from shares. *)
Definition fc_ts_recon (shares : 5.-tuple bool) : bool :=
  fc_three_consec (val shares).

(** Canonical encoding: AND=1 uses (true,true), AND=0 uses (false,false). *)
Definition fc_ts_encode (s : bool) : 5.-tuple bool :=
  fc_arrange_tup (if s then true else false) (if s then true else false).

(** Correctness: reconstruction of valid shares returns the secret. *)
Lemma fc_ts_correct (s : bool) (shares : 5.-tuple bool) :
  fc_ts_valid s shares -> fc_ts_recon shares = s.
Proof. by rewrite /fc_ts_recon /fc_ts_valid => ->. Qed.

(** Canonical encoding is valid. *)
Lemma fc_ts_encode_valid (s : bool) : fc_ts_valid s (fc_ts_encode s).
Proof. by case: s. Qed.

(** Witness: a valid-[s] tuple whose [i]-th element equals [v].
    Used to construct privacy witnesses for the threshold scheme. *)
Definition fc_witness (s : bool) (i : nat) (v : bool) : seq bool :=
  match s, v with
  | false, false => [:: false; false; false; false; false]
  | false, true =>
    match i with
    | 0 => [:: true; false; false; false; false]
    | 1 => [:: false; true; false; false; false]
    | 2 => [:: false; false; true; false; false]
    | 3 => [:: false; false; false; true; false]
    | _ => [:: false; false; false; false; true]
    end
  | true, false =>
    match i with
    | 0 => [:: false; false; true; true; true]
    | 1 => [:: false; false; true; true; true]
    | 2 => [:: true; false; false; true; true]
    | 3 => [:: true; true; false; false; true]
    | _ => [:: false; true; true; true; false]
    end
  | true, true =>
    match i with
    | 0 => [:: true; false; false; true; true]
    | 1 => [:: false; true; true; true; false]
    | 2 => [:: false; false; true; true; true]
    | 3 => [:: false; false; true; true; true]
    | _ => [:: false; false; true; true; true]
    end
  end.

Lemma fc_witness_size (s : bool) (i : nat) (v : bool) :
  i < 5 -> size (fc_witness s i v) == 5.
Proof. by case: s; case: v; case: i => [|[|[|[|[|]]]]]. Qed.

Definition fc_witness_tup (s : bool) (i : 'I_5) (v : bool) : 5.-tuple bool :=
  Tuple (@fc_witness_size s (val i) v (ltn_ord i)).

Lemma fc_witness_val s (i : 'I_5) v :
  val (fc_witness_tup s i v) = fc_witness s (val i) v.
Proof. by []. Qed.

Lemma fc_witness_valid s (i : 'I_5) v :
  fc_three_consec (val (fc_witness_tup s i v)) = s.
Proof.
rewrite fc_witness_val.
by case: s; case: v; case: i => [[|[|[|[|[|]]]]]] //.
Qed.

Lemma fc_witness_tnth s (i : 'I_5) v :
  tnth (fc_witness_tup s i v) i = v.
Proof.
rewrite (tnth_nth false) fc_witness_val.
by case: s; case: v; case: i => [[|[|[|[|[|]]]]]] //.
Qed.

(** Privacy: any single card position (|C| < 2) can be matched
    by shares valid for a different secret. In the five-card trick,
    each individual card position is compatible with both AND=0
    and AND=1, but two or more positions may leak information. *)
Lemma fc_ts_private (s1 s2 : bool) (shares : 5.-tuple bool)
    (C : {set 'I_5}) :
  #|C| < 2 ->
  fc_ts_valid s1 shares ->
  exists shares' : 5.-tuple bool,
    fc_ts_valid s2 shares' /\
    (forall i : 'I_5, i \in C -> tnth shares' i = tnth shares i).
Proof.
case Hs12: (s1 == s2).
- move/eqP: Hs12 => ->; move=> _ Hv; exists shares; split; [exact Hv | done].
- move=> HC Hv.
  case: (set_0Vmem C) => [HC0 | [j Hj]].
  + (* C = set0: any valid-s2 tuple works *)
    exists (fc_ts_encode s2); split; first exact: fc_ts_encode_valid.
    by move=> i; rewrite HC0 inE.
  + (* C contains j: use witness at position j *)
    exists (fc_witness_tup s2 j (tnth shares j)); split.
    * by rewrite /fc_ts_valid fc_witness_valid.
    * move=> i Hi.
      have /card_le1_eqP Heq : #|C| <= 1 by rewrite -ltnS.
      have -> : i = j by apply: Heq.
      exact: fc_witness_tnth.
Qed.

(** The five-card threshold scheme: 5 shares, privacy threshold 2
    (any single card position reveals nothing about the secret). *)
Definition fc_threshold_scheme : ThresholdScheme bool bool :=
  @MkThresholdScheme bool bool 4 1
    fc_ts_valid fc_ts_recon fc_ts_encode
    fc_ts_correct fc_ts_private fc_ts_encode_valid.
