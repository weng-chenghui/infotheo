(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* Session-type infrastructure for den Boer's five-card trick protocol.        *)
(* Reference: Bert den Boer, More Efficient Match-Making and Satisfiability:   *)
(*   The Five Card Trick, EUROCRYPT 1989, LNCS 434, pp. 208-217.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import smc_session_types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(* Five-Card Trick: Data Types and Session-Typed Wrappers                     *)
(*                                                                            *)
(* fc_dtype           == message type tags: DT_CardVal (single card face      *)
(*                       value) and DT_Commit (2-card commitment pair)        *)
(* fc_data            == protocol data: FC_card v (single card, false=club,   *)
(*                       true=heart) and FC_commit cs (commitment pair)       *)
(* fc_data_dtype d    == maps fc_data to its fc_dtype tag                     *)
(* from_card d        == extract bool from FC_card, None otherwise            *)
(* from_commit d      == extract seq bool from FC_commit, None otherwise      *)
(*                                                                            *)
(* Session-typed wrappers:                                                    *)
(*   FCReveal dst v p    == send card value v to dst (DT_CardVal)             *)
(*   FCCommit dst cs p   == send commitment cs to dst (DT_Commit)             *)
(*   FCObserve src f     == receive card value, extract bool, apply f         *)
(*   FCRecvCommit src f  == receive commitment, extract seq bool, apply f     *)
(*   FCFinish            == terminal state                                    *)
(******************************************************************************)

(* ========================================================================== *)
(* Message Type Tags                                                          *)
(* ========================================================================== *)

Inductive fc_dtype : Type := DT_CardVal | DT_Commit.

Definition fc_dtype_eqb (d1 d2 : fc_dtype) : bool :=
  match d1, d2 with
  | DT_CardVal, DT_CardVal => true
  | DT_Commit, DT_Commit => true
  | _, _ => false
  end.

Lemma fc_dtype_eqP : Equality.axiom fc_dtype_eqb.
Proof. by move=> [] []; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build fc_dtype fc_dtype_eqP.

(* ========================================================================== *)
(* Protocol Data Type                                                         *)
(* ========================================================================== *)

Inductive fc_data : Type :=
  | FC_card (v : bool)
  | FC_commit (cs : seq bool).

Definition fc_data_dtype (d : fc_data) : fc_dtype :=
  match d with
  | FC_card _ => DT_CardVal
  | FC_commit _ => DT_Commit
  end.

Definition from_card (d : fc_data) : option bool :=
  if d is FC_card v then Some v else None.

Definition from_commit (d : fc_data) : option (seq bool) :=
  if d is FC_commit cs then Some cs else None.

Lemma from_card_FC_card (v : bool) :
  from_card (FC_card v) = Some v.
Proof. by []. Qed.

Lemma from_commit_FC_commit (cs : seq bool) :
  from_commit (FC_commit cs) = Some cs.
Proof. by []. Qed.

(* ========================================================================== *)
(* Session-Typed Wrappers                                                     *)
(* ========================================================================== *)

(* Reveal a card face value *)
Definition FCReveal {party n env} (dst : nat) (v : bool)
    (p : @sproc fc_dtype fc_data party n env)
    : @sproc fc_dtype fc_data party n.+1 (senv_send env dst DT_CardVal) :=
  SSend dst DT_CardVal (FC_card v) p.

(* Send a commitment pair *)
Definition FCCommit {party n env} (dst : nat) (cs : seq bool)
    (p : @sproc fc_dtype fc_data party n env)
    : @sproc fc_dtype fc_data party n.+1 (senv_send env dst DT_Commit) :=
  SSend dst DT_Commit (FC_commit cs) p.

(* Observe a revealed card *)
Definition FCObserve {party n env} (src : nat)
    (f : bool -> @sproc fc_dtype fc_data party n env)
    : @sproc fc_dtype fc_data party n.+1 (senv_recv env src DT_CardVal) :=
  SRecv src DT_CardVal (fun d =>
    match from_card d with
    | Some v => f v
    | None => SFail
    end).

(* Receive a commitment *)
Definition FCRecvCommit {party n env} (src : nat)
    (f : seq bool -> @sproc fc_dtype fc_data party n env)
    : @sproc fc_dtype fc_data party n.+1 (senv_recv env src DT_Commit) :=
  SRecv src DT_Commit (fun d =>
    match from_commit d with
    | Some cs => f cs
    | None => SFail
    end).

(* Terminal state *)
Definition FCFinish {party : nat}
    : @sproc fc_dtype fc_data party 1 senv_end :=
  SFinish.

(* Arguments declarations for implicit parameters *)
Arguments FCReveal {party n env}.
Arguments FCCommit {party n env}.
Arguments FCObserve {party n env}.
Arguments FCRecvCommit {party n env}.
Arguments FCFinish {party}.
