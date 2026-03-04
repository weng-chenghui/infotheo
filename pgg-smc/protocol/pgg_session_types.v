(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
Require Import smc_session_types pgg_interface.

(******************************************************************************)
(* PGG-SMC: Session-Typed Wrappers                                            *)
(*                                                                            *)
(* Session-typed wrappers for the PGG protocol, following the pattern of      *)
(* dsdp_session_types.v. Each Send/Recv variant has a fixed dtype.            *)
(*                                                                            *)
(*   PGGSend_sheet dst i p == send sheet index i as DT_Sheet                  *)
(*   PGGSend_share dst s p == send share s as DT_Share                        *)
(*   PGGSend_idx dst k p   == send word index k as DT_Idx                     *)
(*   PGGRecv_sheet src f   == receive DT_Sheet, extract 'I_N, apply f         *)
(*   PGGRecv_share src f   == receive DT_Share, extract seq ('I_N), apply f   *)
(*   PGGRecv_idx src f     == receive DT_Idx, extract nat, apply f            *)
(*   PGGInit x p           == store local data x, continue with p            *)
(*   PGGRet x              == return data x                                   *)
(*   PGGFinish             == terminal state                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_session_wrappers.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let data := pgg_data N.

(* Send a sheet index *)
Definition PGGSend_sheet {party n env} (dst : nat) (i : 'I_N)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Sheet) :=
  SSend dst DT_Sheet (PGG_sheet i) p.

(* Send a share *)
Definition PGGSend_share {party n env} (dst : nat) (s : seq ('I_N))
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Share) :=
  SSend dst DT_Share (PGG_share s) p.

(* Send a word index *)
Definition PGGSend_idx {party n env} (dst : nat) (k : nat)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Idx) :=
  SSend dst DT_Idx (@PGG_idx N k) p.

(* Receive a sheet index *)
Definition PGGRecv_sheet {party n env} (src : nat)
    (f : 'I_N -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Sheet) :=
  SRecv src DT_Sheet (fun d =>
    match from_sheet d with
    | Some i => f i
    | None => SFail
    end).

(* Receive a share *)
Definition PGGRecv_share {party n env} (src : nat)
    (f : seq ('I_N) -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Share) :=
  SRecv src DT_Share (fun d =>
    match from_share d with
    | Some s => f s
    | None => SFail
    end).

(* Receive a word index *)
Definition PGGRecv_idx {party n env} (src : nat)
    (f : nat -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Idx) :=
  SRecv src DT_Idx (fun d =>
    match from_idx d with
    | Some k => f k
    | None => SFail
    end).

(* Init/Ret/Finish wrappers *)
Definition PGGInit {party n env} (x : data) (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 env :=
  SInit x p.

Definition PGGRet {party : nat} (x : data)
    : @sproc pgg_dtype data party 2 senv_end :=
  SRet x.

Definition PGGFinish {party : nat}
    : @sproc pgg_dtype data party 1 senv_end :=
  SFinish.

End pgg_session_wrappers.

Arguments PGGSend_sheet {M party n env}.
Arguments PGGSend_share {M party n env}.
Arguments PGGSend_idx {M party n env}.
Arguments PGGRecv_sheet {M party n env}.
Arguments PGGRecv_share {M party n env}.
Arguments PGGRecv_idx {M party n env}.
Arguments PGGInit {M party n env}.
Arguments PGGRet {M party}.
Arguments PGGFinish {M party}.
