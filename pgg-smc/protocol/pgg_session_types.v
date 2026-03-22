(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
Require Import smc_session_types pgg_interface.

(******************************************************************************)
(* PGG: Session-Typed Wrappers                                                *)
(*                                                                            *)
(* Session-typed wrappers for the PGG protocol, following the pattern         *)
(* of dsdp_session_types.v. Each action variant has a fixed dtype.            *)
(*                                                                            *)
(*   PGGReveal_pos dst i p    == reveal card position i (DT_Sheet)             *)
(*   PGGDeal_hand dst s p     == deal hand s to player (DT_Hand)               *)
(*   PGGAnnounce_idx dst k p  == announce selection index k (DT_Idx)           *)
(*   PGGObserve_pos src f     == observe card position, extract 'I_N, apply f  *)
(*   PGGReceive_hand src f    == receive dealt hand, extract seq 'I_N, apply f *)
(*   PGGReceive_idx src f     == receive announcement, extract nat, apply f    *)
(*   PGGInit x p              == store local data x, continue with p           *)
(*   PGGRet x                 == return data x                                 *)
(*   PGGFinish                == terminal state                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_session_wrappers.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let data := pgg_data N.

(* Reveal a card position *)
Definition PGGReveal_pos {party n env} (dst : nat) (i : 'I_N)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Sheet) :=
  SSend dst DT_Sheet (PGG_sheet i) p.

(* Deal a hand to a player *)
Definition PGGDeal_hand {party n env} (dst : nat) (s : seq ('I_N))
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Hand) :=
  SSend dst DT_Hand (PGG_hand s) p.

(* Announce shuffle selection *)
Definition PGGAnnounce_idx {party n env} (dst : nat) (k : nat)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Idx) :=
  SSend dst DT_Idx (@PGG_idx N k) p.

(* Observe a card position *)
Definition PGGObserve_pos {party n env} (src : nat)
    (f : 'I_N -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Sheet) :=
  SRecv src DT_Sheet (fun d =>
    match from_sheet d with
    | Some i => f i
    | None => SFail
    end).

(* Receive a dealt hand *)
Definition PGGReceive_hand {party n env} (src : nat)
    (f : seq ('I_N) -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Hand) :=
  SRecv src DT_Hand (fun d =>
    match from_hand d with
    | Some s => f s
    | None => SFail
    end).

(* Receive shuffle announcement *)
Definition PGGReceive_idx {party n env} (src : nat)
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

Arguments PGGReveal_pos {M party n env}.
Arguments PGGDeal_hand {M party n env}.
Arguments PGGAnnounce_idx {M party n env}.
Arguments PGGObserve_pos {M party n env}.
Arguments PGGReceive_hand {M party n env}.
Arguments PGGReceive_idx {M party n env}.
Arguments PGGInit {M party n env}.
Arguments PGGRet {M party}.
Arguments PGGFinish {M party}.
