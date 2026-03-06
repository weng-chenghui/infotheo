(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types.

(******************************************************************************)
(* PGG-SMC: piSMC Protocol Programs                                          *)
(*                                                                            *)
(* Session-typed protocol programs using \pi{...} notation for the            *)
(* covering-space MPC protocol:                                               *)
(*   pdealer parties W P_idx == dealer distributes shares and word index      *)
(*   pparty i                == party i computes and sends endpoint           *)
(*   precon parties          == reconstructor collects endpoints              *)
(*                                                                            *)
(* Send/Recv notation markers (inside custom pismc):                          *)
(*   Send<p> &x   sends sheet index x as DT_Sheet                            *)
(*   Send<p> #x   sends share x as DT_Share                                  *)
(*   Send<p> $x   sends word index x as DT_Idx                               *)
(*   Recv<p> &x   receives DT_Sheet, binds x : 'I_N                          *)
(*   Recv<p> #x   receives DT_Share, binds x : seq ('I_N)                    *)
(*   Recv<p> $x   receives DT_Idx, binds x : nat                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope pismc_scope.

Section pgg_pismc.

Variable M : MonodromyReprType.
Variable PI : PGG_Interface M.

Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let gT := pgg_gT M.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.
Let data := pgg_data N.

(* Party indices *)
Definition dealer_idx : nat := 0.
Definition recon_idx : nat := 1.
Definition party_idx (i : 'I_T) : nat := i.+2.

(* Make sproc type annotations concise *)
Arguments sproc dtype data party {_} {_}.

(* Session wrapper aliases — one per dtype, like DSend in DSDP *)
Let Send_sheet {party n env} := @PGGSend_sheet M party n env.
Let Send_share {party n env} := @PGGSend_share M party n env.
Let Send_idx {party n env} := @PGGSend_idx M party n env.
Let Recv_sheet {party n env} := @PGGRecv_sheet M party n env.
Let Recv_share {party n env} := @PGGRecv_share M party n env.
Let Recv_idx {party n env} := @PGGRecv_idx M party n env.

(** * Send notations — dtype marker selects the send function *)

Notation "'Send<' p '>' '&' x ; P" := (Send_sheet p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Send<' p '>' '#' x ; P" := (Send_share p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Send<' p '>' '$' x ; P" := (Send_idx p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(** * Recv notations — dtype marker selects the recv function *)

Local Notation "'Recv<' p '>' '&' x '=>' P" :=
  (Recv_sheet p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Local Notation "'Recv<' p '>' '#' x '=>' P" :=
  (Recv_share p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Local Notation "'Recv<' p '>' '$' x '=>' P" :=
  (Recv_idx p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(******************************************************************************)
(** * Environment Step Functions for ForList                                  *)
(******************************************************************************)

Let dealer_share_env (j : 'I_T) (env : senv pgg_dtype) :=
  senv_send env (party_idx j) DT_Share.

Let dealer_idx_env (j : 'I_T) (env : senv pgg_dtype) :=
  senv_send env (party_idx j) DT_Idx.

Let recon_env_step (j : 'I_T) (env : senv pgg_dtype) :=
  senv_recv env (party_idx j) DT_Sheet.

(******************************************************************************)
(** * PGG Protocol Programs                                                   *)
(******************************************************************************)

(* Dealer: distribute shares to each party, broadcast word index *)
Definition pdealer (parties : seq 'I_T) (W : seq gT) (P_idx : nat)
    : sproc pgg_dtype data dealer_idx :=
  \pi{ Init (@PGG_idx N P_idx) ;
     ForList parties step S enstep dealer_share_env as j cont k =>
       Send<(party_idx j)> #(share PI W j) ;
       k
     end ;
     ForList parties step S enstep dealer_idx_env as j cont k =>
       Send<(party_idx j)> $(P_idx) ;
       k
     end ;
     Finish }.

(* Party i: receive share + word index, compute endpoint, send to recon *)
Definition pparty (i : 'I_T)
    : sproc pgg_dtype data (party_idx i) :=
  \pi{ Recv<dealer_idx> #my_share =>
     Recv<dealer_idx> $word_idx =>
     Send<recon_idx> &(nth ord0 my_share word_idx) ;
     Finish }.

(* Reconstructor: collect all endpoints from parties *)
Definition precon (parties : seq 'I_T)
    : sproc pgg_dtype data recon_idx :=
  \pi{ ForList parties step (fun k => k.+2) enstep recon_env_step as j cont k =>
       Recv<(party_idx j)> &ep =>
       Init (PGG_sheet ep) ;
       k
     end ;
     Finish }.

End pgg_pismc.

Arguments pdealer {M} PI.
Arguments pparty {M} PI.
Arguments precon {M} PI.

(******************************************************************************)
(** * Session Type Duality Verification (Idealized, 2-party)                  *)
(******************************************************************************)

Section pgg_idealized_duality.

(* Concrete PGGTypes: symmetric group on N sheets *)
Variable n : nat.
Let N := n.+2.
Let gT : finGroupType := {perm 'I_N}.
Let G : {group gT} := [set: gT].

(* Identity morphism on permutation group *)
Lemma id_perm_morphM :
  {in G &, {morph (@id gT) : x y / (x * y)%g}}.
Proof. by []. Qed.

Definition id_perm_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism id_perm_morphM.

Definition Idealized_PGGTypes := @MkPGG gT N.-1 G.

Definition Idealized_isMonodromyRepr : isMonodromyRepr Idealized_PGGTypes.
Proof.
constructor.
rewrite /Idealized_PGGTypes /=.
exact: id_perm_morph.
Defined.

Definition Idealized_MonodromyRepr : MonodromyReprType :=
  @MonodromyRepr.Pack Idealized_PGGTypes
    (@MonodromyRepr.Class Idealized_PGGTypes Idealized_isMonodromyRepr).

(* 2-party interface: starts = [0, 1] *)
Let M := Idealized_MonodromyRepr.

Definition test_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

Lemma test_starts_2_uniq : uniq test_starts_2.
Proof. by native_compute. Qed.

Definition Test_PGG_2 : PGG_Interface M :=
  @MkPGGI M 1 test_starts_2 test_starts_2_uniq.

Let PI := Test_PGG_2.
Let data := pgg_data (pgg_N' M).+1.

(* Concrete party list *)
Let parties_2 : seq 'I_2 :=
  [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

(* Variable data for programs *)
Variables (W : seq {perm 'I_N}) (P_idx : nat).

Local Open Scope sproc_scope.

(* Wrap as aprocs for duality checking *)
Definition ap_dealer_2 :=
  mk_aproc (pdealer PI parties_2 W P_idx).
Definition ap_party0_2 :=
  mk_aproc (pparty PI (@Ordinal 2 0 isT)).
Definition ap_party1_2 :=
  mk_aproc (pparty PI (@Ordinal 2 1 isT)).
Definition ap_recon_2 :=
  mk_aproc (precon PI parties_2).

(* 4-process duality: all 6 pairs *)
Lemma dealer_party0_dual_2 : channels_dual ap_dealer_2 ap_party0_2.
Proof. by native_compute. Qed.

Lemma dealer_party1_dual_2 : channels_dual ap_dealer_2 ap_party1_2.
Proof. by native_compute. Qed.

Lemma dealer_recon_dual_2 : channels_dual ap_dealer_2 ap_recon_2.
Proof. by native_compute. Qed.

Lemma party0_party1_dual_2 : channels_dual ap_party0_2 ap_party1_2.
Proof. by native_compute. Qed.

Lemma party0_recon_dual_2 : channels_dual ap_party0_2 ap_recon_2.
Proof. by native_compute. Qed.

Lemma party1_recon_dual_2 : channels_dual ap_party1_2 ap_recon_2.
Proof. by native_compute. Qed.

End pgg_idealized_duality.
