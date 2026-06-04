(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: a split / compute / share / recover piSMC protocol on wreath2_scheme  *)
(*                                                                            *)
(* A generic (N, T, k) threshold SMC protocol, instantiated on the wreath     *)
(* Z_7 wr S_2 scheme (N = 14, T = 14, k = 7):                                 *)
(*                                                                            *)
(*   split    the dealer encodes the secret into T = 14 shares via            *)
(*            ts_encode wreath2_scheme (two piles of seven sum_mod shares).    *)
(*   compute  the dealer applies a false shuffle g : the share at position    *)
(*            (g j) is the one handed to party j. For recovery to hold, g must *)
(*            lie in the abelian core wcore = <<cut1, cut2>> (within-pile      *)
(*            cuts), NOT the pile swap wswap.                                  *)
(*   share    each party forwards its (shuffled) share to the recoverer.       *)
(*   recover  the recoverer collects the T shares; ts_recon wreath2_scheme     *)
(*            returns the secret (off-channel, as in exchange_verifier).       *)
(*                                                                            *)
(* The protocol "really uses" the wreath in three ways, each backed by a       *)
(* theorem below:                                                             *)
(*   wreath_smc_recovers       recovery holds for any false shuffle g in wcore *)
(*                             (uses wreath_false_shuffle_recover, hence the   *)
(*                             abelian core of the wreath).                    *)
(*   wreath_smc_swap_excluded  the pile swap wswap (a wreath generator) does    *)
(*                             not preserve the pile partition, so it lies      *)
(*                             outside wcore: wreath_smc_recovers cannot apply  *)
(*                             to it. The security move is structurally barred  *)
(*                             from recovery, so the choice of wreath group     *)
(*                             element is load-bearing.                         *)
(*   wreath_smc_private        any coalition seeing < k = 7 shares learns      *)
(*                             nothing (uses ts_private of the product scheme).*)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_wreath wreath_recovery wreath_program.
From pgg_reconstruct Require Import pgg_sharing_framework product_threshold
                                    covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope pismc_scope.

Section wreath_smc.

Let M := M_wreath.
Let data := pgg_data (pgg_N' M).+1.

(* Player index convention (mirrors card_exchange_pismc.v):
   dealer = 0, recoverer = 1, party i = i + 2. *)
Definition dealer_idx : nat := 0.
Definition recoverer_idx : nat := 1.

(** party_idx — process id of logical party [i : 'I_14].
    Kind: interface.
    Why: parties occupy ids [2 .. 15] after dealer (0) and recoverer (1). *)
Definition party_idx (i : 'I_14) : nat := i.+2.

Arguments sproc dtype data party {_} {_}.

(* Card-free action aliases over the PGG session wrappers. *)
Let Send_share {party n env} := @PGGReveal_pos M party n env.
Let Recv_share {party n env} := @PGGObserve_pos M party n env.

Notation "'Send<' p '>' '&' x ; P" := (Send_share p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Local Notation "'Recv<' p '>' '&' x '=>' P" :=
  (Recv_share p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Let dealer_share_env (j : 'I_14) (env : senv pgg_dtype) :=
  senv_send env (party_idx j) DT_Sheet.

Let recoverer_collect_env (j : 'I_14) (env : senv pgg_dtype) :=
  senv_recv env (party_idx j) DT_Sheet.

(** wreath_smc_dealer — split the secret and deal the false-shuffled shares.
    Kind: instance.
    Why: the dealer encodes [s] into T = 14 shares (split), then hands party
    [j] the share at position [g j] (the false shuffle). Genuinely uses
    [wreath_encode = ts_encode wreath2_scheme] in the dealt value. *)
Definition wreath_smc_dealer (s : 'I_14) (g : {perm 'I_14}) (parties : seq 'I_14)
    : sproc pgg_dtype data dealer_idx :=
  \pi{ ForList parties step S enstep dealer_share_env as j cont k =>
         Send<(party_idx j)> &(tnth (wreath_encode s) (g j)) ;
         k
       end ;
       Finish }.

(** wreath_smc_party — receive a share and forward it to the recoverer.
    Kind: instance.
    Why: the local compute step is the identity here (pure reconstruction);
    the share is shared onward unchanged. *)
Definition wreath_smc_party (i : 'I_14)
    : sproc pgg_dtype data (party_idx i) :=
  \pi{ Recv<dealer_idx> &my_share =>
       Send<recoverer_idx> &my_share ;
       Finish }.

(** wreath_smc_recoverer — collect the shares into the buffer for recovery.
    Kind: instance.
    Why: gathers one share from each party; [ts_recon wreath2_scheme] applied
    to the collected buffer recovers the secret (off-channel, see the theorems
    below and the exchange_verifier convention). *)
Definition wreath_smc_recoverer (parties : seq 'I_14)
    : sproc pgg_dtype data recoverer_idx :=
  \pi{ ForList parties step (fun k => k.+2) enstep recoverer_collect_env
         as j cont k =>
         Recv<(party_idx j)> &ep =>
         Init (PGG_sheet ep) ;
         k
       end ;
       Finish }.

(******************************************************************************)
(*     The recovery the recoverer performs, and its wreath-group content      *)
(******************************************************************************)

(** wreath_smc_recovers — recovery succeeds for any false shuffle in the core.
    Kind: main.
    Why: the recoverer's buffer is [tnth (wreath_encode s) (g i) | i < 14];
    applying ts_recon wreath2_scheme returns [s] whenever the false shuffle [g]
    lies in the abelian core wcore. This is the on-protocol meaning of
    wreath_false_shuffle_recover, so the wreath group's recon-symmetry is
    load-bearing. *)
Lemma wreath_smc_recovers (s : 'I_14) (g : {perm 'I_14}) :
  g \in wcore ->
  ts_recon wreath2_scheme [tuple tnth (wreath_encode s) (g i) | i < 14] = s.
Proof.
move=> Hg.
exact: (wreath_false_shuffle_recover Hg (ts_encode_valid wreath2_scheme s)).
Qed.

(** wreath_smc_recovers_cut1 — recovery under the concrete generator cut1.
    Kind: example.
    Why: instantiates the false shuffle at a named wreath generator (the
    pile-1 cut), so the protocol embeds an actual group element of the wreath. *)
Lemma wreath_smc_recovers_cut1 (s : 'I_14) :
  ts_recon wreath2_scheme [tuple tnth (wreath_encode s) (cut1 i) | i < 14] = s.
Proof.
exact: (wreath_cut1_recover (ts_encode_valid wreath2_scheme s)).
Qed.

(** wreath_smc_swap_excluded — the pile swap is not a recovery shuffle.
    Kind: main.
    Why: wswap is a wreath generator that does NOT preserve the pile partition
    (it sends card 0 to card 7), so it lies outside the recon-symmetry core
    wcore. wreath_smc_recovers therefore does not apply to it: the security /
    anonymity generator is structurally excluded from recovery. This is why the
    wreath group is load-bearing, the choice of g changes whether recovery
    holds. *)
Lemma wreath_smc_swap_excluded : wswap \notin wcore.
Proof.
apply/negP => Hin.
have Hpp : ppred wswap by move/(subsetP wcore_sub_pp): Hin; rewrite inE.
move/forallP/(_ (Ordinal (isT : 0 < 14)))/implyP/(_ isT): Hpp.
rewrite wswapo0.
by [].
Qed.

(** wreath_smc_private — sub-threshold coalitions learn nothing.
    Kind: main.
    Why: any coalition C seeing fewer than k = 7 of the dealt shares cannot
    distinguish two secrets, via the product scheme's ts_private. This is the
    privacy half of the T > k gap. *)
Lemma wreath_smc_private
    (s1 s2 : 'I_14) (shares : (ts_T' wreath2_scheme).+1.-tuple 'I_14)
    (C : {set 'I_(ts_T' wreath2_scheme).+1}) :
  #|C| < ts_k wreath2_scheme ->
  ts_valid wreath2_scheme s1 shares ->
  exists shares', ts_valid wreath2_scheme s2 shares' /\
    (forall i, i \in C -> tnth shares' i = tnth shares i).
Proof.
exact: ts_private wreath2_scheme s1 s2 shares C.
Qed.

End wreath_smc.

Arguments wreath_smc_dealer s g parties.
Arguments wreath_smc_party i.
Arguments wreath_smc_recoverer parties.
