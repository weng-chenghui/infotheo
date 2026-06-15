(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* A concrete inhabitant of RandomizedSharing over a uniform iid row-vector   *)
(* tape: the secret is the head coordinate, the masks are the remaining       *)
(* coordinates, all drawn iid uniform over Z/N.                               *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop matrix perm zmodp.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln ssralg_ext fdist proba entropy graphoid.
From pgg_smc Require Import pgg_fdist_rV_indep pgg_randomized_sharing.

Import GRing.Theory Num.Theory.
Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope.
Local Open Scope ring_scope. Local Open Scope vec_ext_scope.

Section canonical_sharing.
Variable R : realType.
Variable N' T' : nat.
Let N := N'.+2.
Let card_ZN : #|'Z_N| = N'.+1.+1.
Proof. by rewrite card_ord. Qed.
Let P0 : R.-fdist 'Z_N := fdist_uniform card_ZN.
Let P  : R.-fdist 'rV['Z_N]_(T'.+1) := P0 `^ T'.+1.

Definition unif_secret : {RV P -> 'Z_N} := fun v => v ord0 ord0.

Definition unif_mask (k : 'I_T') : {RV P -> 'Z_N} := fun v => v ord0 (lift ord0 k).

(** @composes: unif_randomized_sharing *)
Lemma unif_mask_unif (k : 'I_T') : `p_ (unif_mask k) = fdist_uniform card_ZN.
Proof.
have -> : `p_ (unif_mask k) = fdist_nth P (lift ord0 k) by [].
exact: fdist_nth_unif.
Qed.

(** @composes: unif_randomized_sharing *)
Lemma unif_masks_indep :
  P |= ((fun u => [ffun i : 'I_T' => unif_mask i u]) : {RV P -> {ffun 'I_T' -> 'Z_N}})
     _|_ unif_secret.
Proof.
have Hmv : ((fun u => [ffun i : 'I_T' => unif_mask i u]) : {RV P -> {ffun 'I_T' -> 'Z_N}})
  = (fun t : 'rV['Z_N]_T' => [ffun i : 'I_T' => t``_i])
      `o (fun v : 'rV['Z_N]_(T'.+1) => rbehead v).
  rewrite /comp_RV; apply: boolp.funext => v; apply/ffunP => i.
  rewrite !ffunE /unif_mask mxE.
  congr (v _ _).
rewrite Hmv.
apply/inde_RV_sym.
have Hsec : unif_secret = (fun v : 'rV['Z_N]_(T'.+1) => idfun v``_ord0) by [].
rewrite Hsec /comp_RV.
exact: (@inde_RV_head_rV R 'Z_N P0 T' 'Z_N _ idfun
          (fun t : 'rV['Z_N]_T' => [ffun i : 'I_T' => t``_i])).
Qed.

(** @composes: unif_randomized_sharing *)
Lemma unif_mask_indep (k : 'I_T') :
  P |= unif_mask k
     _|_ [% unif_secret,
            ((fun u => [ffun i : 'I_T' => if i == k then 0 else unif_mask i u])
              : {RV P -> {ffun 'I_T' -> 'Z_N}})].
Proof.
pose g := fun t : 'rV['Z_N]_T' =>
  (t``_k, [ffun i : 'I_T' => if i == k then 0 else t``_i] : {ffun 'I_T' -> 'Z_N}).
have Hrhs : [% unif_secret,
            ((fun u => [ffun i : 'I_T' => if i == k then 0 else unif_mask i u])
              : {RV P -> {ffun 'I_T' -> 'Z_N}})]
  = (fun v : 'rV['Z_N]_(T'.+1) => g (rbehead (col_perm (tperm ord0 (lift ord0 k)) v))).
  apply: boolp.funext => v; rewrite /g /=.
  have Hidx : forall j : 'I_T',
      (rbehead (col_perm (tperm ord0 (lift ord0 k)) v))``_j
      = v``_(tperm ord0 (lift ord0 k) (lift ord0 j)).
    by move=> j; rewrite mxE mxE.
  have Hidxk : (rbehead (col_perm (tperm ord0 (lift ord0 k)) v))``_k = unif_secret v.
    by rewrite Hidx tpermR.
  have Hidxj : forall j : 'I_T', j != k ->
      (rbehead (col_perm (tperm ord0 (lift ord0 k)) v))``_j = unif_mask j v.
    move=> j Hjk; rewrite Hidx tpermD.
    - by [].
    - exact: neq_lift.
    - by rewrite (inj_eq lift_inj) eq_sym.
  congr (_, _).
  - by rewrite Hidxk.
  - apply/ffunP => i; rewrite !ffunE.
    case: ifPn => [//|Hik].
    by rewrite Hidxj.
rewrite Hrhs.
have Hlhs : unif_mask k = (fun v : 'rV['Z_N]_(T'.+1) => v``_(lift ord0 k)) by [].
rewrite Hlhs.
exact: (@inde_RV_nth_rV R 'Z_N P0 T' _ (lift ord0 k) g).
Qed.

(* The record packs `p_ (rsh_mask k) = fdist_uniform (card_ZN_subproof N'),
   where card_ZN_subproof N' is the cardinality proof generated inside
   pgg_randomized_sharing. It is a distinct proof term from this section's
   card_ZN Let, so we transport across it by proof irrelevance. *)
(** @composes: unif_randomized_sharing *)
Lemma unif_mask_unif_subproof (k : 'I_T') :
  `p_ (unif_mask k) = fdist_uniform (pgg_randomized_sharing.card_ZN_subproof N').
Proof.
by rewrite (eq_irrelevance (pgg_randomized_sharing.card_ZN_subproof N') card_ZN)
           unif_mask_unif.
Qed.

(** unif_randomized_sharing — the uniform iid tape as a RandomizedSharing,
    witnessing the record is inhabited.
    @intent: a concrete T-of-T additive sharing whose masks are iid uniform and
    independent of the secret. *)
Definition unif_randomized_sharing : RandomizedSharing P N' T' :=
  @MkRandomizedSharing _ _ P N' T' unif_secret unif_mask
    unif_mask_unif_subproof unif_masks_indep unif_mask_indep.

End canonical_sharing.
