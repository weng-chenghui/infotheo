(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* den Boer instance view-level secrecy. The five-card trick computes a && b  *)
(* under a uniform cyclic cut; revealing one card leaks nothing about the      *)
(* secret. This packages five_card_leakage's leak_k1 as a CyclicCut mechanism. *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset tuple bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import pgg_leakage_witness pgg_cyclic_cut_leakage.
From pgg_smc Require Import pgg_sharing_mechanism five_card_leakage.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section denboer_secrecy.
Variable R : realType.

Let dbP := P R.

(** denboer_indep — the one-card view is independent of the secret a && b.
    @composes: denboer_view_secrecy *)
Lemma denboer_indep : dbP |= ViewA R [:: 0%N] _|_ Secret R.
Proof. by apply/inde_RV_sym; apply: mutual_info_RV0_indep; exact: leak_k1. Qed.

Definition denboer_ccd : CyclicCutData dbP :=
  @MkCyclicCutData _ _ dbP _ _ (Secret R) (ViewA R [:: 0%N]) denboer_indep.

Definition denboer_mechanism : SharingMechanism dbP 0 0 :=
  @CyclicCut _ _ dbP 0 0 denboer_ccd.

(** denboer_view_secrecy — one revealed card of the five-card trick carries zero
    information about the secret a && b.
    @main security: zero mutual information and unchanged conditional entropy for
    the single-card view. *)
Lemma denboer_view_secrecy :
  `I( lw_secret (mechanism_leakage denboer_mechanism) ;
      lw_view  (mechanism_leakage denboer_mechanism) ) = 0%R /\
  `H( lw_secret (mechanism_leakage denboer_mechanism) |
      lw_view  (mechanism_leakage denboer_mechanism) )
    = `H `p_ (lw_secret (mechanism_leakage denboer_mechanism)).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.

End denboer_secrecy.
