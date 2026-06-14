(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* kim instance view-level secrecy. Kim's FiveCardKim_M uses all five         *)
(* rotations sigma^0..sigma^4, which generate the same cyclic cut C_5 =        *)
(* <[fc_sigma]> as den Boer (kim_run_recovers is den_boer_run_recovers), and   *)
(* computes the same a && b. The single-card view leakage is therefore the     *)
(* same leak_k1 fact: five_card_leakage models the uniform 'I_5 cyclic cut and  *)
(* depends only on N = 5, not on either protocol. Kim's distinct contribution  *)
(* is the executed-trace layer, which is deferred.                             *)
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

Section kim_secrecy.
Variable R : realType.

Let kimP := P R.

(** kim_indep — the one-card view is independent of the secret a && b under
    Kim's uniform C_5 cut, the same fact as den Boer.
    @composes: kim_view_secrecy *)
Lemma kim_indep : kimP |= ViewA R [:: 0%N] _|_ Secret R.
Proof. by apply/inde_RV_sym; apply: mutual_info_RV0_indep; exact: leak_k1. Qed.

Definition kim_ccd : CyclicCutData kimP :=
  @MkCyclicCutData _ _ kimP _ _ (Secret R) (ViewA R [:: 0%N]) kim_indep.

Definition kim_mechanism : SharingMechanism kimP 0 0 :=
  @CyclicCut _ _ kimP 0 0 kim_ccd.

(** kim_view_secrecy — one revealed card of Kim's five-card family carries zero
    information about the secret a && b.
    @main security: zero mutual information and unchanged conditional entropy for
    the single-card view. *)
Lemma kim_view_secrecy :
  `I( lw_secret (mechanism_leakage kim_mechanism) ;
      lw_view  (mechanism_leakage kim_mechanism) ) = 0%R /\
  `H( lw_secret (mechanism_leakage kim_mechanism) |
      lw_view  (mechanism_leakage kim_mechanism) )
    = `H `p_ (lw_secret (mechanism_leakage kim_mechanism)).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.

End kim_secrecy.
