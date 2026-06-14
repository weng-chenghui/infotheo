(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* View-level secrecy interface: a LeakageWitness packages a secret random    *)
(* variable with a view independent of it, and the generic tail turns that     *)
(* independence into zero mutual information and unchanged conditional entropy. *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section leakage_witness.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

(** LeakageWitness — a secret random variable together with a view random
    variable that is statistically independent of it.
    @intent: the interface a sub-threshold coalition view satisfies; the secret
    and view finTypes are packed as fields so additive ('Z_N secret) and card
    (bool secret) instances inhabit the one type. *)
Record LeakageWitness := MkLeakageWitness {
  lw_secretT : finType ;
  lw_viewT   : finType ;
  lw_secret  : {RV P -> lw_secretT} ;
  lw_view    : {RV P -> lw_viewT} ;
  lw_indep   : P |= lw_view _|_ lw_secret }.

(** leakage_of_view_indep — a view independent of the secret carries zero mutual
    information with it and leaves the secret's entropy unchanged.
    @main security: distributional secrecy of a sub-threshold view. *)
Lemma leakage_of_view_indep (secretT viewT : finType)
    (Secret : {RV P -> secretT}) (view : {RV P -> viewT}) :
  P |= view _|_ Secret ->
  `I( Secret ; view ) = 0%R /\ `H( Secret | view ) = `H `p_ Secret.
Proof.
move=> Hinde0.
have Hinde : P |= Secret _|_ view by exact/inde_RV_sym/Hinde0.
have HcondE : `H( Secret | view ) = `H `p_ Secret.
  have := chain_rule_RV view Secret.
  rewrite -joint_entropy_RVC (inde_RV_joint_entropyE Hinde) => H1.
  have : (`H `p_ view + `H( Secret | view ) = `H `p_ view + `H `p_ Secret)%R.
    by rewrite -H1 addrC.
  by move/addrI.
split; last exact: HcondE.
by rewrite mutual_info_RVE HcondE subrr.
Qed.

End leakage_witness.

Arguments LeakageWitness {R U} P.
Arguments leakage_of_view_indep {R U P secretT viewT}.
