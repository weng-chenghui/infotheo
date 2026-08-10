(* AUDIT FILE (adversarial soundness audit, 2026-08-10).                      *)
(* Purpose: (1) tautology probe on the leak_view_set goal (Fail reflexivity / *)
(* Fail by []); (2) machine-check fc_adjacent's classification on ALL 10      *)
(* two-sets, not just the 3 the probe covers; (3) confirm the idP-opacity     *)
(* finding: inord / #| | are conversion-blocked, so the enum_val5/card_val5   *)
(* bridge is necessary.  Context transcribed from probe_decomposition.v;      *)
(* Abort is legitimate here (audit scratch, never imported).                  *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program five_card_leakage.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section audit_decomp_checks.

Variable R : realType.

Local Open Scope ring_scope.

Local Notation P := (P R).
Local Notation Secret := (Secret R).
Local Notation ViewA := (ViewA R).

Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

Definition set_tuple (A : {set 'I_5}) : #|A|.-tuple 'I_5 := enum_tuple A.

Definition ViewS (A : {set 'I_5}) : {RV P -> #|A|.-tuple bool} :=
  ViewT (set_tuple A).

Definition fc_adjacent (A : {set 'I_5}) : bool :=
  [exists i : 'I_5, A == [set i; succ5 i]].

Definition fc_leak (A : {set 'I_5}) : R :=
  match #|A| with
  | 0 => 0
  | 1 => 0
  | 2 => if fc_adjacent A
         then 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R
         else 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R / 20%:R) * log 7%:R
  | 3 => 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R
  | _ => 2%:R - (3%:R / 4%:R) * log 3%:R
  end.

Definition i0 : 'I_5 := Ordinal (isT : (0 < 5)%N).
Definition i1 : 'I_5 := Ordinal (isT : (1 < 5)%N).
Definition i2 : 'I_5 := Ordinal (isT : (2 < 5)%N).
Definition i3 : 'I_5 := Ordinal (isT : (3 < 5)%N).
Definition i4 : 'I_5 := Ordinal (isT : (4 < 5)%N).

Lemma succ5_val (i : 'I_5) : val (succ5 i) = (i.+1 %% 5)%N.
Proof. by rewrite /succ5 /= inordK // ltn_pmod. Qed.

(* ---- (1) tautology probe ---- *)

Lemma tauto_probe_abstract (A : {set 'I_5}) :
  `I( Secret ; ViewS A ) = fc_leak A.
Proof.
Fail reflexivity.
Fail (by []).
Abort.

Lemma tauto_probe_concrete :
  `I( Secret ; ViewS [set i0; i1] ) = fc_leak [set i0; i1].
Proof.
Fail reflexivity.
Fail (by []).
Abort.

(* ---- (2) fc_adjacent on all 10 two-sets ---- *)

Lemma adjT_01 : fc_adjacent [set i0; i1].
Proof.
apply/existsP; exists i0; apply/eqP; apply/setP => x.
rewrite !inE -!val_eqE /= succ5_val.
by case: x => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjT_12 : fc_adjacent [set i1; i2].
Proof.
apply/existsP; exists i1; apply/eqP; apply/setP => x.
rewrite !inE -!val_eqE /= succ5_val.
by case: x => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjT_23 : fc_adjacent [set i2; i3].
Proof.
apply/existsP; exists i2; apply/eqP; apply/setP => x.
rewrite !inE -!val_eqE /= succ5_val.
by case: x => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjT_34 : fc_adjacent [set i3; i4].
Proof.
apply/existsP; exists i3; apply/eqP; apply/setP => x.
rewrite !inE -!val_eqE /= succ5_val.
by case: x => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjT_40 : fc_adjacent [set i0; i4].
Proof.
apply/existsP; exists i4; apply/eqP; apply/setP => x.
rewrite !inE -!val_eqE /= succ5_val.
by case: x => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjF_02 : fc_adjacent [set i0; i2] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm i0. have h1 := hm i1. have h2 := hm i2.
have h3 := hm i3. have h4 := hm i4.
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= succ5_val.
by case: i => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjF_03 : fc_adjacent [set i0; i3] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm i0. have h1 := hm i1. have h2 := hm i2.
have h3 := hm i3. have h4 := hm i4.
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= succ5_val.
by case: i => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjF_13 : fc_adjacent [set i1; i3] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm i0. have h1 := hm i1. have h2 := hm i2.
have h3 := hm i3. have h4 := hm i4.
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= succ5_val.
by case: i => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjF_14 : fc_adjacent [set i1; i4] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm i0. have h1 := hm i1. have h2 := hm i2.
have h3 := hm i3. have h4 := hm i4.
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= succ5_val.
by case: i => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma adjF_24 : fc_adjacent [set i2; i4] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm i0. have h1 := hm i1. have h2 := hm i2.
have h3 := hm i3. have h4 := hm i4.
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= succ5_val.
by case: i => [[|[|[|[|[|m]]]]] Hm].
Qed.

(* ---- (3) idP opacity: conversion cannot reduce inord / #| | ---- *)

(* Ordinal literals DO reduce (control). *)
Check (erefl : val i0 = 0%N).

(* inord is conversion-blocked (insub matches Qed-opaque idP). *)
Fail Check (erefl : val (inord 0 : 'I_5) = 0%N).

(* cardinality of a set literal is conversion-blocked too. *)
Fail Check (erefl : #|[set i0]| = 1%N).

End audit_decomp_checks.
