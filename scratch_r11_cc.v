From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix.
From mathcomp Require Import mathcomp_extra reals.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext fdist.
Require Import proba jfdist_cond graphoid.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Import GRing.Theory.

Section cond_functional_comp.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (Wfin Mfin : finType).
Variables (W : {RV P -> Wfin}) (S V2 : {RV P -> Mfin}).
Variable guess_fn : Wfin -> Mfin -> Mfin.
Let GuessRV : {RV P -> Mfin} := fun u => guess_fn (W u) (S u).

Hypothesis HW : P |= W _|_ V2 | S.

(* Direct comp via cinde_RV def + creasoning_by_cases over W. *)
Lemma guess_cinde : P |= GuessRV _|_ V2 | S.
Proof.
move=> g v2 s.
Admitted.

End cond_functional_comp.
