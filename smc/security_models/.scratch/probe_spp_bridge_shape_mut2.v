(* MUTANT 2 of probe_spp_bridge_shape.v.  The guard is flipped, so the
   hypothesis constrains only the zero-mass fibres and leaves the kernel
   free on every mass-carrying fibre.
   This file is EXPECTED TO FAIL to compile.                          *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba jfdist_cond.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section bridge_shape.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (B K : finType).
Variable V : {RV P -> B}.
Variable Kv : {RV P -> K}.
Variable k : K -> R.-fdist B.

Lemma cond_law_to_bind :
  (forall kk : K, `Pr[ Kv = kk ] = 0 ->
     forall v : B, `Pr[ V = v | Kv = kk ] = k kk v) ->
  `p_ V = `p_ Kv >>= k.
Proof.
move=> H; apply/fdist_ext => v.
rewrite fdistbindE -(fst_RV2 V Kv) fdist_fstE.
apply: eq_bigr => kk _; rewrite !dist_of_RVE.
case: (eqVneq `Pr[ Kv = kk ] 0) => [Hz|Hnz].
  by rewrite Hz mul0r pfwd1_domin_RV1.
by rewrite -H // cpr_eqE mulrC divfK.
Qed.

End bridge_shape.
