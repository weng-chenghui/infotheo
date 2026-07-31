(* MUTANT 3 of probe_spp_bridge_shape.v: the two-point counterexample
   refuting the single-fibre mutation of cond_law_to_bind.  Unlike the
   other mutants this file COMPILES: it proves the mutated implication
   false, so the guard "at every mass-carrying fibre" is load-bearing.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_spp_bridge_shape_mut3.v     *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba jfdist_cond.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section counter.
Context {R : realType}.

(* The uniform prior on two points, with the view and the conditioning
   data both the identity, and the constant Dirac kernel at ord0. *)
Definition p2 : R.-fdist 'I_2 := @fdist_uniform R _ 1 (card_ord 2).
Definition v2 : {RV p2 -> 'I_2} := id.
Definition kv2 : {RV p2 -> 'I_2} := id.
Definition k2 (kk : 'I_2) : R.-fdist 'I_2 := @fdist1 R _ ord0.

Lemma p2E i : p2 i = 2%:R^-1.
Proof. by rewrite /p2 fdist_uniformE card_ord. Qed.

Lemma law_v2 : `p_ v2 = p2.
Proof. by rewrite /dist_of_RV /v2 fdistmap_id. Qed.

Lemma law_kv2 : `p_ kv2 = p2.
Proof. by rewrite /dist_of_RV /kv2 fdistmap_id. Qed.

Lemma law_bind : `p_ kv2 >>= k2 = @fdist1 R _ ord0.
Proof.
by apply/fdist_ext => x; rewrite fdistbindE -big_distrl/= FDist.f1 mul1r.
Qed.

(* The conditional law does match the kernel on the fibre ord0. *)
Lemma counter_hyp v : `Pr[ v2 = v | kv2 = ord0 ] = k2 ord0 v.
Proof.
rewrite cpr_eqE /k2 fdist1E.
have Hk : pfwd1 kv2 ord0 = 2%:R^-1 by rewrite -dist_of_RVE law_kv2 p2E.
rewrite Hk !pfwd1E.
case: (altP (v =P ord0)) => [->|vn].
  rewrite (_ : finset _ = [set ord0 : 'I_2]).
    by rewrite Pr_set1 p2E divff // invr_neq0 // pnatr_eq0.
  by apply/setP => u; rewrite !inE /= xpair_eqE andbb.
rewrite (_ : finset _ = set0) ?Pr_set0 ?(negbTE vn) //.
  by rewrite mul0r.
apply/setP => u; rewrite !inE /= xpair_eqE.
rewrite /v2 /kv2 /=; apply/negbTE.
by apply: contra vn => /andP[/eqP <- /eqP ->].
Qed.

(* The bind factorization nevertheless fails: the fibre lift ord0 ord0
   carries mass 2^-1 under the view but no mass under the bind. *)
Lemma counter_concl : `p_ v2 <> `p_ kv2 >>= k2.
Proof.
move=> H; move: (p2E (lift ord0 ord0)); rewrite -law_v2 H law_bind fdist1E.
have H0 : (lift (ord0 : 'I_2) ord0 == ord0) = false.
  by apply/negbTE; rewrite eq_sym neq_lift.
by rewrite H0 mulr0n => /esym/eqP; rewrite invr_eq0 pnatr_eq0.
Qed.

(* The single-fibre mutation of cond_law_to_bind is false. *)
Lemma counter_single_fibre :
  ~ ((`Pr[ kv2 = ord0 ] != 0 ->
      forall v : 'I_2, `Pr[ v2 = v | kv2 = ord0 ] = k2 ord0 v) ->
     `p_ v2 = `p_ kv2 >>= k2).
Proof.
by move=> Hmut; apply: counter_concl; apply: Hmut => _ v; exact: counter_hyp.
Qed.

End counter.
