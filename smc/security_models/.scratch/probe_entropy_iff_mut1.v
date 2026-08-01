(* Mutation/refutation certificates for the R7 probe.

   The implementation plan states Target 2 (the forward CI) without the
   delivery-law hypothesis H0, and Target 3/4 (the converse and the iff)
   without any hypothesis on the input split.  Both are refuted here at
   compiled instances, which is why the landed entropy_link.v carries
   delivery_law_ok on the forward lemma and an injective input split on the
   converse.

   PART A refutes "H1 + H2 => the pair CI" (Target 2 without H0).
   PART B refutes "H0 + full support + entropy equality => a simulator"
   (Target 3, and hence the reverse direction of Target 4, without an
   injective input split).

   The definitions are restated locally, verbatim from entropy_link.v with
   the section parameters instantiated, following the style of the other
   audit certificates in this directory.

   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_entropy_iff_mut1.v                 *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist proba.
Require Import jfdist_cond entropy graphoid divergence.
Require Import entropy_link.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Definition i1 : 'I_2 := Ordinal (isT : (1 < 2)%N).

Lemma i1_neq0 : i1 != ord0.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* PART A: the forward direction needs the delivery law.                *)
(* ------------------------------------------------------------------ *)

(* One corrupted party with a constant input projection and a constant
   read-off map, one honest party whose input is the whole input, a
   deterministic ideal functionality delivering the input, and a real run
   that always delivers the same output.  The real view is the input. *)

Section part_A_forward_needs_H0.
Context {R : realType}.

Definition muA : R.-fdist 'I_2 := fdist_uniform (card_ord 2).
Definition omegaA : R.-fdist 'I_1 := fdist1 ord0.
Definition dA : R.-fdist ('I_2 * 'I_1)%type := (muA `x omegaA)%fdist.

Definition FA (x : 'I_2) : R.-fdist 'I_2 := fdist1 x.
Definition view_atA (e : 'I_2 * 'I_1) : 'I_2 := e.1.
Definition runA (e : 'I_2 * 'I_1) : 'I_2 := ord0.
Definition out_advA (v : 'I_2) : 'I_2 := ord0.
Definition proj_xaA (x : 'I_2) : 'I_1 := ord0.
Definition proj_yhA (yl : 'I_2) : 'I_1 := ord0.

Definition view_rvA : {RV dA -> 'I_2} := view_atA.
Definition input_rvA : {RV dA -> 'I_2} := fst.
Definition ya_rvA : {RV dA -> 'I_2} := fun e => runA e.
Definition yh_rvA : {RV dA -> 'I_1} := fun e => proj_yhA (runA e).
Definition xa_rvA : {RV dA -> 'I_1} := proj_xaA \o fst.
Definition xh_rvA : {RV dA -> 'I_2} := fst.

Definition SimA (p : 'I_1 * 'I_2) : R.-fdist 'I_2 := fdist1 p.2.

Lemma readoffA e : out_advA (view_atA e) = runA e.
Proof. by []. Qed.

Lemma dAE u : dA u = 2%:R^-1 :> R.
Proof.
case: u => x w; rewrite /dA fdist_prodE /omegaA (ord1 w) fdist1xx mulr1.
by rewrite /muA fdist_uniformE card_ord.
Qed.

(* The delivery law fails at this instance.
   Naming: refutation-certificate register; the verb names the certificate's
   role, and the trailing A tags the Part A instance. *)
Lemma delivery_law_failsA :
  ~ (forall x, fdistmap (fun w => runA (x, w)) omegaA = FA x).
Proof.
move=> H; have := H i1; rewrite /omegaA fdistmap1 /FA => Hq.
have Hq1 : (fdist1 (runA (i1, ord0)) : R.-fdist 'I_2) i1
         = (fdist1 i1 : R.-fdist 'I_2) i1 by rewrite Hq.
move: Hq1; rewrite /runA fdist1xx fdist10 //.
by move/eqP; rewrite eq_sym oner_eq0.
Qed.

(* The simulator is consistent: every delivered output of positive mass is
   the constant one, and the read-off map is constant. *)
Lemma consistentA :
  forall a y, `Pr[ [% xa_rvA, ya_rvA] = (a, y) ] != 0 ->
  fdistmap out_advA (SimA (a, y)) = fdist1 y.
Proof.
move=> a y; have [->|Hy] := eqVneq y ord0.
  by rewrite /SimA /= fdistmap1.
rewrite pfwd1E /Pr big_pred0 ?eqxx // => u.
rewrite !inE /= xpair_eqE.
have -> : (ya_rvA u == y) = false by rewrite eq_sym (negbTE Hy).
by rewrite andbF.
Qed.

(* The simulator closes the privacy triangle at every input. *)
Lemma triangleA :
  forall x, fdistmap (fun w => view_atA (x, w)) omegaA
            = (fdistmap (fun yl => (proj_xaA x, yl)) (FA x)) >>= SimA.
Proof.
by move=> x; rewrite /omegaA /FA !fdistmap1 fdist1bind.
Qed.

(* The output-independence clause holds: the honest delivered output is
   constant. *)
Lemma output_independentA :
  dA |= view_rvA _|_ yh_rvA | [% input_rvA, ya_rvA].
Proof.
apply: (@cinde_RV_fun_conditioner R ('I_2 * 'I_1)%type dA 'I_2 'I_1
  ('I_2 * 'I_2)%type view_rvA yh_rvA [% input_rvA, ya_rvA] (fun _ => ord0)).
by [].
Qed.

Lemma pr_view_xh :
  `Pr[ [% [% view_rvA, [% xh_rvA, yh_rvA]], [% xa_rvA, ya_rvA]]
       = ((ord0, (ord0, ord0)), (ord0, ord0)) ] = 2%:R^-1 :> R.
Proof.
rewrite pfwd1E.
have -> : finset (preim [% [% view_rvA, [% xh_rvA, yh_rvA]],
    [% xa_rvA, ya_rvA]] (pred1 ((ord0, (ord0, ord0)), (ord0, ord0))))
  = [set ((ord0 : 'I_2), (ord0 : 'I_1))].
  apply/setP => -[x w]; rewrite !inE /= !xpair_eqE /= (ord1 w) !eqxx.
  by rewrite !andbT /view_rvA /xh_rvA /= andbb.
by rewrite Pr_set1 dAE.
Qed.

Lemma pr_view :
  `Pr[ [% view_rvA, [% xa_rvA, ya_rvA]] = (ord0, (ord0, ord0)) ]
  = 2%:R^-1 :> R.
Proof.
rewrite pfwd1E.
have -> : finset (preim [% view_rvA, [% xa_rvA, ya_rvA]]
    (pred1 ((ord0 : 'I_2), ((ord0 : 'I_1), (ord0 : 'I_2)))))
  = [set ((ord0 : 'I_2), (ord0 : 'I_1))].
  apply/setP => -[x w]; rewrite !inE /= !xpair_eqE /= (ord1 w) !eqxx.
  by rewrite !andbT.
by rewrite Pr_set1 dAE.
Qed.

Lemma pr_xh :
  `Pr[ [% [% xh_rvA, yh_rvA], [% xa_rvA, ya_rvA]]
       = ((ord0, ord0), (ord0, ord0)) ] = 2%:R^-1 :> R.
Proof.
rewrite pfwd1E.
have -> : finset (preim [% [% xh_rvA, yh_rvA], [% xa_rvA, ya_rvA]]
    (pred1 (((ord0 : 'I_2), (ord0 : 'I_1)), ((ord0 : 'I_1), (ord0 : 'I_2)))))
  = [set ((ord0 : 'I_2), (ord0 : 'I_1))].
  apply/setP => -[x w]; rewrite !inE /= !xpair_eqE /= (ord1 w) !eqxx.
  by rewrite !andbT /xh_rvA.
by rewrite Pr_set1 dAE.
Qed.

Lemma pr_allow : `Pr[ [% xa_rvA, ya_rvA] = (ord0, ord0) ] = 1 :> R.
Proof.
rewrite pfwd1E.
have -> : finset (preim [% xa_rvA, ya_rvA]
    (pred1 ((ord0 : 'I_1), (ord0 : 'I_2)))) = [set: ('I_2 * 'I_1)%type].
  by apply/setP => -[x w]; rewrite !inE /= xpair_eqE.
by rewrite Pr_setT.
Qed.

(* PART A.  The support-restricted consistency, the triangle and the
   output-independence clause all hold, the delivery law fails, and the
   conditional independence of the view and the honest pair fails. *)
Lemma not_cinde_pairA :
  ~ (dA |= view_rvA _|_ [% xh_rvA, yh_rvA] | [% xa_rvA, ya_rvA]).
Proof.
move=> H; have := H ord0 (ord0, ord0) (ord0, ord0).
rewrite !cpr_eqE pr_view_xh pr_view pr_xh pr_allow.
rewrite invr1 !mulr1 => Heq.
have Hne : (2%:R : R)^-1 != 0 by rewrite invr_neq0 // pnatr_eq0.
have H1 : (1 : R) = 2%:R^-1 by apply: (mulfI Hne); rewrite mulr1.
have H2 : (1 : R) * 2%:R = 2%:R^-1 * 2%:R by congr (_ * _).
move: H2; rewrite mul1r mulVf ?pnatr_eq0 // => H2.
by move: H2 => /eqP; rewrite pnatr_eq1.
Qed.

End part_A_forward_needs_H0.

(* ------------------------------------------------------------------ *)
(* PART B: the converse needs an injective input split.                 *)
(* ------------------------------------------------------------------ *)

(* Both party projections of the input are trivial, so the honest pair
   carries no information and the entropy equality is 0 = 0, while the real
   view is the input and no simulator can reproduce two different view
   laws. *)

Section part_B_converse_needs_split.
Context {R : realType}.

Definition muB : R.-fdist 'I_2 := fdist_uniform (card_ord 2).
Definition omegaB : R.-fdist 'I_1 := fdist1 ord0.
Definition dB : R.-fdist ('I_2 * 'I_1)%type := (muB `x omegaB)%fdist.

Definition FB (x : 'I_2) : R.-fdist 'I_1 := fdist1 ord0.
Definition view_atB (e : 'I_2 * 'I_1) : 'I_2 := e.1.
Definition runB (e : 'I_2 * 'I_1) : 'I_1 := ord0.
Definition trivB (T : Type) (t : T) : 'I_1 := ord0.

Definition view_rvB : {RV dB -> 'I_2} := view_atB.
Definition xa_rvB : {RV dB -> 'I_1} := fun _ => ord0.
Definition ya_rvB : {RV dB -> 'I_1} := fun _ => ord0.
Definition xh_rvB : {RV dB -> 'I_1} := fun _ => ord0.
Definition yh_rvB : {RV dB -> 'I_1} := fun _ => ord0.

(* The delivery law holds: every law on the one-point output space is the
   point mass. *)
Lemma delivery_law_okB :
  forall x, fdistmap (fun w => runB (x, w)) omegaB = FB x.
Proof. by move=> x; rewrite /omegaB fdistmap1. Qed.

(* The input prior has full support. *)
Lemma mu_fullB : forall x, muB x != 0.
Proof.
move=> x; rewrite /muB fdist_uniformE card_ord invr_neq0//.
by rewrite pnatr_eq0.
Qed.

(* The honest pair is constant, so both conditional entropies vanish and the
   entropy equality holds. *)
Lemma centropy_eqB :
  `H( [% xh_rvB, yh_rvB] | [% view_rvB, [% xa_rvB, ya_rvB]] )
  = `H( [% xh_rvB, yh_rvB] | [% xa_rvB, ya_rvB] ).
Proof.
rewrite (_ : `H( [% xh_rvB, yh_rvB] | [% view_rvB, [% xa_rvB, ya_rvB]] ) = 0);
  last first.
  exact: (centropy_RV_comp0 [% view_rvB, [% xa_rvB, ya_rvB]]
            (fun _ => (ord0, ord0))).
by rewrite (centropy_RV_comp0 [% xa_rvB, ya_rvB] (fun _ => (ord0, ord0))).
Qed.

(* PART B.  The delivery law, the full-support prior and the entropy
   equality all hold, and no simulator closes the privacy triangle. *)
Lemma no_triangleB (Sim : 'I_1 * 'I_1 -> R.-fdist 'I_2) :
  ~ (forall x, fdistmap (fun w => view_atB (x, w)) omegaB
               = (fdistmap (fun yl => ((ord0 : 'I_1), trivB yl)) (FB x))
                 >>= Sim).
Proof.
move=> H.
have H0 := H ord0; have H1 := H i1.
move: H0 H1; rewrite /omegaB /FB !fdistmap1 !fdist1bind => <- /esym Hq.
have Hq0 : (fdist1 (view_atB (ord0, ord0)) : R.-fdist 'I_2) ord0
         = (fdist1 (view_atB (i1, ord0)) : R.-fdist 'I_2) ord0 by rewrite Hq.
by move: Hq0; rewrite /view_atB /= fdist1xx fdist10 // => /eqP; rewrite oner_eq0.
Qed.

End part_B_converse_needs_split.

(* --- verification block --- *)
About delivery_law_failsA.
About consistentA.
About triangleA.
About output_independentA.
About not_cinde_pairA.
About delivery_law_okB.
About mu_fullB.
About centropy_eqB.
About no_triangleB.
Print Assumptions not_cinde_pairA.
Print Assumptions no_triangleB.
