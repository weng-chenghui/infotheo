(* Probe P2 — claims S7-S9 / L5, L8, L10: total-variation distance on
   R.-fdist with the max-advantage identity, ported from the deleted
   smc/ssprove_ext_statdist.v (source saved alongside as
   reference_statdist_distr_source.txt; psum over choiceType becomes a
   finite \sum, dropping every summability side condition), plus the
   tester-class pseudometric of prop:smc:composition.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_statdist_maxadv.v            *)

From mathcomp Require Import all_ssreflect all_algebra reals lra.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section statdist.
Context {R : realType} {B : finType}.
Implicit Types p q r : R.-fdist B.

Definition statdist p q : R := 2%:R^-1 * \sum_b `|p b - q b|.

Lemma statdist_ge0 p q : 0 <= statdist p q.
Proof. by rewrite mulr_ge0 ?invr_ge0 ?ler0n// sumr_ge0. Qed.

Lemma statdist_sym p q : statdist p q = statdist q p.
Proof. by congr (_ * _); apply: eq_bigr => b _; rewrite distrC. Qed.

Lemma statdist_triangle p q r : statdist p q <= statdist p r + statdist r q.
Proof.
rewrite /statdist -mulrDr ler_pM2l ?invr_gt0 ?ltr0n// -big_split/=.
by apply: ler_sum => b _; exact: ler_distD.
Qed.

(* S8: separation — needed for perfect_privacy_testP later. *)
Lemma statdist_eq0 p q : (statdist p q == 0) = (p == q).
Proof.
apply/idP/idP => [|/eqP ->]; last first.
  by apply/eqP; rewrite /statdist big1 ?mulr0// => b _; rewrite subrr normr0.
rewrite /statdist mulf_eq0 invr_eq0 pnatr_eq0/= => /eqP H.
apply/eqP/fdist_ext => b; apply/eqP; rewrite -subr_eq0 -normr_eq0.
by apply/eqP; apply: (psumr_eq0P _ H).
Qed.

(* Testers: the game section's distinguishers.  {ffun B -> bool} is a
   finType, so maxima over all testers are big-operator maxima (L8). *)
Definition tester := {ffun B -> bool}.

Definition accept (D : tester) p : R := Pr p [set b | D b].

Definition adv (D : tester) p q : R := `|accept D p - accept D q|.

(* Off [S] the mass that [q] carries above [p] equals, on [S], the mass
   that [p] carries above [q]. *)
Local Lemma sum_diff_complement p q (S : {set B}) :
  \sum_(b | ~~ (b \in S)) (q b - p b) = \sum_(b in S) (p b - q b).
Proof.
have Hz : \sum_b (p b - q b) = 0 :> R by rewrite sumrB !FDist.f1 subrr.
move: Hz; rewrite (bigID (mem S))/= => Hz'.
under eq_bigr do rewrite -opprB.
by rewrite sumrN; move: Hz'; lra.
Qed.

Local Lemma sum_diff_le p q (S : {set B}) :
  \sum_(b in S) (p b - q b) <= statdist p q.
Proof.
have h2 : (0 : R) < 2%:R by rewrite ltr0n.
rewrite /statdist -(ler_pM2l h2) mulrA divff ?pnatr_eq0// mul1r.
rewrite mulr_natl mulr2n [X in _ <= X](bigID (mem S))/=.
rewrite -[X in _ + X <= _](sum_diff_complement p q S).
apply: lerD; apply: ler_sum => b _; first exact: ler_norm.
by rewrite distrC; exact: ler_norm.
Qed.

Local Lemma accept_diff (D : tester) p q :
  accept D p - accept D q = \sum_(b in [set b | D b]) (p b - q b).
Proof. by rewrite /accept /Pr sumrB. Qed.

(* S7: the max-advantage identity, ported from statdist_test_le /
   statdist_test_max of the reference file.  The optimal tester is
   [ffun b => q b < p b]. *)
Lemma statdist_test_le (D : tester) p q : adv D p q <= statdist p q.
Proof.
rewrite /adv accept_diff ler_norml; apply/andP; split; last exact: sum_diff_le.
rewrite lerNl -sumrN; under eq_bigr do rewrite opprB.
by rewrite statdist_sym; exact: sum_diff_le.
Qed.

(* The statistical distance is the mass of the set on which p exceeds q. *)
Local Lemma statdist_pos_part p q :
  statdist p q = \sum_(b in [set b | q b < p b]) (p b - q b).
Proof.
rewrite /statdist [X in _ * X](bigID (mem [set b | q b < p b]))/=.
rewrite [X in X + _](eq_bigr (fun b => p b - q b)); last first.
  by move=> b; rewrite inE => Hb; rewrite ger0_norm// subr_ge0 ltW.
rewrite [X in _ + X](eq_bigr (fun b => q b - p b)); last first.
  by move=> b; rewrite inE -leNgt => Hb; rewrite distrC ger0_norm// subr_ge0.
by rewrite sum_diff_complement; lra.
Qed.

Lemma statdist_test_max p q :
  \big[Num.max/0]_(D : tester) adv D p q = statdist p q.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: bigmax_le; first exact: statdist_ge0.
  by move=> D _; exact: statdist_test_le.
apply: (bigmax_sup [ffun b => q b < p b]) => //.
rewrite /adv accept_diff.
have -> : [set b | [ffun b => q b < p b] b] = [set b | q b < p b].
  by apply/setP => b; rewrite !inE ffunE.
by rewrite -statdist_pos_part ger0_norm//; exact: statdist_ge0.
Qed.

(* S9: prop:smc:composition — the class-restricted advantage. *)
Definition class_adv (T : {set tester}) p q : R :=
  \big[Num.max/0]_(D in T) adv D p q.

Lemma class_adv_ge0 T p q : 0 <= class_adv T p q.
Proof. exact: bigmax_ge_id. Qed.

Lemma class_adv_sym T p q : class_adv T p q = class_adv T q p.
Proof. by apply: eq_bigr => D _; rewrite /adv distrC. Qed.

Lemma class_advxx T p : class_adv T p p = 0.
Proof.
rewrite /class_adv (eq_bigr (fun=> 0)); last first.
  by move=> D _; rewrite /adv subrr normr0.
by elim/big_rec: _ => // D x _ ->; rewrite maxxx.
Qed.

Lemma class_adv_triangle T p q r :
  class_adv T p q <= class_adv T p r + class_adv T r q.
Proof.
rewrite [X in X <= _]/class_adv; apply: bigmax_le.
  by rewrite addr_ge0//; exact: class_adv_ge0.
move=> D DT; apply: (le_trans (ler_distD (accept D r) _ _)).
by rewrite /class_adv; apply: lerD; apply: (bigmax_sup D).
Qed.

Lemma class_adv_sub (T T' : {set tester}) p q :
  class_adv T p q <= class_adv T' p q.
Proof. by move=> /subsetP TT'; apply: sub_bigmax => D; exact: TT'. Qed.

Lemma class_adv_all p q : class_adv [set: tester] p q = statdist p q.
Proof.
by rewrite -statdist_test_max /class_adv; apply: eq_bigl => D; rewrite in_setT.
Qed.

End statdist.

(* Each of the three prints the boolp trio only — propositional_
   extensionality, functional_extensionality_dep,
   constructive_indefinite_description — which is the mathcomp-analysis
   realType baseline dragged in by [reals]; no probe-local axiom. *)
Print Assumptions statdist_test_max.
Print Assumptions class_adv_triangle.
Print Assumptions class_adv_all.

(* FINDINGS
   1. The header of the probe compiled unchanged: [From mathcomp Require
      Import all_ssreflect all_algebra reals lra] resolves [lra] on
      realType and needs no adjustment.  It does raise
      "Library File mathcomp.ssreflect.all_ssreflect is deprecated since
      mathcomp 2.5.0. Use 'all_boot' and/or 'all_order' instead."
   2. Exception (a) was NOT needed: [\big[Num.max/0]_] is kept verbatim.
      [Num.max] is a notation for [Num.Def.maxr], itself [Order.max] at
      ring_display, so it unifies with the [Order.Def.max] of mathcomp's
      bigmax lemmas with no idiom change.
   3. Exception (b) was NOT needed: [statdist_eq0] is proved at the
      stated boolean-equality phrasing [(statdist p q == 0) = (p == q)],
      via [psumr_eq0P] and [fdist_ext].
   4. Bigmax lemma resolution depends on the import order already in the
      header.  With [Import ... Order.Theory] last, the bare names
      [bigmax_le], [bigmax_sup] resolve to
      Order.POrderTheory.bigmax_le and Order.TotalTheory.bigmax_sup;
      without it they would resolve to the nat-valued [bigmax_sup] of
      fintype and the [x : T] argument would not typecheck.
      Names used: bigmax_le, bigmax_sup, bigmax_ge_id, sub_bigmax,
      plus maxxx / big_rec (class_advxx) and eq_bigl (class_adv_all).
   5. The reference's pointwise ladder collapses.  pw_le, pw_le_swap,
      pw_eqA, pw_eqB, pw_absA, pw_absB, ge0_posA, ge0_negB, split_p,
      split_q, pr_diff_posA, statdist_split, posA_eq_negB, pr_upper and
      pr_lower are replaced by three local lemmas:
      sum_diff_complement, sum_diff_le, statdist_pos_part.  Every
      summable* obligation of the reference vanishes, and the two
      mass-1 hypotheses become one [FDist.f1] rewrite inside
      sum_diff_complement.  [lra] is used only on the two scalar
      identities A + B = 0 -> - B = A and 2^-1 * (A + A) = A.
   6. [accept D p - accept D q] reduces to a single set-restricted
      difference sum by [rewrite /accept /Pr sumrB]; no [pr] analogue
      is needed.
   7. Mutation 1 is a proof-level failure only, not a falsification.
      For two mass-1 laws the positive part equals the negative part, so
      the flipped tester [ffun b => p b < q b] also attains the maximum
      and [statdist_test_max] stays TRUE with that witness.  What breaks
      is the [statdist_pos_part] rewrite, which is stated for
      [set b | q b < p b].  A probe that only checked the final
      statement would not have caught the swap.                        *)

(* MUTATION CHECKS — the two copies sit in this directory; both FAIL.
   Command: coqc -w -all -R . infotheo <copy>.v      (exit status 1)
   1. probe_statdist_maxadv_mut1.v — statdist_test_max instantiated at
      the wrong optimal tester [ffun b => p b < q b].  The bigmax_le
      branch still goes through; the attainment branch dies at line 117:
        Error: The RHS of statdist_pos_part
        (\sum_(b in [set b0 | _ b0 < _ b0]) (_ b - _ b))
        does not match any subterm of the goal
   2. probe_statdist_maxadv_mut2.v — class_adv_sub with the hypothesis
      T \subset T' dropped, line 148:
        Error: No assumption in
        ((class_adv T p q <= class_adv T' p q) = true)                 *)
