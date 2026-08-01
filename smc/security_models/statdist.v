(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order ssralg ssrnum reals lra.
Require Import fdist proba variation_dist.

(**md**************************************************************************)
(* # Statistical distance and testers                                         *)
(*                                                                            *)
(* The statistical distance of two laws over a finType B is half of their     *)
(* total-variation sum.  A tester is a boolean function on B, its acceptance  *)
(* probability under a law is the mass of the set it accepts, and its         *)
(* advantage at a pair of laws is the gap between the two acceptance          *)
(* probabilities.  The statistical distance is the maximal advantage over all *)
(* testers; the maximum restricted to a set of testers is the class           *)
(* advantage, which is monotone in the class.                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*            statdist p q == the statistical distance of the laws p and q    *)
(*       statdist_var_dist == statdist is half of the variation distance      *)
(*            statdist_ge0 == statdist is nonnegative                         *)
(*            statdist_sym == statdist is symmetric                           *)
(*       statdist_triangle == statdist satisfies the triangle inequality      *)
(*            statdist_eq0 == statdist vanishes exactly at equal laws         *)
(*                tester B == the type {ffun B -> bool} of testers on B       *)
(*              accept D p == the mass that p gives to the set accepted by    *)
(*                            the tester D                                    *)
(*               adv D p q == the gap between accept D p and accept D q       *)
(*                 adv_ge0 == a fixed tester has nonnegative advantage        *)
(*            adv_triangle == the advantage of a fixed tester satisfies the   *)
(*                            triangle inequality                             *)
(*        statdist_test_le == the advantage of a tester is at most statdist   *)
(*       statdist_test_max == statdist is the maximal advantage over all      *)
(*                            testers                                         *)
(*         class_adv T p q == the maximal advantage over the testers in T     *)
(*           class_adv_ge0 == class_adv is nonnegative                        *)
(*           class_adv_sym == class_adv is symmetric                          *)
(*             class_advxx == class_adv vanishes at equal arguments           *)
(*      class_adv_triangle == class_adv satisfies the triangle inequality     *)
(*           class_adv_sub == class_adv is monotone in the tester class       *)
(*           class_adv_all == class_adv at the full tester class is statdist  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section statdist.
Context {R : realType}.
Variable B : finType.
Implicit Types p q r : R.-fdist B.

(* def:smc:tv-distance *)
(* The statistical distance of two laws is half of the sum over B of the
   absolute mass differences. *)
Definition statdist p q : R := 2%:R^-1 * \sum_b `|p b - q b|.

(* def:smc:tv-distance *)
(* statdist is half of variation_dist's total-variation sum. *)
Lemma statdist_var_dist p q : statdist p q = 2%:R^-1 * var_dist p q.
Proof. by []. Qed.

(* def:smc:tv-distance *)
(* The statistical distance is nonnegative. *)
Lemma statdist_ge0 p q : 0 <= statdist p q.
Proof.
by rewrite statdist_var_dist mulr_ge0 ?invr_ge0 ?ler0n// pos_var_dist.
Qed.

(* def:smc:tv-distance *)
(* The statistical distance is symmetric. *)
Lemma statdist_sym p q : statdist p q = statdist q p.
Proof. by rewrite !statdist_var_dist symmetric_var_dist. Qed.

(* def:smc:tv-distance *)
(* The statistical distance satisfies the triangle inequality. *)
Lemma statdist_triangle p q r : statdist p q <= statdist p r + statdist r q.
Proof.
rewrite /statdist -mulrDr ler_pM2l ?invr_gt0 ?ltr0n// -big_split/=.
by apply: ler_sum => b _; exact: ler_distD.
Qed.

(* def:smc:tv-distance *)
(* The statistical distance vanishes exactly at equal laws. *)
Lemma statdist_eq0 p q : (statdist p q == 0) = (p == q).
Proof.
apply/idP/idP => [|/eqP ->]; last first.
  by apply/eqP; rewrite /statdist big1 ?mulr0// => b _; rewrite subrr normr0.
rewrite /statdist mulf_eq0 invr_eq0 pnatr_eq0/= => /eqP H.
apply/eqP/fdist_ext => b; apply/eqP; rewrite -subr_eq0 -normr_eq0.
by apply/eqP; apply: (psumr_eq0P _ H).
Qed.

(* sec:smc:enriched-testing *)
(* A tester is a boolean function on B. *)
Definition tester := {ffun B -> bool}.

(* sec:smc:enriched-testing *)
(* The acceptance probability of a tester under a law is the mass the law
   gives to the set the tester accepts. *)
Definition accept (D : tester) p : R := Pr p [set b | D b].

(* sec:smc:enriched-testing *)
(* The advantage of a tester at a pair of laws is the gap between its two
   acceptance probabilities. *)
Definition adv (D : tester) p q : R := `|accept D p - accept D q|.

(* sec:smc:enriched-testing *)
(* The advantage of a fixed tester is nonnegative. *)
Lemma adv_ge0 (D : tester) p q : 0 <= adv D p q.
Proof. exact: normr_ge0. Qed.

(* sec:smc:enriched-testing *)
(* The advantage of a fixed tester satisfies the triangle inequality. *)
Lemma adv_triangle (D : tester) p q r : adv D p q <= adv D p r + adv D r q.
Proof. exact: ler_distD. Qed.

(* Off S the mass that q carries above p equals, on S, the mass that p
   carries above q. *)
Local Lemma sum_diff_complement p q (S : {set B}) :
  \sum_(b | ~~ (b \in S)) (q b - p b) = \sum_(b in S) (p b - q b).
Proof.
have Hz : \sum_b (p b - q b) = 0 :> R by rewrite sumrB !FDist.f1 subrr.
move: Hz; rewrite (bigID (mem S))/= => Hz'.
under eq_bigr do rewrite -opprB.
by rewrite sumrN; move: Hz'; lra.
Qed.

(* The mass that p carries above q on a set is at most the statistical
   distance. *)
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

(* The acceptance gap of a tester is the mass difference of the two laws
   summed over the accepted set. *)
Local Lemma accept_diff (D : tester) p q :
  accept D p - accept D q = \sum_(b in [set b | D b]) (p b - q b).
Proof. by rewrite /accept /Pr sumrB. Qed.

(* prop:smc:max-advantage *)
(* The advantage of a tester is at most the statistical distance.
   Naming: pair naming with statdist_test_max; test = quantified over
   testers; port continuity with the deleted ssprove_ext_statdist.v
   (2bbc1714). *)
Lemma statdist_test_le (D : tester) p q : adv D p q <= statdist p q.
Proof.
rewrite /adv accept_diff ler_norml; apply/andP; split; last exact: sum_diff_le.
rewrite lerNl -sumrN; under eq_bigr do rewrite opprB.
by rewrite statdist_sym; exact: sum_diff_le.
Qed.

(* The statistical distance is the excess of p over q summed on the set
   where p exceeds q. *)
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

(* prop:smc:max-advantage *)
(* The statistical distance is the maximal advantage over all testers.
   Naming: pair naming with statdist_test_le; test = quantified over
   testers; port continuity with the deleted ssprove_ext_statdist.v
   (2bbc1714). *)
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

(* prop:smc:composition *)
(* The class advantage of a set of testers is the maximal advantage over
   its members. *)
Definition class_adv (T : {set tester}) p q : R :=
  \big[Num.max/0]_(D in T) adv D p q.

(* prop:smc:composition *)
(* The class advantage is nonnegative. *)
Lemma class_adv_ge0 T p q : 0 <= class_adv T p q.
Proof. exact: bigmax_ge_id. Qed.

(* prop:smc:composition *)
(* The class advantage is symmetric. *)
Lemma class_adv_sym T p q : class_adv T p q = class_adv T q p.
Proof. by apply: eq_bigr => D _; rewrite /adv distrC. Qed.

(* prop:smc:composition *)
(* The class advantage of a law against itself is zero. *)
Lemma class_advxx T p : class_adv T p p = 0.
Proof.
rewrite /class_adv (eq_bigr (fun=> 0)); last first.
  by move=> D _; rewrite /adv subrr normr0.
by elim/big_rec: _ => // D x _ ->; rewrite maxxx.
Qed.

(* prop:smc:composition *)
(* The class advantage satisfies the triangle inequality. *)
Lemma class_adv_triangle T p q r :
  class_adv T p q <= class_adv T p r + class_adv T r q.
Proof.
rewrite [X in X <= _]/class_adv; apply: bigmax_le.
  by rewrite addr_ge0//; exact: class_adv_ge0.
move=> D DT; apply: (le_trans (ler_distD (accept D r) _ _)).
by rewrite /class_adv; apply: lerD; apply: (bigmax_sup D).
Qed.

(* prop:smc:composition *)
(* The class advantage is monotone in the tester class. *)
Lemma class_adv_sub (T T' : {set tester}) p q :
  T \subset T' -> class_adv T p q <= class_adv T' p q.
Proof. by move=> /subsetP TT'; apply: sub_bigmax => D; exact: TT'. Qed.

(* prop:smc:composition *)
(* The class advantage at the full tester class is the statistical
   distance. *)
Lemma class_adv_all p q : class_adv [set: tester] p q = statdist p q.
Proof.
by rewrite -statdist_test_max /class_adv; apply: eq_bigl => D; rewrite in_setT.
Qed.

End statdist.
