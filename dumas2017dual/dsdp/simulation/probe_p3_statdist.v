(**md**************************************************************************)
(* Probe P3: statistical distance and its optimal distinguisher, developed   *)
(* standalone over the mathcomp-analysis [distr]/[realsum] layer that SSProve *)
(* uses (no Infotheo dependency).                                             *)
(*                                                                            *)
(* For subdistributions [p q : {distr T / R}]:                               *)
(*   statdist p q := psum (fun t => `|p t - q t|) / 2%:R                      *)
(* is half the total variation of the signed mass [p - q].  [psum] sums       *)
(* absolute values, so every intermediate [psum] argument here is kept        *)
(* nonnegative and combined through [psumID] (indicator partition) and        *)
(* [psumD] (additivity of nonnegative summable families).                     *)
(*                                                                            *)
(* Acceptance probability of an event [E : pred T] under [mu] is the          *)
(* mathcomp-analysis [distr.pr]:                                              *)
(*   distr.pr mu E = psum (fun t => (E t)%:R * mu t).                         *)
(*                                                                            *)
(* Main statements.                                                           *)
(* - statdist_ge0, statdist_sym, statdist_triangle : metric properties.       *)
(* - statdist_test_le : for probability distributions [p q] and any test [D], *)
(*     `|distr.pr p D - distr.pr q D| <= statdist p q.                        *)
(* - statdist_test_max : the test [fun t => q t < p t] attains the distance,  *)
(*     distr.pr p (fun t => q t < p t) - distr.pr q (fun t => q t < p t)      *)
(*       = statdist p q.                                                      *)
(******************************************************************************)

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
From mathcomp Require Import boolp lra.

Import Num.Theory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope real_scope.

Section StatDist.
Context {R : realType} {T : choiceType}.
Implicit Types p q r : {distr T / R}.

Definition statdist (p q : {distr T / R}) :=
  psum (fun t => `|p t - q t|) / 2%:R.

(* Additivity of [psum] over a pointwise sum of nonnegative summable          *)
(* families.                                                                  *)
Lemma psum_split (g h : T -> R) :
  (forall t, 0 <= g t) -> (forall t, 0 <= h t) ->
  summable g -> summable h ->
  psum (fun t => g t + h t) = psum g + psum h.
Proof.
by move=> gp hp sg sh; rewrite -(psumD gp hp sg sh); apply: eq_psum.
Qed.

Lemma statdist_ge0 p q : 0 <= statdist p q.
Proof. by rewrite /statdist divr_ge0 ?ge0_psum// ler0n. Qed.

Lemma statdist_sym p q : statdist p q = statdist q p.
Proof.
by rewrite /statdist; congr (_ / _); apply: eq_psum => t; rewrite distrC.
Qed.

Lemma statdist_summable p q : summable (fun t => `|p t - q t|).
Proof.
apply: (summable_abs (fun t => p t - q t)).2.
exact: summableD (summable_mu p) (summableN (summable_mu q)).
Qed.

Lemma statdist_triangle p q r : statdist p q <= statdist p r + statdist r q.
Proof.
rewrite /statdist -mulrDl.
have h2 : (0 : R) < 2%:R^-1 by rewrite invr_gt0 ltr0n.
rewrite (ler_pM2r h2).
have E : psum (fun t => `|p t - r t| + `|r t - q t|)
       = psum (fun t => `|p t - r t|) + psum (fun t => `|r t - q t|).
  apply: psum_split.
  - by move=> t; exact: normr_ge0.
  - by move=> t; exact: normr_ge0.
  - exact: statdist_summable.
  - exact: statdist_summable.
rewrite -E.
apply: le_psum; last first.
  exact: summableD (statdist_summable p r) (statdist_summable r q).
by move=> t; rewrite normr_ge0/=; exact: ler_distD.
Qed.

Section Optimal.
Variables p q : {distr T / R}.
Let Dstar : pred T := fun t => q t < p t.

(* Pointwise ingredients, all discharged by real linear arithmetic after the  *)
(* Boolean coefficients and [ltrgtP] have been reduced.                       *)

Lemma pw_le (D : pred T) t :
  (D t)%:R * p t <= (D t)%:R * q t + (Dstar t)%:R * (p t - q t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => hpq /=;
  case: (D t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Lemma pw_le_swap (D : pred T) t :
  (D t)%:R * q t <= (D t)%:R * p t + (~~ Dstar t)%:R * (q t - p t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => hpq /=;
  case: (D t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Lemma pw_eqA t :
  (Dstar t)%:R * p t = (Dstar t)%:R * q t + (Dstar t)%:R * (p t - q t).
Proof.
rewrite /Dstar !GRing.mulrb.
by case: (q t < p t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Lemma pw_eqB t :
  (~~ Dstar t)%:R * q t
  = (~~ Dstar t)%:R * p t + (~~ Dstar t)%:R * (q t - p t).
Proof.
rewrite /Dstar !GRing.mulrb.
by case: (q t < p t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Lemma pw_absA t :
  (Dstar t)%:R * `|p t - q t| = (Dstar t)%:R * (p t - q t).
Proof.
by rewrite /Dstar !GRing.mulrb; case: (ltrgtP (q t) (p t)) => hpq /=;
  rewrite ?mul0r ?mul1r.
Qed.

Lemma pw_absB t :
  (~~ Dstar t)%:R * `|p t - q t| = (~~ Dstar t)%:R * (q t - p t).
Proof.
by rewrite /Dstar !GRing.mulrb; case: (ltrgtP (q t) (p t)) => hpq /=; lra.
Qed.

Lemma ge0_posA t : 0 <= (Dstar t)%:R * (p t - q t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => hpq /=; rewrite ?mul0r ?mul1r; lra.
Qed.

Lemma ge0_negB t : 0 <= (~~ Dstar t)%:R * (q t - p t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => hpq /=; rewrite ?mul0r ?mul1r; lra.
Qed.

Lemma summable_posA : summable (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
have s : summable (fun t => p t - q t)
  by exact: summableD (summable_mu p) (summableN (summable_mu q)).
exact: (summable_condl Dstar s).
Qed.

Lemma summable_negB : summable (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
have s : summable (fun t => q t - p t)
  by exact: summableD (summable_mu q) (summableN (summable_mu p)).
exact: (summable_condl (fun t => ~~ Dstar t) s).
Qed.

Lemma summable_wgt (D : pred T) (mu : {distr T / R}) :
  summable (fun t => (D t)%:R * mu t).
Proof. exact: summable_pr. Qed.

(* [Dstar]-restricted masses of [p] and [q] differ by the positive part.      *)
Lemma split_p :
  psum (fun t => (Dstar t)%:R * p t)
  = psum (fun t => (Dstar t)%:R * q t)
  + psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
transitivity
  (psum (fun t => (Dstar t)%:R * q t + (Dstar t)%:R * (p t - q t))).
  by apply: eq_psum => t; exact: pw_eqA.
apply: psum_split.
- by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
- exact: ge0_posA.
- exact: summable_wgt.
- exact: summable_posA.
Qed.

Lemma split_q :
  psum (fun t => (~~ Dstar t)%:R * q t)
  = psum (fun t => (~~ Dstar t)%:R * p t)
  + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
transitivity
  (psum (fun t => (~~ Dstar t)%:R * p t + (~~ Dstar t)%:R * (q t - p t))).
  by apply: eq_psum => t; exact: pw_eqB.
apply: psum_split.
- by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
- exact: ge0_negB.
- exact: summable_wgt.
- exact: summable_negB.
Qed.

Lemma pr_diff_posA :
  distr.pr p Dstar - distr.pr q Dstar
  = psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof. by rewrite /distr.pr; move: split_p; lra. Qed.

(* Total variation splits into the positive and negative parts over [Dstar].  *)
Lemma statdist_split :
  psum (fun t => `|p t - q t|)
  = psum (fun t => (Dstar t)%:R * (p t - q t))
  + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
rewrite (psumID Dstar (statdist_summable p q)); congr (_ + _).
- by apply: eq_psum => t; exact: pw_absA.
- by apply: eq_psum => t; exact: pw_absB.
Qed.

(* Equal total masses force the two parts to coincide.                        *)
Lemma posA_eq_negB :
  psum (distr.mu p) = 1 -> psum (distr.mu q) = 1 ->
  psum (fun t => (Dstar t)%:R * (p t - q t))
  = psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
move=> Hp Hq.
have Ep := psumID Dstar (summable_mu p).
have Eq := psumID Dstar (summable_mu q).
rewrite Hp in Ep; rewrite Hq in Eq.
move: split_p split_q Ep Eq; lra.
Qed.

Lemma statdist_test_max :
  psum (distr.mu p) = 1 -> psum (distr.mu q) = 1 ->
  distr.pr p Dstar - distr.pr q Dstar = statdist p q.
Proof.
move=> Hp Hq.
have h2n : (2%:R : R) != 0 by rewrite pnatr_eq0.
rewrite pr_diff_posA /statdist statdist_split (posA_eq_negB Hp Hq).
set B := psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
by rewrite -mulr2n -(mulr_natr B 2) (mulfK h2n).
Qed.

Lemma statdist_eq_posA :
  psum (distr.mu p) = 1 -> psum (distr.mu q) = 1 ->
  statdist p q = psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
by move=> Hp Hq; rewrite -(statdist_test_max Hp Hq); exact: pr_diff_posA.
Qed.

Lemma statdist_eq_negB :
  psum (distr.mu p) = 1 -> psum (distr.mu q) = 1 ->
  statdist p q = psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
by move=> Hp Hq; rewrite (statdist_eq_posA Hp Hq) (posA_eq_negB Hp Hq).
Qed.

(* Any test is dominated by the positive part.                                *)
Lemma pr_upper (D : pred T) :
  distr.pr p D - distr.pr q D
  <= psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
have E : psum (fun t => (D t)%:R * q t + (Dstar t)%:R * (p t - q t))
       = psum (fun t => (D t)%:R * q t)
       + psum (fun t => (Dstar t)%:R * (p t - q t)).
  apply: psum_split.
  - by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
  - exact: ge0_posA.
  - exact: summable_wgt.
  - exact: summable_posA.
rewrite /distr.pr lerBlDr addrC -E.
apply: le_psum; last first.
  by apply: summableD; [exact: summable_wgt | exact: summable_posA].
move=> t; apply/andP; split; last exact: pw_le.
by apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
Qed.

Lemma pr_lower (D : pred T) :
  distr.pr q D - distr.pr p D
  <= psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
have E : psum (fun t => (D t)%:R * p t + (~~ Dstar t)%:R * (q t - p t))
       = psum (fun t => (D t)%:R * p t)
       + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
  apply: psum_split.
  - by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
  - exact: ge0_negB.
  - exact: summable_wgt.
  - exact: summable_negB.
rewrite /distr.pr lerBlDr addrC -E.
apply: le_psum; last first.
  by apply: summableD; [exact: summable_wgt | exact: summable_negB].
move=> t; apply/andP; split; last exact: pw_le_swap.
by apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
Qed.

Lemma statdist_test_le (D : pred T) :
  psum (distr.mu p) = 1 -> psum (distr.mu q) = 1 ->
  `| distr.pr p D - distr.pr q D | <= statdist p q.
Proof.
move=> Hp Hq; rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (statdist_eq_negB Hp Hq); exact: pr_lower.
- rewrite (statdist_eq_posA Hp Hq); exact: pr_upper.
Qed.

End Optimal.

End StatDist.
