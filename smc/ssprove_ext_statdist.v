(** SSProve extension: statistical (total-variation) distance on [{distr T}].

    [statdist p q] is half the pointwise absolute-difference mass between
    two subdistributions.  For mass-1 laws, every boolean test's acceptance
    gap is bounded by [statdist] ([statdist_test_le]) and the strict
    optimal test [fun t => q t < p t] attains it exactly
    ([statdist_test_max]): the maximum distinguisher advantage equals the
    statistical distance. *)

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
From mathcomp Require Import boolp lra.

Import Num.Theory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope real_scope.

Section StatDist.
Context {R : realType} {T : choiceType}.
Implicit Types p q r : {distr T / R}.

(* Statistical (total-variation) distance between two subdistributions:       *)
(* half the summed pointwise absolute difference of their masses.             *)
Definition statdist (p q : {distr T / R}) :=
  psum (fun t => `|p t - q t|) / 2%:R.

(* Additivity of [psum] over a pointwise sum of nonnegative summable          *)
(* families.                                                                  *)
Local Lemma psumD_pw (g h : T -> R) :
  (forall t, 0 <= g t) -> (forall t, 0 <= h t) ->
  summable g -> summable h ->
  psum (fun t => g t + h t) = psum g + psum h.
Proof.
by move=> gp hp sg sh; rewrite -(psumD gp hp sg sh); apply: eq_psum.
Qed.

(* Statistical distance is nonnegative. *)
Lemma statdist_ge0 p q : 0 <= statdist p q.
Proof. by rewrite /statdist divr_ge0 ?ge0_psum// ler0n. Qed.

(* Statistical distance is symmetric in its two arguments. *)
Lemma statdist_sym p q : statdist p q = statdist q p.
Proof.
by rewrite /statdist; congr (_ / _); apply: eq_psum => t; rewrite distrC.
Qed.

(* The pointwise absolute difference of [p] and [q] is a summable family. *)
Lemma summable_dist p q : summable (fun t => `|p t - q t|).
Proof.
apply: (summable_abs (fun t => p t - q t)).2.
exact: summableD (summable_mu p) (summableN (summable_mu q)).
Qed.

(* Statistical distance satisfies the triangle inequality. *)
Lemma statdist_triangle p q r : statdist p q <= statdist p r + statdist r q.
Proof.
rewrite /statdist -mulrDl.
have h2 : (0 : R) < 2%:R^-1 by rewrite invr_gt0 ltr0n.
rewrite (ler_pM2r h2).
have E : psum (fun t => `|p t - r t| + `|r t - q t|)
       = psum (fun t => `|p t - r t|) + psum (fun t => `|r t - q t|).
  apply: psumD_pw.
  - by move=> t; exact: normr_ge0.
  - by move=> t; exact: normr_ge0.
  - exact: summable_dist.
  - exact: summable_dist.
rewrite -E.
apply: le_psum; last first.
  exact: summableD (summable_dist p r) (summable_dist r q).
by move=> t; rewrite normr_ge0/=; exact: ler_distD.
Qed.

Section Optimal.
Variables p q : {distr T / R}.
Let Dstar : pred T := fun t => q t < p t.

(* Pointwise inequalities and identities relating an arbitrary test [D] and   *)
(* the optimal test [Dstar].                                                  *)

Local Lemma pw_le (D : pred T) t :
  (D t)%:R * p t <= (D t)%:R * q t + (Dstar t)%:R * (p t - q t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => ? /=;
  case: (D t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Local Lemma pw_le_swap (D : pred T) t :
  (D t)%:R * q t <= (D t)%:R * p t + (~~ Dstar t)%:R * (q t - p t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => ? /=;
  case: (D t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Local Lemma pw_eqA t :
  (Dstar t)%:R * p t = (Dstar t)%:R * q t + (Dstar t)%:R * (p t - q t).
Proof.
rewrite /Dstar !GRing.mulrb.
by case: (q t < p t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Local Lemma pw_eqB t :
  (~~ Dstar t)%:R * q t
  = (~~ Dstar t)%:R * p t + (~~ Dstar t)%:R * (q t - p t).
Proof.
rewrite /Dstar !GRing.mulrb.
by case: (q t < p t); rewrite ?mul1r ?mul0r ?add0r ?addr0; lra.
Qed.

Local Lemma pw_absA t :
  (Dstar t)%:R * `|p t - q t| = (Dstar t)%:R * (p t - q t).
Proof.
by rewrite /Dstar !GRing.mulrb; case: (ltrgtP (q t) (p t)) => ? /=;
  rewrite ?mul0r ?mul1r.
Qed.

Local Lemma pw_absB t :
  (~~ Dstar t)%:R * `|p t - q t| = (~~ Dstar t)%:R * (q t - p t).
Proof.
by rewrite /Dstar !GRing.mulrb; case: (ltrgtP (q t) (p t)) => ? /=; lra.
Qed.

Local Lemma ge0_posA t : 0 <= (Dstar t)%:R * (p t - q t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => ? /=; rewrite ?mul0r ?mul1r; lra.
Qed.

Local Lemma ge0_negB t : 0 <= (~~ Dstar t)%:R * (q t - p t).
Proof.
have hp := ge0_mu p t; have hq := ge0_mu q t.
rewrite /Dstar !GRing.mulrb.
by case: (ltrgtP (q t) (p t)) => ? /=; rewrite ?mul0r ?mul1r; lra.
Qed.

Local Lemma summable_posA : summable (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
have s : summable (fun t => p t - q t)
  by exact: summableD (summable_mu p) (summableN (summable_mu q)).
exact: (summable_condl Dstar s).
Qed.

Local Lemma summable_negB : summable (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
have s : summable (fun t => q t - p t)
  by exact: summableD (summable_mu q) (summableN (summable_mu p)).
exact: (summable_condl (fun t => ~~ Dstar t) s).
Qed.

(* [Dstar]-restricted masses of [p] and [q] differ by the positive part.      *)
Local Lemma split_p :
  psum (fun t => (Dstar t)%:R * p t)
  = psum (fun t => (Dstar t)%:R * q t)
  + psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
transitivity
  (psum (fun t => (Dstar t)%:R * q t + (Dstar t)%:R * (p t - q t))).
  by apply: eq_psum => t; exact: pw_eqA.
apply: psumD_pw.
- by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
- exact: ge0_posA.
- exact: summable_pr.
- exact: summable_posA.
Qed.

Local Lemma split_q :
  psum (fun t => (~~ Dstar t)%:R * q t)
  = psum (fun t => (~~ Dstar t)%:R * p t)
  + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
transitivity
  (psum (fun t => (~~ Dstar t)%:R * p t + (~~ Dstar t)%:R * (q t - p t))).
  by apply: eq_psum => t; exact: pw_eqB.
apply: psumD_pw.
- by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
- exact: ge0_negB.
- exact: summable_pr.
- exact: summable_negB.
Qed.

Local Lemma pr_diff_posA :
  pr p Dstar - pr q Dstar
  = psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof. by rewrite /pr; move: split_p; lra. Qed.

(* Total variation splits into the positive and negative parts over [Dstar].  *)
Local Lemma statdist_split :
  psum (fun t => `|p t - q t|)
  = psum (fun t => (Dstar t)%:R * (p t - q t))
  + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
rewrite (psumID Dstar (summable_dist p q)); congr (_ + _).
  by apply: eq_psum => t; exact: pw_absA.
by apply: eq_psum => t; exact: pw_absB.
Qed.

(* Equal total masses force the two parts to coincide.                        *)
Local Lemma posA_eq_negB :
  psum p = 1 -> psum q = 1 ->
  psum (fun t => (Dstar t)%:R * (p t - q t))
  = psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
move=> mass_p mass_q.
have Ep := psumID Dstar (summable_mu p).
have Eq := psumID Dstar (summable_mu q).
rewrite mass_p in Ep; rewrite mass_q in Eq.
move: split_p split_q Ep Eq; lra.
Qed.

(* The strict optimal test [fun t => q t < p t] attains the statistical
   distance: for mass-1 laws its acceptance gap equals [statdist p q], the
   maximum distinguisher advantage.
   Naming: intentional; "test" denotes a boolean distinguisher. *)
Lemma statdist_test_max :
  psum p = 1 -> psum q = 1 ->
  pr p Dstar - pr q Dstar = statdist p q.
Proof.
move=> mass_p mass_q.
have h2n : (2%:R : R) != 0 by rewrite pnatr_eq0.
rewrite pr_diff_posA /statdist statdist_split (posA_eq_negB mass_p mass_q).
set B := psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
by rewrite -mulr2n -(mulr_natr B 2) (mulfK h2n).
Qed.

Local Lemma statdist_eq_posA :
  psum p = 1 -> psum q = 1 ->
  statdist p q = psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
move=> mass_p mass_q.
by rewrite -(statdist_test_max mass_p mass_q); exact: pr_diff_posA.
Qed.

Local Lemma statdist_eq_negB :
  psum p = 1 -> psum q = 1 ->
  statdist p q = psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
move=> mass_p mass_q.
by rewrite (statdist_eq_posA mass_p mass_q) (posA_eq_negB mass_p mass_q).
Qed.

(* Any test is dominated by the positive part.                                *)
Local Lemma pr_upper (D : pred T) :
  pr p D - pr q D
  <= psum (fun t => (Dstar t)%:R * (p t - q t)).
Proof.
have E : psum (fun t => (D t)%:R * q t + (Dstar t)%:R * (p t - q t))
       = psum (fun t => (D t)%:R * q t)
       + psum (fun t => (Dstar t)%:R * (p t - q t)).
  apply: psumD_pw.
  - by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
  - exact: ge0_posA.
  - exact: summable_pr.
  - exact: summable_posA.
rewrite /pr lerBlDr addrC -E.
apply: le_psum; last first.
  by apply: summableD; [exact: summable_pr | exact: summable_posA].
move=> t; apply/andP; split; last exact: pw_le.
by apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
Qed.

Local Lemma pr_lower (D : pred T) :
  pr q D - pr p D
  <= psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
Proof.
have E : psum (fun t => (D t)%:R * p t + (~~ Dstar t)%:R * (q t - p t))
       = psum (fun t => (D t)%:R * p t)
       + psum (fun t => (~~ Dstar t)%:R * (q t - p t)).
  apply: psumD_pw.
  - by move=> t; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
  - exact: ge0_negB.
  - exact: summable_pr.
  - exact: summable_negB.
rewrite /pr lerBlDr addrC -E.
apply: le_psum; last first.
  by apply: summableD; [exact: summable_pr | exact: summable_negB].
move=> t; apply/andP; split; last exact: pw_le_swap.
by apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
Qed.

(* For mass-1 laws, every boolean test's acceptance gap is bounded by the
   statistical distance.
   Naming: intentional; "test" denotes a boolean distinguisher. *)
Lemma statdist_test_le (D : pred T) :
  psum p = 1 -> psum q = 1 ->
  `| pr p D - pr q D | <= statdist p q.
Proof.
move=> mass_p mass_q; rewrite ler_norml; apply/andP; split.
  by rewrite lerNl opprB (statdist_eq_negB mass_p mass_q); exact: pr_lower.
by rewrite (statdist_eq_posA mass_p mass_q); exact: pr_upper.
Qed.

End Optimal.

End StatDist.

(** [statdist_test_le] requires mass one: with the point mass [dunit 0%N]
    against the null subdistribution, the always-true test opens gap [1]
    while the distance is [1/2]. *)
Example statdist_test_le_needs_mass1 (R : realType) :
  statdist (dunit 0%N : {distr nat / R}) dnull
    < `|pr (dunit 0%N : {distr nat / R}) predT
         - pr (dnull : {distr nat / R}) predT|.
Proof.
set u := (dunit 0%N : {distr nat / R}).
have Hu : pr u predT = 1 by rewrite /u pr_dunit.
have Hn : pr (dnull : {distr nat / R}) predT = 0.
  by rewrite pr_predT; apply: psum_eq0 => x; exact: dnullE.
have Hpsum : psum (fun t => `|u t - dnull t| : R) = psum u.
  by apply: eq_psum => t; rewrite dnullE subr0 ger0_norm//; exact: ge0_mu.
have Hs : statdist u dnull = 2%:R^-1.
  rewrite /statdist Hpsum /u.
  have -> : psum (dunit 0%N : {distr nat / R}) = 1
    by rewrite -pr_predT pr_dunit.
  by rewrite mul1r.
by rewrite Hs Hu Hn subr0 normr1 invf_lt1 ?ltr0n// ltr1n.
Qed.
