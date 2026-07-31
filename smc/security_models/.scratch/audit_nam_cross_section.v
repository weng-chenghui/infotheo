(* Naming/design audit: cross-section usage of statdist.v names inside
   privacy_kernel.v.
   Check A: probe P2 declares the statdist section with Context {B : finType}
     (implicit).  Probe P5 / the privacy_kernel plan writes [D : tester Bv]
     with tester's finType argument EXPLICIT.  If statdist.v copies P2
     verbatim, [tester Bv] is an illegal application.
   Check B: with the finType argument explicit (Variable, not Context {}),
     every P5 interface Hypothesis restates as the P2 Qed lemma by a bare
     [exact:], i.e. the shapes match exactly.
   Check C: P5's Hypotheses adv_triangle and adv_ge0 have NO Qed counterpart
     in probe_statdist_maxadv.v; both are one-liners, so the gap is a missing
     row in the statdist.v artifact list, not a proof risk.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_nam_cross_section.v          *)
From mathcomp Require Import all_ssreflect all_algebra reals lra.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* ---- Check A: verbatim probe-P2 header, Context {B} implicit. ---- *)
Module ContextStyle.
Section statdist.
Context {R : realType} {B : finType}.
Implicit Types p q r : R.-fdist B.
Definition statdist p q : R := 2%:R^-1 * \sum_b `|p b - q b|.
Definition tester := {ffun B -> bool}.
Definition accept (D : tester) p : R := Pr p [set b | D b].
Definition adv (D : tester) p q : R := `|accept D p - accept D q|.
End statdist.

Section kernel_use.
Context {R : realType}.
Variables X Bv Xa Ya : finType.
Variable view_law : X -> R.-fdist Bv.
Variable sim_view : ((Xa * Ya)%type -> R.-fdist Bv) -> X -> R.-fdist Bv.

(* The P5 spelling [D : tester Bv] does not elaborate: B is implicit,
   so [tester] is already a Type and cannot be applied. *)
Fail Definition test_adv (S : (Xa * Ya)%type -> R.-fdist Bv)
  (D : tester Bv) : R :=
  \big[Num.max/0]_x adv D (view_law x) (sim_view S x).

(* The (B := Bv) workaround elaborates, i.e. the friction is only the
   implicit status, not the definition itself. *)
Definition test_adv (S : (Xa * Ya)%type -> R.-fdist Bv)
  (D : tester (B := Bv)) : R :=
  \big[Num.max/0]_x adv D (view_law x) (sim_view S x).
End kernel_use.
End ContextStyle.

(* ---- Check B: explicit finType argument; P5 hypothesis shapes are the
        P2 lemma shapes, verbatim [exact:]. ---- *)
Module VariableStyle.
Section statdist.
Context {R : realType}.
Variable B : finType.
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

Lemma statdist_eq0 p q : (statdist p q == 0) = (p == q).
Proof.
apply/idP/idP => [|/eqP ->]; last first.
  by apply/eqP; rewrite /statdist big1 ?mulr0// => b _; rewrite subrr normr0.
rewrite /statdist mulf_eq0 invr_eq0 pnatr_eq0/= => /eqP H.
apply/eqP/fdist_ext => b; apply/eqP; rewrite -subr_eq0 -normr_eq0.
by apply/eqP; apply: (psumr_eq0P _ H).
Qed.

Definition tester := {ffun B -> bool}.
Definition accept (D : tester) p : R := Pr p [set b | D b].
Definition adv (D : tester) p q : R := `|accept D p - accept D q|.

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

Lemma statdist_test_le (D : tester) p q : adv D p q <= statdist p q.
Proof.
rewrite /adv accept_diff ler_norml; apply/andP; split; last exact: sum_diff_le.
rewrite lerNl -sumrN; under eq_bigr do rewrite opprB.
by rewrite statdist_sym; exact: sum_diff_le.
Qed.

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

(* Check C: the two P5 Hypotheses with no P2 Qed counterpart. *)
Lemma adv_ge0 (D : tester) p q : 0 <= adv D p q.
Proof. exact: normr_ge0. Qed.

Lemma adv_triangle (D : tester) p q r : adv D p q <= adv D p r + adv D r q.
Proof. exact: ler_distD. Qed.
End statdist.

(* Check B proper: each P5 interface Hypothesis, restated verbatim with its
   quantifier prefix, is the section-closed lemma by a bare [exact:]. *)
Section p5_shapes.
Context {R : realType}.
Lemma p5_statdist_eq0 :
  forall (B : finType) (p q : R.-fdist B), (statdist p q == 0) = (p == q).
Proof. exact: statdist_eq0. Qed.
Lemma p5_statdist_test_le :
  forall (B : finType) (D : tester B) (p q : R.-fdist B),
    adv D p q <= statdist p q.
Proof. exact: statdist_test_le. Qed.
Lemma p5_statdist_test_max :
  forall (B : finType) (p q : R.-fdist B),
    \big[Num.max/0]_(D : tester B) adv D p q = statdist p q.
Proof. exact: statdist_test_max. Qed.
Lemma p5_statdist_triangle :
  forall (B : finType) (p q r : R.-fdist B),
    statdist p q <= statdist p r + statdist r q.
Proof. exact: statdist_triangle. Qed.
Lemma p5_adv_triangle :
  forall (B : finType) (D : tester B) (p q r : R.-fdist B),
    adv D p q <= adv D p r + adv D r q.
Proof. exact: adv_triangle. Qed.
Lemma p5_adv_ge0 :
  forall (B : finType) (D : tester B) (p q : R.-fdist B), 0 <= adv D p q.
Proof. exact: adv_ge0. Qed.
End p5_shapes.
End VariableStyle.

(* Relation to the pre-existing repo object: statdist is half var_dist. *)
Require Import variation_dist.
Section var_dist_link.
Context {R : realType} (B : finType).
Lemma statdist_var_dist (p q : R.-fdist B) :
  VariableStyle.statdist p q = 2%:R^-1 * var_dist p q.
Proof. by []. Qed.
End var_dist_link.
