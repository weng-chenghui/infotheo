(* Probe P5 — claim S13: the decomposition probe.  States the design's
   game-side headlines and derives them to Qed from the interface
   hypotheses: this checks that quantifiers and types agree across the
   whole statement set and that the supports compose into the headlines.
   The section Hypotheses are the interface; their provability is covered
   by probes P1/P2.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_kernel_decomposition.v      *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section decomposition.
Context {R : realType}.

(* --- statdist/tester interface (statements only; provability = P2) --- *)
Variable statdist : forall B : finType, R.-fdist B -> R.-fdist B -> R.
Arguments statdist {B}.
Definition tester (B : finType) := {ffun B -> bool}.
Variable adv : forall B : finType, tester B -> R.-fdist B -> R.-fdist B -> R.
Arguments adv {B}.

Hypothesis statdist_eq0 :
  forall (B : finType) (p q : R.-fdist B), (statdist p q == 0) = (p == q).
Hypothesis statdist_test_le :
  forall (B : finType) (D : tester B) (p q : R.-fdist B),
    adv D p q <= statdist p q.
Hypothesis statdist_test_max :
  forall (B : finType) (p q : R.-fdist B),
    \big[Num.max/0]_(D : tester B) adv D p q = statdist p q.
Hypothesis statdist_triangle :
  forall (B : finType) (p q r : R.-fdist B),
    statdist p q <= statdist p r + statdist r q.
Hypothesis adv_triangle :
  forall (B : finType) (D : tester B) (p q r : R.-fdist B),
    adv D p q <= adv D p r + adv D r q.
Hypothesis adv_ge0 :
  forall (B : finType) (D : tester B) (p q : R.-fdist B), 0 <= adv D p q.

(* --- kernel interface (statements only; provability = P1) --- *)
Variables X Bv Xa Ya : finType.
Variable view_law : X -> R.-fdist Bv.
Variable allow : X -> R.-fdist (Xa * Ya)%type.
Definition simulator := (Xa * Ya)%type -> R.-fdist Bv.
Variable sim_view : simulator -> X -> R.-fdist Bv.
Definition perfect_privacy (S : simulator) := view_law =1 sim_view S.
Definition eps_privacy (S : simulator) (eps : R) :=
  forall x, statdist (view_law x) (sim_view S x) <= eps.

Definition test_adv (D : tester Bv) (S : simulator) : R :=
  \big[Num.max/0]_x adv D (view_law x) (sim_view S x).

(* --- headline 1: perfect privacy iff every test ties --- *)
Lemma perfect_privacy_testP (S : simulator) :
  perfect_privacy S <-> (forall D : tester Bv, test_adv D S = 0).
Proof.
split=> [hS D|hD x].
  have hst (y : X) : statdist (view_law y) (sim_view S y) = 0.
    by apply/eqP; rewrite statdist_eq0 (hS y) eqxx.
  rewrite /test_adv; apply: bigmax_eq_id => y _.
  by rewrite -(hst y); exact: statdist_test_le.
apply/eqP; rewrite -statdist_eq0 -statdist_test_max; apply/eqP.
apply: bigmax_eq_id => D _.
by rewrite -(hD D) /test_adv; exact: le_bigmax.
Qed.

(* --- headline 2: eps-privacy iff every test is eps-bounded --- *)
Lemma eps_privacy_testP (S : simulator) (eps : R) : 0 <= eps ->
  eps_privacy S eps <-> (forall D : tester Bv, test_adv D S <= eps).
Proof.
move=> eps0; split=> [hS D|hD x].
  rewrite /test_adv; apply: bigmax_le; first exact: eps0.
  by move=> y _; exact: le_trans (@statdist_test_le _ _ _ _) (hS y).
rewrite -statdist_test_max; apply: bigmax_le; first exact: eps0.
move=> D _; apply: (le_trans _ (hD D)).
by rewrite /test_adv; exact: le_bigmax.
Qed.

(* --- headline 3: the hybrid bound (def:smc:hybrid's content) --- *)
Lemma hybrid_bound (S : simulator) (H : X -> R.-fdist Bv)
    (D : tester Bv) (e_game e_sim : R) :
  (forall x, adv D (view_law x) (H x) <= e_game) ->
  (forall x, adv D (H x) (sim_view S x) <= e_sim) ->
  forall x, adv D (view_law x) (sim_view S x) <= e_game + e_sim.
Proof.
move=> h_game h_sim x.
apply: le_trans (@adv_triangle _ _ _ _ (H x)) _.
by apply: lerD; [exact: h_game|exact: h_sim].
Qed.

End decomposition.

(* PROBE FINDINGS (P5)
   1. The bigmax API did not resist: test_adv keeps its stated shape and no
      support hypothesis was added.  Order.TotalTheory supplies bigmax_eq_id
      and le_bigmax, Order.POrderTheory supplies bigmax_le, all applying to
      \big[Num.max/0] over a realType without a Monoid.law on Num.max.
   2. Hypotheses consumed, read off the discharged signatures:
        perfect_privacy_testP : statdist_eq0, statdist_test_le,
                                statdist_test_max
        eps_privacy_testP     : statdist_test_le, statdist_test_max
        hybrid_bound          : adv_triangle
      statdist_triangle and adv_ge0 are consumed by no headline.  adv_ge0 is
      dispensable because bigmax_eq_id needs only the upper bound against the
      identity element 0.
   3. Assumption audit: each headline reports the three boolp axioms
      (propositional_extensionality, functional_extensionality_dep,
      constructive_indefinite_description).  That set is the library baseline
      of any statement quantified over R : realType; x <= x for x : R already
      reports it.  No axiom beyond the baseline, and no Admitted.           *)
