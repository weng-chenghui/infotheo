(* MUTATION of probe_unp_composition.v: the prior weight P_X x is dropped from
   the right-hand side of pred_successE.  coqc is expected to fail.

   Probe for Task R8 (unpredictability.v): T-relative unpredictability and its
   composition law.

   Targets, as fixed by the implementation plan:
     1  pred_successE     the joint-prior success is the prior-weighted sum of
                          the per-input guess-tester acceptances on the view law
     2  pred_success_le   composition: real success <= ideal bound + class edge
     3  unp_entropy_ge    log monotonicity turns the bound into an entropy bound

   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_unp_composition.v                   *)

From mathcomp Require Import all_boot all_order ssralg ssrnum reals.
Require Import realType_ext realType_ln fdist proba.
Require Import finstoch statdist privacy_kernel.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section pr_transport.
Context {R : realType}.

Lemma Pr_fdistmap_preim (A B : finType) (g : A -> B) (d : R.-fdist A)
    (E : {set B}) :
  Pr (fdistmap g d) E = Pr d [set a | g a \in E].
Proof.
rewrite /Pr (partition_big g (mem E)) /=; last by move=> a; rewrite inE.
apply: eq_bigr => b bE; rewrite fdistmapE; apply: eq_bigl => a /=.
by rewrite !inE andb_idl // => /eqP ->.
Qed.

End pr_transport.

Section unpredictability_probe.
Context {R : realType}.
Variables X Yfull Xa Ya Bv Omega Sec : finType.
Variable proj_xa : X -> Xa.
Variable proj_ya : Yfull -> Ya.
Variable F : X -> R.-fdist Yfull.
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.
Variable P_X : R.-fdist X.
Variable sec : X -> Sec.

Local Notation view_law := (view_law P_Omega view_at).
Local Notation sim_view := (sim_view proj_xa proj_ya F).

Definition joint_draw : R.-fdist (X * Omega)%type := tensor P_X P_Omega.

Definition predictor := {ffun Bv -> Sec}.

Definition pred_success (pi : predictor) : R :=
  Pr joint_draw [set e | pi (view_at e) == sec e.1].

(* Naming: pair naming with pred_success; test = tester of the view space, as
   in statdist_test_le. *)
Definition guess_test (pi : predictor) (s : Sec) : tester Bv :=
  [ffun b => pi b == s].

Definition ideal_guess (Sim : simulator Xa Ya Bv) (pi : predictor) : R :=
  \sum_x P_X x * accept (guess_test pi (sec x)) (sim_view Sim x).

Lemma pred_successE (pi : predictor) :
  pred_success pi
  = \sum_x accept (guess_test pi (sec x)) (view_law x).
Proof.
rewrite /pred_success /joint_draw /Pr.
under [RHS]eq_bigr => x _ do
  rewrite /accept view_lawE Pr_fdistmap_preim /Pr big_distrr /=.
rewrite pair_big_dep /=.
apply: eq_big => [[x w]|[x w] _]; last by rewrite tensorE.
by rewrite !inE /guess_test ffunE.
Qed.

Lemma class_adv_sup (T : {set tester Bv}) (D : tester Bv) (p q : R.-fdist Bv) :
  D \in T -> adv D p q <= class_adv T p q.
Proof. by move=> DT; rewrite /class_adv; apply: bigmax_sup DT _. Qed.

Lemma pred_success_ideal_le (pi : predictor) (Sim : simulator Xa Ya Bv)
    (T : {set tester Bv}) (e_total : R) :
  (forall s, guess_test pi s \in T) ->
  (forall x, class_adv T (view_law x) (sim_view Sim x) <= e_total) ->
  pred_success pi <= ideal_guess Sim pi + e_total.
Proof.
move=> hT he.
have step x : accept (guess_test pi (sec x)) (view_law x)
    <= accept (guess_test pi (sec x)) (sim_view Sim x) + e_total.
  rewrite addrC -lerBlDr.
  apply: le_trans (he x); apply: le_trans (class_adv_sup _ _ (hT (sec x))).
  exact: ler_norm.
rewrite pred_successE /ideal_guess.
have hsum : \sum_(x in X) P_X x * e_total = e_total.
  by rewrite -big_distrl /= FDist.f1 mul1r.
rewrite -hsum -big_split /=.
by apply: ler_sum => x _; rewrite -mulrDr ler_wpM2l.
Qed.

Lemma pred_success_le (pi : predictor) (Sim : simulator Xa Ya Bv)
    (T : {set tester Bv}) (e_total p_ideal : R) :
  (forall s, guess_test pi s \in T) ->
  (forall x, class_adv T (view_law x) (sim_view Sim x) <= e_total) ->
  ideal_guess Sim pi <= p_ideal ->
  pred_success pi <= p_ideal + e_total.
Proof.
move=> hT he hp.
by apply: le_trans (pred_success_ideal_le hT he) _; rewrite lerD2r.
Qed.

Lemma unp_entropy_ge (pi : predictor) (Sim : simulator Xa Ya Bv)
    (T : {set tester Bv}) (e_total p_ideal : R) :
  (forall s, guess_test pi s \in T) ->
  (forall x, class_adv T (view_law x) (sim_view Sim x) <= e_total) ->
  ideal_guess Sim pi <= p_ideal ->
  0 < pred_success pi ->
  - log (p_ideal + e_total) <= - log (pred_success pi).
Proof.
move=> hT he hp hs.
have hle := pred_success_le hT he hp.
have hpe : 0 < p_ideal + e_total by apply: lt_le_trans hs hle.
by rewrite lerN2 ler_log ?posrE.
Qed.

End unpredictability_probe.
