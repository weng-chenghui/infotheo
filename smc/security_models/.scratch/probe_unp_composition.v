(* Probe for Task R8 (unpredictability.v): T-relative unpredictability and its
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
  = \sum_x P_X x * accept (guess_test pi (sec x)) (view_law x).
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

(* ------------------------------------------------------------------ *)
(* Refutation certificate.                                             *)
(*                                                                     *)
(* The implementation plan states unp_entropy_ge with the side          *)
(* condition 0 < p_ideal + e_total.  That condition does not support    *)
(* the conclusion: log's monotonicity domain is Num.pos on BOTH sides,  *)
(* and log 0 = 0 by the junk value of ln at 0, so a predictor that      *)
(* never succeeds has - log (pred_success pi) = 0 while                 *)
(* - log (p_ideal + e_total) > 0 whenever p_ideal + e_total < 1.        *)
(*                                                                     *)
(* The witness: a one-point ancilla, a one-point view space, a          *)
(* two-point input space carrying the point mass at 1, a secret map     *)
(* that is the identity, and the constant-0 predictor.  Every           *)
(* hypothesis of the composition lemma holds with T the full tester     *)
(* class, e_total = 0 and p_ideal = 2^-1, and pred_success pi = 0.      *)
(* ------------------------------------------------------------------ *)

Section unp_entropy_weak_side_condition.
Context {R : realType}.

Let one : 'I_2 := @Ordinal 2 1 isT.
Let pi0 : predictor 'I_1 'I_2 := [ffun _ => ord0].
Let P_X0 : R.-fdist 'I_2 := fdist1 one.
Let P_Omega0 : R.-fdist 'I_1 := fdist1 ord0.
Let view_at0 : 'I_2 * 'I_1 -> 'I_1 := fun _ => ord0.
Let F0 : 'I_2 -> R.-fdist 'I_1 := fun _ => fdist1 ord0.
Let Sim0 : simulator (R := R) 'I_1 'I_1 'I_1 := fun _ => fdist1 ord0.

Let fdist_I1 (p q : R.-fdist 'I_1) : p = q.
Proof.
have e (r : R.-fdist 'I_1) : r ord0 = 1 by have := FDist.f1 r; rewrite big_ord1.
by apply/fdist_ext => i; rewrite (ord1 i) !e.
Qed.

Let guess_sum (m : 'I_2 -> R.-fdist 'I_1) :
  \sum_x P_X0 x * accept (guess_test pi0 x) (m x) = 0.
Proof.
apply: big1 => x _; have [->|xn] := eqVneq x one; last first.
  by rewrite /P_X0 fdist1E (negbTE xn) mul0r.
rewrite /accept (_ : [set b | guess_test pi0 one b] = set0) ?Pr_set0 ?mulr0//.
by apply/setP => b; rewrite !inE /guess_test /pi0 !ffunE.
Qed.

Let log0 : log (0 : R) = 0.
Proof. by rewrite /log /Log exp.ln0 ?mul0r. Qed.

(* Naming: refutation-certificate register, as delivery_law_failsA; the verb
   names what the certificate shows about the plan's weak side condition. *)
Lemma unp_entropy_weak_fails :
  ~ (forall (X Yfull Xa Ya Bv Omega Sec : finType)
       (proj_xa : X -> Xa) (proj_ya : Yfull -> Ya) (F : X -> R.-fdist Yfull)
       (P_Omega : R.-fdist Omega) (view_at : X * Omega -> Bv)
       (P_X : R.-fdist X) (sec : X -> Sec) (pi : predictor Bv Sec)
       (Sim : simulator Xa Ya Bv) (T : {set tester Bv}) (e_total p_ideal : R),
     (forall s, guess_test pi s \in T) ->
     (forall x, class_adv T (view_law P_Omega view_at x)
                  (sim_view proj_xa proj_ya F Sim x) <= e_total) ->
     ideal_guess proj_xa proj_ya F P_X sec Sim pi <= p_ideal ->
     0 < p_ideal + e_total ->
     - log (p_ideal + e_total)
       <= - log (pred_success P_Omega view_at P_X sec pi)).
Proof.
move=> H.
have hT (s : 'I_2) : guess_test pi0 s \in [set: tester 'I_1] by rewrite inE.
have he x : class_adv [set: tester 'I_1] (view_law P_Omega0 view_at0 x)
    (sim_view (fun _ : 'I_2 => ord0) (id : 'I_1 -> 'I_1) F0 Sim0 x) <= 0.
  rewrite (fdist_I1 (view_law P_Omega0 view_at0 x)
    (sim_view (fun _ : 'I_2 => ord0) id F0 Sim0 x)).
  by rewrite class_advxx.
have hp : ideal_guess (fun _ : 'I_2 => ord0) (id : 'I_1 -> 'I_1) F0 P_X0 id
    Sim0 pi0 <= 2^-1 :> R.
  by rewrite /ideal_guess guess_sum invr_ge0 ler0n.
have hpos : 0 < 2^-1 + 0 :> R by rewrite addr0 invr_gt0 ltr0n.
have := H _ _ _ _ _ _ _ (fun _ : 'I_2 => ord0) (id : 'I_1 -> 'I_1) F0
  P_Omega0 view_at0 P_X0 (id : 'I_2 -> 'I_2) pi0 Sim0 [set: tester 'I_1] 0 2^-1
  hT he hp hpos.
rewrite pred_successE guess_sum log0 oppr0 addr0.
by rewrite logV ?ltr0n// log2 opprK leNgt ltr01.
Qed.

End unp_entropy_weak_side_condition.
