(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order ssralg ssrnum reals.
Require Import realType_ext realType_ln fdist proba.
Require Import finstoch statdist privacy_kernel.

(**md**************************************************************************)
(* # T-relative unpredictability                                              *)
(*                                                                            *)
(* An input prior together with the ancilla law makes the execution context   *)
(* into a probability space, on which a secret map reads a secret off the     *)
(* input.  A predictor is a function from the view space to the secret        *)
(* space, and its success is the probability that it names the secret of the  *)
(* drawn execution.  Each secret value turns a predictor into a tester of     *)
(* the view space, and when those testers belong to the tester class T the    *)
(* success of the predictor against the real view law exceeds its success     *)
(* against the simulated view law by at most the T-relative advantage         *)
(* between the two laws.  Since the base-2 logarithm is decreasing under      *)
(* negation, the same bound reads as a lower bound on the unpredictability    *)
(* entropy of the secret.                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      Pr_fdistmap_preim == the mass a transported law gives to a set is     *)
(*                           the mass the source law gives to its preimage    *)
(*             joint_draw == the law on the execution context that draws the  *)
(*                           input from the prior and the ancilla from the    *)
(*                           ancilla law                                      *)
(*              predictor == the type {ffun Bv -> Sec} of maps from the view  *)
(*                           space to the secret space                        *)
(*        pred_success pi == the probability that pi names the secret of the  *)
(*                           drawn execution                                  *)
(*       guess_test pi s == the tester that accepts the views on which pi     *)
(*                           answers s                                        *)
(*     ideal_guess Sim pi == the success of pi against the simulated view law *)
(*          class_adv_sup == a member tester's advantage is at most the       *)
(*                           class advantage                                  *)
(*          pred_successE == the success of a predictor is the prior-weighted *)
(*                           sum of the acceptances of its guess testers on   *)
(*                           the view laws                                    *)
(*  pred_success_ideal_le == the success of a predictor exceeds its simulated *)
(*                           success by at most the class advantage           *)
(*        pred_success_le == the success of a predictor is at most any bound  *)
(*                           on its simulated success plus the class          *)
(*                           advantage                                        *)
(*         unp_entropy_ge == the unpredictability entropy of the secret is at *)
(*                           least the entropy of that bound                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section pr_transport.
Context {R : realType}.

(* The mass a transported law gives to a set is the mass the source law gives
   to the preimage of that set. *)
Lemma Pr_fdistmap_preim (A B : finType) (g : A -> B) (d : R.-fdist A)
    (E : {set B}) :
  Pr (fdistmap g d) E = Pr d [set a | g a \in E].
Proof.
rewrite /Pr (partition_big g (mem E)) /=; last by move=> a; rewrite inE.
apply: eq_bigr => b bE; rewrite fdistmapE; apply: eq_bigl => a /=.
by rewrite !inE andb_idl // => /eqP ->.
Qed.

End pr_transport.

Section unpredictability.
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

(* The joint law on the execution context draws the input from the prior and
   the ancilla from the ancilla law, independently. *)
Definition joint_draw : R.-fdist (X * Omega)%type := tensor P_X P_Omega.

(* A predictor answers a secret value at every view. *)
Definition predictor := {ffun Bv -> Sec}.

(* The success of a predictor is the probability that it answers the secret of
   the drawn execution.
   Naming: pred abbreviates predictor, the type this success is indexed by. *)
Definition pred_success (pi : predictor) : R :=
  Pr joint_draw [set e | pi (view_at e) == sec e.1].

(* The guess tester of a predictor at a secret value accepts the views on which
   the predictor answers that value.
   Naming: pair naming with pred_success; test = tester of the view space, as
   in statdist_test_le. *)
Definition guess_test (pi : predictor) (s : Sec) : tester Bv :=
  [ffun b => pi b == s].

(* The ideal success of a predictor is the prior-weighted sum of the
   acceptances of its guess testers on the simulated view laws. *)
Definition ideal_guess (Sim : simulator Xa Ya Bv) (pi : predictor) : R :=
  \sum_x P_X x * accept (guess_test pi (sec x)) (sim_view Sim x).

(* The success of a predictor is the prior-weighted sum of the acceptances of
   its guess testers on the view laws. *)
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

(* prop:smc:composition *)
(* The advantage of a tester in a class is at most the class advantage. *)
Lemma class_adv_sup (T : {set tester Bv}) (D : tester Bv) (p q : R.-fdist Bv) :
  D \in T -> adv D p q <= class_adv T p q.
Proof. by move=> DT; rewrite /class_adv; apply: bigmax_sup DT _. Qed.

(* The success of a predictor whose guess testers all lie in the class T
   exceeds its ideal success by at most a bound on the T-relative advantage
   between the view law and the simulated view law. *)
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
rewrite pred_successE /ideal_guess -[e_total]mul1r -(FDist.f1 P_X) big_distrl.
rewrite -big_split /=.
by apply: ler_sum => x _; rewrite -mulrDr ler_wpM2l.
Qed.

(* The success of a predictor whose guess testers all lie in the class T is at
   most any bound on its ideal success plus any bound on the T-relative
   advantage between the view law and the simulated view law. *)
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

(* Under the hypotheses of the composition bound and a predictor of positive
   success, the unpredictability entropy of the secret is at least the entropy
   of the bound.
   Naming: unp abbreviates unpredictability, the entropy this bounds. *)
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

End unpredictability.
