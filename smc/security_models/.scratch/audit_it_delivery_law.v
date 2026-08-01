(* IT-SECURITY ADVERSARIAL AUDIT of the design spec
   phd-thesis/docs/superpowers/specs/
     2026-08-01-security-models-output-independence-fix-design.md

   Two compiled findings.

   PART A (evidence gap in ledger row C1).  The spec's C1 cites
   audit_snd_randomized_F.v for "centropy 0 vs log 2".  That file proves
   only the 0 side (centropy_view_honest0).  The log 2 side is asserted
   in a source comment and is NOT compiled anywhere.  Part A supplies it,
   so that both sides of the inequality behind eq:smc:entropy are
   machine-checked at the counterexample instance.

   PART B (refutation of ledger row C4b, and of C5/C6 as stated).
   The spec's converse claims: the conditional-entropy equality
   eq:smc:entropy implies the existence of a CONSISTENT simulator closing
   the privacy triangle.  This is FALSE in the chapter's own model.  The
   entropy equality is a statement about the honest side of the REAL
   execution; it is blind to whether the real delivered output of the
   CORRUPTED parties has the law the ideal functionality prescribes.  The
   chapter's correctness data (run_correct : agg (run e) = f e.1;
   F_compat : fdistmap agg (F x) = fdist1 (f x)) pins only the AGGREGATE,
   so the real Y_A may differ from the ideal f_A(x) while every stated
   hypothesis holds.  Part B compiles an instance where

     - the conditional-entropy equality eq:smc:entropy HOLDS, and is
       non-degenerate (both sides equal log 2, not 0 = 0),
     - the ideal functionality is DETERMINISTIC (so the spec's det-F
       corollary C5 does not rescue the converse), and
     - NO simulator satisfying the spec's consistency condition
       out_A o Sim(a,y) = y closes the privacy triangle.

   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_it_delivery_law.v            *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln fdist proba.
Require Import jfdist_cond entropy graphoid.
Require Import extra_proba.
Require Import extra_entropy.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(* ------------------------------------------------------------------ *)
(* PART A: the missing half of the C1 certificate.                      *)
(* ------------------------------------------------------------------ *)

Section part_A_log2_half.
Context {R : realType}.

(* Same instance as audit_snd_randomized_F.v. *)
Definition P2 : R.-fdist 'I_2 := @fdist_uniform R _ 1 (card_ord 2).
Definition dA : R.-fdist ('I_1 * 'I_2)%type := ((fdist1 ord0) `x P2)%fdist.

Definition honest_rv : {RV dA -> 'I_2} := snd.
Definition allow_rv  : {RV dA -> 'I_1} := fst.

Lemma dAE u : dA u = 2%:R^-1.
Proof.
case: u => a b; rewrite /dA fdist_prodE (ord1 a) fdist1xx mul1r.
by rewrite /P2 fdist_uniformE card_ord.
Qed.

Lemma p_honest : `p_ honest_rv = P2.
Proof.
apply/fdist_ext => b; rewrite dist_of_RVE pfwd1E.
suff -> : finset (honest_rv @^-1 b) = [set (ord0, b) : 'I_1 * 'I_2].
  by rewrite Pr_set1 dAE /P2 fdist_uniformE card_ord.
by apply/setP => -[a c]; rewrite !inE /honest_rv/= xpair_eqE (ord1 a) eqxx.
Qed.

(* The allowed information is constant, so it is independent of the
   honest output. *)
Lemma joint_honest_allow :
  `p_ [% honest_rv, allow_rv] = (`p_ honest_rv `x `p_ allow_rv)%fdist.
Proof.
apply/fdist_ext => -[b a]; rewrite fdist_prodE !dist_of_RVE.
have -> : `Pr[ allow_rv = a ] = 1.
  rewrite pfwd1E; suff -> : finset (allow_rv @^-1 a) = [set: ('I_1 * 'I_2)%type]
    by rewrite Pr_setT.
  by apply/setP => u; rewrite !inE (ord1 (allow_rv u)) (ord1 a) eqxx.
rewrite mulr1 !pfwd1E; congr Pr; apply/setP => -[c d].
by rewrite !inE /honest_rv /allow_rv/= xpair_eqE (ord1 c) (ord1 a) eqxx andbT.
Qed.

(* PART A.  The half of ledger row C1 that audit_snd_randomized_F.v
   asserts in a comment but does not compile: against
   `H(honest | view, allowed) = 0 there stands `H(honest | allowed) = log 2,
   so eq:smc:entropy genuinely fails at that instance. *)
Lemma centropy_honest_allow : `H( honest_rv | allow_rv ) = log 2%:R :> R.
Proof.
have H1 : `p_ [% honest_rv, allow_rv]
  = ((`p_ [% honest_rv, allow_rv])`1 `x (`p_ [% honest_rv, allow_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_honest_allow.
rewrite /centropy_RV (centropy_indep H1) fst_RV2 p_honest.
by rewrite /P2 entropy_uniform card_ord.
Qed.

End part_A_log2_half.

(* ------------------------------------------------------------------ *)
(* PART B: the converse (ledger row C4b) is false as stated.            *)
(* ------------------------------------------------------------------ *)

(* The instance, in the chapter's vocabulary:

     one corrupted party A, one honest party;
     X_A = 1 (no adversary input), X_h = 'I_2 with the uniform prior;
     the view space B_A = bool, the adversary's delivery space Y_A = bool;
     out_A = id : B_A -> Y_A                    (read-off, surjective);
     the real protocol emits the constant view true, hence delivers
       Y_A = out_A(view) = true                 (read-off square holds);
     the honest delivery space Y_h = 1;
     the ideal functionality is DETERMINISTIC and delivers false to A:
       f_A(x) = false for every x, so allow_A(x) = (tt, false).

   Correctness in the chapter's sense is available: take the aggregation
   agg : Y_A * Y_h -> Y := const tt, so agg o out = f and
   fdistmap agg (F x) = fdist1 (f x) both hold; the aggregate says
   nothing about the Y_A coordinate. *)

Section part_B_converse_counterexample.
Context {R : realType}.

Definition Pu : R.-fdist 'I_2 := @fdist_uniform R _ 1 (card_ord 2).

Definition xh_rv   : {RV Pu -> 'I_2}  := id.        (* honest input   *)
Definition yh_rv   : {RV Pu -> 'I_1}  := fun _ => ord0. (* honest output *)
Definition xa_rv   : {RV Pu -> 'I_1}  := fun _ => ord0. (* adv input    *)
Definition view_rv : {RV Pu -> bool}  := fun _ => true. (* the real view *)

Definition out_A : bool -> bool := id.

(* Read-off square: the adversary's delivered output IS read off its view. *)
Definition ya_rv : {RV Pu -> bool} := out_A \o view_rv.

Lemma readoff_square : forall u, ya_rv u = out_A (view_rv u).
Proof. by []. Qed.

(* --- the conditional-entropy equality eq:smc:entropy holds here --- *)

Lemma pr_view_true (u : 'I_2) : view_rv u = true.
Proof. by []. Qed.

(* The view is a.s. constant, hence conditionally independent of
   anything given anything. *)
Lemma view_cinde (TB TC : finType) (W : {RV Pu -> TB}) (Z : {RV Pu -> TC}) :
  Pu |= view_rv _|_ W | Z.
Proof.
apply: (cinde_RV_factor
          (f := fun (w : TB) (z : TC) => `Pr[ [% W, Z] = (w, z) ])
          (g := fun (_ : TC) (v : bool) => if v then 1 else 0)) => -[] w z /=.
  by rewrite mulr1 !pfwd1E; congr Pr.
rewrite mulr0 pfwd1E /Pr big_pred0//= => u.
by rewrite !inE/= !xpair_eqE.
Qed.

(* eq:smc:entropy at this instance, honest PAIR on the left, exactly the
   chapter's display. *)
Lemma entropy_equality_holds :
  `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
  = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ).
Proof. exact/cinde_centropy_eq/view_cinde. Qed.

(* The spec's output-independence condition also holds at this instance,
   in the chapter's conditioning set (X, Y_A) = ((X_A, X_h), Y_A).  So the
   counterexample below refutes the converse even when the condition is
   assumed on the entropy side, not only when it is dropped. *)
Lemma output_independence_holds :
  Pu |= view_rv _|_ yh_rv | [% [% xa_rv, xh_rv], ya_rv].
Proof. exact: view_cinde. Qed.

(* Non-degeneracy: the two equal sides are log 2, not 0. *)
Lemma p_xh : `p_ xh_rv = Pu.
Proof. exact: fdistmap_id. Qed.

Lemma joint_xh_xa :
  `p_ [% xh_rv, xa_rv] = (`p_ xh_rv `x `p_ xa_rv)%fdist.
Proof.
apply/fdist_ext => -[b a]; rewrite fdist_prodE !dist_of_RVE.
have -> : `Pr[ xa_rv = a ] = 1.
  rewrite pfwd1E; suff -> : finset (xa_rv @^-1 a) = [set: 'I_2] by rewrite Pr_setT.
  by apply/setP => u; rewrite !inE (ord1 (xa_rv u)) (ord1 a) eqxx.
rewrite mulr1 !pfwd1E; congr Pr; apply/setP => c.
by rewrite !inE /xh_rv /xa_rv/= xpair_eqE (ord1 a) eqxx andbT.
Qed.

Lemma entropy_nondegenerate : `H( xh_rv | xa_rv ) = log 2%:R :> R.
Proof.
have H1 : `p_ [% xh_rv, xa_rv]
  = ((`p_ [% xh_rv, xa_rv])`1 `x (`p_ [% xh_rv, xa_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_xh_xa.
rewrite /centropy_RV (centropy_indep H1) fst_RV2 p_xh.
by rewrite /Pu entropy_uniform card_ord.
Qed.

(* --- yet no consistent simulator closes the privacy triangle --- *)

(* The real view law, at every input (the input space is a singleton). *)
Definition view_law : R.-fdist bool := fdist1 true.

(* The allowed information: the deterministic ideal functionality
   delivers false to the adversary. *)
Definition allow_law : R.-fdist ('I_1 * bool)%type := fdist1 (ord0, false).

(* The spec's simulator-consistency condition:
   the output read off a simulated view is the delivered output the
   simulator was handed. *)
Definition consistent (Sim : 'I_1 * bool -> R.-fdist bool) : Prop :=
  forall a y, fdistmap out_A (Sim (a, y)) = fdist1 y.

(* PART B.  eq:smc:entropy holds (entropy_equality_holds, non-degenerately
   by entropy_nondegenerate) at a DETERMINISTIC ideal functionality, and
   yet no consistent simulator closes the triangle
   nu_A = Sim o allow_A.  The spec's converse (ledger row C4b) therefore
   needs a hypothesis the chapter's model does not supply: the real
   delivered output of the corrupted parties must have the law the ideal
   functionality prescribes. *)
Lemma no_consistent_simulator (Sim : 'I_1 * bool -> R.-fdist bool) :
  consistent Sim -> view_law <> (allow_law >>= Sim)%fdist.
Proof.
move=> Hc Htri.
have Hbind : (allow_law >>= Sim)%fdist = Sim (ord0, false) by rewrite fdist1bind.
have Hfalse : Sim (ord0, false) = fdist1 false.
  by rewrite -[LHS](fdistmap_id (Sim (ord0, false))) Hc.
have H1 : (fdist1 true : R.-fdist bool) true = (fdist1 false : R.-fdist bool) true.
  by rewrite -/view_law Htri Hbind Hfalse.
move: H1; rewrite fdist1xx fdist10//.
by move/eqP; rewrite oner_eq0.
Qed.

End part_B_converse_counterexample.

(* --- verification block: statements as compiled, and axiom hygiene --- *)
About centropy_honest_allow.
About entropy_equality_holds.
About entropy_nondegenerate.
About no_consistent_simulator.
Print Assumptions centropy_honest_allow.
Print Assumptions entropy_equality_holds.
Print Assumptions no_consistent_simulator.
