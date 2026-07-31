(* SOUNDNESS AUDIT — quantifier-order check for the design spec
   (smc/notes/20260731-security-models-formalization-design.md, §5).
   Claim under audit: perfect_privacy via =1 fixes ONE simulator for all
   inputs, and the per-input constant simulator does NOT satisfy the
   definition.  This file exhibits a concrete instance ('I_2 inputs and
   views, trivial allowed information, view_law = fdist1 = identity leak)
   in which
     - every input is per-input simulable (per_input_simulable), yet
     - no single simulator satisfies perfect_privacy (no_single_simulator).
   The same instance witnesses satisfiability of the hypothesis pair of
   prop:smc:insecurity (allow x = allow x', view_law x != view_law x'),
   so the insecurity lemma is not vacuous.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_snd_quantifier.v            *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section quantifier_order.
Context {R : realType}.

(* The kernel shapes of the spec at a concrete carrier: inputs and views
   are 'I_2, the allowed-information space is the one-point 'I_1 * 'I_1
   (the adversary is allowed nothing), and the protocol leaks the input:
   view_law x = fdist1 x. *)
Definition simulator := ('I_1 * 'I_1)%type -> R.-fdist 'I_2.
Definition view_law (x : 'I_2) : R.-fdist 'I_2 := fdist1 x.
Definition allow (x : 'I_2) : R.-fdist ('I_1 * 'I_1)%type :=
  fdist1 (ord0, ord0).
Definition sim_view (S : simulator) (x : 'I_2) : R.-fdist 'I_2 :=
  allow x >>= S.
Definition perfect_privacy (S : simulator) := view_law =1 sim_view S.

(* Per-input, the constant simulator S_x := fun _ => view_law x wins. *)
Lemma per_input_simulable (x : 'I_2) :
  exists S : simulator, view_law x = sim_view S x.
Proof.
by exists (fun=> view_law x); rewrite /sim_view /allow fdist1bind.
Qed.

(* The allowed information is constant across inputs... *)
Lemma allow_const (x x' : 'I_2) : allow x = allow x'.
Proof. by []. Qed.

(* ...while the view laws differ, so the insecurity hypotheses hold... *)
Lemma view_law_differs : view_law ord0 <> view_law (lift ord0 ord0).
Proof.
move/(congr1 (fun d : R.-fdist 'I_2 => d ord0)).
rewrite fdist1xx (fdist10 _ (neq_lift _ _)).
by move/eqP; rewrite oner_eq0.
Qed.

(* ...and no ONE simulator satisfies the =1 definition. *)
Lemma no_single_simulator : ~ (exists S : simulator, perfect_privacy S).
Proof.
case=> S hS; apply: view_law_differs.
by rewrite (hS ord0) (hS (lift ord0 ord0)) /sim_view (allow_const _ ord0).
Qed.

End quantifier_order.
