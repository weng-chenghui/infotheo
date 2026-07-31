(* SOUNDNESS AUDIT — tautology probes for the content-carrying equalities
   of the design spec (smc/notes/20260731-security-models-formalization-
   design.md §3): tensorE, view_lawE, allowE, statdist_test_max,
   biased_uniform_eps.  Each Goal restates the equality verbatim (with
   definitions copied from the compiled probes) and checks with Fail that
   neither [by []] nor [reflexivity] closes it: the equalities are not
   definitional trivialities, so the lemmas carry proof content.  A Fail
   that itself fails (i.e. the tactic succeeds) would make this file
   fail to compile — compilation of this file IS the audit evidence.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_snd_tautology.v             *)

From mathcomp Require Import all_ssreflect all_algebra finalg reals lra.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section taut_tensor.
Context {R : realType}.
Variables A B : finType.

Definition tensor (p : R.-fdist A) (q : R.-fdist B)
  : R.-fdist (A * B)%type := (p `x q)%fdist.

(* tensorE (spec: def:smc:tensor read-off). *)
Goal forall (p : R.-fdist A) (q : R.-fdist B) a b,
  tensor p q (a, b) = p a * q b.
Proof.
move=> p q a b.
Fail by [].
Fail reflexivity.
Abort.

End taut_tensor.

Section taut_kernel.
Context {R : realType}.
Variables X Yfull Xa Ya Bv Omega : finType.
Variable proj_xa : X -> Xa.
Variable proj_ya : Yfull -> Ya.
Variable F : X -> R.-fdist Yfull.
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.

Definition draw (x : X) : R.-fdist (X * Omega)%type :=
  ((fdist1 x) `x P_Omega)%fdist.
Definition view_law (x : X) : R.-fdist Bv := fdistmap view_at (draw x).
Definition f_a (x : X) : R.-fdist Ya := fdistmap proj_ya (F x).
Definition allow (x : X) : R.-fdist (Xa * Ya)%type :=
  fdistmap (fun xy : X * Yfull => (proj_xa xy.1, proj_ya xy.2))
           ((fdist1 x) `x (F x))%fdist.

(* view_lawE (spec: def:smc:view-law unpacking). *)
Goal forall x, view_law x = fdistmap (fun w => view_at (x, w)) P_Omega.
Proof.
move=> x.
Fail by [].
Fail reflexivity.
Abort.

(* allowE (spec: def:smc:allowed-info unpacking). *)
Goal forall x, allow x = ((fdist1 (proj_xa x)) `x (f_a x))%fdist.
Proof.
move=> x.
Fail by [].
Fail reflexivity.
Abort.

End taut_kernel.

Section taut_statdist.
Context {R : realType} {B : finType}.

Definition statdist (p q : R.-fdist B) : R := 2%:R^-1 * \sum_b `|p b - q b|.
Definition tester := {ffun B -> bool}.
Definition accept (D : tester) (p : R.-fdist B) : R := Pr p [set b | D b].
Definition adv (D : tester) (p q : R.-fdist B) : R :=
  `|accept D p - accept D q|.

(* statdist_test_max (spec: prop:smc:max-advantage). *)
Goal forall p q : R.-fdist B,
  \big[Num.max/0]_(D : tester) adv D p q = statdist p q.
Proof.
move=> p q.
Fail by [].
Fail reflexivity.
Abort.

End taut_statdist.

Section taut_f3.
Context {R : realType}.
Let F3 : finType := 'F_3.

Lemma card_F3 : #|F3| = 3.
Proof. by rewrite card_ord. Qed.

Definition unif3 : R.-fdist F3 := fdist_uniform card_F3.
Definition biased3 : R.-fdist F3 :=
  (fdist1 0 <| (2^-1 : R)%:pr |>
     (fdist1 1 <| (2^-1 : R)%:pr |> fdist1 (1 + 1)))%fdist.
Definition statdist3 (p q : R.-fdist F3) : R :=
  2%:R^-1 * \sum_b `|p b - q b|.

(* biased_uniform_eps (spec: tab:smc:privacy-laws toy, eps = 6^-1). *)
Goal statdist3 biased3 unif3 = 6%:R^-1.
Proof.
Fail by [].
Fail reflexivity.
Abort.

End taut_f3.
