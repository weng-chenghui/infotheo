(* Probe P1 — claims S1-S6 / L1-L4 of the security_models design.
   Carrier pinned at the weakest structure the spec promises: an abstract
   R : realType and abstract finTypes.  A concrete instantiation section at
   the end is the vacuity probe for the kernel hypothesis set.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_finstoch_kernel.v            *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section stoch.
Context {R : realType}.

(* S1: stochastic maps, Dirac, composition, laws — via the fdist monad. *)
Definition stoch (A B : finType) := A -> R.-fdist B.

Definition dirac (A B : finType) (g : A -> B) : stoch A B :=
  fun a => fdist1 (g a).

Definition stoch_comp (A B C : finType)
    (g : stoch B C) (f : stoch A B) : stoch A C :=
  fun a => f a >>= g.

Lemma stoch_compA (A B C D : finType)
    (h : stoch C D) (g : stoch B C) (f : stoch A B) :
  stoch_comp h (stoch_comp g f) =1 stoch_comp (stoch_comp h g) f.
Proof. by move=> a; rewrite /stoch_comp fdistbindA. Qed.

Lemma stoch_comp_idl (A B : finType) (f : stoch A B) :
  stoch_comp (dirac id) f =1 f.
Proof. by move=> a; rewrite /stoch_comp /dirac fdistbind1. Qed.

Lemma stoch_comp_idr (A B : finType) (f : stoch A B) :
  stoch_comp f (dirac id) =1 f.
Proof. by move=> a; rewrite /stoch_comp /dirac fdist1bind. Qed.

(* prop:smc:transport-commutes *)
Lemma dirac_comp (A B C : finType) (g : B -> C) (f : A -> B) :
  dirac (g \o f) =1 stoch_comp (dirac g) (dirac f).
Proof. by move=> a; rewrite /stoch_comp /dirac fdist1bind. Qed.

(* Bridge to the infotheo idiom: deterministic post-composition is fdistmap. *)
Lemma stoch_comp_dirac_fdistmap (A B C : finType) (g : B -> C) (f : stoch A B) :
  stoch_comp (dirac g) f =1 fun a => fdistmap g (f a).
Proof. by move=> a; rewrite /stoch_comp /dirac /fdistmap. Qed.

(* Pointwise congruence of fdistmap in the transported map. *)
Lemma eq_fdistmap (A B : finType) (g h : A -> B) (p : R.-fdist A) :
  g =1 h -> fdistmap g p = fdistmap h p.
Proof.
move=> gh; apply/fdist_ext => b; rewrite !fdistmapE.
by apply: eq_bigl => a; rewrite !inE gh.
Qed.

(* Transport along a constant map is Dirac. *)
Lemma fdistmap_cst (A B : finType) (p : R.-fdist A) (b : B) :
  fdistmap (fun=> b) p = fdist1 b.
Proof.
apply/fdist_ext => b'; rewrite fdistmapE fdist1E.
rewrite (eq_bigl (fun a : A => (a \in A) && (b == b'))); last first.
  by move=> a; rewrite !inE.
case: (altP (b =P b')) => [<-|nb].
  by rewrite eqxx -(FDist.f1 p); apply: eq_bigl => a; rewrite andbT.
by rewrite eq_sym (negbTE nb) big_pred0// => a; rewrite andbF.
Qed.

Lemma fdistmap_cst_eq (A B : finType) (g : A -> B) (p : R.-fdist A) (b : B) :
  g =1 (fun=> b) -> fdistmap g p = fdist1 b.
Proof. by move=> gb; rewrite -(fdistmap_cst p b); apply: eq_fdistmap. Qed.

(* S2: tensor of two laws.  L4 is resolved in FINDING 1 below: `x is the
   binary product of two laws, notation for `X against a constant kernel. *)
Definition tensor (A B : finType) (p : R.-fdist A) (q : R.-fdist B)
  : R.-fdist (A * B)%type := (p `x q)%fdist.

Lemma tensorE (A B : finType) (p : R.-fdist A) (q : R.-fdist B) a b :
  tensor p q (a, b) = p a * q b.
Proof. by rewrite /tensor fdist_prodE. Qed.

(* A tensor with a Dirac left factor is a transport of the right factor. *)
Lemma tensor_fdist1 (A B : finType) (a : A) (q : R.-fdist B) :
  tensor (fdist1 a) q = fdistmap (fun b => (a, b)) q.
Proof.
apply/fdist_ext => -[a' b']; rewrite tensorE fdistmapE.
rewrite (eq_bigl (fun x : B => (x \in B) && ((a == a') && (x == b'))));
  last by move=> x; rewrite !inE /= xpair_eqE.
rewrite fdist1E; case: (altP (a =P a')) => [<-|na].
  rewrite eqxx mul1r (eq_bigl (fun i : B => i == b')); last first.
    by move=> i; rewrite inE.
  by rewrite big_pred1_eq.
by rewrite eq_sym (negbTE na) mul0r big_pred0// => i; rewrite (negbTE na).
Qed.

End stoch.

Section kernel.
(* The privacy-kernel section context, exactly as the design states it. *)
Context {R : realType}.
Variables X Yfull Y Xa Ya Bv Omega : finType.
Variable f : X -> Y.
Variable agg : Yfull -> Y.
Variable proj_xa : X -> Xa.
Variable proj_ya : Yfull -> Ya.
Variable F : X -> R.-fdist Yfull.
Hypothesis F_compat : forall x, fdistmap agg (F x) = fdist1 (f x).
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.
Variable run : X * Omega -> Yfull.
Hypothesis run_correct : forall e, agg (run e) = f e.1.

Definition draw (x : X) : R.-fdist (X * Omega)%type :=
  tensor (fdist1 x) P_Omega.

Definition view_law (x : X) : R.-fdist Bv := fdistmap view_at (draw x).

(* S3: the unpacking of def:smc:view-law. *)
Lemma view_lawE (x : X) :
  view_law x = fdistmap (fun w => view_at (x, w)) P_Omega.
Proof. by rewrite /view_law /draw tensor_fdist1 fdistmap_comp. Qed.

Definition f_a (x : X) : R.-fdist Ya := fdistmap proj_ya (F x).

Definition allow (x : X) : R.-fdist (Xa * Ya)%type :=
  fdistmap (fun xy : X * Yfull => (proj_xa xy.1, proj_ya xy.2))
           (tensor (fdist1 x) (F x)).

(* S4: the unpacking of def:smc:allowed-info. *)
Lemma allowE (x : X) : allow x = tensor (fdist1 (proj_xa x)) (f_a x).
Proof. by rewrite /allow /f_a !tensor_fdist1 !fdistmap_comp. Qed.

(* S5: prop:smc:worlds-compute-f, both routes. *)
Lemma real_route_f (x : X) :
  fdistmap (fun e => agg (run e)) (draw x) = fdist1 (f x).
Proof.
rewrite /draw tensor_fdist1 fdistmap_comp.
by apply: fdistmap_cst_eq => w /=; exact: run_correct.
Qed.

Lemma ideal_route_f (x : X) :
  fdistmap (fun xy : X * Yfull => agg xy.2) (tensor (fdist1 x) (F x))
  = fdist1 (f x).
Proof.
by rewrite tensor_fdist1 fdistmap_comp -F_compat; apply: eq_fdistmap.
Qed.

Definition simulator := (Xa * Ya)%type -> R.-fdist Bv.

Definition sim_view (S : simulator) (x : X) : R.-fdist Bv :=
  allow x >>= S.

Definition perfect_privacy (S : simulator) := view_law =1 sim_view S.

(* S6: prop:smc:insecurity. *)
Lemma insecurity (x x' : X) :
  allow x = allow x' -> view_law x != view_law x' ->
  ~ (exists S : simulator, perfect_privacy S).
Proof.
move=> ha /eqP hv [S hS]; apply: hv.
by rewrite (hS x) (hS x') /sim_view ha.
Qed.

End kernel.

(* Vacuity probe: the kernel hypothesis set is jointly satisfiable.  The
   identity protocol on a two-point space discharges every hypothesis. *)
Section vacuity.
Context {R : realType}.

Definition vac_F (x : 'I_2) : R.-fdist 'I_2 := fdist1 x.

Definition vac_P : R.-fdist 'I_1 := fdist1 ord0.

Definition vac_sim : @simulator R 'I_2 'I_2 'I_2 := fun p => fdist1 p.1.

Lemma vac_F_compat (x : 'I_2) : fdistmap id (vac_F x) = fdist1 (id x).
Proof. by rewrite /vac_F fdistmap_id. Qed.

Lemma vac_run_correct (e : 'I_2 * 'I_1) : id (fst e) = id e.1.
Proof. by []. Qed.

(* S5 at the instance: both hypotheses are consumed at concrete types. *)
Lemma vac_ideal_route (x : 'I_2) :
  fdistmap (fun xy : 'I_2 * 'I_2 => id xy.2) (tensor (fdist1 x) (vac_F x))
  = fdist1 (id x).
Proof. exact: (@ideal_route_f R _ _ _ id id vac_F vac_F_compat x). Qed.

Lemma vac_real_route (x : 'I_2) :
  fdistmap (fun e : 'I_2 * 'I_1 => id (fst e)) (draw vac_P x) = fdist1 (id x).
Proof.
exact: (@real_route_f R _ _ _ _ id id vac_P fst vac_run_correct x).
Qed.

(* S6 at the instance: the identity protocol is perfectly private. *)
Lemma vac_perfect_privacy :
  @perfect_privacy R 'I_2 'I_2 'I_2 'I_2 'I_2 'I_1 id id vac_F vac_P
    (@fst 'I_2 'I_1) vac_sim.
Proof.
move=> x; rewrite /view_law /draw /sim_view /allow /vac_sim /vac_F /vac_P.
by rewrite !tensor_fdist1 !fdistmap_comp !fdistmap1 fdist1bind.
Qed.

End vacuity.

(* PROBE FINDINGS (P1)
   1. L4 resolved.  `x is the binary product of two laws: fdist.v line 1071
      reads Notation "P1 `x P2" := (P1 `X (fun _ => P2)), so the kernel
      product `X is the primitive and `x is its constant-kernel instance.
      tensor keeps the stated definition and tensorE follows from
      fdist_prodE, whose shape is
        fdist_prodE ab : (P `X W) ab = P ab.1 * W ab.1 ab.2.
      No redefinition through fdistbind was needed.
   2. Three support lemmas were added to Section stoch, none of which changes
      a stated claim: eq_fdistmap (pointwise congruence of fdistmap in the
      transported map), fdistmap_cst (transport along a constant map is
      Dirac), fdistmap_cst_eq (its pointwise form), and tensor_fdist1 (a
      tensor with a Dirac left factor is a transport of the right factor).
      tensor_fdist1 is what all four kernel unfoldings run through.
   3. eq_fdistmap replaces functional extensionality: real_route_f and
      ideal_route_f need only pointwise agreement of the transported map, so
      neither proof appeals to boolp.funext.
   4. The vacuity instance is X = Yfull = Y = Xa = Ya = Bv = 'I_2,
      Omega = 'I_1, f = agg = proj_xa = proj_ya = id, F x = fdist1 x,
      P_Omega = fdist1 ord0, view_at = run = fst.  It discharges F_compat and
      run_correct, instantiates ideal_route_f and real_route_f at those
      proofs, and establishes perfect_privacy for S = fun p => fdist1 p.1.
   5. Assumption audit: stoch_compA, tensorE, view_lawE, allowE,
      real_route_f, ideal_route_f, insecurity and the three vacuity lemmas
      each report the three boolp axioms (propositional_extensionality,
      functional_extensionality_dep, constructive_indefinite_description).
      That set is the library baseline of any statement quantified over
      R : realType; x <= x for x : R already reports it.  No axiom beyond the
      baseline, and no Admitted.                                            *)

(* MUTATION CHECKS — each copy fails to compile; observed error one-liners:
   1. probe_finstoch_kernel_mut1.v — run_correct weakened to the tautology
      forall e, agg (run e) = agg (run e):
        line 145: Error: Cannot apply lemma run_correct
   2. probe_finstoch_kernel_mut2.v — proj_xa/proj_ya swapped in allowE:
        line 137: Error: The term "x" has type "Finite.sort X" while it is
        expected to have type "Finite.sort Yfull".
   3. probe_finstoch_kernel_mut3.v — dirac (g \o f) misordered to
      dirac (f \o g):
        line 48: Error: The term "g" has type "B -> C" while it is expected
        to have type "B -> A" (cannot unify "Finite.sort C" and
        "Finite.sort A").                                                   *)
