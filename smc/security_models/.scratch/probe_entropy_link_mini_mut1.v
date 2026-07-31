(* MUTANT 1 of probe_entropy_link_mini.v.  The triangle is required at
   a single fixed input x0 instead of at every mass-carrying input.
   This file is EXPECTED TO FAIL to compile.                          *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist proba.
Require Import jfdist_cond entropy graphoid.
Require Import extra_proba extra_entropy.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section entropy_link_mini.
Context {R : realType}.
Variables X Omega Bv Al : finType.
Variable mu : R.-fdist X.
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.
Variable allow0 : X -> Al.
Variable Sim : Al -> R.-fdist Bv.
Variable x0 : X.

Definition d : R.-fdist (X * Omega)%type := (mu `x P_Omega)%fdist.

Definition view_rv : {RV d -> Bv} := view_at.
Definition input_rv : {RV d -> X} := fst.
Definition allow_rv : {RV d -> Al} := allow0 \o fst.

Hypothesis triangle :
  `Pr[ input_rv = x0 ] != 0 ->
  forall v : Bv, `Pr[ view_rv = v | input_rv = x0 ] = Sim (allow0 x0) v.

Lemma pfwd1_pair_det (U TA TB : finType) (P : R.-fdist U)
    (W : {RV P -> TA}) (Z : {RV P -> TB}) (g : TA -> TB) :
  (forall u, Z u = g (W u)) ->
  forall w z, `Pr[ [% W, Z] = (w, z) ] = (g w == z)%:R * `Pr[ W = w ].
Proof.
move=> Hg w z; rewrite !pfwd1E /Pr.
case: (eqVneq (g w) z) => [<-|H].
  rewrite mul1r; apply: eq_bigl => u.
  by rewrite !inE /= xpair_eqE Hg; case: eqP => [->|]; rewrite ?eqxx.
rewrite mul0r; apply: big_pred0 => u.
by rewrite !inE /= xpair_eqE Hg; case: eqP => [->|] //=; rewrite (negbTE H).
Qed.

Lemma pfwd1_view_input v x :
  `Pr[ [% view_rv, input_rv] = (v, x) ]
  = Sim (allow0 x) v * `Pr[ input_rv = x ].
Proof.
have [Hx|Hx] := eqVneq (`Pr[ input_rv = x ]) 0.
  by rewrite Hx mulr0 pfwd1_domin_RV1.
by have := triangle Hx v; rewrite cpr_eqE => <-; rewrite divfK.
Qed.

Lemma triangle_cinde : d |= view_rv _|_ input_rv | allow_rv.
Proof.
pose f (x : X) (a : Al) : R := (allow0 x == a)%:R * `Pr[ input_rv = x ].
pose g (a : Al) (v : Bv) : R := Sim a v.
apply: (cinde_RV_factor (f := f) (g := g)) => v x a.
rewrite (pfwd1_pair_det (g := fun p : Bv * X => allow0 p.2)) //.
rewrite /= pfwd1_view_input /f /g.
case: (eqVneq (allow0 x) a) => [->|H].
  by rewrite -mulrA [_ * Sim a v]mulrC mulrA.
by rewrite mulr0n !mul0r.
Qed.

Lemma cinde_centropy_eq :
  `H( input_rv | [% view_rv, allow_rv] ) = `H( input_rv | allow_rv ).
Proof. exact: extra_entropy.cinde_centropy_eq triangle_cinde. Qed.

End entropy_link_mini.
