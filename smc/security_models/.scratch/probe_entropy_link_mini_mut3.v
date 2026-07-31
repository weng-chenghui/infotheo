(* MUTANT 3 of probe_entropy_link_mini.v.  This file COMPILES: it is the
   two-point instance refuting mutation 1.  Over the uniform prior on
   bool with a trivial ancilla, the view equal to the input and the
   allowed information constant, the triangle holds at the single input
   true against the Dirac simulator at true, and conditional
   independence of the view and the input given the allowed information
   is false.                                                          *)

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

Section counter_single_input.
Context {R : realType}.

Definition mu0 : R.-fdist bool := fdist_uniform card_bool.
Definition d0 : R.-fdist (bool * unit)%type := (mu0 `x (fdist1 tt))%fdist.
Definition view0 : {RV d0 -> bool} := fst.
Definition input0 : {RV d0 -> bool} := fst.
Definition allow0c : {RV d0 -> unit} := (fun=> tt) \o fst.
Definition Sim0 : unit -> R.-fdist bool := fun=> fdist1 true.

(* Both marginals of the input are one half. *)
Lemma pr_input0 (b : bool) : `Pr[ input0 = b ] = 2^-1.
Proof.
rewrite -dist_of_RVE /dist_of_RV /input0 -/(fdist_fst d0) /d0.
by rewrite fdist_prod1 /mu0 fdist_uniformE card_bool.
Qed.

(* The joint law of an RV and a deterministic function of it is the law
   of the RV cut down to the fibre of that function. *)
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

(* The mutation-1 hypothesis holds at the input true. *)
Lemma counter_triangle_single :
  `Pr[ input0 = true ] != 0 ->
  forall v : bool, `Pr[ view0 = v | input0 = true ] = Sim0 tt v.
Proof.
move=> _ v.
rewrite cpr_eqE (pfwd1_pair_det (g := id)) // /view0 -/input0 !pr_input0.
have H20 : (2 : R)^-1 != 0 by rewrite invr_eq0 pnatr_eq0.
by rewrite mulfK // /Sim0 fdist1E eq_sym.
Qed.

(* The mutation-1 conclusion fails at the same instance. *)
Lemma counter_single_input : ~ (d0 |= view0 _|_ input0 | allow0c).
Proof.
have -> : allow0c = unit_RV d0 by [].
move/cinde_RV_unit => H.
have := H true true.
rewrite /view0 /input0 pfwd1_diag -/input0 !pr_input0.
rewrite -{1}[2^-1]mulr1 => /mulfI H3.
have H20 : (2 : R)^-1 != 0 by rewrite invr_eq0 pnatr_eq0.
by move: (H3 H20) => /eqP; rewrite eq_sym invr_eq1 pnatr_eq1.
Qed.

End counter_single_input.
