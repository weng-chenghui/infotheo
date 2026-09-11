From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_proba entropy_fiber.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Conditional probability on a fiber of a uniform variable                   *)
(*                                                                            *)
(* A variable uniform on a finite type and independent of the honest inputs   *)
(* stays uniform on the fiber the observed condition cuts out.  That is the   *)
(* counting step behind the residual-entropy bounds of dsdp_entropy.v, and it *)
(* is what makes an observation leak nothing beyond the fiber it names.       *)
(*                                                                            *)
(* The variable type is an arbitrary finType, so the same lemmas serve the    *)
(* pair 'Z_(p * q) * 'Z_(p * q) and the N-party {ffun 'I_n -> 'Z_(p * q)}.    *)
(*                                                                            *)
(* ```                                                                        *)
(* gen_joint_factors_by_indeE == the joint law of the inputs and the          *)
(*                               variable is the product of their laws        *)
(*    gen_uniform_VarRV_probE == the variable takes each value with           *)
(*                               probability K^-1                             *)
(*  gen_Pr_cond_fiber_marginE == the condition has probability                *)
(*                               |fiber c| * K^-1 * Pr[InputRV = proj c]      *)
(*      gen_cPr_uniform_fiber == the variable given the condition is uniform  *)
(*                               on the fiber, with probability |fiber c|^-1  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Section fiber_entropy_gen.

Context {R : realType}.

Variable T : finType.
Variable P : R.-fdist T.

(* Generic variable type and its cardinality (K_pred.+1 ensures non-zero) *)
Variable VarT : finType.
Variable K_pred : nat.
Let K := K_pred.+1.
Variable card_var : #|VarT| = K.

(* Random variables *)
Variable VarRV : {RV P -> VarT}.
Variables (InputT : finType).
Variable InputRV : {RV P -> InputT}.
Variables (CondT : finType).
Variable CondRV : {RV P -> CondT}.

(* Fiber: the set of variable values satisfying the constraint *)
Variable fiber : CondT -> {set VarT}.

(* Projection from CondT to InputT *)
Variable proj_input : CondT -> InputT.

(* The constraint holds: VarRV t is always in the fiber of CondRV t *)
Hypothesis constraint_fiber : forall t, VarRV t \in fiber (CondRV t).

(* InputRV is the projection of CondRV *)
Hypothesis InputRV_proj : forall t, InputRV t = proj_input (CondRV t).

(* Assumptions: VarRV is uniform and independent of InputRV *)
Hypothesis VarRV_uniform : `p_ VarRV = fdist_uniform card_var.
Hypothesis VarRV_indep_inputs : P |= InputRV _|_ VarRV.

(* Joint probability factors by independence *)
Lemma gen_joint_factors_by_indeE (input : InputT) (var : VarT) :
  `Pr[[%VarRV, InputRV] = (var, input)] =
  `Pr[VarRV = var] * `Pr[InputRV = input].
Proof.
have Hinde_sym: P |= VarRV _|_ InputRV.
  by rewrite inde_RV_sym.
move: Hinde_sym.
rewrite /inde_RV.
move=> /(_ var input).
by [].
Qed.

(* Uniform VarRV gives probability K^-1 *)
Lemma gen_uniform_VarRV_probE (var : VarT) :
  `Pr[VarRV = var] = K%:R^-1 :> R.
Proof.
rewrite -dist_of_RVE VarRV_uniform fdist_uniformE.
by rewrite card_var.
Qed.

Section gen_marginal_probability.

Hypothesis joint_eq_input :
  forall (cond : CondT) (var : VarT),
    var \in fiber cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, proj_input cond)].

Lemma gen_Pr_cond_fiber_marginE (cond : CondT) :
  `Pr[InputRV = proj_input cond] != 0 ->
  `Pr[CondRV = cond] =
  #|fiber cond|%:R * K%:R^-1 * `Pr[InputRV = proj_input cond].
Proof.
move=> HInputRV_neq0.
have Hmargin: `Pr[CondRV = cond] =
  \sum_(vv : VarT) `Pr[[%VarRV, CondRV] = (vv, cond)].
  have ->: \sum_(vv : VarT) `Pr[[%VarRV, CondRV] = (vv, cond)] =
           \sum_(vv : VarT) `Pr[[%CondRV, VarRV] = (cond, vv)].
    apply eq_bigr => vv _.
    by rewrite pfwd1_pairC.
  by rewrite -(@PrX_fstRV _ _ _ _ P CondRV VarRV).
rewrite Hmargin.
rewrite (bigID (fun vv => vv \in fiber cond)) /=.
have Hzero: \sum_(vv | vv \notin fiber cond)
            `Pr[[%VarRV, CondRV] = (vv, cond)] = 0.
  rewrite big1 // => vv Hnotin.
  rewrite pfwd1_eq0 //.
  rewrite mem_undup.
  apply/mapP.
  move=> [t0 _ /= Heq].
  case: Heq => Hvar Hcond.
  move: (constraint_fiber t0).
  rewrite -Hcond -Hvar.
  move=> Hin_fiber.
  by move/negP: Hnotin; apply.
rewrite Hzero addr0.
transitivity (\sum_(vv in fiber cond)
              K%:R^-1 * `Pr[InputRV = proj_input cond]).
  apply eq_bigr => vv Hin.
  rewrite (joint_eq_input Hin).
  rewrite gen_joint_factors_by_indeE.
  rewrite gen_uniform_VarRV_probE.
  by [].
rewrite big_const iter_addr addr0.
by ring.
Qed.

End gen_marginal_probability.

Section gen_conditional_probability.

Hypothesis joint_eq_input :
  forall (cond : CondT) (var : VarT),
    var \in fiber cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, proj_input cond)].

Lemma gen_cPr_uniform_fiber (cond : CondT) (v : VarT) :
  `Pr[CondRV = cond] != 0 ->
  v \in fiber cond ->
  `Pr[VarRV = v | CondRV = cond] = #|fiber cond|%:R^-1.
Proof.
move=> HCond_neq0 Hin_fiber.
rewrite cpr_eqE.
have Hfiber_nempty: (0 < #|fiber cond|)%N.
  apply/card_gt0P.
  exists v.
  exact Hin_fiber.
have HInputRV_neq0: `Pr[InputRV = proj_input cond] != 0.
  move/pfwd1_neq0: HCond_neq0 => [t' [Ht'_cond Ht'_pos]].
  apply/pfwd1_neq0.
  exists t'.
  split => //.
  move: Ht'_cond.
  rewrite !inE.
  move/eqP => Hcond_eq.
  apply/eqP.
  rewrite InputRV_proj.
  by rewrite Hcond_eq.
have Hnum: `Pr[[%VarRV, CondRV] = (v, cond)] =
           K%:R^-1 * `Pr[InputRV = proj_input cond].
  rewrite (joint_eq_input Hin_fiber).
  rewrite gen_joint_factors_by_indeE.
  rewrite gen_uniform_VarRV_probE.
  by [].
have Hdenom: `Pr[CondRV = cond] =
             #|fiber cond|%:R * K%:R^-1 *
             `Pr[InputRV = proj_input cond].
  by apply gen_Pr_cond_fiber_marginE.
rewrite Hnum Hdenom.
field.
apply/and3P.
split.
- by rewrite pnatr_eq0 -lt0n.
- by rewrite pnatr_eq0 -lt0n.
- exact HInputRV_neq0.
Qed.

End gen_conditional_probability.

End fiber_entropy_gen.
