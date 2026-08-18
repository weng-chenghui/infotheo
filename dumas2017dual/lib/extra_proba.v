From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import fdist_extra extra_algebra.

Import GRing.Theory.
Import Num.Theory.
Import Order.POrderTheory.

(******************************************************************************)
(*                                                                            *)
(* General probability lemmas used in dumas2017dual formalization             *)
(*                                                                            *)
(* This file contains probability lemmas that are more general than           *)
(* DSDP-specific:                                                             *)
(*   - Conditional probability lemmas                                          *)
(*   - Random variable permutation lemmas                                      *)
(*   - Joint distribution lemmas                                               *)
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

(* ========================================================================== *)
(*                    Conditional probability lemmas                           *)
(* ========================================================================== *)

Section proba_extra.

Context {R : realType}.

(* If a is not in the image of X, then (a, b) cannot be in the joint image.
   This is used to show that pairs outside the support have zero probability. *)
Lemma pair_notin_fin_img_fst (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (a : A) (b : B) :
  a \notin fin_img X -> (a, b) \notin fin_img [% X, Y].
Proof.
move=> a_notin_img.
apply/memPn => p Hp.
move: Hp.
rewrite /fin_img mem_undup.
move/mapP => [] t Ht ->.
rewrite xpair_eqE.
apply/nandP; left.
apply/eqP => Xt_eq_a.
move: a_notin_img.
rewrite mem_undup => /negP.
apply;apply/mapP.
exists t.
  exact: Ht.
symmetry.
exact: Xt_eq_a.
Qed.

(* Conditional probabilities sum to 1: Σ_a Pr[X = a | Y = y] = 1.
   This is the law of total probability for conditional distributions,
   essential for showing that conditional distributions are valid fdists. *)
Lemma sum_cPr_eq 
  (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (y : B) :
  `Pr[Y = y] != 0 ->
  \sum_(a in A) `Pr[X = a | Y = y] = 1.
Proof.
move=> Hy_neq0.
rewrite (bigID (mem (fin_img X))) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> a a_notin_img.
  rewrite cpr_eqE.
  have ->: `Pr[[% X, Y] = (a, y)] = 0.
    apply/eqP; rewrite pfwd1_eq0; apply/eqP.
      by [].
    apply/eqP.
    apply: pair_notin_fin_img_fst.
    exact: a_notin_img.
  by rewrite mul0r.
rewrite [X in _ + X]big1 ?addr0; last by move=> i _.  
rewrite -big_uniq /=.
  apply: cPr_1.
  exact: Hy_neq0.
apply: undup_uniq.
Qed.

(* Helper lemma: if z is not in the image of Z, then conditional probability is 0 *)
Lemma cPr_eq_notin_fin_img (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) (y : V) (z : W) :
  z \notin fin_img Z -> `Pr[Z = z | Y = y] = 0.
Proof.
move=> z_notin.
rewrite cpr_eqE !pfwd1E /Pr big1 ?mul0r //.
move=> t; rewrite inE => /eqP Zt.
exfalso; move/negP: z_notin; apply.
rewrite mem_undup; apply/mapP; exists t => //.
  by rewrite mem_enum.
by move: Zt => [->].
Qed.

(* Helper: If two different values both have conditional probability 1, contradiction *)
Lemma cPr_eq_two_ones_absurd (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) (y : V) (z z' : W) :
  `Pr[Y = y] != 0 ->
  z != z' ->
  `Pr[Z = z | Y = y] = 1 ->
  `Pr[Z = z' | Y = y] = 1 ->
  False.
Proof.
move=> Hy_neq0 Hneq Hz Hz'.
(* All conditional probabilities sum to 1 *)
have H_sum: \sum_(w <- fin_img Z) `Pr[Z = w | Y = y] = 1
  by exact: (cPr_1 Z Hy_neq0).
(* Both z and z' must be in fin_img Z *)
have z_in: z \in fin_img Z by
  apply/negPn/negP => z_notin; move: (cPr_eq_notin_fin_img Y y z_notin); rewrite Hz; lra.
have z'_in: z' \in fin_img Z by
  apply/negPn/negP => z'_notin; move: (cPr_eq_notin_fin_img Y y z'_notin); rewrite Hz'; lra.
(* Extract z from sum: 1 = 1 + rest *)
move: H_sum; rewrite (bigD1_seq z) ?undup_uniq //= Hz => H_sum.
(* So rest = 0 *)
have H_rest: \sum_(w <- fin_img Z | w != z) `Pr[Z = w | Y = y] = 0 by lra.
(* But z' is in rest with value 1 *)
move: H_rest.
rewrite (@bigD1_seq_cond _ _ _ _ (fin_img Z) z' (fun w => w != z) (fun w => `Pr[Z = w | Y = y])) ?undup_uniq //=; last first.
  - by rewrite eq_sym.
rewrite Hz'.
have: 0 <= \sum_(i <- fin_img Z | (i != z) && (i != z')) `Pr[ Z = i | Y = y ].
  by apply: sumr_ge0 => w _; rewrite cPr_eq_def; exact: cPr_ge0.
by lra.
Qed.

(* Conditional fdist equals conditional probability *)
Lemma jfdist_cond_cPr_eq  {T TX TY : finType} (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY}) (x : TX) (y : TY) :
  `Pr[X = x] != 0 ->
  `p_[% X, Y]`(|x) y = `Pr[Y = y | X = x].
Proof.
Proof.
move=> Hx_pos.
rewrite jfdist_condE; last first.
  by rewrite fst_RV2 dist_of_RVE.
rewrite cpr_eqE.
rewrite /jcPr.
congr (_ / _).
- rewrite Pr_fdistX.
  rewrite setX1.
  rewrite Pr_set1 dist_of_RVE.
  by rewrite pfwd1_pairC.
- rewrite fdistX2 fst_RV2.
  by rewrite Pr_set1 dist_of_RVE.
Qed.

(* If Y must satisfy a property determined by X,
   then conditional probability is zero outside that property *)
Lemma cond_prob_zero_outside_constraint 
  {T TX TY : finType} (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY})
  (constraint : TX -> TY -> bool) :
  (* The constraint must hold almost surely *)
  (forall t, constraint (X t) (Y t)) ->
  (* Then conditional probability is zero outside the constraint *)
  forall x y,
    `Pr[X = x] != 0 ->
    ~~ constraint x y ->
    `Pr[Y = y | X = x] = 0.
Proof.
move=> Hconstraint x y Hx_pos Hnot_constraint.
rewrite cpr_eqE.
have Hempty: finset ([%Y, X] @^-1 (y, x)) = set0.
  apply/setP => t.
  rewrite in_set0 inE /preim /pred1 /= xpair_eqE.
  apply: contraTF Hnot_constraint => /andP[/eqP HY /eqP HX].
  by rewrite -HY -HX Hconstraint.
have ->: `Pr[[%Y, X] = (y, x)] = 0.
  by rewrite pfwd1E Hempty Pr_set0.
by rewrite mul0r.
Qed.

(* Marginalization: summing joint probabilities over Y yields marginal of X.
   Σ_y Pr[(X,Y) = (x,y)] = Pr[X = x]. Fundamental for deriving marginals. *)
Lemma PrX_fstRV  (A B T : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (x : A) :
  \sum_(y : B) `Pr[[% X, Y] = (x, y)] = `Pr[X = x].
Proof.
have ->: `Pr[X = x] = Pr (`p_X) [set x].
  by rewrite -pr_in1 Pr_set1 dist_of_RVE pr_in1.
have ->: Pr (`p_X) [set x] = Pr (`p_[% X, Y])`1 [set x].
  by rewrite fst_RV2.
have ->: Pr (`p_[% X, Y])`1 [set x] = 
         \sum_(y : B) Pr (`p_[% X, Y]) (setX [set x] [set y]).
  by rewrite -PrX_fst.
apply: eq_bigr => y _.
have ->: Pr (`p_[% X, Y]) (setX [set x] [set y]) = 
         Pr (`p_[% X, Y]) [set (x, y)].
  congr (Pr (`p_[% X, Y]) _).
  by apply/setP => -[a b]; rewrite !inE xpair_eqE.
have ->: Pr (`p_[% X, Y]) [set (x, y)] = (`p_[% X, Y]) (x, y).
   by rewrite Pr_set1.
by rewrite dist_of_RVE.
Qed.

(* Joint probability product rule: Pr[(X,Y) = (x,y)] = Pr[Y=y] * Pr[X=x|Y=y].
   This is Bayes' theorem in product form, fundamental for decomposing
   joint distributions into marginal × conditional. *)
Lemma jproduct_ruleRV (A B T : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (x : A) (y : B) :
  `Pr[[% X, Y] = (x, y)] = `Pr[Y = y] * `Pr[X = x | Y = y].
Proof.
have ->: `Pr[[% X, Y] = (x, y)] = Pr (`p_[% X, Y]) [set (x, y)].
  by rewrite -pr_in1 Pr_set1 dist_of_RVE pr_in1.
have ->: [set (x, y)] = setX [set x] [set y].
  by apply/setP => -[a b]; rewrite !inE xpair_eqE.
rewrite jproduct_rule.
rewrite mulrC; congr (_ * _).
  by rewrite snd_RV2 Pr_set1 dist_of_RVE.
by rewrite -cpr_in1 -jPr_Pr.
Qed.

End proba_extra.

(* ========================================================================== *)
(*                  Random variable permutation lemmas                         *)
(* ========================================================================== *)

Section perm_extra.

Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).

(* Swap 3rd and 4th components in 4-tuple probability:
   Pr[(X,Y,Z,W)=(a,b,c,d)] = Pr[(X,Y,W,Z)=(a,b,d,c)].
   Used for reordering conditioning variables. *)
Lemma pfwd1_pair4_swap34 (TA TB TC TD : finType) 
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, Y, W, Z] = (a, b, d, c) ].
Proof.
rewrite !pfwd1E; apply eq_bigl => u.
by rewrite !inE /= !xpair_eqE; do ! case: (_ == _) => //=.
Qed.

(* Swap components in nested triple: (a,(b,c,d)) ↔ (a,(b,d,c)).
   Relates different nestings of tuple probabilities. *)
Lemma pfwd1_nested3_AC (TA TB TC TD : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, [% Y, Z, W]] = (a, (b, c, d)) ] = 
  `Pr[ [% X, [% Y, W, Z]] = (a, (b, d, c)) ].
Proof.
rewrite !pfwd1_pairA !pfwd1E.
congr Pr.
apply/setP => u.
by rewrite !inE /= !xpair_eqE [in LHS]andbA [in RHS]andbA andbAC.
Qed.

(* Associativity for 4-tuple: (a,b,c,d) ↔ (a,(b,c),d).
   Shows that flat 4-tuples equal nested representations. *)
Lemma pfwd1_pair4_mid_A (TA TB TC TD : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, [% Y, Z], W] = (a, (b, c), d) ].
Proof.
rewrite !pfwd1E.
congr Pr; apply/setP => u.
by rewrite !inE /= !xpair_eqE andbA.
Qed.

(* Conditional entropy is invariant under swapping last two conditioning vars:
   H(X | Y,Z,W) = H(X | Y,W,Z). Commutativity for conditioning tuple tail. *)
Lemma centropyAC
    (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B}) 
    (Z : {RV P -> C}) (W : {RV P -> D}) :
  `H(X | [% Y, Z, W]) = `H(X | [% Y, W, Z]).
Proof.
rewrite /centropy_RV /centropy /=.
rewrite (reindex (fun '(a, b, c) => (a, c, b)))/=.
  apply: eq_bigr => -[[b c] d] _ /=.
  rewrite !snd_RV2 !dist_of_RVE pfwd1_pairAC.
  congr *%R.
  rewrite /centropy1; congr (- _).
  rewrite /jcPr !snd_RV2.
  apply: eq_bigr => a _.
  by rewrite !setX1 !Pr_set1 !dist_of_RVE pfwd1_nested3_AC pfwd1_pairAC.
- exists (fun '(a, b, c) => (a, c, b)) => -[[? ?] ?] //=.
Qed.

(* Associativity for conditional entropy: H(X | (Y,(Z,W))) = H(X | Y,Z,W).
   Flattens nested conditioning tuples. *)
Lemma centropyA
    (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B}) 
    (Z : {RV P -> C}) (W : {RV P -> D}) :
  `H(X | [% Y, [% Z, W]]) = `H(X | [% Y, Z, W]).
Proof.
rewrite /centropy_RV /centropy !snd_RV2.
rewrite (reindex (fun '(b, (c, d)) => ((b, c), d)))/=.
  apply: eq_bigr => [[b [c d]] H].
  rewrite !dist_of_RVE.
  rewrite pfwd1_pairA.
  congr (_ * _).
  rewrite /centropy1; congr (- _).
  rewrite /jcPr.
  apply: eq_bigr => a _.
  rewrite !snd_RV2.
  rewrite !setX1 !Pr_set1 !dist_of_RVE !pfwd1_pairA.
  congr (_ * _).
    congr (_ / _).
    by rewrite pfwd1_pair4_mid_A.
  congr (_ * _).
  congr exp.ln.
    by rewrite pfwd1_pair4_mid_A.
exists (fun '(b, c, d) => (b, (c, d))).
by move => [b [c d]].
by move => [[b c] d].
Qed.

(* Flatten nested pair in middle position: H(X | W,(V,Z),Y) = H(X | W,V,Z,Y).
   Associativity when the nested pair is in the middle of the conditioning. *)
Lemma centropyA_middle
    {A B C D E : finType} 
    (X : {RV P -> A}) (W : {RV P -> B}) 
    (V : {RV P -> C}) (Z : {RV P -> D}) (Y : {RV P -> E}) :
  `H(X | [% W, [% V, Z], Y]) = `H(X | [% W, V, Z, Y]).
Proof.
rewrite /centropy_RV /centropy //=.
rewrite (reindex (fun '((b, (c, e)), d) => ((b, c), e, d))) //=.
  apply: eq_bigr => [] [] [] b [] c d e _ //=.
  congr (_ * _).
  by rewrite !snd_RV2 !dist_of_RVE pfwd1_pair4_mid_A.
rewrite /centropy1; congr (- _).
rewrite /jcPr; apply: eq_bigr => a _.
rewrite !setX1 !Pr_set1 !snd_RV2 !dist_of_RVE !pfwd1_pairA.
congr (_ * _).
   congr (_ / _); last by rewrite -!pfwd1_pair4_mid_A.
   - rewrite -!pfwd1_pair4_mid_A !pfwd1E.
     congr Pr; apply/setP => u.
     by rewrite !inE /= !xpair_eqE [in RHS]andbA.
   congr (_ * _).
   congr exp.ln.
   congr (_ / _); last by rewrite -!pfwd1_pair4_mid_A.
     rewrite -!pfwd1_pair4_mid_A !pfwd1E.
     congr Pr; apply/setP => u.
     by rewrite !inE /= !xpair_eqE [in RHS]andbA.
exists (fun '(b, c, d, e) => (b, (c, d), e)).
by move => [[] b [] c d e].
by move => [[] [] b] c d e.
Qed.

(* Swap 2nd and 4th positions in 4-variable conditioning:
   H(X | W,Y,Z,V) = H(X | W,V,Z,Y). Used for reordering Alice's view components. *)
Lemma centropy4_swap_2_4
    (A B C D E : finType)
    (X : {RV P -> A}) (W : {RV P -> B}) (Y : {RV P -> C}) 
    (Z : {RV P -> D}) (V : {RV P -> E}) :
  `H(X | [% W, Y, Z, V]) = `H(X | [% W, V, Z, Y]).
Proof.
rewrite centropyAC.
rewrite centropyC.
rewrite centropyC.
rewrite centropyC.
rewrite centropyC.
rewrite -centropyA.
rewrite centropyAC.
rewrite -centropyA.
rewrite centropyA.
by rewrite centropyA_middle.
Qed.

(* Marginal equivalence under swap: the 2nd marginal of (Z,Y) equals
   the 1st marginal of (Y,Z). Both give the distribution of Y. *)
Lemma marginal_swap_YZ
  (V W : finType)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  forall y : V, (`p_[% Z, Y])`2 y = (`p_[% Y, Z])`1 y.
Proof.
move=> y.
by rewrite -fdistX_RV2 fdistX2.
Qed.

End perm_extra.

Section cinde_RV_comp_lemma.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Variable f : A -> C -> D.

Let W : {RV P -> D} := (fun ac => f ac.1 ac.2) `o [% X, Z].

(* Joint law of the composed variable [W = f(X, Z)] with [X] and [Z]: at
   [(dd, a, cc)] it is the indicator [f a cc == dd] times the law of [%X, Z] at
   [(a, cc)], since [X = a] and [Z = cc] force [W = f a cc]. *)
Lemma pr_eq_comp_constraint (dd : D) (cc : C) (a : A) :
  `Pr[ [% W, X, Z] = (dd, a, cc) ] =
  (f a cc == dd)%:R * `Pr[ [% X, Z] = (a, cc) ].
Proof.
have -> : [% W, X, Z]
  = (fun p : A * C => (f p.1 p.2, p.1, p.2)) `o [% X, Z] by [].
rewrite -pr_in1 pr_in_comp' -pr_in1.
case: (eqVneq (f a cc) dd) => [Hf|Hf].
- rewrite mul1r; congr (pr_in _ _).
  apply/setP => p; rewrite !inE.
  case: p => p1 p2; rewrite !xpair_eqE /=.
  case: (eqVneq p1 a) => [->|?]; last by rewrite !andbF.
  case: (eqVneq p2 cc) => [->|?]; last by rewrite andbF.
  by rewrite Hf !eqxx.
- rewrite mul0r.
  have -> : (fun p : A * C => (f p.1 p.2, p.1, p.2))
              @^-1: [set (dd, a, cc)] = set0.
    apply/setP => p; rewrite !inE.
    case: p => p1 p2; rewrite !xpair_eqE /=.
    apply/negbTE; apply: contra Hf.
    by move=> /andP[/andP[H1 /eqP H2] /eqP H3]; rewrite -H2 -H3.
  by rewrite pr_inE preimset0 Pr_set0.
Qed.

(* [pr_eq_comp_constraint] with an extra spectator variable [T] carried through
   the joint law. *)
Lemma pr_eq_comp_constraint_tail (E : finType) (T : {RV P -> E})
    (dd : D) (e : E) (a : A) (cc : C) :
  `Pr[ [% W, T, X, Z] = (dd, e, a, cc) ] =
  (f a cc == dd)%:R * `Pr[ [% T, X, Z] = (e, a, cc) ].
Proof.
have -> : [% W, T, X, Z]
  = (fun q : E * A * C => (f q.1.2 q.2, q.1.1, q.1.2, q.2)) `o [% T, X, Z]
    by [].
rewrite -pr_in1 pr_in_comp' -pr_in1.
case: (eqVneq (f a cc) dd) => [Hf|Hf].
- rewrite mul1r; congr (pr_in _ _).
  apply/setP => q; rewrite !inE.
  case: q => [[q1 q2] q3]; rewrite !xpair_eqE /=.
  case: (eqVneq q2 a) => [->|?]; last by rewrite !andbF.
  case: (eqVneq q3 cc) => [->|?]; last by rewrite !andbF.
  by rewrite Hf !eqxx.
- rewrite mul0r.
  have -> : (fun q : E * A * C => (f q.1.2 q.2, q.1.1, q.1.2, q.2))
              @^-1: [set (dd, e, a, cc)] = set0.
    apply/setP => q; rewrite !inE.
    case: q => [[q1 q2] q3]; rewrite !xpair_eqE /=.
    apply/negbTE; apply: contra Hf.
    by move=> /andP[/andP[/andP[H1 _] /eqP H2] /eqP H3]; rewrite -H2 -H3.
  by rewrite pr_inE preimset0 Pr_set0.
Qed.

(* Conditional independence is preserved by composing a deterministic function
   of the conditioned variable and the conditioning variable: [X _|_ Y | Z]
   entails [f(X, Z) _|_ Y | Z].  The conditional analogue of [inde_RV_comp]. *)
Lemma cinde_RV_comp :
  P |= X _|_ Y | Z -> P |= ((fun ac => f ac.1 ac.2) `o [% X, Z]) _|_ Y | Z.
Proof.
move=> H d b c; rewrite -/W.
have wfib : `Pr[ W = d | Z = c] =
    \sum_(a <- fin_img X | f a c == d) `Pr[ X = a | Z = c].
  rewrite -cpr_in1 (creasoning_by_cases _ X) [RHS]big_mkcond /=.
  apply: eq_bigr => a _.
  rewrite setX1 cpr_in1 cpr_eqE pr_eq_comp_constraint -mulrA -cpr_eqE.
  by case: (f a c == d); rewrite ?mul1r ?mul0r.
have jfib : cPr_eq [% W, Y] (d, b) Z c =
    \sum_(a <- fin_img X | f a c == d) `Pr[ [% Y, X] = (b, a) | Z = c].
  rewrite -cpr_in1 (creasoning_by_cases _ X) [RHS]big_mkcond /=.
  apply: eq_bigr => a _.
  rewrite setX1 cpr_in1 cpr_eqE pr_eq_comp_constraint_tail -mulrA -cpr_eqE.
  by case: (f a c == d); rewrite ?mul1r ?mul0r.
rewrite jfib wfib big_distrl /=.
apply: eq_bigr => a _.
by rewrite cpr_eq_pairC (H a b c).
Qed.

End cinde_RV_comp_lemma.

Section inde_const_RV_sec.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B : finType).

(* A constant random variable is independent of every random variable. *)
Lemma inde_const_RV (c : A) (W : {RV P -> B}) : P |= const_RV P c _|_ W.
Proof.
move=> a b.
rewrite !pfwd1E.
case: (eqVneq a c) => [->|ana].
- rewrite [X in _ = X * _](_ : _ = 1); last first.
    rewrite (_ : finset _ = setT) ?Pr_setT//.
    by apply/setP => t; rewrite !inE /= const_RVE eqxx.
  rewrite mul1r; congr (Pr P _).
  by apply/setP => t; rewrite !inE /= const_RVE xpair_eqE eqxx.
- rewrite [X in _ = X * _](_ : _ = 0); last first.
    rewrite (_ : finset _ = set0) ?Pr_set0//.
    apply/setP => t; rewrite !inE /= const_RVE.
    by apply/negbTE; rewrite eq_sym.
  rewrite mul0r.
  rewrite (_ : finset _ = set0) ?Pr_set0//.
  apply/setP => t; rewrite !inE /= const_RVE xpair_eqE.
  by rewrite eq_sym (negbTE ana).
Qed.

End inde_const_RV_sec.

Section cinde_diagonal_bound_sec.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A C : finType).
Variables (X Y : {RV P -> A}) (Z : {RV P -> C}).

(* The second-coordinate marginal of a pair law recovers the first marginal:
   summing [%W, Z] over Z gives W. *)
Lemma marg_snd {B : finType} (W : {RV P -> B}) (w : B) :
  \sum_(c : C) `Pr[ [% W, Z] = (w, c) ] = `Pr[ W = w ].
Proof.
under eq_bigr => c _ do rewrite pfwd1E /Pr.
rewrite pfwd1E /Pr (partition_big Z xpredT) //=.
apply: eq_bigr => c _; apply: eq_bigl => t.
by rewrite !inE /= !xpair_eqE andbC.
Qed.

(* The probability that X and Y agree is the diagonal sum of their joint law. *)
Lemma Pr_diag_sum :
  Pr P [set t | X t == Y t] = \sum_(a : A) `Pr[ [% X, Y] = (a, a) ].
Proof.
under eq_bigr => a _ do rewrite pfwd1E /Pr.
rewrite /Pr (partition_big X xpredT) //=.
apply: eq_bigr => a _; apply: eq_bigl => t.
rewrite !inE /= !xpair_eqE.
by case: (X t =P a) => [->|]; rewrite ?andbF ?andbT // eq_sym andbb.
Qed.

Variable m : nat.
Hypothesis Hcinde : P |= X _|_ Y | Z.
Hypothesis HYbound : forall (a : A) (c : C), `Pr[ Y = a | Z = c ] <= m%:R^-1.

(* When X and Y are conditionally independent given Z and Y is, conditionally on
   each Z value, spread over at least m outcomes ([`Pr[ Y = a | Z = c ] <= 1/m]),
   the probability that X equals Y is at most 1/m: the predictor X cannot match
   the conditionally-uniform Y better than guessing within each Z-fiber. *)
Lemma cinde_diagonal_bound : Pr P [set t | X t == Y t] <= m%:R^-1.
Proof.
have cge0 : forall (a : A) (c : C), 0 <= `Pr[ X = a | Z = c ].
  move=> a c; rewrite cpr_eqE; apply: mulr_ge0; first exact: pfwd1_ge0.
  by rewrite invr_ge0; exact: pfwd1_ge0.
rewrite Pr_diag_sum.
under eq_bigr => a _ do rewrite -(marg_snd [%X,Y] (a,a)).
rewrite exchange_big /=.
apply: (@le_trans _ _ (\sum_(c : C) m%:R^-1 * `Pr[ Z = c ])); last first.
  by rewrite -big_distrr /= sum_pfwd1 mulr1; apply: lexx.
apply: ler_sum => c _.
have [Hc0|Hc0] := eqVneq (`Pr[ Z = c ]) 0.
- rewrite Hc0 mulr0 big1 // => a _.
  exact: (pfwd1_domin_RV1 [% X, Y] (a, a) Hc0).
- have key : forall a : A,
    `Pr[ [% [% X, Y], Z] = ((a, a), c) ]
      = `Pr[ X = a | Z = c ] * `Pr[ Y = a | Z = c ] * `Pr[ Z = c ].
    by move=> a; rewrite -(Hcinde a a c) cpr_eqE -mulrA mulVf // mulr1.
  have lhs_eq : \sum_(a : A) `Pr[ [% [% X, Y], Z] = ((a, a), c) ]
      = (\sum_(a : A) `Pr[ X = a | Z = c ] * `Pr[ Y = a | Z = c ])
          * `Pr[ Z = c ].
    by rewrite big_distrl /=; apply: eq_bigr => a0 _; exact: (key a0).
  rewrite lhs_eq.
  apply: ler_wpM2r; first exact: pfwd1_ge0.
  apply: (@le_trans _ _ (\sum_(a : A) `Pr[ X = a | Z = c ] * m%:R^-1)).
    apply: ler_sum => a _.
    by apply: ler_wpM2l; [exact: cge0 | exact: HYbound].
  rewrite -big_distrl /=.
  have -> : \sum_(a : A) `Pr[ X = a | Z = c ] = 1.
    by rewrite -(sum_cPr_eq X Hc0); apply: eq_bigl => a; rewrite inE.
  by rewrite mul1r; apply: lexx.
Qed.

End cinde_diagonal_bound_sec.


(* ========================================================================== *)
(*                          fdist glue lemmas                                  *)
(* ========================================================================== *)

(* Relocated from dumas2017dual/dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v,
   where they sat in a local [fdist_glue] section although none of them uses a
   DSDP section variable.  A probe against the loaded environment confirmed
   that none of these statements exists in infotheo, MathComp or
   mathcomp-analysis: [Search] finds nothing for [fdist_uniform _ = _ `x _],
   for [fdistmap] over [fdist_uniform], nor for [_ `X _ = _ >>= _].
   The monad-only members of the original section now live in
   probability/fdist_extra.v, and the preimage transport of [Pr] lives in
   probability/proba.v as [Pr_fdistmap_preim]. *)

Section fdist_glue.

Context {R : realType}.

(* A product distribution with kernel is the bind of the first factor with the
   pairing of each first coordinate. *)
Lemma fdist_prod_bindE (T1 T2 : finType) (Q1 : R.-fdist T1)
    (W : T1 -> R.-fdist T2) :
  (Q1 `X W) = Q1 >>= (fun a => fdistmap (fun b => (a, b)) (W a)).
Proof.
apply/fdist_ext => -[a c].
rewrite fdist_prodE /= fdistbindE (bigD1 a) //=.
rewrite big1 ?addr0; last first.
  move=> i ia; rewrite fdistmapE big1 ?mulr0 // => b.
  by rewrite !inE /= xpair_eqE (negbTE ia).
congr (_ * _); rewrite fdistmapE (big_pred1 c) // => b.
by rewrite !inE /= xpair_eqE eqxx.
Qed.

(* The mass a boolean statistic puts on [true] is the probability of the
   corresponding event, the [[set true]] case of [Pr_fdistmap_preim]. *)
Lemma Pr_fdistmap_bool (T : finType) (D : T -> bool) (m : R.-fdist T) :
  Pr (fdistmap D m) [set true] = Pr m [set t | D t].
Proof.
by rewrite Pr_fdistmap_preim; apply: eq_bigl => t; rewrite !inE /= eqb_id.
Qed.

(* A uniform distribution over a product is the product of uniforms. *)
Lemma fdist_uniform_prod (T1 T2 : finType) (n1 n2 n12 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1)
    (c12 : #|((T1 * T2)%type : finType)| = n12.+1) :
  fdist_uniform (R:=R) c12 = (fdist_uniform c1) `x (fdist_uniform c2).
Proof.
apply/fdist_ext => -[a b]; rewrite fdist_prodE !fdist_uniformE.
by rewrite card_prod natrM invfM.
Qed.

(* The pushforward of a uniform along a bijection is uniform. *)
Lemma fdistmap_bij_uniform (T1 T2 : finType) (n1 n2 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1) (g : T1 -> T2) :
  bijective g ->
  fdistmap g (fdist_uniform (R:=R) c1) = fdist_uniform c2.
Proof.
move=> bg; have [h ghK hgK] := bg; apply/fdist_ext => b.
rewrite fdistmapE fdist_uniformE (big_pred1 (h b)); last first.
  by move=> a; rewrite !inE /=; apply/eqP/eqP => [<-|->].
by rewrite fdist_uniformE (bij_eq_card bg).
Qed.

(* The probability a bind assigns to an event: the mixture of the component
   probabilities. *)
Lemma Pr_fdistbind (A B : finType) (m : R.-fdist A)
    (k : A -> R.-fdist B) (E : {set B}) :
  Pr (m >>= k) E = \sum_(a in A) m a * Pr (k a) E.
Proof.
rewrite /Pr; under eq_bigr do rewrite fdistbindE.
by rewrite exchange_big /=; apply: eq_bigr => a _; rewrite big_distrr.
Qed.

(* A mixture of pairwise-close distributions is close: the distinguishing
   gap of two binds is at most the mixture of the per-component gaps. *)
Lemma fdist_mixture_advantage_le (W T : finType) (u : R.-fdist W)
    (m1 m2 : W -> R.-fdist T) (e : W -> R) (E : {set T}) :
  (forall w, `| Pr (m1 w) E - Pr (m2 w) E | <= e w) ->
  `| Pr (u >>= m1) E - Pr (u >>= m2) E | <= \sum_(w in W) u w * e w.
Proof.
move=> He; rewrite !Pr_fdistbind -sumrB.
apply: le_trans (ler_norm_sum _ _ _) _; apply: ler_sum => w _.
by rewrite -mulrBr normrM ger0_norm //; exact: ler_wpM2l (He w).
Qed.

(* The pushforward of a uniform distribution along a map with equal fiber
   cardinalities over its image is the uniform distribution on the image. *)
Lemma fdistmap_uniform_supp_img (T U : finType) (n : nat)
    (cardT : #|T| = n.+1) (f : T -> U)
    (Himg : (0 < #|f @: [set: T]|)%N)
    (Hfib : forall u u', u \in f @: [set: T] -> u' \in f @: [set: T] ->
        #|[set t | f t == u]| = #|[set t | f t == u']|) :
  fdistmap f (fdist_uniform (R:=R) cardT) = fdist_uniform_supp R Himg.
Proof.
apply/fdist_ext => u; rewrite fdistmapE.
case/boolP : (u \in f @: [set: T]) => Hu; last first.
  rewrite fdist_uniform_supp_notin // big_pred0 // => t.
  by apply/negbTE; apply: contra Hu => /eqP <-; exact: imset_f.
rewrite fdist_uniform_supp_in //.
under eq_bigr do rewrite fdist_uniformE.
rewrite sumr_const (_ : #|preim f (pred1 u)| = #|[set t | f t == u]|);
  last by apply: eq_card => t; rewrite !inE.
have Hpart : #|T| = (#|f @: [set: T]| * #|[set t | f t == u]|)%N.
  rewrite -[LHS]sum1_card (partition_big_imset f) /= -sum_nat_const.
  have -> : [set f x | x : T] = f @: [set: T].
    by apply/setP => y; apply/imsetP/imsetP => -[t _ ->]; exists t;
       rewrite ?inE.
  by apply: eq_bigr => j Hj; rewrite sum1dep_card; exact: (Hfib _ _ Hj Hu).
rewrite -[LHS]mulr_natr Hpart natrM invfM -mulrA mulVf ?mulr1 //.
rewrite pnatr_eq0 -lt0n.
by case/imsetP : Hu => r _ ->; apply/card_gt0P; exists r; rewrite inE.
Qed.

End fdist_glue.

(* ========================================================================== *)
(*                    Dropping an independent conditioner                      *)
(* ========================================================================== *)

Section cpr_eq_drop_indep_sec.

(* A conditioning coordinate independent of the numerator pair may be dropped
   from the conditioning view. *)
Lemma cpr_eq_drop_indep {Rr : realType} {U : finType} {P : FDist.t Rr U}
    {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C})
    (a : A) (y : B) (w : C) :
  `Pr[ W = w ] != 0 ->
  P |= W _|_ [% X, Y] ->
  `Pr[ X = a | [% W, Y] = (w, y) ] = `Pr[ X = a | Y = y ].
Proof.
move=> Hw Hindep; rewrite !cpr_eqE.
have HWY : P |= W _|_ Y := inde_RV_comp idfun snd Hindep.
by rewrite (pfwd1_pairCA X W Y a w y) (Hindep w (a, y)) (HWY w y) invfM
           mulrACA (mulfV Hw) mul1r.
Qed.

End cpr_eq_drop_indep_sec.
