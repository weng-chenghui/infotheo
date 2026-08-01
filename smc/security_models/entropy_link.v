(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist proba.
Require Import jfdist_cond entropy graphoid divergence.

(**md**************************************************************************)
(* # The conditional-entropy characterization of perfect privacy              *)
(*                                                                            *)
(* An execution context pairs an input drawn from a full-support prior with   *)
(* an ancilla; the adversary observes a view and reads its delivered output   *)
(* off that view, and the honest side keeps an input projection and a         *)
(* delivered output.  Under delivery-law correctness, a support-restricted    *)
(* consistent simulator closing the privacy triangle and the                  *)
(* output-independence clause, the honest pair has the same conditional       *)
(* entropy given the adversary's allowed information with and without the     *)
(* view; conversely, an injective input split turns that entropy equality     *)
(* back into a simulator.                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*     cond_mutual_info0_cinde == vanishing conditional mutual information is *)
(*                               conditional independence                     *)
(*         centropy_eq_cinde == the conditional-entropy equality is           *)
(*                              conditional independence                      *)
(*           pfwd1_comp_sum == the law of a recoded variable is the fibre sum *)
(*                             of the law of the variable                     *)
(*          pfwd1_comp_sum2 == the same fibre sum beside a spectator          *)
(*        cinde_RV_comp_snd == conditional independence survives a recoding   *)
(*                             of the second variable                        *)
(*      cinde_RV_recode_inv == conditional independence given an injective    *)
(*                             recoding of the conditioner is conditional     *)
(*                             independence given the conditioner            *)
(*        cinde_RV_cpr_drop == a conditionally independent variable drops out *)
(*                             of the conditioning event                      *)
(*  cinde_RV_fun_conditioner == a function of the conditioner is              *)
(*                              conditionally independent of anything         *)
(*          jfdist_cond_cpr == the conditional law of a variable given an     *)
(*                             event of positive mass                         *)
(*         delivery_law_ok == the real delivered outputs have the law the     *)
(*                            ideal functionality prescribes                  *)
(*            consistent S == the output read off a simulated view is the     *)
(*                            delivered output the simulator was handed, at   *)
(*                            every pair of positive mass                     *)
(*              triangle S == the real view law factors through the allowed   *)
(*                            information along S at every input              *)
(*     output_independent == the view and the honest delivered output are     *)
(*                           conditionally independent given the input and    *)
(*                           the adversary's delivered output                 *)
(* triangle_cond_component == conditioning the view on an input and an        *)
(*                            adversary output of positive mass gives the     *)
(*                            simulator at the allowed information            *)
(*      triangle_cinde_pair == the view is conditionally independent of the   *)
(*                             honest pair given the allowed information      *)
(* perfect_privacy_centropy_eq == the conditional entropy of the honest pair  *)
(*                                is unchanged by the view                    *)
(*          centropy_to_sim == the entropy equality yields a simulator        *)
(*  perfect_privacy_centropyP == a simulator exists exactly when the honest   *)
(*                               pair has that conditional entropy            *)
(*    output_independent_det == real-deterministic delivery discharges the    *)
(*                              output-independence clause                    *)
(* output_independent_determined == output-determined delivery discharges it  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(* The conditional-independence toolbox below is generic information theory
   and probability; it is stated here because the current proba.v and
   entropy.v stop at the forward directions. *)

Section cond_mutual_info0_cinde.
Context {R : realType} {U A B C : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

(* X and Y are conditionally independent given Z when their conditional
   mutual information vanishes.
   Naming: hypothesis-first, because the conclusion-first spelling is the name
   of the forward lemma cinde_cond_mutual_info0 of entropy.v, of which this is
   the converse. *)
Lemma cond_mutual_info0_cinde :
  cond_mutual_info `p_[% X, Y, Z] = 0 -> P |= X _|_ Y | Z.
Proof.
move=> H0 a b c.
have [Hc|Hc] := eqVneq (`Pr[ Z = c ]) 0.
  by rewrite !cpr_eqE Hc invr0 !mulr0.
have Hz : (`p_[% X, Y, Z])`2 c != 0 by rewrite snd_RV3 snd_RV2 dist_of_RVE.
have Hcdiv : cdiv1 `p_[% X, Y, Z] c = 0.
  have Hsum : \sum_(z in C) (`p_[% X, Y, Z])`2 z * cdiv1 `p_[% X, Y, Z] z = 0.
    by rewrite -cond_mutual_infoE2.
  have Hge : forall z : C, z \in C ->
      0 <= (`p_[% X, Y, Z])`2 z * cdiv1 `p_[% X, Y, Z] z.
    by move=> z _; rewrite mulr_ge0 //; exact: cdiv1_ge0.
  have /eqP := psumr_eq0P Hge Hsum (isT : c \in C).
  by rewrite mulf_eq0 (negbTE Hz) /= => /eqP.
have Hc1 : (fdistX `p_[% X, Y, Z])`1 c != 0 by rewrite fdistX1.
have Hc2 : (fdistX (fdist_proj13 `p_[% X, Y, Z]))`1 c != 0
  by rewrite fdistX1 fdist_proj13_snd.
have Hc3 : (fdistX (fdist_proj23 `p_[% X, Y, Z]))`1 c != 0
  by rewrite fdistX1 fdist_proj23_snd.
have Hdom : (fdistX `p_[% X, Y, Z])`(| c) `<<
    ((fdistX (fdist_proj13 `p_[% X, Y, Z]))`(| c)) `x
    ((fdistX (fdist_proj23 `p_[% X, Y, Z]))`(| c)).
  apply/dominatesP => -[a0 b0].
  rewrite fdist_prodE !jfdist_condE //= => /eqP; rewrite mulf_eq0 => /orP[|].
  - rewrite /jcPr !setX1 !Pr_set1 !mulf_eq0 !fdistXI => /orP[/eqP|/eqP].
      by move/fdist_proj13_domin => ->; rewrite mul0r.
    by rewrite fdist_proj13_snd => ->; rewrite mulr0.
  - rewrite /jcPr !setX1 !Pr_set1 mulf_eq0 !fdistXI => /orP[/eqP|/eqP].
      by move/fdist_proj23_domin => ->; rewrite mul0r.
    by rewrite fdist_proj23_snd => ->; rewrite mulr0.
have Heq : (fdistX `p_[% X, Y, Z])`(| c) =
    ((fdistX (fdist_proj13 `p_[% X, Y, Z]))`(| c)) `x
    ((fdistX (fdist_proj23 `p_[% X, Y, Z]))`(| c)).
  by apply/(div0P Hdom); rewrite -cdiv1_is_div.
have Heqab : (fdistX `p_[% X, Y, Z])`(| c) (a, b)
  = ((((fdistX (fdist_proj13 `p_[% X, Y, Z]))`(| c)) `x
      ((fdistX (fdist_proj23 `p_[% X, Y, Z]))`(| c))) (a, b)) by rewrite Heq.
move: Heqab; rewrite fdist_prodE !jfdist_condE //.
rewrite !fdistXI /jcPr !setX1 !Pr_set1 /=.
have -> : (fdist_proj13 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj13_snd; apply/fdist_ext => x; rewrite snd_RV3 snd_RV2.
have -> : (fdist_proj23 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj23_snd; apply/fdist_ext => y; rewrite snd_RV3 snd_RV2.
by rewrite fdist_proj13_RV3 fdist_proj23_RV3 snd_RV3 snd_RV2 !dist_of_RVE
  -!cpr_eqE.
Qed.

End cond_mutual_info0_cinde.

Section centropy_eq_cinde.
Context {R : realType} {U A B C : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

(* X and Y are conditionally independent given Z when conditioning Y on the
   pair (X, Z) leaves its conditional entropy given Z unchanged.
   Naming: hypothesis-first, because the conclusion-first spelling is the name
   of the forward lemma cinde_centropy_eq of entropy.v, of which this is the
   converse. *)
Lemma centropy_eq_cinde :
  `H( Y | [% X, Z] ) = `H( Y | Z ) -> P |= X _|_ Y | Z.
Proof.
move=> Heq; apply/cinde_RV_sym/cond_mutual_info0_cinde.
move: Heq; rewrite /centropy_RV /cond_mutual_info /centropy.
rewrite fdist_proj13_snd snd_RV3 snd_RV2 fdistA_RV3 snd_RV2 fdist_proj13_RV3.
by rewrite snd_RV2 => ->; rewrite subrr.
Qed.

End centropy_eq_cinde.

Section cinde_RV_toolbox.
Context {R : realType} {U : finType} {P : R.-fdist U}.

(* The law of a recoded variable paired with a spectator is the sum of the
   laws over the fibre of the recoding. *)
Lemma pfwd1_comp_sum (B C D : finType) (V : {RV P -> B}) (W : {RV P -> C})
    (g : B -> D) (t : D) (w : C) :
  `Pr[ [% (g `o V), W] = (t, w) ]
  = \sum_(b in B | g b == t) `Pr[ [% V, W] = (b, w) ].
Proof.
rewrite -pr_in1.
have -> : [% (g `o V), W] = ((fun p : B * C => (g p.1, p.2)) `o [% V, W]) by [].
rewrite pr_in_comp'.
have -> : (fun p : B * C => (g p.1, p.2)) @^-1: [set (t, w)]
        = ((g @^-1: [set t]) `* [set w])%SET.
  by apply/setP => -[b c]; rewrite !inE /= !xpair_eqE.
rewrite pr_inE' /Pr big_setX /=.
apply: eq_big => [b|b _]; first by rewrite !inE.
by rewrite big_set1 dist_of_RVE.
Qed.

(* The same fibre sum with a further variable carried along. *)
Lemma pfwd1_comp_sum2 (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B})
    (Z : {RV P -> C}) (g : B -> D) (a : A) (t : D) (c : C) :
  `Pr[ [% [% X, (g `o Y)], Z] = ((a, t), c) ]
  = \sum_(b in B | g b == t) `Pr[ [% [% X, Y], Z] = ((a, b), c) ].
Proof.
rewrite -pr_in1.
have -> : [% [% X, (g `o Y)], Z]
  = ((fun q : A * B * C => ((q.1.1, g q.1.2), q.2)) `o [% [% X, Y], Z]) by [].
rewrite pr_in_comp'.
have -> : (fun q : A * B * C => ((q.1.1, g q.1.2), q.2)) @^-1: [set ((a, t), c)]
        = (([set a] `* (g @^-1: [set t])) `* [set c])%SET.
  by apply/setP => -[[a0 b0] c0]; rewrite !inE /= !xpair_eqE.
rewrite pr_inE' /Pr big_setX /= big_setX /=.
rewrite big_set1 /=; apply: eq_big => [b|b _]; first by rewrite !inE.
by rewrite big_set1 dist_of_RVE.
Qed.

(* Conditional independence given Z is preserved by any recoding of the second
   variable. *)
Lemma cinde_RV_comp_snd (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B})
    (Z : {RV P -> C}) (g : B -> D) :
  P |= X _|_ Y | Z -> P |= X _|_ (g `o Y) | Z.
Proof.
move=> H a t c.
rewrite [X in _ * X]cpr_eqE (pfwd1_comp_sum Y Z g) big_distrl /= big_distrr /=.
rewrite cpr_eqE (pfwd1_comp_sum2 X Y Z g) big_distrl /=.
by apply: eq_bigr => b _; rewrite -!cpr_eqE H.
Qed.

(* Conditional independence given an injective recoding of the conditioner is
   conditional independence given the conditioner, the converse of
   cinde_RV_recode. *)
Lemma cinde_RV_recode_inv (A B C C' : finType) (X : {RV P -> A})
    (Y : {RV P -> B}) (Z : {RV P -> C}) (phi : C -> C') :
  injective phi -> P |= X _|_ Y | (phi `o Z) -> P |= X _|_ Y | Z.
Proof.
move=> phi_inj H a b c.
have pfE : forall (E : finType) (W : {RV P -> E}) (e : E),
    `Pr[ [% W, phi `o Z] = (e, phi c) ] = `Pr[ [% W, Z] = (e, c) ].
  move=> E W e; rewrite !pfwd1E; congr (Pr P _).
  by apply/setP => u; rewrite !inE /= !xpair_eqE (inj_eq phi_inj).
have pZ : `Pr[ (phi `o Z) = phi c ] = `Pr[ Z = c ].
  rewrite !pfwd1E; congr (Pr P _).
  by apply/setP => u; rewrite !inE /= (inj_eq phi_inj).
by have := H a b (phi c); rewrite !cpr_eqE !pfE pZ -!cpr_eqE.
Qed.

(* A variable conditionally independent of X given Z drops out of the
   conditioning event of X. *)
Lemma cinde_RV_cpr_drop (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B})
    (Z : {RV P -> C}) (a : A) (b : B) (c : C) :
  P |= X _|_ Y | Z -> `Pr[ [% Y, Z] = (b, c) ] != 0 ->
  `Pr[ X = a | [% Y, Z] = (b, c) ] = `Pr[ X = a | Z = c ].
Proof.
move=> H Hbc.
have Hc : `Pr[ Z = c ] != 0.
  apply: contraNN Hbc => /eqP Hc0.
  by apply/eqP; exact: (pfwd1_domin_RV1 Y b Hc0).
have := H a b c; rewrite !cpr_eqE => Hcinde.
have Hi : `Pr[ Z = c ]^-1 != 0 by rewrite invr_eq0.
move: Hcinde; rewrite mulrA => /(mulIf Hi) HN.
have -> : `Pr[ [% X, [% Y, Z]] = (a, (b, c)) ]
        = `Pr[ [% [% X, Y], Z] = ((a, b), c) ].
  rewrite !pfwd1E; congr (Pr P _); apply/setP => u; rewrite !inE /= !xpair_eqE.
  by rewrite andbA.
by rewrite HN mulfK.
Qed.

(* A variable that is a function of the conditioner is conditionally
   independent of every variable given that conditioner. *)
Lemma cinde_RV_fun_conditioner (A B C : finType) (X : {RV P -> A})
    (Y : {RV P -> B}) (Z : {RV P -> C}) (h : C -> B) :
  (forall u, Y u = h (Z u)) -> P |= X _|_ Y | Z.
Proof.
move=> HY a b c.
have E1 : `Pr[ [% [% X, Y], Z] = ((a, b), c) ]
        = (h c == b)%:R * `Pr[ [% X, Z] = (a, c) ].
  rewrite !pfwd1E; have [Hb|Hb] := eqVneq (h c) b.
    rewrite mul1r; congr (Pr P _); apply/setP => u; rewrite !inE /= !xpair_eqE.
    case: (eqVneq (Z u) c) => [Hu|Hu]; last by rewrite !andbF.
    by rewrite HY Hu Hb !eqxx !andbT.
  rewrite mul0r /Pr; apply: big_pred0 => u; rewrite !inE /= !xpair_eqE.
  case: (eqVneq (Z u) c) => [Hu|Hu]; last by rewrite !andbF.
  by rewrite HY Hu (negbTE Hb) andbF.
have E2 : `Pr[ [% Y, Z] = (b, c) ] = (h c == b)%:R * `Pr[ Z = c ].
  rewrite !pfwd1E; have [Hb|Hb] := eqVneq (h c) b.
    rewrite mul1r; congr (Pr P _); apply/setP => u; rewrite !inE /= !xpair_eqE.
    case: (eqVneq (Z u) c) => [Hu|Hu]; last by rewrite andbF.
    by rewrite HY Hu Hb eqxx.
  rewrite mul0r /Pr; apply: big_pred0 => u; rewrite !inE /= !xpair_eqE.
  case: (eqVneq (Z u) c) => [Hu|Hu]; last by rewrite andbF.
  by rewrite HY Hu (negbTE Hb).
rewrite !cpr_eqE E1 E2.
have [Hc|Hc] := eqVneq (`Pr[ Z = c ]) 0.
  by rewrite Hc invr0 !mulr0.
by rewrite mulfK // -mulrA mulrC.
Qed.

(* The conditional law of a variable given an event of positive mass is the
   conditional probability of that variable. *)
Lemma jfdist_cond_cpr (B C : finType) (Z : {RV P -> C}) (V : {RV P -> B})
    (z : C) (v : B) :
  `Pr[ Z = z ] != 0 -> (`p_ [% Z, V]) `(| z ) v = `Pr[ V = v | Z = z ].
Proof.
move=> Hz.
have Hz' : (`p_ [% Z, V])`1 z != 0 by rewrite fst_RV2 dist_of_RVE.
rewrite (jfdist_condE Hz') /jcPr setX1 !Pr_set1 fdistXE fdistX2 fst_RV2.
rewrite cpr_eqE dist_of_RVE; congr (_ / _).
rewrite dist_of_RVE !pfwd1E; congr (Pr P _); apply/setP => u.
by rewrite !inE /= !xpair_eqE andbC.
Qed.

End cinde_RV_toolbox.

Section entropy_link.
Context {R : realType}.
Variables X Yfull Xa Ya Xh Yh Bv Omega : finType.
Variables (proj_xa : X -> Xa) (proj_xh : X -> Xh).
Variables (proj_ya : Yfull -> Ya) (proj_yh : Yfull -> Yh).
Variable F : X -> R.-fdist Yfull.
Variable P_Omega : R.-fdist Omega.
Variables (view_at : X * Omega -> Bv) (run : X * Omega -> Yfull).
Variable out_adv : Bv -> Ya.
Hypothesis readoff : forall e, out_adv (view_at e) = proj_ya (run e).
Variable mu : R.-fdist X.
Hypothesis mu_full : forall x, mu x != 0.

(* The joint prior on the execution context. *)
Let d : R.-fdist (X * Omega)%type := (mu `x P_Omega)%fdist.

(* The random variables of the execution context: the adversary's view, the
   input, the delivered outputs and the two input projections. *)
Let view_rv : {RV d -> Bv} := view_at.
Let input_rv : {RV d -> X} := fst.
Let ya_rv : {RV d -> Ya} := fun e => proj_ya (run e).
Let yh_rv : {RV d -> Yh} := fun e => proj_yh (run e).
Let xa_rv : {RV d -> Xa} := proj_xa \o fst.
Let xh_rv : {RV d -> Xh} := proj_xh \o fst.

(* The real delivered outputs have the law the ideal functionality prescribes
   at every input. *)
Definition delivery_law_ok :=
  forall x, fdistmap (fun w => run (x, w)) P_Omega = F x.

(* The output read off a simulated view is the delivered output the simulator
   was handed, at every pair of positive mass. *)
Definition consistent (Sim : Xa * Ya -> R.-fdist Bv) :=
  forall a y, `Pr[ [% xa_rv, ya_rv] = (a, y) ] != 0 ->
  fdistmap out_adv (Sim (a, y)) = fdist1 y.

(* The real view law at an input is the simulator run on the allowed
   information at that input. *)
Definition triangle (Sim : Xa * Ya -> R.-fdist Bv) :=
  forall x, fdistmap (fun w => view_at (x, w)) P_Omega
            = (fdistmap (fun yl => (proj_xa x, proj_ya yl)) (F x)) >>= Sim.

(* The view and the honest delivered output are conditionally independent
   given the input and the adversary's delivered output. *)
Definition output_independent :=
  d |= view_rv _|_ yh_rv | [% input_rv, ya_rv].

(* The law of the adversary's delivered outputs at an input. *)
Let beta_law (x : X) : R.-fdist Ya :=
  fdistmap (fun w => proj_ya (run (x, w))) P_Omega.

(* The law of the adversary's view at an input. *)
Let nu_law (x : X) : R.-fdist Bv :=
  fdistmap (fun w => view_at (x, w)) P_Omega.

(* The joint law of the input with an observable of the run is the input law
   times the law of that observable at the input. *)
Lemma pfwd1_input_pair (T : finType) (h : X * Omega -> T) (x : X) (t : T) :
  `Pr[ [% input_rv, (h : {RV d -> T})] = (x, t) ]
  = mu x * (fdistmap (fun w => h (x, w)) P_Omega) t.
Proof.
rewrite pfwd1E /Pr fdistmapE big_distrr /=.
rewrite (reindex_onto (fun w : Omega => (x, w)) snd) /=; last first.
  by move=> [x' w]; rewrite inE /= xpair_eqE => /andP[/eqP <- _].
apply: eq_big => [w|w _]; last by rewrite /d fdist_prodE.
by rewrite !inE /= !xpair_eqE !eqxx andbT.
Qed.

(* The joint law of the input with the adversary's delivered output. *)
Lemma pfwd1_input_ya x y :
  `Pr[ [% input_rv, ya_rv] = (x, y) ] = mu x * beta_law x y.
Proof. exact: pfwd1_input_pair. Qed.

(* The joint law of the view with the input and the adversary's delivered
   output: reading the output off the view makes it a fibre indicator.
   Naming: main symbol pfwd1, then the three random variables in the order
   they occur in the statement. *)
Lemma pfwd1_view_input_ya v x y :
  `Pr[ [% view_rv, [% input_rv, ya_rv]] = (v, (x, y)) ]
  = mu x * ((out_adv v == y)%:R * nu_law x v).
Proof.
transitivity (`Pr[ [% input_rv,
    ((fun e => (view_at e, proj_ya (run e))) : {RV d -> (Bv * Ya)%type})]
    = (x, (v, y)) ]).
  rewrite !pfwd1E; congr (Pr d _); apply/setP => u.
  by rewrite !inE /= !xpair_eqE /= andbA [X in X && _]andbC -andbA.
rewrite pfwd1_input_pair; congr (mu x * _).
have -> : fdistmap (fun w : Omega => (view_at (x, w), proj_ya (run (x, w))))
    P_Omega (v, y)
  = `Pr[ [% ((fun w => view_at (x, w)) : {RV P_Omega -> Bv}),
            ((fun w => proj_ya (run (x, w))) : {RV P_Omega -> Ya})] = (v, y) ].
  by rewrite -dist_of_RVE.
rewrite (pfwd1_pair_det (g := out_adv)); last by move=> w; rewrite readoff.
by rewrite /nu_law -dist_of_RVE.
Qed.

(* An input of positive joint mass carries its adversary projection.
   Naming: main symbol pfwd1, then the conclusion's two random variables and
   the neq0 shape of the conclusion. *)
Lemma pfwd1_xa_ya_neq0 x y :
  `Pr[ [% input_rv, ya_rv] = (x, y) ] != 0 ->
  `Pr[ [% xa_rv, ya_rv] = (proj_xa x, y) ] != 0.
Proof.
have Hle : `Pr[ [% input_rv, ya_rv] = (x, y) ]
           <= `Pr[ [% xa_rv, ya_rv] = (proj_xa x, y) ].
  rewrite !pfwd1E; apply: subset_Pr; apply/subsetP => u.
  rewrite !inE /= !xpair_eqE.
  by move=> /andP[/eqP <- ->]; rewrite andbT; exact: eqxx.
apply: contraNN => /eqP HB; apply/eqP.
by apply/le_anti; rewrite pfwd1_ge0 andbT -HB.
Qed.

(* A consistent simulator is supported on the fibre of the delivered output it
   was handed. *)
Lemma sim_supp0 (Sim : Xa * Ya -> R.-fdist Bv) a y v :
  fdistmap out_adv (Sim (a, y)) = fdist1 y ->
  out_adv v != y -> Sim (a, y) v = 0.
Proof.
by move=> Hc Hv; apply: (fdistmap_eq0 (f := out_adv)); rewrite Hc fdist10.
Qed.

(* The simulated view law is the mixture of the simulator over the delivered
   outputs of the ideal functionality. *)
Lemma sim_mixtureE (Sim : Xa * Ya -> R.-fdist Bv) x v :
  ((fdistmap (fun yl => (proj_xa x, proj_ya yl)) (F x)) >>= Sim) v
  = \sum_(y : Ya) (fdistmap proj_ya (F x)) y * Sim (proj_xa x, y) v.
Proof.
rewrite -(fdistmap_comp (fun y => (proj_xa x, y)) proj_ya) /fdistmap.
by rewrite fdistbindA fdistbindE; apply: eq_bigr => y _; rewrite fdist1bind.
Qed.

(* Conditioning the view on an input and an adversary output of positive mass
   gives the simulator at the allowed information.
   Naming: main symbol triangle, the hypothesis the lemma decomposes; the
   suffix names the component of its mixture that is selected. *)
Lemma triangle_cond_component Sim :
  delivery_law_ok -> consistent Sim -> triangle Sim ->
  forall x y, `Pr[ [% input_rv, ya_rv] = (x, y) ] != 0 ->
  forall v, `Pr[ view_rv = v | [% input_rv, ya_rv] = (x, y) ]
            = Sim (proj_xa x, y) v.
Proof.
move=> H0 Hcons Htri x y Hxy v.
have Hbeta : beta_law x = fdistmap proj_ya (F x).
  by rewrite /beta_law -H0 fdistmap_comp.
have Hsupp : forall y', beta_law x y' != 0 ->
    forall v', out_adv v' != y' -> Sim (proj_xa x, y') v' = 0.
  move=> y' Hy' v' Hv'; apply: sim_supp0 => //.
  apply: Hcons; apply: pfwd1_xa_ya_neq0.
  by rewrite pfwd1_input_ya mulf_neq0.
have Hnu : forall v', nu_law x v'
    = beta_law x (out_adv v') * Sim (proj_xa x, out_adv v') v'.
  move=> v'; rewrite /nu_law Htri sim_mixtureE -Hbeta.
  rewrite (bigD1 (out_adv v')) //= big1 ?addr0 // => y' Hy'.
  have [->|Hb] := eqVneq (beta_law x y') 0; first by rewrite mul0r.
  by rewrite (Hsupp _ Hb) ?mulr0 // eq_sym.
move: Hxy; rewrite cpr_eqE pfwd1_view_input_ya !pfwd1_input_ya => Hxy.
have [Hv|Hv] := eqVneq (out_adv v) y.
  by rewrite mul1r Hnu Hv mulrA [X in X / _]mulrC -mulrA divff ?mulr1.
rewrite mul0r mulr0 mul0r; symmetry; apply: Hsupp => //.
by apply/negP => /eqP Hb0; move: Hxy; rewrite Hb0 mulr0 eqxx.
Qed.

(* The adversary input is redundant beside the full input. *)
Lemma pfwd1_split_xa v x a y :
  `Pr[ [% [% view_rv, input_rv], [% xa_rv, ya_rv]] = ((v, x), (a, y)) ]
  = (proj_xa x == a)%:R * `Pr[ [% view_rv, [% input_rv, ya_rv]] = (v, (x, y)) ].
Proof.
rewrite !pfwd1E.
have [Ha|Ha] := eqVneq (proj_xa x) a.
  rewrite mul1r; congr (Pr d _); apply/setP => u; rewrite !inE /= !xpair_eqE.
  case: (eqVneq (input_rv u) x) => [Hu|Hu]; last by rewrite !andbF.
  have Hxu : xa_rv u = proj_xa (input_rv u) by [].
  by rewrite Hxu Hu Ha eqxx andbT.
rewrite mul0r /Pr; apply: big_pred0 => u; rewrite !inE /= !xpair_eqE.
case: (eqVneq (input_rv u) x) => [Hu|Hu]; last by rewrite !andbF.
have Hxu : xa_rv u = proj_xa (input_rv u) by [].
have -> : (xa_rv u == a) = false by apply/negbTE; rewrite Hxu Hu.
by rewrite andbF.
Qed.

(* The view is conditionally independent of the honest input and output pair
   given the adversary's allowed information. *)
Lemma triangle_cinde_pair Sim :
  delivery_law_ok -> consistent Sim -> triangle Sim -> output_independent ->
  d |= view_rv _|_ [% xh_rv, yh_rv] | [% xa_rv, ya_rv].
Proof.
move=> H0 Hcons Htri H2.
have HA : d |= view_rv _|_ input_rv | [% xa_rv, ya_rv].
  apply: (cinde_RV_factor
    (f := fun (x : X) (p : Xa * Ya) =>
            (proj_xa x == p.1)%:R * `Pr[ [% input_rv, ya_rv] = (x, p.2) ])
    (g := fun (p : Xa * Ya) (v : Bv) => Sim p v)) => v x [a y].
  rewrite pfwd1_split_xa /=.
  have [Hxy|Hxy] := eqVneq (`Pr[ [% input_rv, ya_rv] = (x, y) ]) 0.
    by rewrite Hxy (pfwd1_domin_RV1 view_rv v Hxy) !mulr0 mul0r.
  have [Ha|Ha] := eqVneq (proj_xa x) a; last by rewrite !mul0r.
  rewrite !mul1r -Ha.
  have Hc := triangle_cond_component H0 Hcons Htri Hxy v.
  rewrite cpr_eqE in Hc.
  by rewrite -[LHS](divfK Hxy) Hc mulrC.
have Hinj : injective (fun p : X * Ya => ((proj_xa p.1, p.2), p.1)).
  by move=> [x1 y1] [x2 y2] /= [] _ -> ->.
have HB : d |= view_rv _|_ yh_rv | [% [% xa_rv, ya_rv], input_rv]
  := cinde_RV_recode Hinj H2.
have HC := contraction HB HA.
exact: (cinde_RV_comp_snd (Y := [% input_rv, yh_rv])
          (fun p : X * Yh => (proj_xh p.1, p.2)) HC).
Qed.

(* Conditioning the honest pair on the view on top of the allowed information
   leaves its conditional entropy unchanged. *)
Lemma perfect_privacy_centropy_eq Sim :
  delivery_law_ok -> consistent Sim -> triangle Sim -> output_independent ->
  `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
  = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ).
Proof.
move=> H0 Hc Ht Hi.
exact/cinde_centropy_eq/(triangle_cinde_pair H0 Hc Ht Hi).
Qed.

(* Under delivery-law correctness and an injective input split, the
   conditional-entropy equality yields a consistent simulator closing the
   privacy triangle with output independence. *)
Lemma centropy_to_sim :
  injective (fun x => (proj_xa x, proj_xh x)) ->
  delivery_law_ok ->
  `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
    = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ) ->
  exists Sim, [/\ consistent Sim, triangle Sim & output_independent].
Proof.
move=> Hsplit H0 Heq.
have CI : d |= view_rv _|_ [% xh_rv, yh_rv] | [% xa_rv, ya_rv]
  := centropy_eq_cinde Heq.
have Hsp : forall (u : X * Omega) (x : X),
    (input_rv u == x) = (xh_rv u == proj_xh x) && (xa_rv u == proj_xa x).
  move=> u x.
  have Hh : xh_rv u = proj_xh (input_rv u) by [].
  have Ha : xa_rv u = proj_xa (input_rv u) by [].
  rewrite Hh Ha; apply/idP/idP; first by move=> /eqP ->; rewrite !eqxx.
  move=> /andP[/eqP H1 /eqP H2]; apply/eqP; apply: Hsplit => /=.
  by rewrite H1 H2.
have H2 : output_independent.
  apply: (cinde_RV_recode_inv
    (phi := fun p : X * Ya => ((proj_xa p.1, p.2), proj_xh p.1))).
    move=> [x1 y1] [x2 y2] /= [] [] Ha -> Hh.
    by congr pair; apply: Hsplit => /=; rewrite Ha Hh.
  exact: (weak_union (cinde_drv_2C CI)).
have Hev1 : forall (T : finType) (W : {RV d -> T}) (t : T) (x : X) (y : Ya),
    `Pr[ [% W, [% input_rv, ya_rv]] = (t, (x, y)) ]
    = `Pr[ [% W, [% xh_rv, [% xa_rv, ya_rv]]]
           = (t, (proj_xh x, (proj_xa x, y))) ].
  move=> T W t x y; rewrite !pfwd1E; congr (Pr d _); apply/setP => u.
  by rewrite !inE /= !xpair_eqE Hsp -andbA.
have Hev2 : forall (x : X) (y : Ya),
    `Pr[ [% input_rv, ya_rv] = (x, y) ]
    = `Pr[ [% xh_rv, [% xa_rv, ya_rv]] = (proj_xh x, (proj_xa x, y)) ].
  move=> x y; rewrite !pfwd1E; congr (Pr d _); apply/setP => u.
  by rewrite !inE /= !xpair_eqE Hsp -andbA.
have Hcond : forall (v : Bv) (x : X) (y : Ya),
    `Pr[ [% input_rv, ya_rv] = (x, y) ] != 0 ->
    `Pr[ view_rv = v | [% input_rv, ya_rv] = (x, y) ]
    = `Pr[ view_rv = v | [% xa_rv, ya_rv] = (proj_xa x, y) ].
  move=> v x y Hxy; rewrite cpr_eqE Hev1 Hev2 -cpr_eqE.
  by apply: (cinde_RV_cpr_drop v (decomposition CI)); rewrite -Hev2.
have Hoa : forall (y' : Ya) (z : Xa * Ya),
    `Pr[ [% (out_adv `o view_rv), [% xa_rv, ya_rv]] = (y', z) ]
    = `Pr[ [% ya_rv, [% xa_rv, ya_rv]] = (y', z) ].
  move=> y' z; rewrite !pfwd1E; congr (Pr d _); apply/setP => u.
  rewrite !inE /= !xpair_eqE.
  have -> : (out_adv `o view_rv) u = out_adv (view_at u) by [].
  by rewrite readoff.
have Hyy : forall (y' : Ya) (a : Xa) (y : Ya),
    `Pr[ [% ya_rv, [% xa_rv, ya_rv]] = (y', (a, y)) ]
    = (y' == y)%:R * `Pr[ [% xa_rv, ya_rv] = (a, y) ].
  move=> y' a y; rewrite !pfwd1E.
  have [Hy|Hy] := eqVneq y' y.
    rewrite mul1r; congr (Pr d _); apply/setP => u.
    rewrite !inE /= !xpair_eqE Hy.
    by case: (ya_rv u == y); rewrite ?andbT ?andbF.
  rewrite mul0r /Pr; apply: big_pred0 => u; rewrite !inE /= !xpair_eqE.
  by case: (eqVneq (ya_rv u) y') => [->|_]; rewrite ?(negbTE Hy) ?andbF.
pose Sim : Xa * Ya -> R.-fdist Bv :=
  fun p => (`p_ [% [% xa_rv, ya_rv], view_rv]) `(| p ).
have HSim : forall (a : Xa) (y : Ya), `Pr[ [% xa_rv, ya_rv] = (a, y) ] != 0 ->
    forall v, Sim (a, y) v = `Pr[ view_rv = v | [% xa_rv, ya_rv] = (a, y) ].
  by move=> a y Hay v; rewrite /Sim jfdist_cond_cpr.
exists Sim; split; last exact: H2.
  move=> a y Hay; apply/fdist_ext => y'.
  rewrite fdistmapE fdist1E.
  transitivity (\sum_(v in Bv | out_adv v == y') Sim (a, y) v).
    by apply: eq_bigl => v; rewrite !inE.
  under eq_bigr do rewrite (HSim _ _ Hay) cpr_eqE.
  rewrite -big_distrl /=.
  rewrite -(pfwd1_comp_sum view_rv [% xa_rv, ya_rv] out_adv) Hoa Hyy.
  by rewrite mulfK.
move=> x; apply/fdist_ext => v.
rewrite sim_mixtureE.
have Hbeta : beta_law x = fdistmap proj_ya (F x).
  by rewrite /beta_law -H0 fdistmap_comp.
rewrite -Hbeta.
apply: (mulfI (mu_full x)).
rewrite big_distrr /=.
transitivity (\sum_(y : Ya)
    `Pr[ [% view_rv, [% input_rv, ya_rv]] = (v, (x, y)) ]).
  rewrite (eq_bigr (fun y => mu x * ((out_adv v == y)%:R * nu_law x v)));
    last by move=> y _; rewrite pfwd1_view_input_ya.
  rewrite -big_distrr /=; congr (mu x * _).
  rewrite (bigD1 (out_adv v)) //= eqxx mul1r big1 ?addr0 // => y Hy.
  by rewrite eq_sym (negbTE Hy) mul0r.
apply: eq_bigr => y _.
have [Hxy|Hxy] := eqVneq (`Pr[ [% input_rv, ya_rv] = (x, y) ]) 0.
  by rewrite mulrA -pfwd1_input_ya Hxy mul0r (pfwd1_domin_RV1 view_rv v Hxy).
have Hay := pfwd1_xa_ya_neq0 Hxy.
by rewrite mulrA -pfwd1_input_ya (HSim _ _ Hay) -Hcond // cpr_eqE mulrC divfK.
Qed.

(* Under delivery-law correctness and an injective input split, a consistent
   simulator closing the privacy triangle with output independence exists
   exactly when the view leaves the conditional entropy of the honest pair
   given the allowed information unchanged.
   Naming: P = iff characterization, ffunP/setP precedent, and the prefix
   perfect_privacy_ keeps the generic cinde_centropy_eq of entropy.v
   unshadowed. *)
Lemma perfect_privacy_centropyP :
  injective (fun x => (proj_xa x, proj_xh x)) ->
  delivery_law_ok ->
  ((exists Sim, [/\ consistent Sim, triangle Sim & output_independent])
   <-> `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
       = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] )).
Proof.
move=> Hsplit H0; split=> [[Sim [Hc Ht Hi]]|Heq]; last exact: centropy_to_sim.
exact: (perfect_privacy_centropy_eq H0 Hc Ht Hi).
Qed.

(* Real-deterministic delivery discharges the output-independence condition. *)
Lemma output_independent_det (g : X -> Yh) :
  (forall e : X * Omega, proj_yh (run e) = g e.1) -> output_independent.
Proof.
by move=> Hg; apply: (cinde_RV_fun_conditioner view_rv (h := fun p => g p.1)).
Qed.

(* Output-determined delivery discharges the condition. *)
Lemma output_independent_determined (g : X -> Ya -> Yh) :
  (forall e : X * Omega, proj_yh (run e) = g e.1 (proj_ya (run e))) ->
  output_independent.
Proof.
by move=> Hg;
  apply: (cinde_RV_fun_conditioner view_rv (h := fun p => g p.1 p.2)).
Qed.

End entropy_link.
