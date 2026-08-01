(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist proba.
Require Import jfdist_cond entropy graphoid.
Require Import finstoch privacy_kernel.

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
(* perfect_privacy_cond_mutual_info0P == a simulator exists exactly when the  *)
(*                                       conditional mutual information of    *)
(*                                       the view and the honest pair given   *)
(*                                       the allowed information vanishes     *)
(*    output_independent_det == real-deterministic delivery discharges the    *)
(*                              output-independence clause                    *)
(* output_independent_determined == output-determined delivery discharges it  *)
(*  triangle_perfect_privacyP == the privacy triangle at a simulator is the   *)
(*                               perfect privacy of the privacy kernel at     *)
(*                               that simulator                               *)
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

(* Under delivery-law correctness and an injective input split, a consistent
   simulator closing the privacy triangle with output independence exists
   exactly when the conditional mutual information of the view and the honest
   pair given the allowed information vanishes.
   Naming: P = iff characterization, ffunP/setP precedent; the right-hand side
   is named by its head symbol cond_mutual_info and the value 0 it takes. *)
Lemma perfect_privacy_cond_mutual_info0P :
  injective (fun x => (proj_xa x, proj_xh x)) ->
  delivery_law_ok ->
  ((exists Sim, [/\ consistent Sim, triangle Sim & output_independent])
   <-> cond_mutual_info
         `p_[% view_rv, [% xh_rv, yh_rv], [% xa_rv, ya_rv]] = 0).
Proof.
move=> Hsplit H0.
have Hiff := perfect_privacy_centropyP Hsplit H0.
split=> [/Hiff/centropy_eq_cinde/cinde_cond_mutual_info0//|H].
by apply/Hiff; apply/cinde_centropy_eq/cond_mutual_info0_cinde.
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
move=> Hg.
by apply: (cinde_RV_fun_conditioner view_rv (h := fun p => g p.1 p.2)).
Qed.

End entropy_link.

Section triangle_perfect_privacy.
Context {R : realType}.
Variables (X Yfull Xa Ya Bv Omega : finType).
Variables (proj_xa : X -> Xa) (proj_ya : Yfull -> Ya).
Variable F : X -> R.-fdist Yfull.
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.

(* The privacy triangle at a simulator is the perfect privacy of the privacy
   kernel at that simulator.
   Naming: P = iff characterization, ffunP/setP precedent. *)
Lemma triangle_perfect_privacyP (Sim : Xa * Ya -> R.-fdist Bv) :
  triangle proj_xa proj_ya F P_Omega view_at Sim
  <-> perfect_privacy proj_xa proj_ya F P_Omega view_at Sim.
Proof.
have hallow : forall x, allow proj_xa proj_ya F x
    = fdistmap (fun yl : Yfull => (proj_xa x, proj_ya yl)) (F x).
  by move=> x; rewrite /allow tensor_fdist1 fdistmap_comp.
by split=> h x; move: (h x); rewrite /sim_view view_lawE hallow.
Qed.

End triangle_perfect_privacy.
