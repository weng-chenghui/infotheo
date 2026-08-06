(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist fdist_extra proba.
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
(* back into a simulator.  Lindell's joint comparison of the real and the     *)
(* ideal pair of a view with a delivered output is those same conditions      *)
(* together with the delivery law, under an injective output split.           *)
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
(*    output_independent_det == real-deterministic delivery at every          *)
(*                              execution of positive mass discharges the     *)
(*                              output-independence clause                    *)
(* output_independent_determined == output-determined delivery at every       *)
(*                                  execution of positive mass discharges it  *)
(*  triangle_perfect_privacyP == the privacy triangle at a simulator is the   *)
(*                               perfect privacy of the privacy kernel at     *)
(*                               that simulator                               *)
(*            pair_readoff == Lindell's joint comparison of the real and the  *)
(*                            ideal pair of a view with a delivered output    *)
(*             real_pair x == the joint law of the view and the delivered     *)
(*                            outputs at the input x                          *)
(*     ideal_pair_of Sim x == the view Sim produces at the input x coupled    *)
(*                            with the functionality draw it was handed       *)
(*             pair_eq Sim == the two joint laws agree at every input         *)
(*       real_pair_readoff == the real joint law is carried by the pairs      *)
(*                            whose view reads off to the delivered output    *)
(*      ideal_pair_readoff == a simulator consistent on the support of the    *)
(*                            functionality carries the ideal joint law on    *)
(*                            those pairs too                                 *)
(*      conditions_pair_eq == the delivery law, a consistent simulator        *)
(*                            closing the privacy triangle and output         *)
(*                            independence give the joint equality            *)
(*                 pair_eqP == the joint equality at a simulator is those     *)
(*                             four conditions                                *)
(*          exists_pair_eqP == the joint equality has a witness exactly when  *)
(*                             the delivery law holds and some simulator      *)
(*                             meets the other three conditions               *)
(* exists_pair_eq_centropyP == the joint equality has a witness exactly when  *)
(*                             the delivery law holds and the view leaves     *)
(*                             the conditional entropy of the honest pair     *)
(*                             unchanged                                      *)
(* exists_pair_eq_cond_mutual_info0P == the joint equality has a witness      *)
(*                             exactly when the delivery law holds and that   *)
(*                             conditional mutual information vanishes        *)
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

(* Delivery that is a function of the input at every execution of positive mass
   discharges the output-independence condition.  Positive mass is mass under
   the execution law mu `x P_Omega.  On a finite carrier, equality at every
   point of positive mass and a null exception set are equivalent, as
   almost_sure_eqP records.  That equivalence is a fact about finite
   carriers. *)
Lemma output_independent_det (g : X -> Yh) :
  (forall e : X * Omega, d e != 0 -> proj_yh (run e) = g e.1) ->
  output_independent.
Proof.
move=> Hg.
by apply: (cinde_RV_fun_conditioner_almost_sure view_rv (h := g \o fst)).
Qed.

(* Delivery that is a function of the input and the adversary's delivered
   output at every execution of positive mass discharges the condition.
   Positive mass is mass under the execution law mu `x P_Omega, as in
   output_independent_det. *)
Lemma output_independent_determined (g : X -> Ya -> Yh) :
  (forall e : X * Omega, d e != 0 ->
     proj_yh (run e) = g e.1 (proj_ya (run e))) ->
  output_independent.
Proof.
move=> Hg.
by apply: (cinde_RV_fun_conditioner_almost_sure view_rv (h := uncurry g)).
Qed.

End entropy_link.

(* Lindell's joint comparison of the real and the ideal pair of a view with a
   delivered output, at the execution context of entropy_link above. *)
Module pair_readoff.
Section pair_readoff.
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

(* The real joint law of the view and the delivered outputs at an input. *)
Definition real_pair (x : X) : R.-fdist (Bv * Yfull)%type :=
  fdistmap (fun w => (view_at (x, w), run (x, w))) P_Omega.

(* The view a simulator produces coupled with the functionality draw it was
   handed. *)
Definition ideal_pair_of (Sim : Xa * Ya -> R.-fdist Bv) (x : X)
    : R.-fdist (Bv * Yfull)%type :=
  F x >>= (fun y => tensor (Sim (proj_xa x, proj_ya y)) (fdist1 y)).

(* Lindell's joint comparison at a simulator: the two joint laws agree at
   every input.
   Naming: the predicate the pair_eq_ family decomposes, named by its two
   sides real_pair and ideal_pair_of and the equality between them. *)
Definition pair_eq (Sim : Xa * Ya -> R.-fdist Bv) :=
  forall x, real_pair x = ideal_pair_of Sim x.

(* The real joint law is carried by the pairs whose view reads off to the
   delivered output. *)
Lemma real_pair_readoff (x : X) (v : Bv) (y : Yfull) :
  real_pair x (v, y) != 0 -> out_adv v = proj_ya y.
Proof.
by rewrite /real_pair => /fdistmap_neq0P[w [<- <-] _]; exact: readoff.
Qed.

(* The ideal joint law at a pair is the functionality mass times the simulator
   mass at the allowed information. *)
Lemma ideal_pair_ofE (Sim : Xa * Ya -> R.-fdist Bv) (x : X) (q : Bv * Yfull) :
  ideal_pair_of Sim x q = F x q.2 * Sim (proj_xa x, proj_ya q.2) q.1.
Proof.
case: q => v y; rewrite /ideal_pair_of fdistbindE (bigD1 y)//= tensorE.
rewrite fdist1E eqxx mulr1 big1 ?addr0// => y' y'ne.
by rewrite tensorE fdist1E eq_sym (negbTE y'ne) mulr0 mulr0.
Qed.

(* At a simulator consistent on the support of the functionality, the ideal
   joint law is carried by the pairs whose view reads off to the delivered
   output. *)
Lemma ideal_pair_readoff (Sim : Xa * Ya -> R.-fdist Bv) (x : X) (v : Bv)
    (y : Yfull) :
  (forall y', F x y' != 0 ->
     fdistmap out_adv (Sim (proj_xa x, proj_ya y')) = fdist1 (proj_ya y')) ->
  ideal_pair_of Sim x (v, y) != 0 -> out_adv v = proj_ya y.
Proof.
move=> hcons; rewrite ideal_pair_ofE/= mulf_eq0 negb_or => /andP[hF hSv].
by apply/eqP; apply: contraNT hSv => /(sim_supp0 (hcons y hF))/eqP.
Qed.

(* At an input where the two joint laws agree, the simulator reads off to
   every delivered output the functionality reaches at that input.
   Naming: _at_input names the single input the premise is taken at, as
   entropy_link spells out the conditioner of a one-point statement. *)
Lemma pair_eq_consistent_at_input (Sim : Xa * Ya -> R.-fdist Bv) (x : X) :
  real_pair x = ideal_pair_of Sim x ->
  forall y, fdistmap proj_ya (F x) y != 0 ->
  fdistmap out_adv (Sim (proj_xa x, y)) = fdist1 y.
Proof.
move=> hpair y /fdistmap_neq0P[y0 hy0 hFy0].
have hread : forall v, Sim (proj_xa x, y) v != 0 -> out_adv v = y.
  move=> v hSv; rewrite -hy0; apply: (real_pair_readoff (x := x)).
  by rewrite hpair ideal_pair_ofE/= hy0 mulf_neq0.
apply/eqP; rewrite -fdist1E1; apply/fdist1P => y' y'ne; apply/eqP.
by apply: contraNT y'ne => /fdistmap_neq0P[v /esym -> /hread ->].
Qed.

(* Under delivery-law correctness, a simulator whose ideal joint law is the
   real joint law at every input is consistent. *)
Lemma pair_eq_consistent (Sim : Xa * Ya -> R.-fdist Bv) :
  delivery_law_ok F P_Omega run -> pair_eq Sim ->
  consistent proj_xa proj_ya P_Omega run out_adv mu Sim.
Proof.
move=> hdel hpair a y; rewrite -dist_of_RVE /dist_of_RV.
case/fdistmap_neq0P => -[x w] [/= hxa hya].
rewrite fdist_prodE mulf_eq0 negb_or => /andP[_ hPw]; rewrite -hxa.
apply: (pair_eq_consistent_at_input (hpair x)).
by rewrite -(hdel x) fdistmap_comp -hya; exact: fdistmap_neq0 hPw.
Qed.

(* The delivered-output marginal of the real joint law is the real delivered
   law.
   Naming: main symbol real_pair, snd_marginal for the marginal taken and E
   for the closed form, the spelling of the landed pair family. *)
Lemma snd_marginal_real_pairE (x : X) :
  fdistmap snd (real_pair x) = fdistmap (fun w => run (x, w)) P_Omega.
Proof. by rewrite /real_pair fdistmap_comp; apply: eq_fdistmap. Qed.

(* The view marginal of the real joint law is the real view law. *)
Lemma fst_marginal_real_pairE (x : X) :
  fdistmap fst (real_pair x) = fdistmap (fun w => view_at (x, w)) P_Omega.
Proof. by rewrite /real_pair fdistmap_comp; apply: eq_fdistmap. Qed.

(* The delivered-output marginal of the ideal joint law is the ideal
   functionality. *)
Lemma snd_marginal_ideal_pairE (Sim : Xa * Ya -> R.-fdist Bv) (x : X) :
  fdistmap snd (ideal_pair_of Sim x) = F x.
Proof.
rewrite /ideal_pair_of fdistmap_bind -[RHS]fdistbind1.
congr (fdistbind _ _); apply/boolp.funext => y.
by rewrite tensor_fdist1r fdistmap_comp; apply: eq_fdistmap_cst.
Qed.

(* The view marginal of the ideal joint law is the allowed-information law
   bound through the simulator. *)
Lemma fst_marginal_ideal_pairE (Sim : Xa * Ya -> R.-fdist Bv) (x : X) :
  fdistmap fst (ideal_pair_of Sim x)
  = (fdistmap (fun yl => (proj_xa x, proj_ya yl)) (F x)) >>= Sim.
Proof.
rewrite /ideal_pair_of fdistmap_bind [in RHS]/fdistmap fdistbindA.
congr (fdistbind _ _); apply/boolp.funext => y; rewrite fdist1bind.
by rewrite tensor_fdist1r fdistmap_comp -[RHS]fdistmap_id; apply: eq_fdistmap.
Qed.

(* The joint equality gives the delivery law.
   Naming: main symbol pair_eq, the hypothesis the lemma consumes, then the
   delivery_law_ok condition it concludes. *)
Lemma pair_eq_delivery_law (Sim : Xa * Ya -> R.-fdist Bv) :
  pair_eq Sim -> delivery_law_ok F P_Omega run.
Proof.
by move=> hpair x;
   rewrite -snd_marginal_real_pairE hpair snd_marginal_ideal_pairE.
Qed.

(* The joint equality gives the privacy triangle. *)
Lemma pair_eq_triangle (Sim : Xa * Ya -> R.-fdist Bv) :
  pair_eq Sim -> triangle proj_xa proj_ya F P_Omega view_at Sim.
Proof.
by move=> hpair x;
   rewrite -fst_marginal_real_pairE hpair fst_marginal_ideal_pairE.
Qed.

(* The joint law of the input with an observable of the real joint pair.
   Naming: main symbol pfwd1, then the two random variables of the statement,
   the second read off real_pair. *)
Lemma pfwd1_input_real_pair (T : finType) (k : Bv * Yfull -> T) (x : X)
    (t : T) :
  `Pr[ [% input_rv, ((fun e => k (view_at e, run e)) : {RV d -> T})] = (x, t) ]
  = mu x * fdistmap k (real_pair x) t.
Proof.
by rewrite (pfwd1_input_pair P_Omega mu (fun e => k (view_at e, run e)) x t)
   /real_pair fdistmap_comp.
Qed.

(* The ideal joint law transported along the view, the honest delivered output
   and the adversary delivered output.
   Naming: main symbol fdistmap, the law it transports ideal_pair_of, and E
   for the closed form. *)
Lemma fdistmap_ideal_pair_ofE (Sim : Xa * Ya -> R.-fdist Bv) (x : X)
    (v : Bv) (h : Yh) (s : Ya) :
  fdistmap (fun q : Bv * Yfull => ((q.1, proj_yh q.2), proj_ya q.2))
           (ideal_pair_of Sim x) ((v, h), s)
  = (\sum_(y | (proj_ya y == s) && (proj_yh y == h)) F x y)
    * Sim (proj_xa x, s) v.
Proof.
rewrite fdistmapE; under eq_bigr do rewrite ideal_pair_ofE.
rewrite (reindex_onto (fun y : Yfull => (v, y)) snd)/=; last first.
  by move=> [v' y]; rewrite unfold_in/= !xpair_eqE => /andP[/andP[/eqP -> _] _].
rewrite big_distrl/=; apply: eq_big => y.
  by rewrite eqxx andbT unfold_in/= !xpair_eqE eqxx/= andbC.
by rewrite eqxx andbT unfold_in/= !xpair_eqE eqxx/= => /andP[_ /eqP ->].
Qed.

(* Under the joint equality the law of the view, the honest delivered output,
   the input and the adversary delivered output factors through the
   simulator.
   Naming: main symbol pfwd1, then the four random variables of the statement
   in the order they occur; _cond is reserved for cond_rv. *)
Lemma pfwd1_view_yh_input_ya (Sim : Xa * Ya -> R.-fdist Bv) (v : Bv) (h : Yh)
    (x : X) (s : Ya) :
  pair_eq Sim ->
  `Pr[ [% [% view_rv, yh_rv], [% input_rv, ya_rv]] = ((v, h), (x, s)) ]
  = (mu x * \sum_(y | (proj_ya y == s) && (proj_yh y == h)) F x y)
    * Sim (proj_xa x, s) v.
Proof.
move=> hpair.
transitivity (`Pr[ [% input_rv, ((fun e => ((view_at e, proj_yh (run e)),
  proj_ya (run e))) : {RV d -> ((Bv * Yh) * Ya)%type})] = (x, ((v, h), s)) ]).
  by apply: pfwd1_congr_preim => u; rewrite !xpair_eqE/= andbCA.
rewrite (pfwd1_input_real_pair
  (fun q : Bv * Yfull => ((q.1, proj_yh q.2), proj_ya q.2))).
by rewrite hpair fdistmap_ideal_pair_ofE mulrA.
Qed.

(* The joint equality gives output independence.
   Naming: main symbol pair_eq, the hypothesis the lemma consumes, then the
   output_independent condition it concludes. *)
Lemma pair_eq_output_independent (Sim : Xa * Ya -> R.-fdist Bv) :
  pair_eq Sim -> output_independent proj_ya proj_yh P_Omega view_at run mu.
Proof.
move=> hpair; apply: (cinde_RV_factor
  (f := fun (h : Yh) (c : X * Ya) =>
          mu c.1 * \sum_(y | (proj_ya y == c.2) && (proj_yh y == h)) F c.1 y)
  (g := fun (c : X * Ya) (v : Bv) => Sim (proj_xa c.1, c.2) v)).
by move=> v h [x s]; exact: pfwd1_view_yh_input_ya.
Qed.

(* The split of a delivered output into the adversary's and the honest
   parties' parts. *)
Let split_y (y : Yfull) := (proj_ya y, proj_yh y).

(* The delivered output is determined by its adversary and honest parts. *)
Hypothesis split_y_inj : injective split_y.

(* Two delivered outputs are equal exactly when their adversary parts and
   their honest parts are.
   Naming: main symbol split_y and E for the closed form its injectivity
   gives the equality test. *)
Lemma split_y_eqE (y1 y2 : Yfull) :
  (y1 == y2) = (proj_ya y1 == proj_ya y2) && (proj_yh y1 == proj_yh y2).
Proof.
by rewrite -xpair_eqE -/(split_y y1) -/(split_y y2) (inj_eq split_y_inj).
Qed.

(* Under delivery-law correctness the honest delivered output paired with the
   input and the adversary delivered output has the law of the input times the
   ideal functionality.
   Naming: main symbol pfwd1, the three random variables of the statement and
   the delivery law the closed form consumes. *)
Lemma pfwd1_yh_input_ya_delivery (x : X) (y : Yfull) :
  delivery_law_ok F P_Omega run ->
  `Pr[ [% yh_rv, [% input_rv, ya_rv]] = (proj_yh y, (x, proj_ya y)) ]
  = mu x * F x y.
Proof.
move=> hdel.
transitivity (`Pr[ [% input_rv, (run : {RV d -> Yfull})] = (x, y) ]).
  apply: pfwd1_congr_preim => u; rewrite !xpair_eqE/= (split_y_eqE (run u) y).
  by rewrite andbCA [X in _ && X]andbC.
by rewrite (pfwd1_input_pair P_Omega mu run) (hdel x).
Qed.

(* The view paired with the honest delivered output, the input and the
   adversary delivered output has the law of the input times the real joint
   law.
   Naming: main symbol pfwd1, the four random variables of the statement and
   the real_pair the closed form is stated in. *)
Lemma pfwd1_view_yh_real_pair (x : X) (v : Bv) (y : Yfull) :
  `Pr[ [% [% view_rv, yh_rv], [% input_rv, ya_rv]]
       = ((v, proj_yh y), (x, proj_ya y)) ]
  = mu x * real_pair x (v, y).
Proof.
transitivity (`Pr[ [% input_rv, ((fun e => (view_at e, run e))
                     : {RV d -> (Bv * Yfull)%type})] = (x, (v, y)) ]).
  apply: pfwd1_congr_preim => u; rewrite !xpair_eqE/= (split_y_eqE (run u) y).
  by rewrite andbCA -andbA [X in _ && (_ && X)]andbC.
by rewrite (pfwd1_input_pair P_Omega mu (fun e => (view_at e, run e))).
Qed.

(* The delivery law, a consistent simulator closing the privacy triangle and
   output independence give the joint equality.
   Naming: the consumed conditions come first and the conclusion pair_eq
   second, the order of entropy.v's cinde_centropy_eq. *)
Lemma conditions_pair_eq (Sim : Xa * Ya -> R.-fdist Bv) :
  delivery_law_ok F P_Omega run ->
  consistent proj_xa proj_ya P_Omega run out_adv mu Sim ->
  triangle proj_xa proj_ya F P_Omega view_at Sim ->
  output_independent proj_ya proj_yh P_Omega view_at run mu ->
  pair_eq Sim.
Proof.
move=> hdel hcons htri hind x; apply/fdist_ext => -[v y].
rewrite ideal_pair_ofE/=; have [hF|hF] := eqVneq (F x y) 0.
  rewrite hF mul0r; apply: (fdistmap_eq0 (f := snd)).
  by rewrite snd_marginal_real_pairE (hdel x).
have hC : `Pr[ [% input_rv, ya_rv] = (x, proj_ya y) ] != 0.
  rewrite (pfwd1_input_pair P_Omega mu (fun e => proj_ya (run e))).
  apply: mulf_neq0; first exact: mu_full.
  have -> : fdistmap (fun w => proj_ya (run (x, w))) P_Omega
          = fdistmap proj_ya (F x) by rewrite -(hdel x) fdistmap_comp.
  exact: fdistmap_neq0 hF.
apply: (mulfI (mu_full x)); rewrite -pfwd1_view_yh_real_pair.
have h1 := hind v (proj_yh y) (x, proj_ya y).
rewrite (triangle_cond_component readoff mu_full hdel hcons htri hC v)
        !cpr_eqE in h1.
rewrite -[LHS](divfK hC) h1 -mulrA (divfK hC).
by rewrite (pfwd1_yh_input_ya_delivery _ _ hdel) mulrC mulrA.
Qed.

(* The joint equality at a simulator is the conjunction of the delivery law,
   the consistency of that simulator, the privacy triangle at that simulator
   and output independence.
   Naming: P = iff characterization, ffunP/setP precedent. *)
Lemma pair_eqP (Sim : Xa * Ya -> R.-fdist Bv) :
  pair_eq Sim
  <-> [/\ delivery_law_ok F P_Omega run,
          consistent proj_xa proj_ya P_Omega run out_adv mu Sim,
          triangle proj_xa proj_ya F P_Omega view_at Sim
        & output_independent proj_ya proj_yh P_Omega view_at run mu].
Proof.
split=> [hpair|[hdel hcons htri hind]]; last exact: conditions_pair_eq.
split; [exact: pair_eq_delivery_law hpair
       |exact: pair_eq_consistent (pair_eq_delivery_law hpair) hpair
       |exact: pair_eq_triangle hpair|exact: pair_eq_output_independent hpair].
Qed.

(* A simulator making the two joint laws agree exists exactly when the
   delivery law holds and some simulator is consistent, closes the privacy
   triangle and has output independence.
   Naming: the exists_ prefix of the file's existential statements, P = iff
   characterization. *)
Lemma exists_pair_eqP :
  (exists Sim, pair_eq Sim)
  <-> delivery_law_ok F P_Omega run /\
      (exists Sim, [/\ consistent proj_xa proj_ya P_Omega run out_adv mu Sim,
                       triangle proj_xa proj_ya F P_Omega view_at Sim
                     & output_independent proj_ya proj_yh P_Omega view_at run
                                          mu]).
Proof.
split=> [[Sim /pair_eqP[h1 h2 h3 h4]]|[hdel [Sim [hcons htri hind]]]].
  by split=> //; exists Sim; split.
by exists Sim; apply/pair_eqP; split.
Qed.

(* The split of an input into the adversary's and the honest parties' parts is
   injective. *)
Hypothesis split_x_inj : injective (fun x => (proj_xa x, proj_xh x)).

(* A simulator making the two joint laws agree exists exactly when the
   delivery law holds and the view leaves the conditional entropy of the
   honest pair given the allowed information unchanged.
   Naming: the exists_ prefix of the file's existential statements, the two
   sides pair_eq and centropy, P = iff characterization. *)
Lemma exists_pair_eq_centropyP :
  (exists Sim, pair_eq Sim)
  <-> delivery_law_ok F P_Omega run /\
      `H( [% xh_rv, yh_rv] | [% view_rv, [% xa_rv, ya_rv]] )
      = `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ).
Proof.
have hP := perfect_privacy_centropyP proj_yh readoff mu_full split_x_inj.
split=> [/exists_pair_eqP[hdel hsim]|[hdel hH]]; last first.
  by apply/exists_pair_eqP; split=> //; apply: (hP _ _ hdel).2.
by split=> //; apply: (hP _ _ hdel).1.
Qed.

(* A simulator making the two joint laws agree exists exactly when the
   delivery law holds and the conditional mutual information of the view and
   the honest pair given the allowed information vanishes.
   Naming: the exists_ prefix of the file's existential statements, the two
   sides pair_eq and cond_mutual_info with the value 0 it takes, P = iff
   characterization. *)
Lemma exists_pair_eq_cond_mutual_info0P :
  (exists Sim, pair_eq Sim)
  <-> delivery_law_ok F P_Omega run /\
      cond_mutual_info `p_[% view_rv, [% xh_rv, yh_rv], [% xa_rv, ya_rv]] = 0.
Proof.
have hP := perfect_privacy_cond_mutual_info0P proj_yh readoff mu_full
             split_x_inj.
split=> [/exists_pair_eqP[hdel hsim]|[hdel hI]]; last first.
  by apply/exists_pair_eqP; split=> //; apply: (hP _ _ hdel).2.
by split=> //; apply: (hP _ _ hdel).1.
Qed.

End pair_readoff.
End pair_readoff.

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
