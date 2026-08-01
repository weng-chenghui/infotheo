(* Mutation 2 of probe_spp_bridge_r10.v: the delivery-law instance drops
   the positive-mass guard on the input pair.  coqc must exit 1.          *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid spp_proba spp_entropy.
Require Import smc_interpreter spp_tactics smc_session_types.
Require Import spp_interface spp_program spp_pismc spp_proof spp_simulator.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope vec_ext_scope.

Section spp_bob_bridge.
Context {R : realType}.
Variables (T : finType) (m n : nat).
Variable P : R.-fdist T.

Let TX := [the finComNzRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Let unif_TX : R.-fdist TX := fdist_uniform (card_TX m).

Variable inputs : scalar_product_random_inputs n m P.

Let x1 := x1 inputs.
Let x2 := x2 inputs.
Let s1 := s1 inputs.
Let s2 := s2 inputs.
Let r1 := r1 inputs.
Let y2 := y2 inputs.
Let x1' : {RV P -> VX} := x1 \+ s1.
Let x2' : {RV P -> VX} := x2 \+ s2.
Let r2 : {RV P -> TX} := (s1 \*d s2) \- r1.
Let t : {RV P -> TX} := x1' \*d x2 \+ r2 \- y2.
Let y1 : {RV P -> TX} := t \- (x2' \*d s1) \+ r1.

Lemma spp_alice_share : y1 = (x1 \*d x2) \- y2.
Proof.
apply/boolp.funext => u.
rewrite /y1 /t /r2 /x1' /x2' /dotproduct_rv /=.
rewrite (dot_productC (x1 u + s1 u) (x2 u)) dot_productDr.
rewrite (dot_productC (x2 u + s2 u) (s1 u)) dot_productDr.
rewrite (dot_productC (x2 u) (x1 u)) (dot_productC (x2 u) (s1 u)).
by ring.
Qed.

Definition spp_ideal_share_law (a b : VX) : R.-fdist (TX * TX) :=
  fdistmap (fun s : TX => (a *d b - s, s)) unif_TX.

Lemma spp_ideal_share_lawE a b u s :
  spp_ideal_share_law a b (u, s) = (u == a *d b - s)%:R * unif_TX s.
Proof.
rewrite /spp_ideal_share_law fdistmapE.
under eq_bigl => s' do rewrite !inE /= xpair_eqE andbC.
by rewrite big_mkcondr big_pred1_eq eq_sym mulr_natl mulrb.
Qed.

Lemma spp_y2_indep : P |= [% x1, x2] _|_ y2.
Proof.
have := y2_indep inputs.
pose f := fun (w : (VX * VX * VX * VX * TX)%type) =>
  let '(xb, _, xa, _, _) := w in (xa, xb).
pose g := fun (w : TX) => w.
by apply_inde_rv_comp f g.
Qed.

(* MUTATION: no `Pr[ [% x1, x2] = (a, b) ] != 0 hypothesis. *)
Theorem spp_delivery_law_ok a b :
  forall v, `Pr[ [% y1, y2] = v | [% x1, x2] = (a, b) ]
            = spp_ideal_share_law a b v.
Proof.
move=> [u s].
rewrite cpr_eqE spp_ideal_share_lawE.
have Hy1 w : y1 w = x1 w *d x2 w - y2 w by rewrite spp_alice_share.
have Hnum : pfwd1 [% [% y1, y2], [% x1, x2]] ((u, s), (a, b))
  = (u == a *d b - s)%:R * pfwd1 [% y2, [% x1, x2]] (s, (a, b)).
  case: (altP (u =P a *d b - s)) => [Eu|Eu]; last first.
    rewrite mul0r pfwd1E (_ : finset _ = set0) ?Pr_set0 //.
    apply/setP => w; rewrite !inE.
    apply/negbTE; apply: contra Eu; rewrite !xpair_eqE.
    by move=> /and3P[/andP[/eqP <- /eqP <-] /eqP <- /eqP <-]; rewrite Hy1.
  rewrite mul1r Eu !pfwd1E; congr (Pr P _).
  apply/setP => w; rewrite !inE !xpair_eqE.
  by case: (altP (x1 w =P a)) => [Ea|]; case: (altP (x2 w =P b)) => [Eb|];
     case: (altP (y2 w =P s)) => [Es|];
     rewrite ?andbF ?andbT //= Hy1 Ea Eb Es eqxx.
rewrite Hnum -mulrA; congr (_ * _).
have Hsym := (proj1 (@inde_RV_sym _ _ _ _ _ _ _) spp_y2_indep).
rewrite (Hsym s (a, b)) mulfK //.
by rewrite -dist_of_RVE (py2_unif inputs).
Qed.

End spp_bob_bridge.
