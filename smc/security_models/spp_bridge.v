(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid spp_proba spp_entropy.
Require Import smc_interpreter spp_tactics smc_session_types.
Require Import spp_interface spp_program spp_pismc spp_proof spp_simulator.

(**md**************************************************************************)
(* # The scalar-product protocol as a privacy-kernel instance                 *)
(*                                                                            *)
(* A random variable whose conditional law on every mass-carrying fibre of a  *)
(* second random variable is a kernel at that fibre has, as its own law, the  *)
(* law of the second variable bound through the kernel.  Applied to the       *)
(* corrupted-Bob view of the scalar-product protocol this turns the           *)
(* conditional-law statement of the privacy triangle into the factorization   *)
(* of the view law through Bob's inputs, and applied to the delivered output  *)
(* shares it turns the protocol's independence and uniformity facts into the  *)
(* delivery-law equality between the real and the ideal share laws.           *)
(*                                                                            *)
(* ```                                                                        *)
(*       dist_of_RV_bind == a variable whose conditional law on every         *)
(*                          mass-carrying fibre of a second variable is a     *)
(*                          kernel has the law of that second variable bound  *)
(*                          through the kernel                               *)
(* spp_bob_factorization == the corrupted-Bob view law is the law of Bob's    *)
(*                          inputs bound through the simulator                *)
(*       spp_alice_share == Alice's delivered share is the scalar product of  *)
(*                          the two inputs less Bob's share                   *)
(*   spp_ideal_share_law == the ideal share law at a pair of inputs: Bob's    *)
(*                          share uniform, Alice's its complement in the      *)
(*                          scalar product                                    *)
(*  spp_ideal_share_lawE == the ideal share law is the uniform mass of Bob's  *)
(*                          share cut down to the complementary pair          *)
(*          spp_y2_indep == Bob's output share is independent of the two      *)
(*                          inputs                                            *)
(*   spp_delivery_law_ok == the delivered share pair conditioned on a pair of *)
(*                          inputs of positive mass is the ideal share law    *)
(*      spp_delivery_law == the law of the delivered share pair is the input  *)
(*                          law bound through the ideal share law             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

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

Section bridge_shape.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (B K : finType).
Variable V : {RV P -> B}.
Variable Kv : {RV P -> K}.
Variable k : K -> R.-fdist B.

(* eq:smc:simulation *)
(* The law of a variable whose conditional law on every mass-carrying fibre
   of a second variable is the kernel at that fibre is the law of the second
   variable bound through the kernel.
   Naming: mainSymbols of the conclusion, dist_of_RV for `p_ and bind for
   >>=; the conversion-function idiom _to_ is reserved in this development
   for maps such as party_to_kernel. *)
Lemma dist_of_RV_bind :
  (forall kk : K, `Pr[ Kv = kk ] != 0 ->
     forall v : B, `Pr[ V = v | Kv = kk ] = k kk v) ->
  `p_ V = `p_ Kv >>= k.
Proof.
move=> H; apply/fdist_ext => v.
rewrite fdistbindE -(fst_RV2 V Kv) fdist_fstE.
apply: eq_bigr => kk _; rewrite !dist_of_RVE.
case: (eqVneq `Pr[ Kv = kk ] 0) => [Hz|Hnz].
  by rewrite Hz mul0r pfwd1_domin_RV1.
by rewrite -H // cpr_eqE mulrC divfK.
Qed.

End bridge_shape.

Section spp_bob_bridge.
Context {R : realType}.
Variables (T : finType) (m n : nat).
Variable P : R.-fdist T.

Let TX := [the finComNzRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

(* The uniform law over the scalars, built from the cardinality of
   spp_proof.v so the fdist_uniform proof term matches the one the input
   record carries. *)
Let unif_TX : R.-fdist TX := fdist_uniform (card_TX m).

Variable inputs : scalar_product_random_inputs n m P.

(* The protocol variables of spp_proof.v: the two inputs x1, x2, the pads
   s1, s2, r1, Bob's output share y2, the masked inputs x1', x2', the
   recombined pad r2, Bob's message t, Alice's output share y1 and the
   corrupted-Bob view.  They are section-local there, so they are restated
   here; each is definitionally the term the du2002 lemmas are stated at. *)
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
Let BobView := [% x2, s2, x1', r2, y2].

(* eq:smc:simulation, fig:infotheo:spp-triangle *)
(* The law of the corrupted-Bob view is the law of Bob's inputs bound
   through the simulator. *)
Theorem spp_bob_factorization :
  `p_ BobView = `p_ [% x2, y2] >>= (fun ay => bob_simulator ay.1 ay.2).
Proof.
by apply: dist_of_RV_bind => -[b y] Hby v; exact: bob_view_cond_sim_xy.
Qed.

(* Alice's delivered share is the scalar product of the two inputs less
   Bob's share. *)
Lemma spp_alice_share : y1 = (x1 \*d x2) \- y2.
Proof.
apply/boolp.funext => u.
rewrite /y1 /t /r2 /x1' /x2' /dotproduct_rv /=.
rewrite (dot_productC (x1 u + s1 u) (x2 u)) dot_productDr.
rewrite (dot_productC (x2 u + s2 u) (s1 u)) dot_productDr.
rewrite (dot_productC (x2 u) (x1 u)) (dot_productC (x2 u) (s1 u)).
by ring.
Qed.

(* The share law the ideal functionality prescribes at a pair of inputs:
   Bob's share uniform, Alice's its complement in the scalar product.
   Naming: the spp_ prefix names the protocol this file instantiates, the
   role prefixes alice_ and bob_ being taken by du2002/spp_simulator.v. *)
Definition spp_ideal_share_law (a b : VX) : R.-fdist (TX * TX) :=
  fdistmap (fun s : TX => (a *d b - s, s)) unif_TX.

(* The ideal share law is the uniform mass of Bob's share cut down to the
   pairs whose first coordinate completes the scalar product. *)
Lemma spp_ideal_share_lawE a b u s :
  spp_ideal_share_law a b (u, s) = (u == a *d b - s)%:R * unif_TX s.
Proof.
rewrite /spp_ideal_share_law fdistmapE.
under eq_bigl => s' do rewrite !inE /= xpair_eqE andbC.
by rewrite big_mkcondr big_pred1_eq eq_sym mulr_natl mulrb.
Qed.

(* Bob's output share is independent of the two inputs. *)
Lemma spp_y2_indep : P |= [% x1, x2] _|_ y2.
Proof.
have := y2_indep inputs.
pose f := fun (w : (VX * VX * VX * VX * TX)%type) =>
  let '(xb, _, xa, _, _) := w in (xa, xb).
pose g := fun (w : TX) => w.
by apply_inde_rv_comp f g.
Qed.

(* The delivered share pair conditioned on a pair of inputs of positive mass
   is the ideal share law at that pair, the instance of the delivery-law
   condition delivery_law_ok of entropy_link.v.
   Naming: the _ok suffix carries over from that condition. *)
Theorem spp_delivery_law_ok a b :
  `Pr[ [% x1, x2] = (a, b) ] != 0 ->
  forall v, `Pr[ [% y1, y2] = v | [% x1, x2] = (a, b) ]
            = spp_ideal_share_law a b v.
Proof.
move=> Hab [u s].
rewrite cpr_eqE spp_ideal_share_lawE.
have Hy1 w : y1 w = x1 w *d x2 w - y2 w by rewrite spp_alice_share.
(* On the input event the delivered pair carries one degree of freedom, so
   the joint mass is the mass of Bob's share cut by the Dirac indicator of
   Alice's. *)
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
(* Conditioning Bob's share on the inputs cancels the denominator by
   independence and returns its uniform marginal. *)
rewrite Hnum -mulrA; congr (_ * _).
have /inde_RV_sym Hsym := spp_y2_indep.
rewrite (Hsym s (a, b)) mulfK //.
by rewrite -dist_of_RVE (py2_unif inputs).
Qed.

(* The law of the delivered share pair is the law of the two inputs bound
   through the ideal share law. *)
Theorem spp_delivery_law :
  `p_ [% y1, y2] = `p_ [% x1, x2] >>= (fun ab => spp_ideal_share_law ab.1 ab.2).
Proof.
by apply: dist_of_RV_bind => -[a b] Hab v; exact: spp_delivery_law_ok.
Qed.

End spp_bob_bridge.
