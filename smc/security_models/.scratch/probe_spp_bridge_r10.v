(* Probe R10 — the SPP corrupted-Bob bridge, in the du2002 import closure.
   T1: dist_of_RV_bind, the probe-P4 shape lemma under its audited name
       (probe_spp_bridge_shape.v:35, body verbatim).
   T2: spp_bob_factorization, the marginal form of the privacy triangle,
       from bob_view_cond_sim_xy through T1.
   T3 (spec C8): spp_delivery_law_ok / spp_delivery_law, the SPP instance
       of the delivery-law hypothesis of entropy_link.v.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_spp_bridge_r10.v              *)

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

Section bridge_shape.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (B K : finType).
Variable V : {RV P -> B}.
Variable Kv : {RV P -> K}.
Variable k : K -> R.-fdist B.

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
Let BobView := [% x2, s2, x1', r2, y2].

Theorem spp_bob_factorization :
  `p_ BobView = `p_ [% x2, y2] >>= (fun ay => bob_simulator ay.1 ay.2).
Proof.
apply: dist_of_RV_bind => -[b y] Hby v.
exact: bob_view_cond_sim_xy Hby.
Qed.

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

Theorem spp_delivery_law_ok a b :
  `Pr[ [% x1, x2] = (a, b) ] != 0 ->
  forall v, `Pr[ [% y1, y2] = v | [% x1, x2] = (a, b) ]
            = spp_ideal_share_law a b v.
Proof.
move=> Hab [u s].
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
have /inde_RV_sym Hsym := spp_y2_indep.
rewrite (Hsym s (a, b)) mulfK //.
by rewrite -dist_of_RVE (py2_unif inputs).
Qed.

Theorem spp_delivery_law :
  `p_ [% y1, y2] = `p_ [% x1, x2] >>= (fun ab => spp_ideal_share_law ab.1 ab.2).
Proof.
apply: dist_of_RV_bind => -[a b] Hab v.
exact: spp_delivery_law_ok Hab v.
Qed.

End spp_bob_bridge.

Print Assumptions dist_of_RV_bind.
Print Assumptions spp_bob_factorization.
Print Assumptions spp_alice_share.
Print Assumptions spp_ideal_share_lawE.
Print Assumptions spp_y2_indep.
Print Assumptions spp_delivery_law_ok.
Print Assumptions spp_delivery_law.

(* FINDINGS
   1. du2002/spp_simulator.vo was NOT stale at the time of this probe: the
      whole chain rebuilt during the proba.v/entropy.v upstreaming of tasks
      R1/R2, so `make -f Makefile.coq -j1 du2002/spp_simulator.vo` reports
      "is up to date" and the preamble loads.
   2. The notations *d (dotproduct) and \*d (dotproduct_rv) are already
      global in this import closure; the local Notation lines of
      spp_simulator.v are not needed here.
   3. bob_simulator, bob_view_cond_sim_xy and the record
      scalar_product_random_inputs discharge over R, m, n (and T, P, inputs
      for the lemma), in the argument order n then m, so the section header
      of spp_proof.v has to be mirrored exactly: Variables (T : finType)
      (m n : nat) with scalar_product_random_inputs n m P.
   4. x1', x2', r2, t, y1 and BobView are Let-bound inside spp_proof.v and
      spp_simulator.v, hence invisible after End; they are restated here
      with the same bodies, which makes them the very terms the du2002
      lemmas are stated at (spp_bob_factorization closes by exact:).
   5. `p_ V = `p_ Kv >>= k is reached from the conditional-law form by
      dist_of_RV_bind alone; no other glue was needed for the triangle.
   6. Alice's delivered share needs the dot-product normalization of
      smc_scalar_product_is_correct (dot_productC then dot_productDr, twice)
      before ring closes; ring alone does not see through *d.
   7. inde_RV_sym is an iff, so the symmetric direction is best taken as a
      view: have /inde_RV_sym Hsym := spp_y2_indep.

   AXIOMS
   All seven results rest on boolp.propositional_extensionality,
   boolp.functional_extensionality_dep and
   boolp.constructive_indefinite_description, and on nothing else.  The
   du2002 closure adds no axiom of its own.

   MUTATION CHECKS, copies kept in this directory
   1. probe_spp_bridge_r10_mut1.v turns the ideal share law into
      a *d b + s; coqc exits 1 at the Hnum step of spp_delivery_law_ok with
      Error: No applicable tactic, because Alice's real share is the
      complement, not the sum.
   2. probe_spp_bridge_r10_mut2.v drops the positive-mass guard on the
      input pair; coqc exits 1 with Attempt to save an incomplete proof,
      the mulfK step having no nonzero denominator.  On a zero-mass input
      pair the conditional law is identically 0 while the ideal share law
      has total mass 1, so the guard is not removable; the shape-level
      counterexample for the same guard is probe_spp_bridge_shape_mut3.v.
   3. probe_spp_bridge_r10_mut3.v feeds the simulator ay.2 + 1 in place of
      ay.2; coqc exits 1 with Cannot apply lemma bob_view_cond_sim_xy.    *)
