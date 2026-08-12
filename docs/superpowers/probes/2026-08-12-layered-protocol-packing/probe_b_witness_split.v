(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe B: the security witness split into a bound layer and a bundle layer  *)
(*                                                                            *)
(* Stage A/B of the layered-packing refactor replaces the six-field record    *)
(* SecurityWitness (algebraic_rigidity.v:147-157) by two records:             *)
(*   ShuffleMarginalBound      the always-present marginal bound (4 fields)   *)
(*   ShuffleCertificateBundle  that bound plus the two optional certificates  *)
(* SecurityExact and SecurityAsymptotic are preserved unchanged.              *)
(*                                                                            *)
(* Module WS below carries the two revised records with the production field  *)
(* names sw_* and scb_*, the two lossless converters from the old record,     *)
(* one value per migration bucket, the four mirrored core records with their  *)
(* values, the two consumer access patterns, and the five witness-tie         *)
(* restatements of section 15.2 of the design.                                *)
(*                                                                            *)
(* Measured claims (all confirmed unless stated otherwise in the report):     *)
(*                                                                            *)
(*  1. THE MIGRATION IS MECHANICAL. bundle_of_witness typechecks with no cast *)
(*     and no transport: the rho index of scb_exact accepts the old sw_exact  *)
(*     unchanged, because sw_rho_dist (bound_of_witness w) is convertible to  *)
(*     algebraic_rigidity.sw_rho_dist w by iota reduction alone.              *)
(*                                                                            *)
(*  2. THE OPTIONAL SLOTS SURVIVE PROJECTION DEFINITIONALLY. Every bucket's   *)
(*     scb_exact / scb_asymptotic equation closes by [].                      *)
(*                                                                            *)
(*  3. THE CONSUMER PATTERNS TRANSCRIBE. dealer_words_epsilon_bound and       *)
(*     security_per_position keep the proof exact: sw_bound once the projection*)
(*     chain gains scb_bound.                                                 *)
(*                                                                            *)
(*  4. THE FIVE WITNESS TIES KEEP THEIR PROOF SCRIPTS, modulo replacing the   *)
(*     /den_boer_profile and mp_security unfolds by the bound value's own     *)
(*     /bound_of_witness unfold.                                              *)
(*                                                                            *)
(* One elaboration adjustment was forced and is recorded at its site: under   *)
(* Set Implicit Arguments the field scb_bound is inferable from the type of   *)
(* scb_exact, so MkShuffleCertificateBundle makes it implicit; the two        *)
(* Arguments lines below restore the request's three-explicit-argument shape. *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_sample_adapter.
From pgg_smc Require Import pgg_weighted_words pgg_schreier.
From pgg_smc Require Import perm_uniform pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_security_solver.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity
                                    combinatorial_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace five_card_exec.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_word_privacy pgl27_exec.
From pgg_smc Require Import rigidity_s5_instance rigidity_s5x5_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

Module WS.

(******************************************************************************)
(*     The two revised records                                                *)
(******************************************************************************)

(** ShuffleMarginalBound — the single-position marginal bound of a shuffle
    distribution against the uniform distribution on sheets.
    @intent: the four always-present fields of algebraic_rigidity.v:147-157,
    with the sw_bound statement copied verbatim from :151-154 with N'
    instantiated to pgg_N' M. *)
Record ShuffleMarginalBound (R : realType) (M : MonodromyReprWithGeneratorType)
  := MkShuffleMarginalBound {
  sw_L : nat;
  sw_bound_eps : R;
  sw_rho_dist : R.-fdist {perm 'I_(pgg_N' M).+1};
  sw_bound : forall s,
    (var_dist (fdistmap (fun sigma : {perm 'I_(pgg_N' M).+1} => sigma s)
                        sw_rho_dist)
              (fdist_uniform (card_ord (pgg_N' M).+1)) <= sw_bound_eps)%O }.

(** ShuffleCertificateBundle — a marginal bound together with the optional
    exact-equality and asymptotic-convergence certificates for the same
    shuffle distribution.
    @intent: the two optional fields of SecurityWitness, re-indexed on the
    bound's own sw_rho_dist. *)
Record ShuffleCertificateBundle (R : realType)
    (M : MonodromyReprWithGeneratorType) := MkShuffleCertificateBundle {
  scb_bound : ShuffleMarginalBound R M;
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  scb_asymptotic : option (@SecurityAsymptotic R M) }.

(* ELABORATION ADJUSTMENT (probe finding, reported verbatim).
   Without the two Arguments lines below the request's own body
     Definition shuffle_bundle_of_bound R M (b : ShuffleMarginalBound R M)
       : ShuffleCertificateBundle R M := MkShuffleCertificateBundle b None None.
   is rejected with

     In environment
     R : realType
     M : MonodromyReprWithGeneratorType
     b : ShuffleMarginalBound R M
     The term "b" has type "ShuffleMarginalBound R M"
     while it is expected to have type
      "option (SecurityExact (sw_rho_dist ?scb_bound))".

   Cause: scb_bound occurs in the type of scb_exact, so Set Implicit Arguments
   makes the constructor's first field implicit. The fix is a scope-free
   Arguments directive, not a change to the record; the same directive is
   needed on MkShuffleMarginalBound only to keep R and M implicit there. *)
Arguments MkShuffleMarginalBound {R M} _ _ _ _.
Arguments MkShuffleCertificateBundle {R M} _ _ _.
Arguments ShuffleMarginalBound R M : clear implicits.
Arguments ShuffleCertificateBundle R M : clear implicits.

(** shuffle_bundle_of_bound — the bundle carrying a bound and no certificate.
    @intent: the BOUND bucket's image in the bundle layer. *)
Definition shuffle_bundle_of_bound R M (b : ShuffleMarginalBound R M)
  : ShuffleCertificateBundle R M := MkShuffleCertificateBundle b None None.

(******************************************************************************)
(*     The two lossless converters                                            *)
(******************************************************************************)

(** bound_of_witness — the marginal bound of an old six-field witness.
    @intent: the four always-present fields of a SecurityWitness read as a
    ShuffleMarginalBound. *)
Definition bound_of_witness R M (w : SecurityWitness R M)
  : ShuffleMarginalBound R M :=
  MkShuffleMarginalBound (algebraic_rigidity.sw_L w)
    (algebraic_rigidity.sw_bound_eps w) (algebraic_rigidity.sw_rho_dist w)
    (algebraic_rigidity.sw_bound w).

(** bundle_of_witness — the certificate bundle of an old six-field witness.
    @intent: the whole SecurityWitness read as a ShuffleCertificateBundle. The
    old sw_exact is accepted at the new rho index with no cast: sw_rho_dist
    (bound_of_witness w) reduces to algebraic_rigidity.sw_rho_dist w. *)
Definition bundle_of_witness R M (w : SecurityWitness R M)
  : ShuffleCertificateBundle R M :=
  MkShuffleCertificateBundle (bound_of_witness w)
    (algebraic_rigidity.sw_exact w) (algebraic_rigidity.sw_asymptotic w).

(******************************************************************************)
(*     One value per migration bucket                                         *)
(******************************************************************************)

Section probe_values.
Variable R : realType.

(** s5_boundB — the BOUND bucket at the S_5 fiber witness.
    @intent: bound_of_witness applied to the L = 1 fiber-counted S_5 witness. *)
Definition s5_boundB := bound_of_witness (s5_security_witness_1 R).

(** pgl27_marginal_boundB — the marginal bound of the eight-card orbit shuffle.
    @intent: the bound half of pgl27_security, epsilon = 0 at L = 0. *)
Definition pgl27_marginal_boundB := bound_of_witness (pgl27_security R).

(** pgl27_security_bundleB — the EXACT bucket at PGL(2,7).
    @intent: the bound above with the exact-equality certificate attached. *)
Definition pgl27_security_bundleB := bundle_of_witness (pgl27_security R).

(** s5_schreier_bundleB — the ASYM bucket at the S_5 Schreier witness.
    @intent: the L = 286 spectral witness read as a bundle. *)
Definition s5_schreier_bundleB :=
  bundle_of_witness (s5_security_witness_schreier R 286).

(** pgl27_bundle_exact_someE — the exact slot survives bundling.
    @composes: pgl27_security_bundleB *)
Lemma pgl27_bundle_exact_someE :
  scb_exact pgl27_security_bundleB
  = algebraic_rigidity.sw_exact (pgl27_security R).
Proof. by []. Qed.

(** pgl27_bundle_exact_isSome — the PGL(2,7) bundle carries an exact slot.
    @composes: pgl27_security_bundleB *)
Lemma pgl27_bundle_exact_isSome : isSome (scb_exact pgl27_security_bundleB).
Proof. by []. Qed.

(** pgl27_bundle_asym_noneE — the PGL(2,7) bundle has no asymptotic slot.
    @composes: pgl27_security_bundleB *)
Lemma pgl27_bundle_asym_noneE : scb_asymptotic pgl27_security_bundleB = None.
Proof. by []. Qed.

(** s5_schreier_bundle_asymptoticE — the asymptotic slot survives bundling.
    @composes: s5_schreier_bundleB *)
Lemma s5_schreier_bundle_asymptoticE :
  scb_asymptotic s5_schreier_bundleB
  = algebraic_rigidity.sw_asymptotic (s5_security_witness_schreier R 286).
Proof. by []. Qed.

(** s5_schreier_bundle_asym_isSome — the S_5 spectral bundle carries an
    asymptotic slot.
    @composes: s5_schreier_bundleB *)
Lemma s5_schreier_bundle_asym_isSome :
  isSome (scb_asymptotic s5_schreier_bundleB).
Proof. by []. Qed.

(** s5_schreier_bundle_exact_noneE — the S_5 spectral bundle has no exact slot.
    @composes: s5_schreier_bundleB *)
Lemma s5_schreier_bundle_exact_noneE : scb_exact s5_schreier_bundleB = None.
Proof. by []. Qed.

End probe_values.

(******************************************************************************)
(*     The BOTH bucket: Kim's biased five-card family                         *)
(******************************************************************************)

Section probe_kim.
Variable R : realType.
Variable eps : R.
Hypothesis Hlt : (eps < 5%:R^-1)%R.
Hypothesis Hgt : (- (4%:R * 5%:R^-1) < eps)%R.
Hypothesis Hspec : (`|eps| < 4%:R / 5%:R)%R.
Variable L : nat.

(** fc_kim_marginal_boundB — the marginal bound of the biased five-card shuffle
    at bias eps and word length L.
    @intent: the bound half of fc_kim_security_witness. *)
Definition fc_kim_marginal_boundB :=
  bound_of_witness (fc_kim_security_witness Hlt Hgt Hspec L).

(** fc_kim_security_bundleB — the BOTH bucket at the five-card family.
    @intent: the bound above with both certificates attached. *)
Definition fc_kim_security_bundleB :=
  bundle_of_witness (fc_kim_security_witness Hlt Hgt Hspec L).

(** fc_kim_bundle_exactE — the exact slot survives bundling.
    @composes: fc_kim_security_bundleB *)
Lemma fc_kim_bundle_exactE :
  scb_exact fc_kim_security_bundleB
  = algebraic_rigidity.sw_exact (fc_kim_security_witness Hlt Hgt Hspec L).
Proof. by []. Qed.

(** fc_kim_bundle_asymptoticE — the asymptotic slot survives bundling.
    @composes: fc_kim_security_bundleB *)
Lemma fc_kim_bundle_asymptoticE :
  scb_asymptotic fc_kim_security_bundleB
  = algebraic_rigidity.sw_asymptotic (fc_kim_security_witness Hlt Hgt Hspec L).
Proof. by []. Qed.

(** fc_kim_bundle_exact_isSome — the five-card bundle carries an exact slot.
    @composes: fc_kim_security_bundleB *)
Lemma fc_kim_bundle_exact_isSome : isSome (scb_exact fc_kim_security_bundleB).
Proof. by []. Qed.

(** fc_kim_bundle_asym_isSome — the five-card bundle carries an asymptotic slot.
    @composes: fc_kim_security_bundleB *)
Lemma fc_kim_bundle_asym_isSome :
  isSome (scb_asymptotic fc_kim_security_bundleB).
Proof. by []. Qed.

End probe_kim.

(******************************************************************************)
(*     The mirrored core records                                              *)
(******************************************************************************)

Section probe_core_records.
Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

(** AlgebraicRigidityB — algebraic_rigidity.v:187-190 with ar_security a
    certificate bundle.
    @intent: the security-and-threshold record over the bundle layer. *)
Record AlgebraicRigidityB := MkAlgebraicRigidityB {
  arb_security : ShuffleCertificateBundle R M ;
  arb_threshold : ThresholdWitness M
}.

(** CombinatorialRigidityB — combinatorial_rigidity.v:42-47 with cr_security a
    certificate bundle.
    @intent: the curve-free rigidity record over the bundle layer. *)
Record CombinatorialRigidityB := MkCombinatorialRigidityB {
  crb_security : ShuffleCertificateBundle R M ;
  crb_covering : CoveringScheme M ;
  crb_genus_gt0 : (0 < cd_genus (cs_data crb_covering))%N ;
  crb_klein_lt_card : (klein_genus0_bound M < #|pgg_G M|)%N
}.

Local Open Scope ring_scope.

Let eps_bound := (2%:R : R).

(** SecurityProfileB — algebraic_rigidity.v:475-480 with sp_witness a marginal
    bound, its two side conditions reading the new sw_L and sw_bound_eps.
    @intent: the turning-point profile over the bound layer. *)
Record SecurityProfileB := MkSecurityProfileB {
  spb_Lstar : nat ;
  spb_witness : ShuffleMarginalBound R M ;
  spb_at_Lstar : sw_L spb_witness = spb_Lstar ;
  spb_nontrivial : is_true (Num.lt (sw_bound_eps spb_witness) eps_bound)
}.

(** arb_security_profile — algebraic_rigidity.v:483-490 with the bound reached
    through scb_bound.
    @composes: SecurityProfileB *)
Definition arb_security_profile (ar : AlgebraicRigidityB)
    (Hlt2 : is_true
      (Num.lt (sw_bound_eps (scb_bound (arb_security ar))) eps_bound))
    : SecurityProfileB :=
  @MkSecurityProfileB
    (sw_L (scb_bound (arb_security ar)))
    (scb_bound (arb_security ar))
    erefl
    Hlt2.

(** CertifiedSolutionB — algebraic_rigidity.v:514-521 with cs_witness a
    marginal bound.
    @intent: the solver-to-proof bridge over the bound layer. *)
Record CertifiedSolutionB := MkCertifiedSolutionB {
  csb_params  : SecurityParams ;
  csb_witness : ShuffleMarginalBound R M ;
  csb_L_eq    : sw_L csb_witness = sp_L csb_params ;
  csb_denom_pos : (0 < (sp_eps csb_params).2)%N ;
  csb_eps_le  : (sw_bound_eps csb_witness <=
                 (sp_eps csb_params).1%:R / (sp_eps csb_params).2%:R)%O
}.

(** certified_from_boundB — algebraic_rigidity.v:554-561 taking a marginal
    bound in place of a witness.
    @composes: CertifiedSolutionB *)
Definition certified_from_boundB
    (b : ShuffleMarginalBound R M)
    (eps_n eps_d : nat) (Hd : (0 < eps_d)%N)
    (Hle : (sw_bound_eps b <= eps_n%:R / eps_d%:R)%O)
    : CertifiedSolutionB :=
  @MkCertifiedSolutionB
    (MkSP (@pgg_ngens' M).+1 (pgg_N' M).+1 (sw_L b) (eps_n, eps_d))
    b erefl Hd Hle.

(** consumer_L — pgg_dealer_bridge.v:38 with the bound reached through
    scb_bound.
    @intent: the solver-determined word length of a rigidity record. *)
Definition consumer_L (ar : AlgebraicRigidityB) : nat :=
  sw_L (scb_bound (arb_security ar)).

(** dealer_words_epsilon_boundB — pgg_dealer_bridge.v:79-84 with the bound
    reached through scb_bound.
    @composes: consumer_L *)
Lemma dealer_words_epsilon_boundB (ar : AlgebraicRigidityB)
    (s : 'I_(pgg_N' M).+1) :
  (var_dist (fdistmap (fun sigma : {perm 'I_(pgg_N' M).+1} => sigma s)
                      (sw_rho_dist (scb_bound (arb_security ar))))
            (fdist_uniform (card_ord (pgg_N' M).+1))
   <= sw_bound_eps (scb_bound (arb_security ar)))%O.
Proof. exact: sw_bound. Qed.

(** security_per_positionB — pgg_protocol_landscape.v:124-127 at a marginal
    bound.
    @composes: dealer_words_epsilon_boundB *)
Lemma security_per_positionB (sw : ShuffleMarginalBound R M)
    (s : 'I_(pgg_N' M).+1) :
  (var_dist (fdistmap (fun sigma : {perm 'I_(pgg_N' M).+1} => sigma s)
                      (sw_rho_dist sw))
            (fdist_uniform (card_ord (pgg_N' M).+1)) <= sw_bound_eps sw)%O.
Proof. exact: sw_bound. Qed.

End probe_core_records.

Arguments AlgebraicRigidityB R M : clear implicits.
Arguments CombinatorialRigidityB R M : clear implicits.
Arguments SecurityProfileB R M : clear implicits.
Arguments CertifiedSolutionB R M : clear implicits.

(******************************************************************************)
(*     One value per mirrored core record                                     *)
(******************************************************************************)

Section probe_core_values.
Variable R : realType.
Local Open Scope ring_scope.

(** s5_rigidityB — the BOUND-bucket rigidity value of the S_5 instance.
    @intent: rigidity_s5_instance.v:434-437 with the fiber witness routed
    through shuffle_bundle_of_bound, reusing the landed threshold witness. *)
Definition s5_rigidityB :=
  @MkAlgebraicRigidityB R _ (shuffle_bundle_of_bound (s5_boundB R))
    (ar_threshold (s5_rigidity R)).

(** s5_rigidity_asymB — the ASYM-bucket rigidity value of the S_5 instance.
    @intent: rigidity_s5_instance.v:384-387 with the L = 286 spectral bundle. *)
Definition s5_rigidity_asymB :=
  @MkAlgebraicRigidityB R _ (s5_schreier_bundleB R)
    (ar_threshold (s5_rigidity_cryptographically_secure R)).

(** s5x5_combinatorial_rigidityB — the curve-free rigidity value of S_5 x S_5.
    @intent: rigidity_s5x5_instance.v:571 with its witness bundled and its
    three remaining fields reused by projection. *)
Definition s5x5_combinatorial_rigidityB :=
  @MkCombinatorialRigidityB R _
    (bundle_of_witness (cr_security (s5x5_combinatorial_rigidity R)))
    (cr_covering (s5x5_combinatorial_rigidity R))
    (cr_genus_gt0 (s5x5_combinatorial_rigidity R))
    (cr_klein_lt_card (s5x5_combinatorial_rigidity R)).

(** pgl27_eps_lt2B — the eight-card orbit epsilon is below the trivial bound.
    @composes: pgl27_security_profileB *)
Lemma pgl27_eps_lt2B : Num.lt (sw_bound_eps (pgl27_marginal_boundB R)) 2%:R.
Proof. by rewrite /= ltr0n. Qed.

(** pgl27_security_profileB — the turning-point profile of the eight-card
    orbit bound.
    @intent: SecurityProfileB at L* = 0 and epsilon = 0. *)
Definition pgl27_security_profileB :=
  @MkSecurityProfileB R _ (sw_L (pgl27_marginal_boundB R))
    (pgl27_marginal_boundB R) erefl pgl27_eps_lt2B.

(** pgl27_eps_le01B — the eight-card orbit epsilon is at most the rational 0/1.
    @composes: pgl27_certifiedB *)
Lemma pgl27_eps_le01B :
  (sw_bound_eps (pgl27_marginal_boundB R) <= 0%:R / 1%:R)%O.
Proof. by rewrite /= mul0r. Qed.

(** pgl27_certifiedB — the certified solution of the eight-card orbit bound.
    @intent: CertifiedSolutionB at the rational epsilon 0/1. *)
Definition pgl27_certifiedB :=
  @certified_from_boundB R pgl27_M (pgl27_marginal_boundB R) 0 1 isT
    pgl27_eps_le01B.

(** consumer_L_s5B — the dealer-bridge word length of the fiber rigidity is 1.
    @composes: s5_rigidityB *)
Lemma consumer_L_s5B : consumer_L s5_rigidityB = 1%N.
Proof. by []. Qed.

(** consumer_L_s5_asymB — the dealer-bridge word length of the spectral
    rigidity is 286.
    @composes: s5_rigidity_asymB *)
Lemma consumer_L_s5_asymB : consumer_L s5_rigidity_asymB = 286%N.
Proof. by []. Qed.

(*     Witness tie 1 of 5: pgl27_profile.v:115-120 profile_eps_pgl27          *)

(** profile_eps_pgl27B — the eight-card orbit security character is zero.
    @main bound: sw_bound_eps of the PGL(2,7) marginal bound is 0. *)
Lemma profile_eps_pgl27B : sw_bound_eps (pgl27_marginal_boundB R) = 0.
Proof. by []. Qed.

(*     Witness tie 2 of 5: den_boer_profile.v:86-88 den_boer_perfect          *)

(** den_boer_marginal_boundB — the marginal bound of the unbiased one-cut
    five-card member.
    @intent: the bound half of fc_kim_security_witness at bias 0 and L = 1. *)
Definition den_boer_marginal_boundB :=
  bound_of_witness (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1).

(** den_boer_security_bundleB — the BOTH bucket at the den Boer member.
    @intent: the bound above with both certificates attached. *)
Definition den_boer_security_bundleB :=
  bundle_of_witness (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1).

(** den_boer_perfectB — the den Boer dealing-phase bound is exactly 0.
    @main bound: sw_bound_eps den_boer_marginal_boundB = 0. *)
Lemma den_boer_perfectB : sw_bound_eps den_boer_marginal_boundB = 0.
Proof. by rewrite /= kim_security_at_zero. Qed.

End probe_core_values.

(******************************************************************************)
(*     The concrete Kim bias 1/100 at word length 7                           *)
(******************************************************************************)

Section probe_kim_centi.
Variable R : realType.
Local Open Scope ring_scope.

(** kim_marginal_bound_centiB — the marginal bound at bias 1/100, L = 7.
    @intent: the bound half of kim_security_witness_centi. *)
Definition kim_marginal_bound_centiB :=
  bound_of_witness (kim_security_witness_centi R).

(** kim_security_bundle_centiB — the BOTH bucket at bias 1/100, L = 7.
    @intent: the bound above with both certificates attached. *)
Definition kim_security_bundle_centiB :=
  bundle_of_witness (kim_security_witness_centi R).

(** kim_centi_bundle_exactE — the exact slot survives bundling at 1/100.
    @composes: kim_security_bundle_centiB *)
Lemma kim_centi_bundle_exactE :
  scb_exact kim_security_bundle_centiB
  = algebraic_rigidity.sw_exact (kim_security_witness_centi R).
Proof. by []. Qed.

(** kim_centi_bundle_asymptoticE — the asymptotic slot survives bundling at
    1/100.
    @composes: kim_security_bundle_centiB *)
Lemma kim_centi_bundle_asymptoticE :
  scb_asymptotic kim_security_bundle_centiB
  = algebraic_rigidity.sw_asymptotic (kim_security_witness_centi R).
Proof. by []. Qed.

(** kim_deal_centi_ltB — five_card_kim.v:635-644 with the bound reached
    through scb_bound.
    @main security: the 7-cut biased deal is within 2^-40 of uniform. *)
Lemma kim_deal_centi_ltB (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sw_rho_dist (scb_bound kim_security_bundle_centiB)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof.
apply: (Order.POrderTheory.le_lt_trans
  (sw_bound (scb_bound kim_security_bundle_centiB) s)).
rewrite /kim_security_bundle_centiB /bundle_of_witness /bound_of_witness.
rewrite /kim_security_witness_centi /fc_kim_security_witness /=.
exact: kim_bound_centi.
Qed.

End probe_kim_centi.

(******************************************************************************)
(*     Witness ties 3 to 5: the executed-sample cut distributions             *)
(******************************************************************************)

Section probe_exec_ties.
Variable R : realType.

(** pgl27_sample_witness_prodEB — pgl27_exec.v:381-386 stated against the
    separate PGL(2,7) bound value.
    @composes: pgl27_sample_cut_distEB *)
Lemma pgl27_sample_witness_prodEB :
  pgl27P R
  = ((fdist_uniform card_bool) `x (sw_rho_dist (pgl27_marginal_boundB R)))%fdist.
Proof. by []. Qed.

(*     Witness tie 3 of 5: pgl27_exec.v:387-393 pgl27_sample_cut_distE        *)

(** pgl27_sample_cut_distEB — the exact sample space's cut distribution is the
    marginal bound's own shuffle distribution.
    @main architecture: sa_cut_dist pgl27_sample = sw_rho_dist
    pgl27_marginal_boundB. *)
Lemma pgl27_sample_cut_distEB :
  @sa_cut_dist R _ _ (pgl27_sample R) = sw_rho_dist (pgl27_marginal_boundB R).
Proof.
rewrite /sa_cut_dist /pgl27_sample /=.
rewrite pgl27_sample_witness_prodEB.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(*     Witness tie 4 of 5: five_card_exec.v:857-864 den_boer_witness_rotationE *)

(** den_boer_witness_rotationEB — the den Boer marginal bound's distribution is
    the image of the uniform rotation distribution.
    @composes: den_boer_sample_cut_witnessEB *)
Lemma den_boer_witness_rotationEB :
  sw_rho_dist (den_boer_marginal_boundB R)
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /den_boer_marginal_boundB /bound_of_witness /=.
rewrite rho_from_words_weighted1 kim_weight_uniform_at0.
by congr fdistmap; apply: funext => k; exact: fc_kim_sigmasE.
Qed.

(*     Witness tie 5 of 5: five_card_exec.v:873-878                           *)
(*                        den_boer_sample_cut_witnessE                        *)

(** den_boer_sample_cut_witnessEB — the five-card sample's cut distribution is
    bias-independent and equals the den Boer marginal bound's distribution.
    @main architecture: five_card_sample_cut_dist Hlt Hgt Hspec L =
    sw_rho_dist den_boer_marginal_boundB, at every bias and word length. *)
Lemma den_boer_sample_cut_witnessEB (eps : R)
    (Hlt : (eps < 5%:R^-1)%R) (Hgt : (- (4%:R * 5%:R^-1) < eps)%R)
    (Hspec : (`|eps| < 4%:R / 5%:R)%R) (L : nat) :
  five_card_sample_cut_dist Hlt Hgt Hspec L
  = sw_rho_dist (den_boer_marginal_boundB R).
Proof. by rewrite five_card_sample_cut_distE den_boer_witness_rotationEB. Qed.

End probe_exec_ties.

End WS.

(******************************************************************************)
(*     Axiom ledger                                                           *)
(******************************************************************************)

Print Assumptions WS.pgl27_bundle_exact_someE.
Print Assumptions WS.fc_kim_bundle_exactE.
Print Assumptions WS.fc_kim_bundle_asymptoticE.
Print Assumptions WS.kim_centi_bundle_exactE.
Print Assumptions WS.kim_centi_bundle_asymptoticE.
Print Assumptions WS.profile_eps_pgl27B.
Print Assumptions WS.den_boer_perfectB.
Print Assumptions WS.pgl27_sample_cut_distEB.
Print Assumptions WS.den_boer_witness_rotationEB.
Print Assumptions WS.den_boer_sample_cut_witnessEB.
Print Assumptions WS.consumer_L_s5B.
Print Assumptions WS.consumer_L_s5_asymB.
Print Assumptions WS.kim_deal_centi_ltB.
Print Assumptions WS.dealer_words_epsilon_boundB.
Print Assumptions WS.security_per_positionB.

(* The four mirrored-core values are Definitions, so their well-typedness is
   witnessed by these three type-level checks rather than by a Qed. *)
Check WS.s5_rigidityB.
Check WS.s5_rigidity_asymB.
Check WS.s5x5_combinatorial_rigidityB.
Check WS.pgl27_security_profileB.
Check WS.pgl27_certifiedB.
