(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_profile: the PGL(2,7) plug of the shared MonodromyProfile program    *)
(*                                                                            *)
(* The eight-card orbit scheme (pgl27_scheme) is packaged as a               *)
(* MonodromyProfile, a program-layer value carrying no epsilon, together with *)
(* a separate marginal bound at epsilon = 0: the single-card pushforward of   *)
(* the uniform shuffle over PGL(2,7) is exactly uniform, by the transitivity  *)
(* marginal ttrans_point_uniform.                                             *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_PI       == the eight-sheet starting interface (ord_tuple 8)       *)
(*   pgl27_rho_dist == the uniform distribution over the shuffle group        *)
(*   pgl27_marginal_bound == the ShuffleMarginalBound at epsilon = 0          *)
(*   pgl27_certificate_bundle == that bound with the exact certificate         *)
(*   pgl27_profile  == the MonodromyProfile bundling PI and plug              *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_point_uniform == the single-card pushforward is exactly uniform    *)
(*   profile_k_pgl27     == the plug's privacy threshold is four              *)
(*   profile_eps_pgl27   == the marginal bound's epsilon is zero              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

(** pgl27_starts_uniq — the eight starting card positions are distinct.
    @composes: pgl27_PI *)
Lemma pgl27_starts_uniq : uniq (ord_tuple 8).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** pgl27_PI — the eight-sheet starting interface for the PGL(2,7) plug.
    @intent: the identity start tuple driving the shared exchange program. *)
Definition pgl27_PI : PGGInterface pgl27_M :=
  @MkPGGI pgl27_M 7 (ord_tuple 8) pgl27_starts_uniq.

Section witness.
Variable R : realType.

(** pgl27_G_pos — the shuffle group is nonempty.
    @composes: pgl27_marginal_bound *)
Lemma pgl27_G_pos : (0 < #|pgg_G pgl27_M|)%N.
Proof. exact: cardG_gt0. Qed.

(** pgl27_rho_dist — the uniform distribution over the PGL(2,7) shuffle group.
    @intent: the shuffle law of the eight-card orbit scheme. *)
Definition pgl27_rho_dist : R.-fdist {perm 'I_8} := `U pgl27_G_pos.

(** pgl27_point_uniform — the single-card pushforward of the uniform shuffle
    is exactly uniform, via the transitivity marginal.
    @composes: pgl27_marginal_bound *)
Lemma pgl27_point_uniform (s : 'I_8) :
  fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist
  = fdist_uniform (card_ord 8).
Proof.
exact: (@ttrans_point_uniform (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos s isT).
Qed.

(** pgl27_se_exact — the single-card pushforward is at variational distance
    zero from uniform.
    @composes: pgl27_certificate_bundle *)
Lemma pgl27_se_exact (s : 'I_8) :
  var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
           (fdist_uniform (card_ord 8)) = 0%R.
Proof.
rewrite pgl27_point_uniform /var_dist.
by apply: big1 => a _; rewrite subrr normr0.
Qed.

(** pgl27_sw_bound — the single-card pushforward meets the epsilon = 0 bound.
    @composes: pgl27_marginal_bound *)
Lemma pgl27_sw_bound (s : 'I_8) :
  (var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
            (fdist_uniform (card_ord 8)) <= 0%R)%O.
Proof. rewrite pgl27_se_exact; exact: lexx. Qed.

(** pgl27_marginal_bound — the marginal bound at epsilon = 0: single-card
    perfect uniformity of the PGL(2,7) shuffle.
    @intent: MkShuffleMarginalBound at word length 0, epsilon 0, the uniform
    shuffle distribution and its per-position bound. *)
Definition pgl27_marginal_bound : ShuffleMarginalBound R pgl27_M :=
  @MkShuffleMarginalBound R pgl27_M 0 0%R pgl27_rho_dist pgl27_sw_bound.

(** pgl27_certificate_bundle — the marginal bound above with the exact-equality
    certificate attached and no asymptotic certificate.
    @intent: MkShuffleCertificateBundle at pgl27_marginal_bound with scb_exact
    the closed-form equality var_dist ... = 0 and scb_asymptotic None. *)
Definition pgl27_certificate_bundle : ShuffleCertificateBundle R pgl27_M :=
  @MkShuffleCertificateBundle R pgl27_M pgl27_marginal_bound
    (Some (@MkSecurityExact R pgl27_M pgl27_rho_dist 0%R pgl27_se_exact)) None.

End witness.

(** pgl27_profile — the PGL(2,7) plug of the shared MonodromyProfile: the group,
    the secret type, PI and the orbit plug.
    @intent: the eight-card orbit-class plug of the MonodromyProfile program. *)
Definition pgl27_profile : MonodromyProfile :=
  @MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_plug.

(** profile_k_pgl27 — the PGL(2,7) plug's privacy threshold is four.
    @main bound: coalitions of at most three cards are private, k = 4. *)
Lemma profile_k_pgl27 : profile_k pgl27_profile = 4.
Proof. by []. Qed.

(** profile_eps_pgl27 — the PGL(2,7) marginal bound's epsilon is zero.
    @main bound: sw_bound_eps of pgl27_marginal_bound is 0; the single-card
    pushforward of the uniform-over-the-group shuffle is exactly uniform. *)
Lemma profile_eps_pgl27 (R : realType) :
  sw_bound_eps (pgl27_marginal_bound R) = 0%R.
Proof. by []. Qed.
