(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_profile: the PGL(2,7) plug of the shared MonodromyProfile program    *)
(*                                                                            *)
(* The eight-card orbit scheme (pgl27_scheme) is packaged as a               *)
(* MonodromyProfile with an exact (epsilon = 0) SecurityWitness: the single- *)
(* card pushforward of the uniform shuffle over PGL(2,7) is exactly uniform,  *)
(* by the transitivity marginal ttrans_point_uniform.                         *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_PI       == the eight-sheet starting interface (ord_tuple 8)       *)
(*   pgl27_rho_dist == the uniform distribution over the shuffle group        *)
(*   pgl27_security == the exact SecurityWitness at epsilon = 0               *)
(*   pgl27_profile  == the MonodromyProfile bundling PI, security and plug    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_point_uniform == the single-card pushforward is exactly uniform    *)
(*   profile_k_pgl27     == the plug's privacy threshold is four              *)
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
    @composes: pgl27_security *)
Lemma pgl27_G_pos : (0 < #|pgg_G pgl27_M|)%N.
Proof. exact: cardG_gt0. Qed.

(** pgl27_rho_dist — the uniform distribution over the PGL(2,7) shuffle group.
    @intent: the shuffle law of the eight-card orbit scheme. *)
Definition pgl27_rho_dist : R.-fdist {perm 'I_8} := `U pgl27_G_pos.

(** pgl27_point_uniform — the single-card pushforward of the uniform shuffle
    is exactly uniform, via the transitivity marginal.
    @composes: pgl27_security *)
Lemma pgl27_point_uniform (s : 'I_8) :
  fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist
  = fdist_uniform (card_ord 8).
Proof.
exact: (@ttrans_point_uniform (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos s isT).
Qed.

(** pgl27_se_exact — the single-card pushforward is at variational distance
    zero from uniform.
    @composes: pgl27_security *)
Lemma pgl27_se_exact (s : 'I_8) :
  var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
           (fdist_uniform (card_ord 8)) = 0%R.
Proof.
rewrite pgl27_point_uniform /var_dist.
by apply: big1 => a _; rewrite subrr normr0.
Qed.

(** pgl27_sw_bound — the single-card pushforward meets the epsilon = 0 bound.
    @composes: pgl27_security *)
Lemma pgl27_sw_bound (s : 'I_8) :
  (var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
            (fdist_uniform (card_ord 8)) <= 0%R)%O.
Proof. rewrite pgl27_se_exact; exact: lexx. Qed.

(** pgl27_security — the exact SecurityWitness at epsilon = 0: single-card
    perfect uniformity of the PGL(2,7) shuffle.
    @intent: the exact security witness of the eight-card orbit scheme. *)
Definition pgl27_security : SecurityWitness R pgl27_M :=
  @MkSecurityWitness R pgl27_M 0 0%R pgl27_rho_dist pgl27_sw_bound
    (Some (@MkSecurityExact R pgl27_M pgl27_rho_dist 0%R pgl27_se_exact)) None.

(** pgl27_profile — the PGL(2,7) plug of the shared MonodromyProfile: PI, the
    exact security witness, and the orbit plug.
    @intent: the eight-card orbit-class plug of the MonodromyProfile program. *)
Definition pgl27_profile : MonodromyProfile R :=
  @MkMonodromyProfile R pgl27_M bool pgl27_PI pgl27_security pgl27_plug.

End witness.

(** profile_k_pgl27 — the PGL(2,7) plug's privacy threshold is four.
    @main bound: coalitions of at most three cards are private, k = 4. *)
Lemma profile_k_pgl27 (R : realType) : profile_k (pgl27_profile R) = 4.
Proof. by []. Qed.
