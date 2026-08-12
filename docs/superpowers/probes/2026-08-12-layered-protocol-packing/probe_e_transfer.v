(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_e_transfer: the generic exact-to-finite transfer bound, a concrete   *)
(* two-point instance, and the PGL(2,7) coalition bound re-derived from it    *)
(*                                                                           *)
(* Probe unit E of the 2026-08-12 layered-protocol-packing gate: section      *)
(* 15.6.  The proof of pgl27_word_view_indist                                 *)
(* (pgg-smc/instances/pgl27/pgl27_word_privacy.v, line 168) is a triangle     *)
(* through the ideal distribution, a data-processing step on each half, and   *)
(* an ideal-distribution equality in the middle.  Nothing in that argument    *)
(* mentions PGL(2,7), three-transitivity or Boolean secrets, so the whole     *)
(* argument is stated here once over an arbitrary pair of distributions and   *)
(* an arbitrary pair of readers, and the landed bound is recovered as an      *)
(* instance.                                                                  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   var_dist_refl              == a distribution is at variation distance    *)
(*                                 zero from itself                           *)
(*   var_dist_fdistmap_transfer == two readers whose pushforwards agree on    *)
(*                                 the ideal distribution have pushforwards   *)
(*                                 within twice delta on any distribution     *)
(*                                 within delta of the ideal one              *)
(*   transfer_uniform_bool      == the transfer bound at the uniform          *)
(*                                 distribution on bool, both readers the     *)
(*                                 identity and delta zero                    *)
(*   pgl27_word_view_indist_via_transfer == the landed 2^-39 coalition-view   *)
(*                                 bound of pgl27_word_privacy, obtained by   *)
(*                                 instantiating the generic bound at the     *)
(*                                 word shuffle, the uniform shuffle and the  *)
(*                                 two secrets                                *)
(*                                                                            *)
(* The three library facts the generic bound consumes are var_dist_triangle   *)
(* and var_dist_fdistmap (pgg-smc/security/pgg_collusion_bound.v, lines 44    *)
(* and 73) and symmetric_var_dist (probability/variation_dist.v, line 37).    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssralg ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_scheme.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Part 1: the generic transfer bound                                     *)
(******************************************************************************)

(** var_dist_refl — the variation distance of a distribution to itself is
    zero.
    @composes: transfer_uniform_bool *)
Lemma var_dist_refl (R : realType) (A : finType) (P : R.-fdist A) :
  var_dist P P = 0.
Proof. by rewrite /var_dist big1 // => a _; rewrite subrr normr0. Qed.

Section e_generic_transfer.
Variables (R : realType) (A B : finType) (P Q : R.-fdist A).
Variables (fx fy : A -> B) (delta : R).
Hypothesis HPQ : var_dist P Q <= delta.
Hypothesis Hideal : fdistmap fx Q = fdistmap fy Q.

(** var_dist_fdistmap_transfer — two readers of a distribution P within delta
    of Q, whose pushforwards along Q are equal, have pushforwards along P
    within delta + delta.
    @main bound: the exact-to-finite transfer inequality, a triangle through
    the ideal distribution with a data-processing step on each half. *)
Lemma var_dist_fdistmap_transfer :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta.
Proof.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (fdistmap fx Q) _)).
apply: lerD.
- apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)); exact: HPQ.
- rewrite Hideal symmetric_var_dist.
  apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)); exact: HPQ.
Qed.

End e_generic_transfer.

(******************************************************************************)
(*     Part 2: a concrete two-point instance                                  *)
(******************************************************************************)

Section e_bool_instance.
Variable R : realType.

(** uniform_bool — the uniform distribution on the two-element carrier.
    @intent: the concrete carrier the generic bound is exercised on. *)
Definition uniform_bool : R.-fdist bool := fdist_uniform card_bool.

(** transfer_uniform_bool — at the uniform distribution on bool, with the
    identity as both readers and delta zero, the generic bound gives distance
    zero.
    @composes: var_dist_fdistmap_transfer *)
Lemma transfer_uniform_bool :
  var_dist (fdistmap idfun uniform_bool) (fdistmap idfun uniform_bool)
  <= 0 + 0.
Proof.
apply: (@var_dist_fdistmap_transfer R bool bool uniform_bool uniform_bool
  idfun idfun 0).
- by rewrite var_dist_refl.
- by [].
Qed.

End e_bool_instance.

(******************************************************************************)
(*     Part 3: the PGL(2,7) instance                                          *)
(******************************************************************************)

Section e_pgl27_instance.
Variable R : realType.

(* Two halves of 2^-40 make 2^-39, copied verbatim from the landed proof:
   the mulr_natl and mulr_natr routes fail here because the ring numeral 2 is
   itself a natmul and the rewrite fires inside it. *)
Let pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

(** pgl27_word_view_indist_via_transfer — under the two-hundred-letter word
    shuffle the coalition-view distributions of two secrets are within 2^-39
    in variation distance, for every coalition of at most three positions.
    Naming: the name records the derivation, not the statement: the statement
    is pgl27_word_view_indist verbatim and the suffix distinguishes this
    re-derivation from the landed theorem it reproduces.
    @main security: statistical coalition privacy under the realistic
    shuffle, obtained as an instance of var_dist_fdistmap_transfer. *)
Corollary pgl27_word_view_indist_via_transfer (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
           (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
  <= 2%:R^-39.
Proof.
move=> HC; rewrite -pow2_split.
apply: (@var_dist_fdistmap_transfer R (pgg_gT pgl27_M) _ (rho_word R)
  (`U pgl27_G_pos) (fun g => pgl27_view R C (s, g))
  (fun g => pgl27_view R C (s', g)) (2%:R^-40)).
- exact: pgl27_word_mixing.
- exact: (pgl27_view_law_const _ s s' HC).
Qed.

(* Statement agreement: the landed theorem inhabits the written statement of
   the corollary above, so the re-derivation reproduces pgl27_word_view_indist
   itself and not a differently shaped or weaker bound.  The constant is the
   landed 2^-39 on both sides. *)
Check (@pgl27_word_view_indist R
  : forall (C : {set 'I_8}) (s s' : bool),
      (#|C| <= 3)%N ->
      var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
               (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
      <= 2%:R^-39).

End e_pgl27_instance.

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions var_dist_refl.
Print Assumptions var_dist_fdistmap_transfer.
Print Assumptions transfer_uniform_bool.
Print Assumptions pgl27_word_view_indist_via_transfer.
