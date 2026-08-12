(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_e_mutation: the ideal-agreement hypothesis of the transfer bound is  *)
(* load-bearing, in the proof and in the mathematics                          *)
(*                                                                            *)
(* Mutation of probe unit E of the 2026-08-12 layered-protocol-packing gate.  *)
(* The generic bound var_dist_fdistmap_transfer (probe_e_transfer.v) carries  *)
(* two hypotheses: the distributions are within delta, and the two readers    *)
(* have the same pushforward along the ideal distribution.  Deleting the      *)
(* second one is refuted twice.                                              *)
(*                                                                            *)
(* Key results:                                                               *)
(*   mu1_control       == the unmutated proof script, delivered through the   *)
(*                        same ltac term the rejected attempts use            *)
(*   mu1a_attempt      == rejected: the script mentions the deleted           *)
(*                        hypothesis                                          *)
(*   mu1b_attempt      == rejected: deleting the rewrite step as well leaves  *)
(*                        a goal the data-processing lemma does not apply to  *)
(*   point_mass_true   == the point mass at true on the two-element carrier   *)
(*   transfer_needs_ideal == the hypothesis-free implication is false, not    *)
(*                        merely unprovable: at P = Q the distance premise    *)
(*                        holds at delta zero and the conclusion fails        *)
(*                                                                            *)
(* The message quoted above a Fail is the verbatim diagnostic obtained by     *)
(* removing that one Fail and re-elaborating the declaration under the        *)
(* interactive checker: batch mode does not echo the message of a Fail that   *)
(* succeeds in failing.                                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop order.
From mathcomp Require Import ssralg ssrnum boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Part 1: the unmutated proof, as a positive control                     *)
(******************************************************************************)

Section e_mu1_control.
Variables (R : realType) (A B : finType) (P Q : R.-fdist A).
Variables (fx fy : A -> B) (delta : R).
Hypothesis HPQ : var_dist P Q <= delta.
Hypothesis Hideal : fdistmap fx Q = fdistmap fy Q.

(** mu1_control — the landed transfer proof, delivered as an ltac term so that
    the rejections below differ from it in the hypothesis alone.
    @intent: the positive control of the M1 mutation. *)
Definition mu1_control :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta :=
  ltac:(apply: (Order.POrderTheory.le_trans
                  (var_dist_triangle _ (fdistmap fx Q) _));
        apply: lerD;
        [ apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ
        | rewrite Hideal symmetric_var_dist;
          apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ ]).

End e_mu1_control.

(******************************************************************************)
(*     Part 2 (M1): the proof-level mutation                                  *)
(******************************************************************************)

Section e_mu1_mutation.
Variables (R : realType) (A B : finType) (P Q : R.-fdist A).
Variables (fx fy : A -> B) (delta : R).
Hypothesis HPQ : var_dist P Q <= delta.

(* M1a: the ideal-agreement hypothesis is deleted from the context and the
   proof script is left verbatim.  Rejected with

     The variable Hideal was not found in the current environment. *)
Fail Definition mu1a_attempt :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta :=
  ltac:(apply: (Order.POrderTheory.le_trans
                  (var_dist_triangle _ (fdistmap fx Q) _));
        apply: lerD;
        [ apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ
        | rewrite Hideal symmetric_var_dist;
          apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ ]).

(* M1b: the rejection is not an artefact of a dangling name.  Deleting the
   rewrite step along with the hypothesis leaves the second summand as
   var_dist (fdistmap fx Q) (fdistmap fy P) <= delta, whose two pushforwards
   are along different readers, so the data-processing lemma does not apply.
   Rejected with

     Cannot apply lemma (Order.POrderTheory.le_trans
       (var_dist_fdistmap _ _ _))

   the two lines above being one line in the checker's output. *)
Fail Definition mu1b_attempt :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta :=
  ltac:(apply: (Order.POrderTheory.le_trans
                  (var_dist_triangle _ (fdistmap fx Q) _));
        apply: lerD;
        [ apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ
        | rewrite symmetric_var_dist;
          apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
          exact: HPQ ]).

End e_mu1_mutation.

(******************************************************************************)
(*     Part 3 (M2): the semantic mutation                                     *)
(******************************************************************************)

Section e_mu2_counterexample.
Variable R : realType.

(** point_mass_true — the point mass at true on the two-element carrier.
    @intent: the witness distribution of the M2 counterexample. *)
Definition point_mass_true : R.-fdist bool := fdist1 true.

(** var_dist_refl — the variation distance of a distribution to itself is
    zero.
    @composes: mu2_distance_premise *)
Lemma var_dist_refl (A : finType) (P : R.-fdist A) : var_dist P P = 0.
Proof. by rewrite /var_dist big1 // => a _; rewrite subrr normr0. Qed.

(** mu2_distance_premise — the surviving premise of the mutated statement
    holds at delta zero, the witness distribution being taken for both the
    real and the ideal distribution.
    @composes: transfer_needs_ideal *)
Lemma mu2_distance_premise : var_dist point_mass_true point_mass_true <= 0.
Proof. by rewrite var_dist_refl. Qed.

(** mu2_ideal_premise_fails — the deleted premise fails at the witness: the
    identity and the negation push the point mass at true to different
    distributions.
    @composes: transfer_needs_ideal *)
Lemma mu2_ideal_premise_fails :
  fdistmap idfun point_mass_true <> fdistmap negb point_mass_true.
Proof.
rewrite /point_mass_true !fdistmap1 /=.
move=> /(congr1 (fun d : R.-fdist bool => d true)).
by rewrite !fdist1E /= => /eqP; rewrite oner_eq0.
Qed.

(** mu2_transfer_control — with both readers the identity the deleted premise
    is an identity and the unmutated bound applies at the witness
    distribution, so the M2 rejection is about the premise and not about the
    carrier or the value of delta.
    @composes: transfer_needs_ideal *)
Lemma mu2_transfer_control :
  var_dist (fdistmap idfun point_mass_true) (fdistmap idfun point_mass_true)
  <= 0 + 0.
Proof.
exact: (@mu1_control R bool bool point_mass_true point_mass_true idfun idfun 0
  mu2_distance_premise (erefl _)).
Qed.

(** mu2_var_dist_value — the two pushforwards of the witness distribution are
    at variation distance two, the largest value the distance takes.
    @composes: transfer_needs_ideal *)
Lemma mu2_var_dist_value :
  var_dist (fdistmap idfun point_mass_true) (fdistmap negb point_mass_true)
  = 2%:R.
Proof.
by rewrite /point_mass_true !fdistmap1 /var_dist big_bool !fdist1E /= subr0
  sub0r normr1 normrN normr1 -natr1.
Qed.

(** transfer_needs_ideal — the transfer bound with the ideal-agreement premise
    deleted is false: at the point mass at true, taken for both the real and
    the ideal distribution, the distance premise holds at delta zero while the
    conclusion asks for a distance of two to be at most zero.
    @main bound: the ideal-agreement premise of var_dist_fdistmap_transfer is
    load-bearing in the mathematics, not only in the proof script. *)
Lemma transfer_needs_ideal :
  ~ (var_dist (fdistmap idfun point_mass_true) (fdistmap negb point_mass_true)
     <= 0 + 0).
Proof.
rewrite mu2_var_dist_value addr0.
by apply/negP; rewrite -Order.TotalTheory.ltNge ltr0n.
Qed.

End e_mu2_counterexample.

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions mu1_control.
Print Assumptions mu2_distance_premise.
Print Assumptions mu2_ideal_premise_fails.
Print Assumptions mu2_var_dist_value.
Print Assumptions transfer_needs_ideal.
