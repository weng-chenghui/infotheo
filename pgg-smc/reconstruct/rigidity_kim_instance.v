(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Kim Biased Five Card Trick Algebraic Rigidity Instance                     *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for Kim & Cetinkaya's     *)
(* biased five card trick (arXiv:2511.05111), where the cyclic cut is biased  *)
(* with probability 1/5 - eps for no-cut and 1/5 + eps/4 for each rotation.  *)
(*                                                                            *)
(* The SecurityWitness is proved via spectral convergence of the 5x5          *)
(* circulant Schreier matrix (from five_card_kim.v):                          *)
(*   var_dist <= sqrt(5) * ((5/4)*|eps|)^L                                    *)
(*                                                                            *)
(* The ThresholdWitness follows the standard genus-0 covering construction    *)
(* from Reed-Solomon codes (+ PGL hypothesis), same as all other instances.   *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   kim_rigidity : AlgebraicRigidity (security + threshold)                  *)
(*   kim_complexity : search_space L <= |G|                                   *)
(*   kim_tradeoff : genus-0/bounded-G OR positive-genus tradeoff              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound five_card_kim.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section kim_rigidity.

Variable R : realType.

(* Bias parameter and its constraints *)
Variable eps : R.
Hypothesis eps_lt : eps < 5%:R^-1.
Hypothesis eps_gt : - (4%:R * 5%:R^-1) < eps.
Hypothesis eps_spectral : (`|eps| < 4%:R / 5%:R)%R.
Let M_kim : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 4 3 fc_kim_sigmas.

(* Group nontriviality *)
Hypothesis HG_kim : (1 < #|pgg_G M_kim|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = 5 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' M_kim).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT M_kim -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G M_kim -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G M_kim ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition kim_covering : CoveringScheme M_kim :=
  genus0_covering HG_kim qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis kim_genus0_pgl :
  (#|pgg_G M_kim| <= pgl_bound M_kim)%N.

Definition kim_threshold_witness : ThresholdWitness M_kim :=
  @MkThresholdWitness M_kim kim_covering (fun _ => kim_genus0_pgl).

Definition kim_rigidity (L : nat) : AlgebraicRigidity R M_kim :=
  @MkAlgebraicRigidity R M_kim
    (@fc_kim_security_witness R eps eps_lt eps_gt eps_spectral L)
    kim_threshold_witness.

(* Derived properties *)

Lemma kim_complexity (L : nat) :
  (@search_space M_kim L <= #|pgg_G M_kim|)%N.
Proof. exact: search_space_leG. Qed.

Lemma kim_tradeoff (L : nat) :
  let cs := tw_covering (ar_threshold (kim_rigidity L)) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G M_kim| <= pgl_bound M_kim)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff M_kim kim_covering
                                     (fun _ => kim_genus0_pgl)).
Qed.

End kim_rigidity.
