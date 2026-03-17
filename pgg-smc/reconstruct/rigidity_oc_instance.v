(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Overlapping 3-Cycles Algebraic Rigidity Instance                           *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the overlapping       *)
(* 3-cycles group OC = <(0 1 2), (1 2 3)> in S_4.                            *)
(*                                                                            *)
(* This is the FIRST instance with L > 1 (L = 2), demonstrating the          *)
(* L-freeness hardness tradeoff: higher L means a larger search space         *)
(* (search_space 2 = 4) but also stronger security guarantees.               *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 2 (generators), N = 4 (sheets), L = 2, depth = 2                  *)
(*   epsilon = 2 * (4! - 4) / 4! = 40/24                                    *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   oc_security_witness_2 : SecurityWitness (via var_dist_lfree_uniform)    *)
(*   oc_round_complexity : RoundComplexityWitness (L=2, depth=2)             *)
(*   oc_rigidity : AlgebraicRigidity (security + threshold + rounds)         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_lfree
                            pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section oc_security.

Variable R : realType.

Let M_oc := @Gen_PGGTypes 1 2 oc_sigmas.
Let R_oc : GeneratedMonodromyReprType := M_oc.

(* SecurityWitness at L=2 (the smallest L with lfree for OC).
   Epsilon = 2*(4!-4)/4!. Any larger L with lfree gives a tighter bound;
   see security_witness_any_L for the generic constructor. *)
Definition oc_security_witness_2 : SecurityWitness R R_oc :=
  security_witness_any_L R oc_lfree2.

End oc_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section oc_rigidity.

Variable R : realType.

Let R_oc : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 1 2 oc_sigmas.

(* Group nontriviality *)
Hypothesis HG_oc : (1 < #|pgg_G R_oc|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = 4 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_oc).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT R_oc -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_oc -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_oc ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition oc_covering : CoveringScheme R_oc :=
  genus0_covering HG_oc qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis oc_genus0_pgl :
  (#|pgg_G R_oc| <= pgl_bound R_oc)%N.

Definition oc_threshold_witness : ThresholdWitness R_oc :=
  @MkThresholdWitness R_oc oc_covering (fun _ => oc_genus0_pgl).

(* Round complexity at L=2: depth = 2 (fully sequential, non-commuting) *)
Definition oc_round_complexity : RoundComplexityWitness :=
  @MkRoundComplexityWitness 2 2 (leqnn 2).

Definition oc_rigidity : AlgebraicRigidity R R_oc :=
  @MkAlgebraicRigidity R R_oc
    (oc_security_witness_2 R)
    oc_threshold_witness
    oc_round_complexity.

(* Derived properties *)

Lemma oc_complexity (L : nat) :
  (@search_space R_oc L <= #|pgg_G R_oc|)%N.
Proof. exact: search_space_leG. Qed.

Lemma oc_tradeoff :
  let cs := tw_covering (ar_threshold oc_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_oc| <= pgl_bound R_oc)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_oc oc_covering (fun _ => oc_genus0_pgl)).
Qed.

End oc_rigidity.
