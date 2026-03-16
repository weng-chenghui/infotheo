(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Star-Graph Algebraic Rigidity Instance                                     *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the star-graph RAAG.  *)
(*                                                                            *)
(* The SecurityWitness is fully proved using var_dist_lfree_uniform:          *)
(*   epsilon = 2 * (N! - Tg^L) / N!  for any L with lfree(L)                *)
(*                                                                            *)
(* The ThresholdWitness axiomatizes the covering scheme and PGL bound,        *)
(* as their construction requires algebraic geometry (Reed-Solomon codes      *)
(* over genus-0 curves) beyond the scope of this formalization.              *)
(*                                                                            *)
(* vm_compute demonstrations:                                                 *)
(*   star_nt_m2_L1 : n_traces_natB 3 1 (star_comm_nat 2) = 3                *)
(*   star_nt_m2_L2 : n_traces_natB 3 2 (star_comm_nat 2) = 7                *)
(*   star_nt_m2_L3 : n_traces_natB 3 3 (star_comm_nat 2) = 15               *)
(*   star_nt_m2_L4 : n_traces_natB 3 4 (star_comm_nat 2) = 31               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_lfree pgg_raag.
From pgg_smc Require Import pgg_raag_star pgg_raag_clique pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     vm_compute Demonstrations                                              *)
(******************************************************************************)

(* m=2 (N=5, Tg=3): star with 2 leaves *)
Lemma star_nt_m2_L1 : n_traces_natB 3 1 (star_comm_nat 2) = 3.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L2 : n_traces_natB 3 2 (star_comm_nat 2) = 7.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L3 : n_traces_natB 3 3 (star_comm_nat 2) = 15.
Proof. by vm_compute. Qed.

Lemma star_nt_m2_L4 : n_traces_natB 3 4 (star_comm_nat 2) = 31.
Proof. by vm_compute. Qed.

(* m=3 (N=6, Tg=4): star with 3 leaves — cross-check with pgg_raag_clique *)
Lemma star_nt_m3_L1 : n_traces_natB 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

Lemma star_nt_m3_L2 : n_traces_natB 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

Lemma star_nt_m3_L3 : n_traces_natB 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section star_security.

Variable R : realType.
Variable m : nat.

Let M_star := @Gen_PGGTypes m m.+1 (star_gen_tuple m).
Let R_star : GeneratedMonodromyReprType := M_star.
Let N := m.+3.
Let Tg := m.+1.

(* L-freeness at L=1 *)
Lemma star_lfree1 : @lfree M_star 1.
Proof. exact: raag_lfree1. Qed.

(* SecurityWitness at L=1, with epsilon = 2*(N!-Tg)/N! *)
Definition star_security_witness_1 : SecurityWitness R R_star :=
  @MkSecurityWitness R R_star 1 _
    (rho_from_words 1 (star_gen_tuple m))
    (@var_dist_lfree_uniform R _ m 1 (star_gen_tuple m) star_lfree1).

End star_security.

(******************************************************************************)
(*     ThresholdWitness (Axiomatized)                                         *)
(******************************************************************************)

(******************************************************************************)
(*     AlgebraicRigidity Instance (with axiomatized threshold)                *)
(******************************************************************************)

Section star_rigidity.

Variable R : realType.
Variable m : nat.

Let R_star : GeneratedMonodromyReprType :=
  @Gen_PGGTypes m m.+1 (star_gen_tuple m).

(* Axiom: the star graph admits a genus-0 covering scheme.
   This requires constructing a Reed-Solomon code over a prime field
   of characteristic N = m+3 and proving share compatibility with the
   monodromy action — algebraic geometry beyond this formalization. *)
Axiom star_covering : CoveringScheme R_star.

(* Axiom: for the star covering, genus 0 implies |G| <= PGL(2,N).
   This is about the SPECIFIC covering scheme, not universal.
   Each instance provides its own proof — either by computation
   (small groups) or vacuously (large groups whose coverings have genus > 0). *)
Axiom star_genus0_pgl :
  cd_genus (cs_data star_covering) = 0 ->
  (#|pgg_G R_star| <= pgl_bound R_star)%N.

Definition star_threshold_witness : ThresholdWitness R_star :=
  @MkThresholdWitness R_star star_covering star_genus0_pgl.

(* Round complexity at L=1: depth = 1 (trivially, depth <= L) *)
Definition star_round_complexity : RoundComplexityWitness :=
  @MkRoundComplexityWitness 1 1 (leqnn 1).

Definition star_rigidity : AlgebraicRigidity R R_star :=
  @MkAlgebraicRigidity R R_star
    (star_security_witness_1 R m)
    star_threshold_witness
    star_round_complexity.

(* Verify that derived properties instantiate correctly *)

Lemma star_complexity (L : nat) :
  (@search_space R_star L <= #|pgg_G R_star|)%N.
Proof. exact: search_space_leG. Qed.

(* Search chain needs RAAGType *)
Let R_star_raag : RAAGType := @Gen_PGGTypes m m.+1 (star_gen_tuple m).

Lemma star_search_chain (L : nat) :
  ((@search_space R_star_raag L <= @n_traces R_star_raag L) &&
   (@n_traces R_star_raag L <= m.+1 ^ L))%N.
Proof. exact: search_space_chain. Qed.

Lemma star_tradeoff :
  let cs := tw_covering (ar_threshold star_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_star| <= pgl_bound R_star)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_star star_covering star_genus0_pgl).
Qed.

End star_rigidity.
