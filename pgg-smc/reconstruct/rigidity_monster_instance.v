(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Monster Group Algebraic Rigidity Instance                                  *)
(*                                                                            *)
(* The Monster group M is the largest of the 26 sporadic simple finite        *)
(* groups, with order                                                         *)
(*   |M| = 2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 *          *)
(*         29 * 31 * 41 * 47 * 59 * 71   (approx 8 * 10^53).                 *)
(*                                                                            *)
(* Discovered by Fischer and Griess, it was first constructed by Griess       *)
(* (1982) as the automorphism group of a 196,884-dimensional commutative      *)
(* non-associative algebra. It is connected to number theory through          *)
(* Monstrous Moonshine (Conway-Norton conjecture 1979, proved by              *)
(* Borcherds 1992, Fields Medal).                                             *)
(*                                                                            *)
(* Key facts relevant to SMC-PGG:                                             *)
(* - Smallest faithful permutation degree N ~ 10^20 (97,239,461,142,009,     *)
(*   186,000 points — the index of the largest maximal subgroup)              *)
(* - 2-generated: every finite simple group is 2-generated (Steinberg)        *)
(* - The Monster is far too large to enumerate computationally                *)
(*                                                                            *)
(* SMC-PGG implications:                                                      *)
(* - Security is astronomically strong: N ~ 10^20 sheets, search space ~      *)
(*   |M| ~ 10^53 — no feasible brute-force attack on the monodromy           *)
(* - Threshold is catastrophic: genus ~ |M| ~ 10^53 — the covering           *)
(*   genus grows with |G|, so the threshold gap is enormous                   *)
(* - This illustrates the security/threshold coupling in AlgebraicRigidity:   *)
(*   large groups give strong security but poor threshold, and conversely     *)
(*                                                                            *)
(* All group-level data (generators, L-freeness) is axiomatized since the     *)
(* Monster is not computationally enumerable in Rocq. The algebraic           *)
(* properties (SecurityWitness, derived theorems) are proved, showing that    *)
(* protocol correctness depends only on algebraic structure, not on           *)
(* computability.                                                             *)
(*                                                                            *)
(* Axioms (5):                                                                *)
(*   monster_n      : number of sheets (abstract, known to be ~ 10^20)       *)
(*   monster_sigmas : two generators (exist by Steinberg's theorem)           *)
(*   monster_sigmas_distinct : generators are distinct permutations          *)
(*   monster_covering : existence of a covering scheme                        *)
(*   monster_genus0_pgl : genus-0 coverings have |G| <= PGL(2,N)             *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   monster_security_witness_1 : SecurityWitness (via var_dist_lfree_uniform)*)
(*   monster_round_complexity : RoundComplexityWitness (L=1, depth=1)        *)
(*   monster_rigidity : AlgebraicRigidity (security + threshold + rounds)    *)
(*   monster_complexity : search space <= |G|                                 *)
(*   monster_tradeoff : genus-0/bounded or genus>0/gap dichotomy             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Group Axioms                                                           *)
(******************************************************************************)

(* monster_n.+2 = number of sheets in the smallest faithful permutation
   representation of the Monster group (~ 10^20) *)
Axiom monster_n : nat.

(* Two generators — every finite simple group is 2-generated (Steinberg) *)
Axiom monster_sigmas : 2.-tuple {perm 'I_monster_n.+2}.

Definition M_monster := @Gen_PGGTypes 1 monster_n monster_sigmas.
Definition R_monster : GeneratedMonodromyReprType := M_monster.

(* Generators are distinct: weaker than L-freeness, implies it via
   gen_inj_lfree1. Axiomatized because the generators are abstract. *)
Axiom monster_sigmas_distinct :
  injective (fun i : 'I_2 => tnth monster_sigmas i).

Lemma monster_lfree1 : @lfree M_monster 1.
Proof. exact: gen_inj_lfree1 monster_sigmas_distinct. Qed.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section monster_security.

Variable R : realType.

(* SecurityWitness at L=1 (the smallest L with lfree for Monster).
   Epsilon = 2*(N!-Tg)/N!. Any larger L with lfree gives a tighter bound;
   see security_witness_any_L for the generic constructor. *)
Definition monster_security_witness_1 : SecurityWitness R R_monster :=
  security_witness_any_L R monster_lfree1.

End monster_security.

(******************************************************************************)
(*     ThresholdWitness (Axiomatized)                                         *)
(******************************************************************************)

(******************************************************************************)
(*     AlgebraicRigidity Instance (with axiomatized threshold)                *)
(******************************************************************************)

Section monster_rigidity.

Variable R : realType.

(* Axiom: the Monster admits a covering scheme.
   Like the star instance, this requires algebraic geometry (covering
   spaces of Riemann surfaces) beyond this formalization. *)
Axiom monster_covering : CoveringScheme R_monster.

(* Axiom: for the monster covering, genus 0 implies |G| <= PGL(2,N).
   This is about the SPECIFIC covering scheme, not universal.
   For the Monster (|G| ~ 10^53), this is vacuously true since the
   covering genus is necessarily > 0 for such a large group. *)
Axiom monster_genus0_pgl :
  cd_genus (cs_data monster_covering) = 0 ->
  (#|pgg_G R_monster| <= pgl_bound R_monster)%N.

Definition monster_threshold_witness : ThresholdWitness R_monster :=
  @MkThresholdWitness R_monster monster_covering monster_genus0_pgl.

(* Round complexity at L=1: depth = 1, trivial bound *)
Definition monster_round_complexity : RoundComplexityWitness :=
  @MkRoundComplexityWitness 1 1 (leqnn 1).

Definition monster_rigidity : AlgebraicRigidity R R_monster :=
  @MkAlgebraicRigidity R R_monster
    (monster_security_witness_1 R)
    monster_threshold_witness
    monster_round_complexity.

(* Derived properties — all PROVED from the axioms *)

Lemma monster_complexity (L : nat) :
  (@search_space R_monster L <= #|pgg_G R_monster|)%N.
Proof. exact: search_space_leG. Qed.

Lemma monster_tradeoff :
  let cs := tw_covering (ar_threshold monster_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_monster| <= pgl_bound R_monster)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_monster monster_covering monster_genus0_pgl).
Qed.

End monster_rigidity.
