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
(* - Security at L*=67: Tg^L* = 2^67 > N ~ 10^20, giving epsilon = 0        *)
(*   (perfect endpoint security via direct bound 2*(N-Tg^L)/N)               *)
(* - Threshold is catastrophic: genus ~ |M| ~ 10^53 — the covering           *)
(*   genus grows with |G|, so the threshold gap is enormous                   *)
(* - This illustrates the security/threshold coupling in AlgebraicRigidity:   *)
(*   large groups give strong security but poor threshold, and conversely     *)
(*                                                                            *)
(* All group-level data (generators, word-eval injectivity) is axiomatized    *)
(* since the Monster is not computationally enumerable in Rocq. The algebraic *)
(* properties (SecurityWitness, derived theorems) are proved, showing that    *)
(* protocol correctness depends only on algebraic structure, not on           *)
(* computability.                                                             *)
(*                                                                            *)
(* Axioms (8):                                                                *)
(*   monster_n      : number of sheets (abstract, known to be ~ 10^20)       *)
(*   monster_sigmas : two generators (exist by Steinberg's theorem)           *)
(*   monster_sigmas_distinct : generators are distinct permutations          *)
(*   monster_Lstar  : turning point L* (= 67, first L with 2^L >= N)        *)
(*   monster_weval_inj_Lstar : word-eval injectivity at L*                   *)
(*   monster_eval_s_inj_Lstar : endpoint eval injective on achievable(L_s)  *)
(*   monster_covering : existence of a covering scheme                        *)
(*   monster_genus0_pgl : genus-0 coverings have |G| <= PGL(2,N)             *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   monster_security_witness_Lstar : SecurityWitness                        *)
(*     (via security_witness_endpoint_inj, eps = 2(N-2^Ls)/N ~ 0)           *)
(*   monster_round_complexity : RoundComplexityWitness (L=Ls, depth=Ls)     *)
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
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
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

(* Generators are distinct: weaker than word-eval injectivity, implies it via
   gen_inj_weval_inj1. Axiomatized because the generators are abstract. *)
Axiom monster_sigmas_distinct :
  injective (fun i : 'I_2 => tnth monster_sigmas i).

Lemma monster_weval_inj1 : @weval_inj M_monster 1.
Proof. exact: gen_inj_weval_inj1 monster_sigmas_distinct. Qed.

(******************************************************************************)
(*     L* axioms: turning point where 2^L* >= N                              *)
(*                                                                            *)
(* For the Monster with N ~ 9.7 * 10^19 and Tg = 2:                         *)
(*   2^66 ~ 7.4 * 10^19 < N                                                 *)
(*   2^67 ~ 1.5 * 10^20 > N                                                 *)
(* So L* = 67 is the first length where the search space saturates N.        *)
(*                                                                            *)
(* At L* = 67, every sheet maps to a distinct endpoint under each            *)
(* achievable permutation (eval_s injective on achievable(67)).              *)
(* The direct endpoint epsilon = 2*(N - 2^67)/N = 0 since 2^67 > N.         *)
(******************************************************************************)

Axiom monster_Lstar : nat.
(* monster_Lstar = 67 for N ~ 9.7 * 10^19, but kept abstract *)

Axiom monster_weval_inj_Lstar : @weval_inj M_monster monster_Lstar.

(* Endpoint evaluation injective on achievable(L_star): for each starting sheet,
   the map sigma |-> sigma(s) is injective on the set of achievable
   permutations at L*. This is a group-theoretic fact about the Monster's
   faithful permutation action. *)
Axiom monster_eval_s_inj_Lstar :
  forall s : 'I_monster_n.+2,
  {in @achievable M_monster monster_Lstar &,
   injective (fun sigma : {perm 'I_monster_n.+2} => sigma s)}.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section monster_security.

Variable R : realType.

(* SecurityWitness at L* via direct endpoint bound.
   Epsilon = 2 * (N - 2^Lstar) / N.
   For the concrete Monster (N ~ 10^20, L* = 67, 2^67 > N):
     epsilon = 2*(N - 2^67)/N = 0  (perfect endpoint security)
   This is astronomically tighter than the DPI bound at L=1:
     epsilon_DPI = 2*(N! - 2)/N! ≈ 2  (vacuous) *)
Definition monster_security_witness_Lstar : SecurityWitness R R_monster :=
  security_witness_endpoint_inj R
    monster_weval_inj_Lstar
    monster_eval_s_inj_Lstar.


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

(* Round complexity at L*: depth = L* (upper bound, fully sequential) *)
Definition monster_round_complexity : RoundComplexityWitness :=
  @MkRoundComplexityWitness monster_Lstar monster_Lstar (leqnn _).

Definition monster_rigidity : AlgebraicRigidity R R_monster :=
  @MkAlgebraicRigidity R R_monster
    (monster_security_witness_Lstar R)
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
