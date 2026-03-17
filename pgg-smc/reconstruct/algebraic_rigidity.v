(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Algebraic Rigidity: One Algebraic Choice Determines Four Parameters        *)
(*                                                                            *)
(* Given a monodromy representation with generators M, the algebraic          *)
(* structure determines:                                                      *)
(*   1. Complexity — search_space L <= |G| (from pgg_interface.v)            *)
(*   2. Security — var_dist(rho_dist, uniform) <= epsilon (collusion_bound)  *)
(*   3. Threshold — gap <= 2*genus, with genus-0 -> gap=0 (covering_scheme)  *)
(*   4. Round complexity — depth <= L (trivial), refined for RAAG via Foata  *)
(*                                                                            *)
(* The key insight: all four are consequences of the single algebraic         *)
(* choice (G, rho, sigmas). No further degrees of freedom exist.             *)
(*                                                                            *)
(* Records:                                                                   *)
(*   SecurityWitness R M == packages the security guarantee                   *)
(*   ThresholdWitness M  == packages the covering scheme + PGL hypothesis     *)
(*   RoundComplexityWitness == packages word length, round depth, and bound   *)
(*   AlgebraicRigidity R M == combines all three into a unified witness       *)
(*                                                                            *)
(* Generic constructor:                                                       *)
(*   security_witness_any_L == SecurityWitness for ANY L with lfree(L)        *)
(*                                                                            *)
(* Note on SecurityWitness and L:                                             *)
(*   The security bound epsilon = 2*(N! - Tg^L)/N! is parametric in L:       *)
(*   var_dist_lfree_uniform proves it for any L where lfree(L) holds.         *)
(*   Since Tg^L is monotonically increasing in L, epsilon DECREASES with L:  *)
(*   larger L means more distinct group elements are reachable, bringing the  *)
(*   word distribution closer to uniform over S_N. Therefore:                 *)
(*     - The SMALLEST L with lfree(L) gives the WORST-CASE (largest) epsilon  *)
(*     - Concrete instances (S_5 at L=1, OC at L=2) pick this smallest L     *)
(*       because it represents the most conservative security guarantee       *)
(*     - All larger L with lfree(L) automatically have tighter bounds         *)
(*   The generic constructor security_witness_any_L makes this explicit:      *)
(*   given ANY (G, sigmas) and ANY L with lfree(L), it produces a valid      *)
(*   SecurityWitness.                                                         *)
(*                                                                            *)
(* Derived properties:                                                        *)
(*   ar_complexity      == search space bounded by |G|                        *)
(*   ar_tradeoff        == genus-0/bounded or genus>0/gap tradeoff           *)
(*   ar_search_gap_tradeoff == search space vs threshold gap                 *)
(*   ar_large_group_forces_gap == |G| > PGL -> genus > 0                    *)
(*   ar_gap_bound       == threshold gap <= 2*genus                          *)
(*   ar_protocol_correct == end-to-end protocol correctness                  *)
(*   ar_depth_bound     == round depth <= word length                        *)
(*                                                                            *)
(* RAAG-specific derived properties:                                          *)
(*   ar_search_space_chain == search_space <= n_traces <= Tg^L               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_lfree pgg_raag.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.

(******************************************************************************)
(*     Record Definitions                                                     *)
(******************************************************************************)

Section algebraic_rigidity_records.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Let N' := pgg_N' M.
Let G := pgg_G M.

Record SecurityWitness := MkSecurityWitness {
  sw_L : nat;
  sw_epsilon : R;
  sw_rho_dist : R.-fdist {perm 'I_N'.+1};
  sw_assumption1 :
    (var_dist sw_rho_dist
             (fdist_uniform (card_permT_N N')) <= sw_epsilon)%O
}.

Record ThresholdWitness := MkThresholdWitness {
  tw_covering : CoveringScheme M;
  tw_genus0_pgl :
    cd_genus (cs_data tw_covering) = 0 -> #|G| <= pgl_bound M
}.

Record RoundComplexityWitness := MkRoundComplexityWitness {
  rc_L : nat;        (* word length *)
  rc_depth : nat;    (* round count (= L for general, Foata depth for RAAG) *)
  rc_bound : rc_depth <= rc_L  (* depth never exceeds word length *)
}.

Record AlgebraicRigidity := MkAlgebraicRigidity {
  ar_security : SecurityWitness;
  ar_threshold : ThresholdWitness;
  ar_round_complexity : RoundComplexityWitness
}.

End algebraic_rigidity_records.

Arguments SecurityWitness R M : clear implicits.
Arguments ThresholdWitness M : clear implicits.
Arguments RoundComplexityWitness : clear implicits.
Arguments AlgebraicRigidity R M : clear implicits.

(******************************************************************************)
(*     Generic SecurityWitness Constructor                                    *)
(*                                                                            *)
(* The security bound var_dist(rho_L, uniform) <= 2*(N! - Tg^L)/N! holds     *)
(* for ANY L where lfree(L) is satisfied (see var_dist_lfree_uniform in       *)
(* pgg_collusion_bound.v). This constructor makes the generality explicit:    *)
(* given any generated monodromy representation and any L with lfree(L),      *)
(* it produces a SecurityWitness. Concrete instances (S_5, OC, etc.) pick     *)
(* specific L values — typically the smallest L with lfree(L), which gives    *)
(* the worst-case (largest) epsilon and thus the most conservative bound.     *)
(******************************************************************************)

Section generic_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(* For any L where lfree holds, we get a SecurityWitness *)
Definition security_witness_any_L (L : nat) (Hlfree : @lfree M L) :
    SecurityWitness R M :=
  @MkSecurityWitness R M L _
    (rho_from_words L sigmas)
    (@var_dist_lfree_uniform R _ m L sigmas Hlfree).

End generic_security.

(******************************************************************************)
(*     Derived Properties                                                     *)
(******************************************************************************)

Section derived_properties.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Variable ar : AlgebraicRigidity R M.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** Complexity: search space is bounded by |G| *)
Lemma ar_complexity (L : nat) : @search_space M L <= #|G|.
Proof. exact: search_space_leG. Qed.

(** Tradeoff: either genus-0 with bounded |G|, or positive genus with gap *)
Lemma ar_tradeoff :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@security_threshold_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar))).
Qed.

(** Search-gap tradeoff: search space bounded or threshold has gap *)
Lemma ar_search_gap_tradeoff (L : nat) :
  let cs := tw_covering (ar_threshold ar) in
  (@search_space M L <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@search_gap_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar)) L).
Qed.

(** Large groups force positive genus *)
Lemma ar_large_group_forces_gap :
  let cs := tw_covering (ar_threshold ar) in
  pgl_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> /=.
exact (@large_group_forces_gap M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar))).
Qed.

(** Gap bound: threshold gap is bounded by twice the genus *)
Lemma ar_gap_bound :
  let cs := tw_covering (ar_threshold ar) in
  ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).
Proof. move=> /=. exact: gap_bound. Qed.

(** Round complexity: depth is bounded by word length *)
Lemma ar_depth_bound :
  rc_depth (ar_round_complexity ar) <= rc_L (ar_round_complexity ar).
Proof. exact: rc_bound. Qed.

(** Protocol correctness: perm-compatible scheme + valid shares + G-stable starts *)
Lemma ar_protocol_correct (PI : PGGInterface M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold ar))) = pi_T' PI)
    (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in G ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1,
         @pgg_rho M g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
         tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI))
              (cs_perm (tw_covering (ar_threshold ar)) g i)) :
  P \in G ->
  ts_valid (cs_scheme (tw_covering (ar_threshold ar))) s
          (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_secret_invariant_perm (perm := cs_perm (tw_covering (ar_threshold ar)))) => //.
exact: cs_perm_compatible.
Qed.

End derived_properties.

(******************************************************************************)
(*     RAAG-Specific Derived Properties                                       *)
(******************************************************************************)

Section raag_derived_properties.

Variable R : realType.
Variable M : RAAGType.
Variable ar : AlgebraicRigidity R M.

Let Tg := (@pgg_ngens' M).+1.

(** Search space chain: search_space <= n_traces <= Tg^L (RAAG-specific) *)
Lemma ar_search_space_chain (L : nat) :
  (@search_space M L <= @n_traces M L) && (@n_traces M L <= Tg ^ L).
Proof. exact: search_space_chain. Qed.

End raag_derived_properties.
