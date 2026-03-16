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
    forall cd : CoveringData M,
      cd_genus cd = 0 -> #|G| <= pgl_bound M
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
apply: (@security_threshold_tradeoff M (tw_genus0_pgl (ar_threshold ar))).
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
apply: (@search_gap_tradeoff M (tw_genus0_pgl (ar_threshold ar))).
Qed.

(** Large groups force positive genus *)
Lemma ar_large_group_forces_gap :
  let cs := tw_covering (ar_threshold ar) in
  pgl_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> /=.
apply: (@large_group_forces_gap M (tw_genus0_pgl (ar_threshold ar))).
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
