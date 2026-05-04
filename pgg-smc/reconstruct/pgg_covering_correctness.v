(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Protocol + Covering Scheme: End-to-End Correctness                     *)
(*                                                                            *)
(* Capstone file unifying the protocol layer (PGGInterface) with the          *)
(* algebraic layer (CoveringScheme + security-threshold tradeoff +            *)
(* multiplicative extension).                                                 *)
(*                                                                            *)
(* The main results:                                                          *)
(*   pgg_covering_correct   == For any MonodromyReprType M with a compatible  *)
(*     CoveringScheme, the PGG protocol correctly reconstructs secrets.       *)
(*   covering_gap_bound     == The threshold gap is bounded by 2 * genus.     *)
(*   pgg_covering_tradeoff  == Either genus 0 with exact threshold, or        *)
(*     positive genus with bounded gap — instantiating the main tradeoff.     *)
(*   pgg_multiplicative_correct == Multiplying shares locally computes the    *)
(*     product secret in the doubled scheme.                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div ssralg finalg.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import covering_scheme cover_tradeoff.
From pgg_reconstruct Require Import ag_multiplicative.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Protocol Correctness via CoveringScheme                     *)
(******************************************************************************)

Section pgg_covering.

Variable M : MonodromyReprType.
Variable cs : CoveringScheme M.
Variable PI : PGGInterface M.

Let N := (pgg_N' M).+1.
Let G := pgg_G M.
Let rho := @pgg_rho M.
Let ts := cs_scheme cs.

Hypothesis HT : ts_T' ts = pi_T' PI.

(* Main correctness theorem: CoveringScheme + PGGInterface + G-stable starts
   -> reconstruction recovers the hidden value. Uses pgg_hidden_invariant_perm
   with cs_recon_invariant. *)
Theorem pgg_covering_correct (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in G ->
       forall i : 'I_(ts_T' ts).+1,
         rho g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
         tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) (cs_monodromy cs g i)) :
  P \in G ->
  ts_valid ts s (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_hidden_invariant_perm (perm := cs_monodromy cs)) => //.
exact: cs_recon_invariant.
Qed.

(* The threshold gap is bounded by twice the covering genus *)
Lemma covering_gap_bound :
  ts_T ts - ts_k ts <= 2 * cd_genus (cs_data cs).
Proof. exact: gap_bound. Qed.

End pgg_covering.

(******************************************************************************)
(*     Section 2: Tradeoff Instantiation                                      *)
(******************************************************************************)

Section covering_tradeoff.

Variable M : GeneratedMonodromyReprType.
Let G := pgg_G M.

(* Genus 0 -> |G| bounded by PGL(2,N) *)
Hypothesis genus0_pgl :
  forall (cd : CoveringData M),
    cd_genus cd = 0 -> #|G| <= pgl_bound M.

(* The security-threshold tradeoff, restated for the capstone:
   Either the covering has genus 0 (exact threshold, bounded group)
   or genus > 0 (threshold gap proportional to genus). *)
Theorem pgg_covering_tradeoff (cs : CoveringScheme M) :
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof. exact: (@security_threshold_tradeoff M cs (@genus0_pgl (cs_data cs))). Qed.

End covering_tradeoff.

(******************************************************************************)
(*     Section 3: Multiplicative Extension                                    *)
(******************************************************************************)

Section multiplicative_covering.

Variable F : finFieldType.
Variable ms : @MultiplicativeScheme F.

(* Multiplying shares locally computes the product secret in the doubled
   scheme. This is the key property enabling secure multiplication gates
   in arithmetic circuits over secret-shared data. *)
Theorem pgg_multiplicative_correct (s1 s2 : F)
    (shares1 shares2 : (ts_T' (ms_base ms)).+1.-tuple F) :
  ts_valid (ms_base ms) s1 shares1 ->
  ts_valid (ms_base ms) s2 shares2 ->
  ts_valid (ms_doubled ms) (s1 * s2)
    (cast_tuple (congr1 S (ms_T_eq ms))
      [tuple tnth shares1 i * tnth shares2 i
       | i < (ts_T' (ms_base ms)).+1]).
Proof. exact: ms_mult. Qed.

End multiplicative_covering.
