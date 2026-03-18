(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Dealer Bridge: Solver Output to Protocol Correctness                       *)
(*                                                                            *)
(* Connects the solver-determined word length (from SecurityWitness) to the   *)
(* session-typed protocol (dealer_from_words) via AlgebraicRigidity.          *)
(*                                                                            *)
(*   dealer_words_correct == end-to-end: word of solver-determined length L   *)
(*     produces a correct protocol execution                                  *)
(*   dealer_words_epsilon_bound == endpoint security bound from the           *)
(*     AlgebraicRigidity witness                                              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_pismc.
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework
                                    covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.

Section dealer_bridge.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Variable PI : PGGInterface M.
Variable ar : AlgebraicRigidity R M.

Let L := sw_L (ar_security ar).
Let Tg := (@pgg_ngens' M).+1.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let G := pgg_G M.

Variable HT : ts_T' (cs_scheme (tw_covering (ar_threshold ar))) = pi_T' PI.
Hypothesis G_stable : forall g, g \in G ->
  forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1,
    @pgg_rho M g
      (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
    tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI))
      (cs_perm (tw_covering (ar_threshold ar)) g i).

Theorem dealer_words_correct
    (w : L.-tuple 'I_Tg) (s : 'I_N) :
  let P := @word_eval M L w in
  P \in G ->
  ts_valid (cs_scheme (tw_covering (ar_threshold ar))) s
    (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> /= PG Hvalid.
exact: (@ar_protocol_correct R M ar PI HT s (word_eval w) G_stable PG Hvalid).
Qed.

Lemma dealer_words_epsilon_bound (s : 'I_N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                      (sw_rho_dist (ar_security ar)))
            (fdist_uniform (card_ord N))
   <= sw_epsilon (ar_security ar))%O.
Proof. exact: sw_endpoint_bound. Qed.

End dealer_bridge.
