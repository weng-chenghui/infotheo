(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop binomial.
From pgg_smc Require Import pgg_interface abelian_word_collapse.

(******************************************************************************)
(* PGG-SMC: Abelian Security Collapse (Theorem 8, items (3)-(4))             *)
(*                                                                           *)
(* Item 3: In a regular (free + transitive) monodromy action, knowing the    *)
(* endpoint rho(g)(s) at a single sheet s determines g uniquely.             *)
(*                                                                           *)
(* Item 4: For abelian groups with regular action, an adversary seeing one   *)
(* endpoint can reconstruct the full permutation. Combined with B1           *)
(* (abelian_search_space_bound), the search space collapses to               *)
(* 'C(L + r - 1, r - 1) where r is the number of generators.               *)
(*                                                                           *)
(*   one_eval_determines_perm == regularity: one endpoint determines g       *)
(*   abelian_adversary_full_recovery == two words with same endpoint are eq  *)
(*   abelian_security_collapse == search_space <= 'C(L + ngens', ngens')     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Regular action -- one evaluation determines the permutation     *)
(* ========================================================================== *)

Section regular_action.

Variable M : MonodromyReprType.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let G := pgg_G M.

(* Regular action hypothesis: if two group elements act the same on any
   single sheet, they must be equal. This is stronger than faithfulness
   (which requires agreement on ALL points). Regularity = free + transitive. *)
Hypothesis Hreg : forall (g1 g2 : gT) (s : 'I_N),
  g1 \in G -> g2 \in G ->
  endpoint g1 s = endpoint g2 s -> g1 = g2.

Lemma one_eval_determines_perm (g1 g2 : gT) (s : 'I_N) :
  g1 \in G -> g2 \in G ->
  endpoint g1 s = endpoint g2 s -> g1 = g2.
Proof. exact: Hreg. Qed.

End regular_action.

(* ========================================================================== *)
(* Section 2: Abelian security collapse                                       *)
(* ========================================================================== *)

Section abelian_collapse.

Variable M : GeneratedMonodromyReprType.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.

Variable L : nat.

Hypothesis Habel : abelian G.

(* Regularity hypothesis for the monodromy representation *)
Hypothesis Hreg : forall (g1 g2 : gT) (s : 'I_N),
  g1 \in G -> g2 \in G ->
  endpoint g1 s = endpoint g2 s -> g1 = g2.

(* Helper: word_eval produces elements of G *)
Lemma word_eval_in_G (w : pgg_word M L) : word_eval w \in G.
Proof.
apply: (subsetP (achievable_sub M L)).
by apply/imsetP; exists w.
Qed.

(* Item 4: Adversary seeing one endpoint determines the group element.
   For words w1, w2: if endpoint(word_eval w1)(s) = endpoint(word_eval w2)(s),
   then word_eval w1 = word_eval w2. *)
Lemma abelian_adversary_full_recovery (w1 w2 : pgg_word M L) (s : 'I_N) :
  endpoint (word_eval w1) s = endpoint (word_eval w2) s ->
  word_eval w1 = word_eval w2.
Proof.
by move=> Heq; apply: (Hreg (word_eval_in_G w1) (word_eval_in_G w2) Heq).
Qed.

(* Security collapse: search space bounded by frequency vector count *)
Theorem abelian_security_collapse :
  search_space M L <= 'C(L + @pgg_ngens' M, @pgg_ngens' M).
Proof. exact: abelian_search_space_bound. Qed.

End abelian_collapse.
