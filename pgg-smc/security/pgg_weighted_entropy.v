(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Weighted Entropy                                                       *)
(*                                                                            *)
(* Standalone lemmas factored out of pgg_entropy_security.v for reuse         *)
(* in the weighted generator pipeline (Step 7).                               *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   KL_div_uniform == D(P || U_{n+1}) = log(n+1) - H(P)                    *)
(*     Standard identity relating KL divergence from uniform to entropy.     *)
(*     This is the rearrangement of entropy_log_div from entropy_convex.     *)
(*                                                                            *)
(* Definitions:                                                                *)
(*   fiber_entropy_weighted == entropy of a weighted endpoint distribution     *)
(*     Wrapper around fiber_entropy with explicit weight parameter.           *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_from_weighted_entropy == Pinsker bridge for weighted entropy     *)
(*     var_dist(P, U) <= sqrt(2 * (log N - H_weighted))                      *)
(*     Specializes the general Pinsker bridge to weighted distributions.     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From mathcomp Require Import reals exp.
From infotheo Require Import realType_ext realType_ln fdist proba variation_dist.
From infotheo Require Import divergence entropy pinsker entropy_convex.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1: KL divergence from uniform = log N - H(P)                      *)
(*                                                                            *)
(*  Standalone version of the identity that was inlined in                     *)
(*  security_witness_from_entropy (pgg_entropy_security.v:572-574).           *)
(******************************************************************************)

Section KL_div_uniform_section.

Variable R : realType.
Variable n : nat.
Variable P : R.-fdist 'I_n.+1.

Lemma KL_div_uniform :
  D(P || fdist_uniform (card_ord n.+1)) = log n.+1%:R - `H P.
Proof.
have Helog := @entropy_log_div R _ P _ (card_ord n.+1).
rewrite card_ord in Helog.
by rewrite Helog opprB addrCA subrr addr0.
Qed.

End KL_div_uniform_section.

(******************************************************************************)
(*  Section 2: Weighted endpoint entropy                                      *)
(*                                                                            *)
(*  A definition wrapper: the entropy of the endpoint distribution arising     *)
(*  from a weighted generator selection. In the weighted pipeline, the        *)
(*  dealer samples generators with non-uniform weights, producing a          *)
(*  different permutation distribution than rho_from_words. The entropy       *)
(*  of the resulting endpoint distribution is the key quantity for security.  *)
(******************************************************************************)

Section fiber_entropy_weighted_section.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

(* The weighted endpoint entropy: given any distribution rho_dist over
   permutations, the entropy of the pushforward through sigma |-> sigma(s)
   measures how much information the endpoint reveals. *)
Definition fiber_entropy_weighted
    (rho_dist : R.-fdist {perm 'I_N})
    (s : 'I_N) : R :=
  `H (fdistmap (fun sigma : {perm 'I_N} => sigma s) rho_dist).

End fiber_entropy_weighted_section.

(******************************************************************************)
(*  Section 3: Pinsker bridge for weighted entropy                            *)
(*                                                                            *)
(*  var_dist(P_s, U_N) <= sqrt(2 * (log N - fiber_entropy_weighted rho s))   *)
(*  Combines KL_div_uniform with Pinsker's inequality.                        *)
(******************************************************************************)

Section var_dist_weighted_section.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable rho_dist : R.-fdist {perm 'I_N}.

Let P_s (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s) rho_dist.

Lemma var_dist_from_weighted_entropy (s : 'I_N) :
  var_dist (P_s s) (fdist_uniform (card_ord N)) <=
  Num.sqrt (2%:R * (log N%:R - fiber_entropy_weighted rho_dist s)).
Proof.
rewrite /fiber_entropy_weighted -/N -/(P_s s).
have Hpinsker := Pinsker_inequality_weak
                   (dom_by_uniform (P_s s) (card_ord N)).
apply: (le_trans Hpinsker).
rewrite ler_wsqrtr // ler_pM2l // ?(ltr0n _ 2) //.
rewrite KL_div_uniform.
exact: lexx.
Qed.

End var_dist_weighted_section.
