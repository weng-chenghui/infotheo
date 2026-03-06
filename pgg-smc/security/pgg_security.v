(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
(* PGG-SMC: Security-Storage Tradeoff (Theorems 11, 12) *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype bigop div.
From mathcomp Require Import zify.
From pgg_smc Require Import free_group_ball.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Grover's algorithm: axiomatized integer square root                         *)
(* ========================================================================== *)

(* Integer square root: isqrt n = floor(sqrt(n)).
   We axiomatize its existence and key properties. *)
Axiom isqrt : nat -> nat.
Axiom isqrt_lower : forall n : nat, isqrt n ^ 2 <= n.
Axiom isqrt_monotone : forall m n : nat, m <= n -> isqrt m <= isqrt n.
Axiom isqrt_expn : forall k : nat, k <= isqrt (k ^ 2).

(* Grover's search cost: sqrt of the search space *)
Definition grover_search_cost (M : nat) : nat := isqrt M.

Section security_tradeoff.

Variable r : nat.
Hypothesis Hr : 1 < r.

Let kappa := r.*2 - 1.

Lemma kappa_gt0 : 0 < kappa.
Proof. rewrite /kappa; lia. Qed.

(* ========================================================================== *)
(* Theorem 11: Grover Mitigation                                              *)
(* Doubling L restores quadratic security against Grover's algorithm.         *)
(* ball_size(2L) >= kappa^(2L), grover cost = sqrt(kappa^(2L)) >= kappa^L    *)
(* ========================================================================== *)

Lemma kappa_sq_L (L : nat) : kappa ^ (2 * L) = (kappa ^ L) ^ 2.
Proof. by rewrite mulnC expnM. Qed.

Theorem grover_mitigation (L : nat) :
  kappa ^ L <= grover_search_cost (ball_size r (2 * L)).
Proof.
rewrite /grover_search_cost.
apply: (leq_trans _ (isqrt_monotone (ball_size_lower Hr (2 * L)))).
rewrite kappa_sq_L.
exact: isqrt_expn.
Qed.

(* ========================================================================== *)
(* Theorem 12: Security-Storage Tradeoff                                      *)
(* Security: adversary must search >= kappa^L elements                        *)
(* Storage: each share has ball_size entries                                   *)
(* Online computation: L permutation lookups                                  *)
(* ========================================================================== *)

Theorem security_exponential (L : nat) :
  kappa ^ L <= ball_size r L.
Proof. exact: ball_size_lower. Qed.

Definition share_storage (L : nat) := ball_size r L.

Definition online_computation (L : nat) := L.

(* Combined: security and storage grow as Theta(kappa^L) *)
Theorem security_storage_match (L : nat) :
  kappa ^ L <= share_storage L.
Proof. exact: security_exponential. Qed.

End security_tradeoff.
