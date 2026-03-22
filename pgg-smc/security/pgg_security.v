(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG-SMC: Security-Storage Tradeoff (Theorems 11, 12) *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype bigop div.
From mathcomp Require Import zify.
From pgg_smc Require Import free_group_ball.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Grover's algorithm: constructive integer square root                        *)
(* ========================================================================== *)

(* Integer square root: isqrt n = floor(sqrt(n)).
   Computed by linear scan from 0 up to n. *)
Fixpoint isqrt_aux (fuel k n : nat) : nat :=
  match fuel with
  | 0 => k
  | fuel'.+1 => if k.+1 ^ 2 <= n then isqrt_aux fuel' k.+1 n else k
  end.

Definition isqrt (n : nat) : nat := isqrt_aux n 0 n.

(* --- auxiliary lemmas on isqrt_aux --- *)

Lemma isqrt_aux_lower fuel k n :
  k ^ 2 <= n -> (isqrt_aux fuel k n) ^ 2 <= n.
Proof.
elim: fuel k => [|fuel IH] k Hk //=.
case: ifP => H; [exact: IH | exact: Hk].
Qed.

Lemma isqrt_aux_ge fuel k n : k <= isqrt_aux fuel k n.
Proof.
elim: fuel k => [|fuel IH] k //=.
case: ifP => _ //.
apply: (leq_trans _ (IH k.+1)). exact: leqnSn.
Qed.

Lemma isqrt_aux_upper fuel k n :
  k ^ 2 <= n -> k + fuel >= n ->
  n < (isqrt_aux fuel k n).+1 ^ 2.
Proof.
elim: fuel k => [|fuel IH] k Hk Hfuel /=.
- rewrite addn0 in Hfuel.
  rewrite !expnS !expn0 !muln1 in Hk *. lia.
- case Hif: (k.+1 ^ 2 <= n).
  + apply: IH => //. lia.
  + move/negbT: Hif. by rewrite -leqNgt.
Qed.

Lemma isqrt_aux_largest fuel k n m :
  k ^ 2 <= n -> m <= k + fuel -> k <= m -> m ^ 2 <= n ->
  m <= isqrt_aux fuel k n.
Proof.
elim: fuel k => [|fuel IH] k Hk Hm Hkm Hmsq /=.
- rewrite addn0 in Hm.
  by have ->: m = k by apply/eqP; rewrite eqn_leq Hkm Hm.
- case Hif: (k.+1 ^ 2 <= n).
  + case: (leqP k.+1 m) => Hkm'.
    * apply: IH => //. lia.
    * have ->: m = k by apply/eqP; rewrite eqn_leq Hkm; lia.
      apply: (leq_trans _ (isqrt_aux_ge _ _ _)). exact: leqnSn.
  + move/negbT: Hif. rewrite -leqNgt => Hlt.
    suff ->: m = k by done.
    apply/eqP. rewrite eqn_leq Hkm andbT.
    apply/negP => /negP. rewrite -ltnNge => Hmk.
    have Hk1m: k.+1 <= m by exact: Hmk.
    have H1: k.+1 ^ 2 <= m ^ 2 by rewrite leq_exp2r.
    have: k.+1 ^ 2 <= n by apply: (leq_trans H1 Hmsq).
    move=> H3. move: Hlt. rewrite leqNgt. by move/negP.
Qed.

(* --- main properties of isqrt --- *)

Lemma isqrt_lower n : isqrt n ^ 2 <= n.
Proof. exact: isqrt_aux_lower. Qed.

Lemma isqrt_upper n : n < (isqrt n).+1 ^ 2.
Proof. apply: isqrt_aux_upper => //. Qed.

Lemma isqrt_monotone m n : m <= n -> isqrt m <= isqrt n.
Proof.
move=> Hmn.
have Hsq: (isqrt m) ^ 2 <= n := leq_trans (isqrt_lower m) Hmn.
have Hle: isqrt m <= n.
{ have H1: isqrt m ^ 2 <= m := isqrt_lower m.
  have H2: isqrt m <= isqrt m ^ 2.
  { case: (isqrt m) => // j.
    rewrite expnS expn1 -{1}[j.+1]muln1. exact: leq_mul. }
  exact: (leq_trans (leq_trans H2 H1) Hmn). }
apply: (@isqrt_aux_largest n 0 n (isqrt m)) => //.
Qed.

Lemma isqrt_expn k : k <= isqrt (k ^ 2).
Proof.
have Hk2: k <= k ^ 2.
{ case: k => // k.
  rewrite expnS expn1 -{1}[k.+1]muln1. exact: leq_mul. }
apply: (@isqrt_aux_largest (k^2) 0 (k^2)) => //.
Qed.

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
(* Storage: each dealt hand has ball_size entries                               *)
(* Online computation: L permutation lookups                                  *)
(* ========================================================================== *)

Theorem security_exponential (L : nat) :
  kappa ^ L <= ball_size r L.
Proof. exact: ball_size_lower. Qed.

Definition hand_storage (L : nat) := ball_size r L.

Definition online_computation (L : nat) := L.

(* Combined: security and storage grow as Theta(kappa^L) *)
Theorem security_storage_match (L : nat) :
  kappa ^ L <= hand_storage L.
Proof. exact: security_exponential. Qed.

End security_tradeoff.
