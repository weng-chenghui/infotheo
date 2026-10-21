From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Require Import negligible negligible_harmonic.

(**md**************************************************************************)
(* # Negligibility as Lipschitz continuity in the harmonic metric             *)
(*                                                                            *)
(* negligible_harmonic.v reads negligibility as a Lipschitz bound of the      *)
(* extended function at the single point at infinity.  This file lifts that   *)
(* bound to every pair of points: a nonnegative f is negligible iff, for      *)
(* every positive exponent c, |f m - f n| is at most a constant times the     *)
(* distance |m ^- c - n ^- c|, with the point at infinity included.  This is  *)
(* Lipschitz continuity in the textbook sense, between any two points other   *)
(* than the parameter 0.                                                      *)
(*                                                                            *)
(* The bound at the point at infinity is the pair (n, infinity) of the        *)
(* two-point bound.  The converse rests on one inequality: for 0 < m < n and  *)
(* a positive exponent c, m ^- (c + 1) <= 2 * (m ^- c - n ^- c), so the       *)
(* distance between two parameters is at least half an inverse monomial of    *)
(* the smaller one, one order higher.  Decay of order c + 1 at the point at   *)
(* infinity then bounds the variation of f between any two parameters by four *)
(* times the distance at exponent c.                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*         harmonic_lipschitz c f == extend_infty f is Lipschitz on the       *)
(*                                   points other than the parameter 0 in     *)
(*                                   harmonic_dist c                          *)
(*           harmonic_dist_ge_inv == m ^- (c + 1) <= 2 * harmonic_dist c m n  *)
(*                                   for 0 < m < n and 0 < c                  *)
(*            harmonic_lipschitzW == Lipschitz on every pair gives            *)
(*                                   Lipschitz at the point at infinity       *)
(*   lipschitz_at_inftyS_harmonic == Lipschitz at infinity with exponent      *)
(*                                   c + 1 gives Lipschitz on every pair at   *)
(*                                   exponent c                               *)
(* negligible_fun_harmonic_lipschitz == a nonnegative f is negligible iff     *)
(*                                   Lipschitz in the harmonic metric at      *)
(*                                   every positive exponent                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section harmonic_lipschitz.
Context {R : realType}.
Implicit Types (c m n : nat) (f : nat -> R).

(* Lipschitz continuity of the extension of f in the harmonic metric at
   exponent c, away from the parameter 0.  That parameter is excluded because
   its coordinate coincides with the point at infinity. *)
Definition harmonic_lipschitz c f : Prop :=
  exists L : R, forall x y : option nat, x != Some 0%N -> y != Some 0%N ->
    `|extend_infty f x - extend_infty f y| <= L * harmonic_dist c x y.

(* At a positive exponent, two parameters are at least half an inverse
   monomial of the smaller apart, one order up. *)
Lemma harmonic_dist_ge_inv c m n :
  (0 < c)%N -> (0 < m)%N -> (m < n)%N ->
  m%:R ^- c.+1 <= 2 * harmonic_dist c (Some m) (Some n) :> R.
Proof.
case: c => // c _ m0 mn.
have m0R : 0 < m%:R :> R by rewrite ltr0n.
rewrite /harmonic_dist /= ger0_norm; last first.
  rewrite subr_ge0; apply: inv_expn_le_base m0R _.
  by rewrite ler_nat; exact: ltnW.
pose a : R := m%:R; pose b : R := m.+1%:R.
have b0 : 0 < b by rewrite ltr0n.
have a_neq0 := lt0r_neq0 m0R; have b_neq0 := lt0r_neq0 b0.
apply: le_trans (_ : _ <= 2 * (a ^- c.+1 - a ^- c / b)) _.
  rewrite 2!exprSr 2!invfM -mulrBr mulrCA -mulrA.
  rewrite ler_pM2l ?invr_gt0 ?exprn_gt0 //.
  have -> : a^-1 - b^-1 = a^-1 / b.
    apply: (mulIf b_neq0); rewrite mulfVK // mulrBl mulVf //.
    by rewrite /b -addn1 natrD mulrDr mulVf // mulr1 addrC addKr.
  rewrite mulrCA ler_pM2l ?invr_gt0 // ler_pdivlMr // mulrC ler_pdivrMr //.
  by rewrite -natrM ler_nat mul2n -addnn -addn1 leq_add2l.
have bn : b <= n%:R by rewrite ler_nat.
rewrite ler_pM2l // lerB // (le_trans (inv_expn_le_base _ b0 bn)) //.
rewrite exprSr invfM ler_pM2r ?invr_gt0 //.
by apply: inv_expn_le_base m0R _; rewrite ler_nat.
Qed.

(* Lipschitz continuity on every pair restricts to the pairs with the point
   at infinity. *)
Lemma harmonic_lipschitzW c f :
  harmonic_lipschitz c f -> lipschitz_at_infty c f.
Proof.
move=> [L HL]; apply/lipschitz_at_inftyP; exists L => x x0; exact: HL.
Qed.

(* Decay of order c + 1 at the point at infinity bounds the variation of f
   between any two points.  The bound is four times the distance at
   exponent c. *)
Lemma lipschitz_at_inftyS_harmonic c f :
  (0 < c)%N -> lipschitz_at_infty c.+1 f -> harmonic_lipschitz c f.
Proof.
move=> c0 [L HL]; have L0 := lipschitz_const_ge0 HL.
have le_L4L : L <= 4 * L by rewrite ler_peMl // ler1n.
have Hinf n : (0 < n)%N -> `|f n| <= 4 * L * n%:R ^- c.
  move=> n0; apply: le_trans (HL n n0) _.
  rewrite ler_pM ?invr_ge0 ?exprn_ge0 //.
  exact: inv_expn_le_exponent n0 (leqnSn c).
have Hlt m n : (0 < m)%N -> (m < n)%N ->
    `|f m - f n| <= 4 * L * harmonic_dist c (Some m) (Some n).
  move=> m0 mn; have n0 := ltn_trans m0 mn.
  apply: le_trans (ler_normB _ _) _.
  apply: le_trans (lerD (HL m m0) (HL n n0)) _.
  apply: le_trans (_ : _ <= 2 * L * m%:R ^- c.+1) _.
    rewrite -mulrA mulr2n mulrDl mul1r lerD2l ler_wpM2l //.
    by apply: inv_expn_le_base; [rewrite ltr0n | rewrite ler_nat; exact: ltnW].
  rewrite (_ : 4 * L = 2 * L * 2); last by rewrite mulrAC -natrM.
  rewrite -[_ * 2 * _]mulrA ler_wpM2l ?mulr_ge0 //; exact: harmonic_dist_ge_inv.
exists (4 * L) => -[[|m]|] [[|n]|] //= _ _.
- have [mn|nm|->] := ltngtP m n.
  + exact: Hlt.
  + by rewrite distrC harmonic_distC Hlt.
  + by rewrite subrr normr0 harmonic_distxx mulr0.
- by rewrite subr0 harmonic_dist_infty Hinf.
- by rewrite sub0r normrN harmonic_distC harmonic_dist_infty Hinf.
- by rewrite subrr normr0 harmonic_distxx mulr0.
Qed.

(* A nonnegative function is negligible iff its extension is Lipschitz in
   the harmonic metric at every positive exponent.  Negligibility is thus
   Lipschitz continuity away from the parameter 0, one exponent per inverse
   monomial. *)
Theorem negligible_fun_harmonic_lipschitz f :
  (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c, (0 < c)%N -> harmonic_lipschitz c f.
Proof.
move=> f_ge0; rewrite (negligible_fun_lipschitz_at_infty f_ge0).
split=> Hf c; first by move=> c0; exact: lipschitz_at_inftyS_harmonic (Hf c.+1).
apply: lipschitz_at_infty_le (leqnSn c) _.
exact: harmonic_lipschitzW (Hf c.+1 isT).
Qed.

End harmonic_lipschitz.
