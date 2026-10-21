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
(* Lipschitz continuity in the textbook sense, between any two points of the  *)
(* compactified parameter space.                                              *)
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
(*   harmonic_lipschitz c f == extend_infty f is Lipschitz on the points      *)
(*                             other than the parameter 0 in harmonic_dist c  *)
(*     harmonic_dist_ge_inv == m ^- (c + 1) <= 2 * harmonic_dist c m n for    *)
(*                             0 < m < n and 0 < c                            *)
(* harmonic_lipschitz_at_infty == Lipschitz on every pair gives Lipschitz at  *)
(*                             the point at infinity                          *)
(* lipschitz_at_infty_harmonic == Lipschitz at infinity with exponent c + 1   *)
(*                             gives Lipschitz on every pair at exponent c    *)
(* negligible_fun_harmonic_lipschitz == a nonnegative f is negligible iff     *)
(*                             Lipschitz in the harmonic metric at every      *)
(*                             positive exponent                              *)
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
Admitted.

(* Lipschitz continuity on every pair restricts to the pairs with the point
   at infinity. *)
Lemma harmonic_lipschitz_at_infty c f :
  harmonic_lipschitz c f -> lipschitz_at_infty c f.
Proof.
Admitted.

(* Decay of order c + 1 at the point at infinity bounds the variation of f
   between any two points.  The bound is four times the distance at
   exponent c. *)
Lemma lipschitz_at_infty_harmonic c f :
  (0 < c)%N -> lipschitz_at_infty c.+1 f -> harmonic_lipschitz c f.
Proof.
Admitted.

(* A nonnegative function is negligible iff its extension is Lipschitz in
   the harmonic metric at every positive exponent.  Negligibility is thus
   Lipschitz continuity on the compactified parameter space, one exponent
   per inverse monomial. *)
Theorem negligible_fun_harmonic_lipschitz f :
  (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c, (0 < c)%N -> harmonic_lipschitz c f.
Proof.
Admitted.

End harmonic_lipschitz.
