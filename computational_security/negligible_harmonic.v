From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Require Import negligible.

(**md**************************************************************************)
(* # The harmonic pseudometric and Lipschitz decay at the point at infinity   *)
(*                                                                            *)
(* The security parameter is read as a point of the one-point                 *)
(* compactification of the positive integers.  At exponent c the parameter n  *)
(* has the coordinate n ^- c on the real line and the point at infinity has   *)
(* the coordinate 0; the distance between two points is the distance between  *)
(* their coordinates.  This is a pseudometric on option nat, and a metric on  *)
(* the positive parameters together with the point at infinity for c >= 1:    *)
(* the parameter 0 has the coordinate 0 ^- c = 0 of the point at infinity,    *)
(* and at c = 0 every parameter has the coordinate 1.  That is why every      *)
(* Lipschitz statement excludes the parameter 0.  At c = 1 the distance is    *)
(* the harmonic metric, and at c > 1 the coordinates are the c-th powers of   *)
(* the harmonic coordinates.  A function of the parameter is extended by zero *)
(* to the point at infinity.                                                  *)
(*                                                                            *)
(* Negligibility is then a Lipschitz condition at the point at infinity:      *)
(* |f n| <= L * n ^- c for every exponent c and a constant L depending on c.  *)
(* One exponent alone gives inverse polynomial decay of that order; the whole *)
(* family gives decay below every inverse monomial.  For a nonnegative f the  *)
(* condition is equivalent to negligible_fun: the constant absorbs the finite *)
(* prefix on which the eventual bound of negligible_fun says nothing, and the *)
(* exponent shift c + 1 turns a constant back into an eventual strict bound.  *)
(* negligible_lipschitz.v extends the condition from the point at infinity to *)
(* every pair of points other than the parameter 0.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*      harmonic_coord c x == n ^- c at the parameter n, 0 at the point at    *)
(*                            infinity                                        *)
(*     harmonic_dist c x y == |harmonic_coord c x - harmonic_coord c y|       *)
(*          harmonic_distC == harmonic_dist c is symmetric                    *)
(*       harmonic_dist_ge0 == harmonic_dist c is nonnegative                  *)
(*         harmonic_distxx == harmonic_dist c vanishes on the diagonal        *)
(*  harmonic_dist_triangle == the triangle inequality for harmonic_dist c     *)
(*     harmonic_dist_infty == the distance from the parameter n to the point  *)
(*                            at infinity is n ^- c                           *)
(*        extend_infty f x == f at a parameter, 0 at the point at infinity    *)
(*        inv_expn_le_base == b ^- k <= a ^- k for 0 < a <= b                 *)
(*    inv_expn_le_exponent == n ^- d <= n ^- c for 0 < n and c <= d           *)
(*  lipschitz_at_infty c f == |f n| <= L * n ^- c for some L and every        *)
(*                            positive n                                      *)
(*     lipschitz_const_ge0 == a constant L with |f n| <= L * n ^- c at every  *)
(*                            positive n is nonnegative                       *)
(*     lipschitz_at_inftyP == lipschitz_at_infty c f as a Lipschitz bound of  *)
(*                            extend_infty f at the point at infinity         *)
(*   lipschitz_at_infty_le == Lipschitz at infinity at exponent d gives it at *)
(*                            every exponent c <= d                           *)
(* negligible_fun_lipschitz_at_infty == a nonnegative f is negligible iff it  *)
(*                            is Lipschitz at infinity for every exponent     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section harmonic_metric.
Context {R : realType}.

(* The real coordinate of a point at exponent c.  A parameter n sits at
   n ^- c and the point at infinity at 0. *)
(* TODO: notation for the `option nat` which is \omega+1*)
Definition harmonic_coord (c : nat) (x : option nat) : R :=
  if x is Some n then n%:R ^- c else 0.

(* The harmonic pseudometric at exponent c, pulled back from the real line
   through the coordinates.  For c >= 1 it is a metric once the parameter 0
   is excluded. *)
Definition harmonic_dist (c : nat) (x y : option nat) : R :=
  `|harmonic_coord c x - harmonic_coord c y|.

Lemma harmonic_distC c x y : harmonic_dist c x y = harmonic_dist c y x.
Proof. by rewrite /harmonic_dist distrC. Qed.

Lemma harmonic_dist_ge0 c x y : 0 <= harmonic_dist c x y.
Proof. exact: normr_ge0. Qed.

Lemma harmonic_distxx c x : harmonic_dist c x x = 0.
Proof. by rewrite /harmonic_dist subrr normr0. Qed.

(* The triangle inequality, inherited from the real line. *)
Lemma harmonic_dist_triangle c x y z :
  harmonic_dist c x z <= harmonic_dist c x y + harmonic_dist c y z.
Proof. exact: ler_distD. Qed.

(* The distance of a parameter to the point at infinity is its inverse
   monomial. *)
Lemma harmonic_dist_infty c n : harmonic_dist c (Some n) None = n%:R ^- c.
Proof.
by rewrite /harmonic_dist /= subr0 ger0_norm // invr_ge0 exprn_ge0.
Qed.

(* A function of the parameter extended by zero to the point at infinity.
   For nonnegative f, negligibility is this extension being Lipschitz at
   infinity at every exponent. *)
Definition extend_infty (f : nat -> R) (x : option nat) : R :=
  if x is Some n then f n else 0.

(* Inverse powers of positive reals reverse the order of their bases.  At
   one exponent, a larger parameter sits closer to the point at infinity. *)
Lemma inv_expn_le_base (k : nat) (a b : R) :
  0 < a -> a <= b -> b ^- k <= a ^- k.
Proof.
move=> a0 ab; have b0 := lt_le_trans a0 ab.
by rewrite lef_pV2 ?posrE ?exprn_gt0 // lerXn2r // nnegrE ltW.
Qed.

(* At a positive parameter the coordinate decreases as the exponent grows.
   A Lipschitz bound at one exponent therefore implies it at smaller ones. *)
Lemma inv_expn_le_exponent (c d n : nat) :
  (0 < n)%N -> (c <= d)%N -> n%:R ^- d <= n%:R ^- c :> R.
Proof.
move=> n0 cd.
by rewrite lef_pV2 ?posrE ?exprn_gt0 ?ltr0n // ler_weXn2l // ler1n.
Qed.

End harmonic_metric.

Section lipschitz_at_infty.
Context {R : realType}.
Implicit Types (c d : nat) (f : nat -> R).

(* Lipschitz decay at the point at infinity with exponent c: |f n| is below
   L * n ^- c at every positive parameter.  The constant L is the Lipschitz
   constant of extend_infty f at the point at infinity in harmonic_dist c. *)
Definition lipschitz_at_infty c f : Prop :=
  exists L : R, forall n : nat, (0 < n)%N -> `|f n| <= L * n%:R ^- c.

(* A constant of a Lipschitz bound at the point at infinity is nonnegative.
   It therefore scales inequalities between coordinates without reversing
   them. *)
Lemma lipschitz_const_ge0 c f (L : R) :
  (forall n, (0 < n)%N -> `|f n| <= L * n%:R ^- c) -> 0 <= L.
Proof. by move/(_ 1%N isT); rewrite expr1n invr1 mulr1; apply: le_trans. Qed.

(* The condition in the vocabulary of the metric: the extension of f is
   Lipschitz at the point at infinity. *)
Lemma lipschitz_at_inftyP c f :
  lipschitz_at_infty c f <->
  exists L : R, forall x : option nat, x != Some 0%N ->
    `|extend_infty f x - extend_infty f None| <= L * harmonic_dist c x None.
Proof.
split=> -[L HL]; exists L.
  case=> [[|n]|] //= _; first by rewrite subr0 harmonic_dist_infty; exact: HL.
  by rewrite subrr normr0 harmonic_distxx mulr0.
move=> n n0; have := HL (Some n); rewrite /= subr0 harmonic_dist_infty.
by apply; rewrite -lt0n.
Qed.

(* Lipschitz decay at a larger exponent gives it at every smaller one. *)
Lemma lipschitz_at_infty_le c d f :
  (c <= d)%N -> lipschitz_at_infty d f -> lipschitz_at_infty c f.
Proof.
move=> cd [L HL]; exists L => n n0; apply: le_trans (HL n n0) _.
exact: (ler_wpM2l (lipschitz_const_ge0 HL) (inv_expn_le_exponent n0 cd)).
Qed.

(* A nonnegative function is negligible iff it is Lipschitz at the point at
   infinity for every exponent. *)
Lemma negligible_fun_lipschitz_at_infty f :
  (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c, lipschitz_at_infty c f.
Proof.
move=> f_ge0; split=> Hf c.
  (* The constant absorbs the finite prefix below the threshold N. *)
  have [N HN] := Hf c.
  pose M := \big[maxr/0]_(i < N.+1) (f i * i%:R ^+ c).
  exists (maxr 1 M) => n n0; rewrite ger0_norm //.
  have nc0 : 0 < n%:R ^- c :> R by rewrite invr_gt0 exprn_gt0 ?ltr0n.
  have [Nn|nN] := ltnP N n.
    apply/ltW/(lt_le_trans (HN n Nn)).
    by rewrite ler_peMl ?(ltW nc0) // le_max lexx.
  have nc : n%:R ^+ c != 0 :> R by rewrite expf_neq0 // pnatr_eq0 -lt0n.
  rewrite -[f n](mulfK nc) ler_wpM2r ?(ltW nc0) // le_max.
  by rewrite (le_bigmax _ _ (Ordinal (nN : (n < N.+1)%N))) orbT.
(* The exponent shift c + 1 restores an eventual strict bound. *)
have [L HL] := Hf c.+1; have L0 := lipschitz_const_ge0 HL.
exists (archi_bound L) => n Nn.
have n0 : (0 < n)%N by apply: leq_ltn_trans Nn.
have Ln : L < n%:R.
  by apply: lt_le_trans (archi_boundP L0) _; rewrite ler_nat; exact: ltnW.
rewrite -[f n]ger0_norm //; apply: le_lt_trans (HL n n0) _.
rewrite exprS invfM mulrA gtr_pMl ?invr_gt0 ?exprn_gt0 ?ltr0n //.
by rewrite ltr_pdivrMr ?ltr0n // mul1r.
Qed.

End lipschitz_at_infty.
