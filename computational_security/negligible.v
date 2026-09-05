From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.

(**md**************************************************************************)
(* # Negligible families                                                      *)
(*                                                                            *)
(* A family of reals indexed by a security parameter is negligible when it    *)
(* eventually falls below every inverse monomial in that parameter.  This is  *)
(* the asymptotic reading of every concrete quantity of this directory: each  *)
(* epsilon of indcpa_game.v and each loss of epshop.v is measured at one      *)
(* fixed instance, where an asymptotic notion has nothing to measure, and     *)
(* negligible_fun states what a family of such instances must satisfy for a   *)
(* bound of that shape to vanish in the security parameter.                   *)
(*                                                                            *)
(* The negligible families form an additive submonoid of the families of      *)
(* reals: closed under addition, containing the zero family, and closed       *)
(* under a finite sum indexed by a list, which is the form a total over a     *)
(* list of hop labels takes.  That submonoid is downward closed, a family     *)
(* dominated pointwise by a negligible one being negligible, and that is the  *)
(* direction a security claim is read in.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*          negligible_fun f == f eventually falls below every inverse        *)
(*                              monomial in its argument                      *)
(*        negligible_fun_add == a sum of negligible families is negligible    *)
(*         negligible_fun_le == a family dominated pointwise by a negligible  *)
(*                              one is negligible                             *)
(*     negligible_fun_double == twice a negligible family is negligible       *)
(*       negligible_fun_cst0 == the zero family is negligible                 *)
(*        negligible_fun_sum == a finite sum of negligible families is        *)
(*                              negligible                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section negligible_asymptotics.
Context {R : realType}.

(* A function of the security parameter is negligible when it eventually falls
   below every inverse monomial.

   forall c : nat (Given any exponent c): Represents the upper bound of
   the attacker's capability.

   exists N : nat (There exists a threshold N): Guarantees that once our key
   length (security parameter n) exceeds this threshold N,
   the cryptosystem exhibits an absolute security advantage.

   f : nat -> R is a function that monitors attacker success probability (R)
   as the key gets longer (nat).

   f n < n%:R ^- c : Bound on the attacker's success
   probability (f(n). It means that when the security parameter is
   sufficiently large, the attacker's success probability drops strictly
   below any inverse monomial or polynomial.

   Katz and Lindell, Introduction to
   Modern Cryptography, 2nd edition, 2015, Definition 3.4, p. 48.

   FCF's negligible states the same test in negated form over its rational
   probability type, ~ (1 / x ^ c <= f x), a shape that needs no classical
   totality of the order; the CertiCrypt paper bounds an absolute value,
   |nu n| <= n ^- c.

   Classical reasoning is in scope here through boolp, and
   the intended arguments are nonnegative advantage families, so the test is
   the direct strict inequality, and the closure lemmas [negligible_fun_add]
   and [negligible_fun_le] are direct order arithmetic.

   Every bound in the DSDP files is stated at one fixed instance, where an
   asymptotic notion has nothing to measure.  What this supplies is the shape
   a family of instances must have for such a bound to vanish in the security
   parameter, which is the asymptotic form a computational security claim
   takes. *)
Definition negligible_fun (f : nat -> R) : Prop :=
  forall c : nat, exists N : nat,
    forall n : nat, (N < n)%N -> f n < n%:R ^- c.

(* Negligible functions are closed under addition.  A security bound written
   as a sum of per-hop advantages stays negligible when each summand is, so a
   chain of two hops is bounded one hop at a time. *)
Lemma negligible_fun_add (f g : nat -> R) :
  negligible_fun f -> negligible_fun g ->
  negligible_fun (fun n => f n + g n).
Proof.
move=> Hf Hg c.
have [Nf HNf] := Hf c.+1; have [Ng HNg] := Hg c.+1.
exists (maxn (maxn Nf Ng) 1) => n.
rewrite !gtn_max => /andP[/andP[HNfn HNgn] Hn1].
have Hn0 : (0 < n%:R :> R) by rewrite ltr0n (leq_trans _ Hn1).
apply: lt_le_trans (_ : n%:R ^- c.+1 + n%:R ^- c.+1 <= _).
  by rewrite ltrD // ?HNf ?HNg.
rewrite exprS invfM -mulrDl -[X in _ <= X]mul1r.
rewrite ler_pM2r ?invr_gt0 ?exprn_gt0 //.
by rewrite -div1r -mulrDl ler_pdivrMr // mul1r -(natrD R 1 1) ler_nat.
Qed.

(* A nonnegative function dominated pointwise by a negligible function is
   negligible.  A success probability bounded by a negligible bound is
   therefore itself negligible, which is the direction a security claim is
   read in. *)
Lemma negligible_fun_le (f g : nat -> R) :
  (forall n, f n <= g n) -> negligible_fun g -> negligible_fun f.
Proof.
move=> Hfg Hg c; have [N HN] := Hg c.
by exists N => n Hn; apply: le_lt_trans (Hfg n) (HN n Hn).
Qed.

(* Twice a negligible function is negligible.  A reduction that calls its
   assumption once per experiment bounds one key at twice the assumed
   advantage, and the family of such bounds vanishes exactly when the assumed
   family does. *)
Lemma negligible_fun_double (f : nat -> R) :
  negligible_fun f -> negligible_fun (fun k => 2 * f k).
Proof.
move=> Hf; apply: negligible_fun_le (negligible_fun_add Hf Hf) => k.
by rewrite mulr_natl mulr2n.
Qed.

(* The zero family is negligible: the unit of the additive submonoid the
   negligible families form, and so the value a total over no labels takes. *)
Lemma negligible_fun_cst0 : negligible_fun (fun _ : nat => 0 : R).
Proof. by move=> c; exists 0 => n Hn; rewrite invr_gt0 exprn_gt0 // ltr0n. Qed.

(* A finite sum of negligible families is negligible.  A total over a list of
   hop labels sums the cost family of each label, so this is the closure the
   asymptotic reading of such a total needs, one summand per label. *)
Lemma negligible_fun_sum (I : Type) (s : seq I) (F : I -> nat -> R) :
  (forall i, negligible_fun (F i)) ->
  negligible_fun (fun k => \sum_(i <- s) F i k).
Proof.
move=> HF; elim: s => [|i s IH].
  by apply: negligible_fun_le negligible_fun_cst0 => k; rewrite big_nil lexx.
apply: negligible_fun_le (negligible_fun_add (HF i) IH) => k.
by rewrite big_cons lexx.
Qed.

End negligible_asymptotics.
