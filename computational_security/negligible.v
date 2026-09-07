From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.

(**md**************************************************************************)
(* # Negligible functions                                                     *)
(*                                                                            *)
(* A function of the security parameter into the reals is negligible when it  *)
(* eventually falls below every inverse monomial in that parameter.  This is  *)
(* the asymptotic reading of every concrete quantity of this directory: each  *)
(* epsilon of indcpa_game.v and each loss of epshop.v is measured at one      *)
(* fixed instance, where an asymptotic notion has nothing to measure, and     *)
(* negligible_fun states what a sequence of such instances must satisfy for   *)
(* a bound of that shape to vanish in the security parameter.                 *)
(*                                                                            *)
(* The negligible functions form an additive submonoid of the functions of    *)
(* the parameter: closed under addition, containing the zero function, and    *)
(* closed under a finite sum indexed by a list, which is the form a total     *)
(* over a list of hop labels takes.  That submonoid is downward closed, a     *)
(* function dominated pointwise by a negligible one being negligible, and     *)
(* that is the direction a security claim is read in.                         *)
(*                                                                            *)
(* FCF states the same test in negated form over its rational probability     *)
(* type, in src/FCF/Asymptotic.v lines 227-230 at commit 2550fa27.  The       *)
(* negated inequality needs no classical totality of the order.               *)
(*                                                                            *)
(* ```                                                                        *)
(* Definition negligible(f : nat -> Rat) :=                                   *)
(*   forall c, exists n, forall x (pf_nz : nz x),                             *)
(*     x > n ->                                                               *)
(*     ~ ((1 / expnat x c) <= f x)%rat.                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* The CertiCrypt paper bounds an absolute value instead, |nu n| <= n ^- c.   *)
(* Classical reasoning is in scope here through boolp, and the intended       *)
(* arguments are nonnegative advantage functions, so the test is the direct   *)
(* strict inequality and the closure lemmas are direct order arithmetic.      *)
(*                                                                            *)
(* ```                                                                        *)
(*          negligible_fun f == f eventually falls below every inverse        *)
(*                              monomial in its argument                      *)
(*        negligible_fun_add == a sum of negligible functions is negligible   *)
(*         negligible_fun_le == a function below a negligible one pointwise   *)
(*                              is negligible                                 *)
(*     negligible_fun_double == twice a negligible function is negligible     *)
(*       negligible_fun_cst0 == the zero function is negligible               *)
(*        negligible_fun_sum == a finite sum of negligible functions is       *)
(*                              negligible                                    *)
(*         expnn_gt_monomial == (n+2)^(n+2) exceeds every monomial n^c        *)
(*                              past c                                        *)
(*            exp2_gt_linear == 2 ^ k exceeds c * (k+1) past c * c + c        *)
(*          exp2_gt_monomial == 2 ^ n exceeds n ^ c past 2 ^ (c * c + c)      *)
(*  negligible_fun_inv_expnn == the inverse of (k+2)^(k+2) is negligible      *)
(* negligible_fun_inv_ge_expnn == a sequence dominating (k+2)^(k+2) has       *)
(*                              a negligible inverse                          *)
(*   negligible_fun_inv_exp2 == the inverse of 2 ^ k is negligible            *)
(* negligible_fun_inv_ge_exp2 == a sequence dominating 2 ^ k has a            *)
(*                              negligible inverse                            *)
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
   below every inverse monomial.  Katz and Lindell, Introduction to Modern
   Cryptography, 2nd edition, 2015, Definition 3.4, p. 48. *)
Definition negligible_fun (f : nat -> R) : Prop :=
  forall c : nat, exists N : nat,
    forall n : nat, (N < n)%N -> f n < n%:R ^- c.

(* Negligible functions are closed under addition.  A bound written as a sum
   of per-hop advantages is therefore negligible one hop at a time. *)
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

(* A function dominated pointwise by a negligible function is negligible.
   A success probability below a negligible bound is therefore negligible,
   the direction a security claim is read in. *)
Lemma negligible_fun_le (f g : nat -> R) :
  (forall n, f n <= g n) -> negligible_fun g -> negligible_fun f.
Proof.
move=> Hfg Hg c; have [N HN] := Hg c.
by exists N => n Hn; apply: le_lt_trans (Hfg n) (HN n Hn).
Qed.

(* Twice a negligible function is negligible.  A reduction calling its
   assumption once per experiment bounds one key at twice the assumed
   advantage. *)
Lemma negligible_fun_double (f : nat -> R) :
  negligible_fun f -> negligible_fun (fun k => 2 * f k).
Proof.
move=> Hf; apply: negligible_fun_le (negligible_fun_add Hf Hf) => k.
by rewrite mulr_natl mulr2n.
Qed.

(* The zero function is negligible, the unit of the submonoid the negligible
   functions form.  It is the value a total over no labels takes. *)
Lemma negligible_fun_cst0 : negligible_fun (fun _ : nat => 0 : R).
Proof. by move=> c; exists 0 => n Hn; rewrite invr_gt0 exprn_gt0 // ltr0n. Qed.

(* A finite sum of negligible functions is negligible.  A total over a list
   of hop labels is such a sum, one summand per label. *)
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

Section growth_rates.
Implicit Types c d k n : nat.

(* Superpolynomial growth of (n+2)^(n+2): past c it exceeds every monomial
   n^c. *)
Lemma expnn_gt_monomial (c n : nat) : (c < n)%N -> (n ^ c < n.+2 ^ n.+2)%N.
Proof.
move=> Hcn; apply: leq_ltn_trans (_ : (n.+2) ^ c < _)%N; last first.
  by rewrite ltn_exp2l //; exact: (leq_trans Hcn (leqW (leqnSn n))).
move: Hcn; case: c => [_|c _]; first by rewrite !expn0.
by rewrite leq_exp2r //; exact: (leqW (leqnSn n)).
Qed.

(* Two to the k exceeds the linear term c * (k+1) once k reaches c * c + c.
   It is the linear case of the monomial comparison. *)
Lemma exp2_gt_linear (c k : nat) : (c * c + c <= k)%N -> (c * k.+1 < 2 ^ k)%N.
Proof.
move=> Hk.
have leq_mulS_expn2 a b : (a.+1 * b.+1 <= 2 ^ (a + b))%N.
  by rewrite expnD; apply: leq_mul; rewrite ltn_expl.
have ltn_mul_split a b : (a * a <= b)%N -> (a * (a + b).+1 < a.+1 * b.+1)%N.
  move=> le_aa_b; rewrite mulnS mulnDr mulSn mulnS.
  by rewrite addnA addnA ltn_add2r addnC ltn_add2r ltnS.
have Hck : (c <= k)%N by rewrite (leq_trans _ Hk) // leq_addl.
have [d Hd] : exists d, k = (c + d)%N by exists (k - c)%N; rewrite subnKC.
rewrite Hd; apply: leq_trans (leq_mulS_expn2 c d); apply: ltn_mul_split.
by move: Hk; rewrite Hd [(c + d)%N]addnC leq_add2r.
Qed.

(* Two to the n exceeds every monomial n^c once n reaches 2 ^ (c * c + c).
   A security parameter read as a bit length grows at this rate. *)
Lemma exp2_gt_monomial (c n : nat) :
  (2 ^ (c * c + c) <= n)%N -> (n ^ c < 2 ^ n)%N.
Proof.
(* The truncated logarithm of n brackets n between two powers of two, and the
   linear case closes the gap between the brackets. *)
move=> Hn.
have Hn0 : (0 < n)%N by rewrite (leq_trans _ Hn) // expn_gt0.
move: Hn; case: c => [_|c Hn].
  by rewrite expn0 -{1}(expn0 2) ltn_exp2l.
set k := trunc_log 2 n.
have Hk : (c.+1 * c.+1 + c.+1 <= k)%N by apply: trunc_log_max.
apply: leq_ltn_trans (_ : 2 ^ (c.+1 * k.+1) < _)%N.
  by rewrite mulnC expnM leq_exp2r // ltnW // trunc_log_ltn.
apply: leq_trans (_ : 2 ^ (2 ^ k) <= _)%N.
  by rewrite ltn_exp2l // exp2_gt_linear.
by rewrite leq_exp2l // trunc_logP.
Qed.

End growth_rates.

Section negligible_inverses.
Context {R : realType}.

(* The inverse of (k+2)^(k+2) is negligible, falling below every inverse
   polynomial.  It is the growth rate a scheme sequence's plaintext spaces
   have to follow. *)
Lemma negligible_fun_inv_expnn :
  negligible_fun (fun k : nat => (((k.+2) ^ k.+2)%N%:R : R)^-1).
Proof.
move=> c; exists c => n Hn.
have Hn0 : (0 < n)%N by apply: leq_ltn_trans Hn.
rewrite -natrX ltf_pV2 ?ltr_nat ?expnn_gt_monomial //.
  by rewrite posrE ltr0n expn_gt0.
by rewrite posrE ltr0n expn_gt0 Hn0.
Qed.

(* A sequence dominating (k+2)^(k+2) has negligible inverse.  Paillier and
   Benaloh sequences are checked against it to supply size_negligible. *)
Lemma negligible_fun_inv_ge_expnn (f : nat -> nat) :
  (forall k, ((k.+2) ^ k.+2 <= f k)%N) ->
  negligible_fun (fun k => ((f k)%:R : R)^-1).
Proof.
move=> Hf; apply: negligible_fun_le negligible_fun_inv_expnn => k.
rewrite lef_pV2 ?ler_nat //.
  by rewrite posrE ltr0n (leq_trans _ (Hf k)) // expn_gt0.
by rewrite posrE ltr0n expn_gt0.
Qed.

(* The inverse of 2 ^ k is negligible.  It is the growth rate a scheme
   sequence follows when k counts the bits of its key. *)
Lemma negligible_fun_inv_exp2 :
  negligible_fun (fun k : nat => ((2 ^ k)%N%:R : R)^-1).
Proof.
move=> c; exists (2 ^ (c * c + c))%N => n Hn.
have Hn0 : (0 < n)%N by apply: leq_ltn_trans Hn.
rewrite -natrX ltf_pV2 ?ltr_nat ?exp2_gt_monomial ?(ltnW Hn) //.
  by rewrite posrE ltr0n expn_gt0.
by rewrite posrE ltr0n expn_gt0 Hn0.
Qed.

(* A sequence dominating 2 ^ k has negligible inverse.  A scheme sequence
   whose k-th key has k bits supplies size_negligible through it. *)
Lemma negligible_fun_inv_ge_exp2 (f : nat -> nat) :
  (forall k, (2 ^ k <= f k)%N) ->
  negligible_fun (fun k => ((f k)%:R : R)^-1).
Proof.
move=> Hf; apply: negligible_fun_le negligible_fun_inv_exp2 => k.
rewrite lef_pV2 ?ler_nat //.
  by rewrite posrE ltr0n (leq_trans _ (Hf k)) // expn_gt0.
by rewrite posrE ltr0n expn_gt0.
Qed.

End negligible_inverses.
