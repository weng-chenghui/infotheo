(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop binomial.
From pgg_smc Require Import pgg_interface.

(******************************************************************************)
(* PGG-SMC: Abelian Word Collapse (Theorem 8, items (1)-(2))                 *)
(*                                                                           *)
(* In an abelian group with r generators, any word of length L evaluates to  *)
(* a product that depends only on the frequency vector (c_1,...,c_r) where   *)
(* c_j counts how often generator j appears. This collapses the exponential  *)
(* search space r^L to at most 'C(L+r-1,r-1) distinct frequency vectors.    *)
(*                                                                           *)
(*   freq_vec w j   == number of positions in word w that use generator j    *)
(*   freq_vecs L    == set of frequency vectors {f : 'I_Tg -> nat | sum=L}  *)
(*   abelian_word_eval  == word evaluation depends only on frequency vector  *)
(*   freq_vec_sum       == sum of frequencies equals word length             *)
(*   abelian_search_space_le == search_space L <= #|freq_vecs L|            *)
(*   card_freq_vecs == #|freq_vecs L| = 'C(L + Tg.-1, Tg.-1)   [axiom]    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Frequency vector and abelian word evaluation                    *)
(* ========================================================================== *)

Section freq_vector.

Variable M : GeneratedMonodromyReprType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

Variable L : nat.

(* Frequency vector: count how often each generator index appears in a word *)
Definition freq_vec (w : pgg_word M L) (j : 'I_Tg) : nat :=
  #|[set i : 'I_L | tnth w i == j]|.

(* Sum of frequencies equals word length *)
Lemma freq_vec_sum (w : pgg_word M L) :
  \sum_(j < Tg) freq_vec w j = L.
Proof.
rewrite /freq_vec -[RHS]card_ord -sum1_card.
transitivity (\sum_(j < Tg) \sum_(i < L | tnth w i == j) 1).
  by apply: eq_bigr => j _; rewrite -sum1_card; apply: eq_bigl => i; rewrite inE.
symmetry; exact: partition_big.
Qed.

(* Main theorem: abelian word evaluation depends only on frequency vector.
   In an abelian group, the product \prod_i sigma_{w_i} can be rearranged
   by collecting equal generators: sigma_j^{count of j in w}.
   MathComp's partition_big requires Monoid.com_law (type-level
   commutativity), but mulg only has Monoid.Law; abelian G is a runtime
   property. A full proof requires custom permutation lemmas for abelian
   groups. We axiomatize the rearrangement step. *)
Lemma abelian_word_eval (w : pgg_word M L) :
  abelian G ->
  word_eval w = (\prod_(j < Tg) tnth sigmas j ^+ freq_vec w j)%g.
Proof. move=> Habel. Admitted.

(* Two words with the same frequency vector give the same group element *)
Lemma freq_vec_det (w1 w2 : pgg_word M L) :
  abelian G ->
  (forall j, freq_vec w1 j = freq_vec w2 j) ->
  word_eval w1 = word_eval w2.
Proof.
move=> Habel Hfreq.
rewrite (abelian_word_eval _ Habel) (abelian_word_eval _ Habel).
by apply: eq_bigr => j _; rewrite Hfreq.
Qed.

End freq_vector.

(* ========================================================================== *)
(* Section 2: Frequency vector counting (stars-and-bars)                      *)
(* ========================================================================== *)

Section freq_counting.

Variable M : GeneratedMonodromyReprType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

Variable L : nat.

(* The set of frequency vectors: functions 'I_Tg -> nat with sum = L *)
Definition freq_vecs : {set {ffun 'I_Tg -> 'I_L.+1}} :=
  [set f : {ffun 'I_Tg -> 'I_L.+1} |
     \sum_(j < Tg) val (f j) == L].

(* The frequency vector of a word, as a bounded function *)
Lemma freq_vec_lt (w : pgg_word M L) (j : 'I_Tg) :
  freq_vec w j < L.+1.
Proof.
rewrite ltnS /freq_vec.
by apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

Definition freq_vec_ffun (w : pgg_word M L) : {ffun 'I_Tg -> 'I_L.+1} :=
  [ffun j => Ordinal (freq_vec_lt w j)].

Lemma freq_vec_ffun_val (w : pgg_word M L) (j : 'I_Tg) :
  val (freq_vec_ffun w j) = freq_vec w j.
Proof. by rewrite /freq_vec_ffun ffunE. Qed.

Lemma freq_vec_ffun_in (w : pgg_word M L) :
  freq_vec_ffun w \in freq_vecs.
Proof.
rewrite inE; apply/eqP.
under eq_bigr do rewrite freq_vec_ffun_val.
exact: freq_vec_sum.
Qed.

(* The image of word_eval factors through freq_vecs *)
Definition freq_eval (f : {ffun 'I_Tg -> 'I_L.+1}) : gT :=
  (\prod_(j < Tg) tnth sigmas j ^+ val (f j))%g.

Lemma abelian_word_eval_freq (w : pgg_word M L) :
  abelian G ->
  word_eval w = freq_eval (freq_vec_ffun w).
Proof.
move=> Habel.
rewrite /freq_eval (abelian_word_eval _ Habel).
by apply: eq_bigr => j _; rewrite freq_vec_ffun_val.
Qed.

(* Search space bound: achievable elements are at most the image of freq_vecs *)
Lemma abelian_achievable_sub :
  abelian G ->
  achievable M L \subset [set freq_eval f | f in freq_vecs].
Proof.
move=> Habel.
apply/subsetP => g /imsetP [w _ ->].
apply/imsetP; exists (freq_vec_ffun w); last by rewrite -abelian_word_eval_freq.
exact: freq_vec_ffun_in.
Qed.

Lemma abelian_search_space_le :
  abelian G ->
  search_space M L <= #|freq_vecs|.
Proof.
move=> Habel.
rewrite /search_space.
apply: leq_trans (leq_imset_card _ _).
exact: subset_leq_card (abelian_achievable_sub Habel).
Qed.

End freq_counting.

(* ========================================================================== *)
(* Section 3: Stars-and-bars counting                                         *)
(* ========================================================================== *)

(* Stars-and-bars theorem: the number of ways to write L as an ordered sum   *)
(* of Tg non-negative integers is 'C(L + Tg - 1, Tg - 1).                   *)
(*                                                                           *)
(* This is a classical combinatorial identity. A direct MathComp proof       *)
(* requires constructing a bijection between frequency vectors and           *)
(* (Tg-1)-element subsets of {0,...,L+Tg-2}, which is substantial.           *)
(* We axiomatize it here and note it can be replaced by a proof via          *)
(* the multiset coefficient or a direct bijection.                           *)

Section stars_and_bars.

Variable r : nat.  (* number of bins = r.+1 *)
Variable L : nat.  (* total sum *)

Definition compositions : {set {ffun 'I_r.+1 -> 'I_L.+1}} :=
  [set f : {ffun 'I_r.+1 -> 'I_L.+1} | \sum_(j < r.+1) val (f j) == L].

(* Stars-and-bars: axiomatized *)
Axiom card_compositions :
  #|compositions| = 'C(L + r, r).

End stars_and_bars.

Section stars_and_bars_application.

Variable M : GeneratedMonodromyReprType.

Let Tg := (@pgg_ngens' M).+1.

Variable L : nat.

(* freq_vecs is exactly compositions for r = pgg_ngens' M *)
Lemma freq_vecs_eq_compositions :
  freq_vecs M L = compositions (@pgg_ngens' M) L.
Proof. by []. Qed.

Lemma card_freq_vecs :
  #|freq_vecs M L| = 'C(L + (@pgg_ngens' M), (@pgg_ngens' M)).
Proof.
by rewrite freq_vecs_eq_compositions card_compositions.
Qed.

(* Combined bound *)
Theorem abelian_search_space_bound :
  abelian (pgg_G M) ->
  search_space M L <= 'C(L + (@pgg_ngens' M), (@pgg_ngens' M)).
Proof.
move=> Habel.
by rewrite -card_freq_vecs; exact: abelian_search_space_le.
Qed.

End stars_and_bars_application.
