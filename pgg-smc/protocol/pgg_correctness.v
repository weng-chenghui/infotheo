(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.

(******************************************************************************)
(* PGG-SMC: Correctness Theorems                                              *)
(*                                                                            *)
(*   Theorem 1 (Correctness): rho(g*h)(s) = rho(h)(rho(g)(s))               *)
(*     The monodromy representation composes correctly.                       *)
(*                                                                            *)
(*   Theorem 2 (Bijectivity/UPLP): rho(P) is a bijection on sheets.          *)
(*     Trivially true since rho(P) : {perm 'I_N}.                            *)
(*                                                                            *)
(*   Proposition 3 (Distinctness): Endpoints of distinct starting sheets      *)
(*     remain distinct under any monodromy evaluation.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_correctness.

Variable gT : finGroupType.
Variable N' : nat.
Let N := N'.+1.
Variable G : {group gT}.
Variable rho : {morphism G >-> {perm 'I_N}}.

(* Theorem 1: Correctness — monodromy composition *)
Theorem pgg_correctness (g h : gT) (s : 'I_N) :
  g \in G -> h \in G ->
  rho (g * h)%g s = rho h (rho g s).
Proof. by move=> gG hG; rewrite (morphM rho gG hG) permM. Qed.

(* Identity evaluation *)
Lemma pgg_correctness1 (s : 'I_N) : rho 1%g s = s.
Proof. by rewrite morph1 perm1. Qed.

(* Inverse evaluation *)
Lemma pgg_correctnessV (g : gT) (s : 'I_N) :
  g \in G -> rho g^-1%g (rho g s) = s.
Proof.
by move=> gG; rewrite -permM (morphV rho gG) mulgV perm1.
Qed.

(* Theorem 2: Bijectivity — permutations are bijections *)
Theorem pgg_bijectivity (P : gT) : bijective (rho P).
Proof. by exists (rho P)^-1%g => x; rewrite ?permK ?permKV. Qed.

Theorem pgg_injective (P : gT) : injective (rho P).
Proof. exact: perm_inj. Qed.

(* Proposition 3: Distinctness of endpoints *)
Variable T' : nat.
Let T := T'.+1.
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

Proposition pgg_distinctness (P : gT) :
  uniq (map (rho P) starts).
Proof. by rewrite map_inj_uniq //; exact: perm_inj. Qed.

(* Injectivity of tnth on a uniq tuple *)
Let x0 := tnth starts ord0.

Lemma starts_tnth_inj : injective (tnth starts).
Proof.
move=> i j eq_ij.
have Hi : (i < size starts)%N by rewrite size_tuple.
have Hj : (j < size starts)%N by rewrite size_tuple.
have := @nth_uniq _ x0 starts i j Hi Hj starts_uniq.
have -> : nth x0 starts i = tnth starts i by rewrite (tnth_nth x0).
have -> : nth x0 starts j = tnth starts j by rewrite (tnth_nth x0).
rewrite eq_ij eqxx => /esym/eqP. exact: ord_inj.
Qed.

(* The set of endpoints has the same cardinality as the set of starts *)
Lemma endpoints_card (P : gT) :
  #|[set rho P (tnth starts i) | i : 'I_T]| = T.
Proof.
rewrite card_imset ?card_ord //.
by move=> i j /(perm_inj (s := rho P)) /starts_tnth_inj.
Qed.

End pgg_correctness.
