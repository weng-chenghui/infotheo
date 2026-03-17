(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop.
From pgg_smc Require Import pgg_interface.

(******************************************************************************)
(* PGG-SMC: Word-Eval Injective Generators and Optimal Search Space           *)
(*                                                                            *)
(* MathComp's finGroupType cannot represent the infinite free group needed    *)
(* for maximal PGG search spaces.  Word evaluation injectivity at length L    *)
(* approximates it on demand: given a word length L, we ask only that         *)
(* word_eval be injective on L-words (i.e., the group "looks free" up to     *)
(* depth L).  This suffices to achieve search_space(L) = Tg^L, matching the  *)
(* free group for all protocol uses.                                          *)
(*                                                                            *)
(* Parameters for a word-eval injective PGG instance:                         *)
(*   L  -- word length (security/search space depth)                          *)
(*   Tg -- number of generators (branching factor), search space = Tg^L      *)
(*   N  -- number of sheets (permutation domain), must satisfy N! >= Tg^L    *)
(*   sigmas -- Tg permutations in S_N generating a group of order >= Tg^L    *)
(* Example: for L=10 with Tg=2, need 2^10=1024 distinct group elements,     *)
(* so N >= 7 (since 7!=5040 >= 1024). Pick two sigma_i in S_7 generating a   *)
(* subgroup of order >= 1024 with no word collisions at length 10.            *)
(*                                                                            *)
(* Section 1 -- Nat-level computable word-eval injectivity check:             *)
(*   weval_inj_natB N Tg L gens == boolean check via uniq of word fingerprints*)
(*   weval_inj_of_natB == reflection: weval_inj_natB true -> weval_inj L     *)
(*   Usage: define a nat-level gens_nat mirroring the permutations, prove     *)
(*   gens_agree, then discharge weval_inj by vm_compute on weval_inj_natB.   *)
(*                                                                            *)
(* Section 2 -- Parameterized word-eval injective theory:                     *)
(*   Given generators with hypothesis weval_inj L, derives                    *)
(*   search_space = Tg^L.                                                     *)
(*                                                                            *)
(* Section 3 -- Concrete instance: overlapping 3-cycles in S_4:              *)
(*   < s0, s1 | s0^3 = s1^3 = (s0*s1)^2 = 1 >  (A_4, order 12)            *)
(*   sigma_0 = (0 1 2), sigma_1 = (1 2 3) -- two 3-cycles sharing (1,2).    *)
(*   Tg=2, N=4, L=2: search_space = 4.  L >= 3 fails (s0^3 = s1^3 = 1      *)
(*   so words [0,0,0] and [1,1,1] both map to the identity).                *)
(*   oc_weval_inj2 == word-eval injectivity at L=2 via weval_inj_of_natB    *)
(*                    + vm_compute                                            *)
(*   oc_search_space_2 == search_space 2 = 4                                 *)
(*   oc_noncommute == the generators do not commute                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Nat-level computable word-eval injectivity check                 *)
(* ========================================================================== *)

Fixpoint all_words (Tg L : nat) : seq (seq nat) :=
  match L with
  | 0 => [:: [::]]
  | L'.+1 =>
    flatten [seq map (cons i) (all_words Tg L') | i <- iota 0 Tg]
  end.

(* foldl matches MathComp's \prod convention for permutations:
   foldl f x [a;b;c] = f(f(f(x,a),b),c) = sigma_c(sigma_b(sigma_a(x)))
   = (\prod_(i <- [a;b;c]) sigma_i)%g x *)
Definition eval_word_nat (gens : nat -> nat -> nat) (w : seq nat) (x : nat) : nat :=
  foldl (fun acc i => gens i acc) x w.

Definition word_fp (N : nat) (gens : nat -> nat -> nat) (w : seq nat) : seq nat :=
  map (eval_word_nat gens w) (iota 0 N).

Definition weval_inj_natB (N Tg L : nat) (gens : nat -> nat -> nat) : bool :=
  uniq (map (word_fp N gens) (all_words Tg L)).

Lemma map_uniq_injective (T1 T2 : eqType) (f : T1 -> T2) (xs : seq T1) (a b : T1) :
  uniq (map f xs) -> a \in xs -> b \in xs -> f a = f b -> a = b.
Proof.
move=> Huniq Ha Hb Hfab.
set ia := index a xs; set ib := index b xs.
have Hia : ia < size [seq f i | i <- xs] by rewrite size_map index_mem.
have Hib : ib < size [seq f i | i <- xs] by rewrite size_map index_mem.
have Ha' : nth (f a) [seq f i | i <- xs] ia = f a.
  by rewrite (nth_map a) ?index_mem // nth_index.
have Hb' : nth (f a) [seq f i | i <- xs] ib = f a.
  by rewrite (nth_map a) ?index_mem // nth_index // Hfab.
have /eqP Hiab : ia == ib.
  by rewrite -(nth_uniq (f a) Hia Hib Huniq) Ha' Hb' eqxx.
by rewrite -(nth_index a Ha) -(nth_index a Hb) -/ia -/ib Hiab.
Qed.

Lemma mem_all_words Tg L (w : seq nat) :
  size w = L -> all (fun i => i < Tg) w -> w \in all_words Tg L.
Proof.
elim: L w => [|L IH] w /=.
  by move=> /size0nil -> _.
case: w => [// | a w'] /= [Hsz] /andP [Ha Hw'].
apply/flattenP; exists (map (cons a) (all_words Tg L)).
  by apply/mapP; exists a => //; rewrite mem_iota add0n.
by apply/mapP; exists w' => //; exact: IH.
Qed.

(* ========================================================================== *)
(* Reflection for Gen_PGGTypes instances                                      *)
(* ========================================================================== *)

Section weval_inj_gen_reflect.

Variable m n : nat.
Let Tg := m.+1.
Let N := n.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Variable gens_nat : nat -> nat -> nat.

Hypothesis Hgens : forall (i : 'I_Tg) (x : 'I_N),
  gens_nat (val i) (val x) = val (tnth sigmas i x).

(* Key lemma 1: foldl on nat matches foldl on ordinals *)
Lemma eval_foldl_agree (ws : seq 'I_Tg) (x : 'I_N) :
  foldl (fun acc i => gens_nat i acc) (val x) (map val ws) =
  val (foldl (fun (acc : 'I_N) (i : 'I_Tg) => tnth sigmas i acc) x ws).
Proof.
by elim: ws x => [|j js IH] x //=; rewrite Hgens IH.
Qed.

(* Key lemma 2: word_eval equals foldl over the tuple *)
Lemma word_eval_foldl (L : nat) (w : @pgg_word M L) (x : 'I_N) :
  @word_eval M L w x =
  foldl (fun (acc : 'I_N) (j : 'I_Tg) => tnth sigmas j acc) x (tval w).
Proof.
rewrite /word_eval; have -> : @pgg_sigmas M = sigmas by [].
elim: L w x => [|L IH] w x.
  by rewrite big_ord0 perm1; case: w => [[] //].
rewrite big_ord_recl permM.
case Hw: (tval w) => [|a s].
  by move: (size_tuple w); rewrite Hw.
have Ha : a = tnth w ord0 by rewrite (tnth_nth a) Hw.
have Hsz : size s == L by move: (size_tuple w); rewrite Hw /= => [[->]].
set wt : L.-tuple 'I_Tg := Tuple Hsz.
have Hlift : forall i : 'I_L, tnth w (lift ord0 i) = tnth wt i.
  by move=> i; rewrite !(tnth_nth a) Hw.
rewrite (eq_bigr (fun i => tnth sigmas (tnth wt i))); last first.
  by move=> i _; rewrite Hlift.
rewrite -/(word_eval (L:=L) wt) /= Ha.
have -> : s = tval wt by [].
exact: IH.
Qed.

(* Combine: eval_word_nat agrees with word_eval *)
Lemma eval_word_agree (L : nat) (w : @pgg_word M L) (x : 'I_N) :
  eval_word_nat gens_nat (map val (tval w)) (val x) =
  val (@word_eval M L w x).
Proof.
by rewrite /eval_word_nat eval_foldl_agree word_eval_foldl.
Qed.

(* map val is injective on pgg_word *)
Lemma map_val_tuple_inj (L : nat) (w1 w2 : @pgg_word M L) :
  map val (tval w1) = map val (tval w2) -> w1 = w2.
Proof. by move/(inj_map val_inj) => /val_inj. Qed.

(* map val of a pgg_word is in all_words *)
Lemma map_val_in_all_words (L : nat) (w : @pgg_word M L) :
  map val (tval w) \in all_words Tg L.
Proof.
apply: mem_all_words.
  by rewrite size_map size_tuple.
by apply/allP => k /mapP [i _ ->]; case: i.
Qed.

(* Main reflection lemma *)
Lemma weval_inj_of_natB (L : nat) :
  weval_inj_natB N Tg L gens_nat -> @weval_inj M L.
Proof.
rewrite /weval_inj_natB /weval_inj => Huniq w1 w2 Heval.
apply: map_val_tuple_inj.
apply: (map_uniq_injective Huniq (map_val_in_all_words w1) (map_val_in_all_words w2)).
rewrite /word_fp.
apply: (@eq_from_nth _ 0); first by rewrite !size_map !size_iota.
move=> j; rewrite size_map size_iota => Hj.
rewrite !(nth_map 0) ?size_iota // !nth_iota // !add0n.
have -> : j = val (Ordinal Hj) by [].
by rewrite (eval_word_agree w1) (eval_word_agree w2) Heval.
Qed.

End weval_inj_gen_reflect.

(* ========================================================================== *)
(* Section 2: Parameterized word-eval injective theory                        *)
(* ========================================================================== *)

Section weval_inj_instance.

Variable L m n : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n.+2}.
Let M := Gen_PGGTypes sigmas.
Hypothesis Hlfree : @weval_inj M L.

Lemma weval_inj_inst_search_space : @search_space M L = m.+1 ^ L.
Proof. exact: weval_inj_search_space Hlfree. Qed.

End weval_inj_instance.

(* ========================================================================== *)
(* Section 3: Concrete word-eval injective instance — overlapping 3-cycles    *)
(*            in S_4                                                           *)
(* ========================================================================== *)

Section overlapping_3cycles.

Definition oc_N := 4.

(* sigma_0 = (0 1 2): the 3-cycle mapping 0->1->2->0 *)
Definition oc_s0_fun (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 0 => @Ordinal oc_N 1 isT | 1 => @Ordinal oc_N 2 isT
  | 2 => @Ordinal oc_N 0 isT | _ => i end.
Definition oc_s0_inv (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 0 => @Ordinal oc_N 2 isT | 1 => @Ordinal oc_N 0 isT
  | 2 => @Ordinal oc_N 1 isT | _ => i end.
Lemma oc_s0K : cancel oc_s0_fun oc_s0_inv.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|?]]]] ?]. Qed.
Definition oc_s0 : {perm 'I_oc_N} := perm (can_inj oc_s0K).
Lemma oc_s0E x : oc_s0 x = oc_s0_fun x. Proof. by rewrite permE. Qed.

(* sigma_1 = (1 2 3): the 3-cycle mapping 1->2->3->1 *)
Definition oc_s1_fun (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 1 => @Ordinal oc_N 2 isT | 2 => @Ordinal oc_N 3 isT
  | 3 => @Ordinal oc_N 1 isT | _ => i end.
Definition oc_s1_inv (i : 'I_oc_N) : 'I_oc_N :=
  match val i with
  | 1 => @Ordinal oc_N 3 isT | 2 => @Ordinal oc_N 1 isT
  | 3 => @Ordinal oc_N 2 isT | _ => i end.
Lemma oc_s1K : cancel oc_s1_fun oc_s1_inv.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|?]]]] ?]. Qed.
Definition oc_s1 : {perm 'I_oc_N} := perm (can_inj oc_s1K).
Lemma oc_s1E x : oc_s1 x = oc_s1_fun x. Proof. by rewrite permE. Qed.

(* Generator tuple *)
Lemma oc_sigmas_size : size [:: oc_s0; oc_s1] == 2.
Proof. by []. Qed.

Definition oc_sigmas : 2.-tuple {perm 'I_oc_N} := Tuple oc_sigmas_size.

Lemma oc_sigmasE (i : 'I_2) : tnth oc_sigmas i =
  match val i with 0 => oc_s0 | _ => oc_s1 end.
Proof.
by rewrite (tnth_nth oc_s0) /=; case: i => [[|[|?]] ?].
Qed.

Definition OC_PGGTypes := Gen_PGGTypes oc_sigmas.

(* Nat-level generator function for vm_compute *)
Definition oc_gens_nat (i x : nat) : nat :=
  match i with
  | 0 => match x with 0 => 1 | 1 => 2 | 2 => 0 | _ => x end
  | _ => match x with 1 => 2 | 2 => 3 | 3 => 1 | _ => x end
  end.

Lemma oc_gens_agree (i : 'I_2) (x : 'I_oc_N) :
  oc_gens_nat (val i) (val x) = val (tnth oc_sigmas i x).
Proof.
by case: i => [[|[|?]] ?]; case: x => [[|[|[|[|?]]]] ?];
  rewrite oc_sigmasE /= permE.
Qed.

(* Order 3 *)
Lemma oc_s0_order3 : (oc_s0 ^+ 3 = 1 :> {perm 'I_oc_N})%g.
Proof.
apply/permP => x; rewrite perm1 expgS permM expgS permM expg1 !oc_s0E.
by apply: val_inj; case: x => [[|[|[|[|?]]]] ?].
Qed.

Lemma oc_s1_order3 : (oc_s1 ^+ 3 = 1 :> {perm 'I_oc_N})%g.
Proof.
apply/permP => x; rewrite perm1 expgS permM expgS permM expg1 !oc_s1E.
by apply: val_inj; case: x => [[|[|[|[|?]]]] ?].
Qed.

(* Non-commutativity *)
Lemma oc_noncommute : (oc_s0 * oc_s1 != oc_s1 * oc_s0)%g.
Proof.
apply/negP => /eqP/permP /(_ (Ordinal (isT : 0 < oc_N))).
by rewrite !permM !oc_s0E !oc_s1E.
Qed.

(* Word-eval injectivity via nat-level boolean decision + vm_compute *)
Lemma oc_weval_inj2 : @weval_inj OC_PGGTypes 2.
Proof.
apply: (weval_inj_of_natB oc_gens_agree).
by vm_compute.
Qed.

(* Search space instantiation *)
Lemma oc_search_space_2 : @search_space OC_PGGTypes 2 = 4.
Proof. exact: weval_inj_inst_search_space oc_weval_inj2. Qed.

End overlapping_3cycles.
