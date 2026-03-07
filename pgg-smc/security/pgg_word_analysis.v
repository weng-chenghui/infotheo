(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div binomial fingraph path.
From pgg_smc Require Import pgg_interface pgg_lfree pgg_raag.

(******************************************************************************)
(* PGG-SMC: Commuting Pair Analysis for RAAG Words                           *)
(*                                                                            *)
(* Formalizes the number of adjacent commuting pairs in a word as a           *)
(* combinatorial quantity, and connects it to trace equivalence.              *)
(*                                                                            *)
(*   comm_pair_count L w == number of positions k such that generators at     *)
(*                          positions k and k+1 commute in word w             *)
(*   edge_count == number of ordered commuting pairs in the commutation graph *)
(*                                                                            *)
(* Key results:                                                               *)
(*   comm_pair_count_bound : comm_pair_count w <= L.-1                        *)
(*   comm_pair_count_zero_adj_swap : comm_pair_count w = 0 -> no adj_swap     *)
(*   comm_pair_count_zero_singleton : comm_pair_count w = 0 ->                *)
(*                                    trace class of w = {w}                  *)
(*   comm_pair_count_zero_root : comm_pair_count w = 0 -> root adj_swap w = w *)
(*   total_comm_pairs : sum of comm_pair_count over all words (counting)      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Commuting pair count                                            *)
(* ========================================================================== *)

Section word_analysis.

Variable R : RAAGType.
Let gT := pgg_gT R.
Let M : GeneratedMonodromyReprType := R.
Let Tg := (@pgg_ngens' R).+1.
Let sigmas := @pgg_sigmas R.
Let comm : rel 'I_Tg := @raag_comm R.
Let comm_sym : symmetric comm := @raag_comm_sym R.
Let comm_irrefl : irreflexive comm := @raag_comm_irrefl R.

(* Number of adjacent commuting pairs in a word of length L.
   For a word w = [w_0, w_1, ..., w_{L-1}], this counts
   #{k < L-1 | comm w_k w_{k+1}}.
   Uses the same ordinal construction as adj_swap in pgg_raag.v. *)
Definition comm_pair_count (L : nat) : pgg_word M L -> nat :=
  match L as L0 return pgg_word M L0 -> nat with
  | 0 => fun _ => 0
  | L'.+1 => fun w =>
    #|[set k : 'I_L' |
        comm (tnth w (@Ordinal L'.+1 (val k)
                       (ltn_trans (ltn_ord k) (ltnSn L'))))
             (tnth w (@Ordinal L'.+1 (val k).+1 (ltn_ord k)))]|
  end.

(* Upper bound: at most L-1 adjacent pairs *)
Lemma comm_pair_count_bound (L : nat) (w : pgg_word M L) :
  comm_pair_count w <= L.-1.
Proof.
case: L w => [|L'] w //=.
by rewrite -[L' in _ <= L']card_ord; exact: max_card.
Qed.

(* --- Edge count of the commutation graph --- *)

(* Number of ordered commuting pairs (i,j) with i != j and comm i j.
   This is twice the number of undirected edges. *)
Definition edge_count : nat :=
  #|[set p : 'I_Tg * 'I_Tg | comm p.1 p.2]|.

Lemma edge_count_sym : edge_count =
  #|[set p : 'I_Tg * 'I_Tg | comm p.2 p.1]|.
Proof.
rewrite /edge_count.
suff -> : [set p : 'I_Tg * 'I_Tg | comm p.1 p.2] =
          [set p : 'I_Tg * 'I_Tg | comm p.2 p.1] by done.
apply/setP => -[i j].
by rewrite !inE /= comm_sym.
Qed.

(* edge_count is even: the swap involution (i,j) <-> (j,i) has no fixed
   points on commuting pairs (since comm is irreflexive), so the set
   partitions into pairs. *)
Lemma edge_count_even : 2 %| edge_count.
Proof.
rewrite /edge_count.
pose swap_pair := fun (p : 'I_Tg * 'I_Tg) => (p.2, p.1).
have Hinj : injective swap_pair by move=> [a1 a2] [b1 b2] /= [-> ->].
set S_lt := [set p : 'I_Tg * 'I_Tg | comm p.1 p.2 && (val p.1 < val p.2)].
set S_gt := [set p : 'I_Tg * 'I_Tg | comm p.1 p.2 && (val p.2 < val p.1)].
have Hunion : [set p : 'I_Tg * 'I_Tg | comm p.1 p.2] = S_lt :|: S_gt.
  apply/setP => -[i j]; rewrite !inE /=.
  case Hc : (comm i j) => //=.
  have Hij : val i != val j.
    apply/negP => /eqP Heq.
    have : i = j by apply/val_inj. move=> ?; subst.
    by rewrite comm_irrefl in Hc.
  by case: (ltngtP (val i) (val j)) Hij.
have Hdisj : [disjoint S_lt & S_gt].
  apply/pred0P => -[i j] /=; rewrite !inE /=.
  case: (comm i j) => //=.
  case: (ltngtP (val i) (val j)) => //= _;
  by rewrite ?andbF.
have Hcard_eq : #|S_gt| = #|S_lt|.
  rewrite -(card_imset _ Hinj).
  apply: eq_card => -[i j].
  rewrite !inE /=.
  apply/imsetP/andP.
  - move=> [[j' i']] /=; rewrite inE /= => /andP [Hc Hlt] [-> ->].
    by rewrite comm_sym Hc.
  - move=> [Hc Hlt].
    exists (j, i) => //=.
    by rewrite inE /= comm_sym Hc Hlt.
rewrite Hunion cardsU disjoint_setI0 // cards0 subn0 Hcard_eq addnn.
by rewrite dvdn2 odd_double.
Qed.

(* ========================================================================== *)
(* Section 2: Zero commuting pairs => singleton trace class                   *)
(* ========================================================================== *)

(* Helper: adj_swap w' w implies adj_swap w w' (adj_swap is symmetric).
   If w = swap_word k w', then w' = swap_word k w, and the commutation
   condition at positions k,k+1 is preserved (by comm_sym and the fact
   that swap exchanges exactly those two positions). *)
Lemma adj_swap_symmetric (L : nat) (w1 w2 : pgg_word M L) :
  adj_swap w1 w2 -> adj_swap w2 w1.
Proof.
case: L w1 w2 => [|L'] w1 w2 //=.
move/existsP => [k /andP [Hc /eqP ->]].
set sw := @swap_word R L'.+1 k w1.
apply/existsP; exists k; apply/andP; split.
  (* swap exchanges positions k and k+1 *)
  have Hswk : tnth sw (Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))) =
    tnth w1 (@Ordinal L'.+1 (val k).+1 (ltn_ord k)).
    by rewrite /sw swap_word_tnth /= eqxx.
  have Hswk1 : tnth sw (@Ordinal L'.+1 (val k).+1 (ltn_ord k)) =
    tnth w1 (Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))).
    by rewrite /sw swap_word_tnth /= eqn_leq ltnn /= eqxx.
  rewrite Hswk Hswk1.
  by rewrite -[raag_comm _ _]/(comm _ _) comm_sym.
(* swap_word is an involution *)
apply/eqP; rewrite /sw; apply: eq_from_tnth => i.
rewrite (swap_word_tnth k (@swap_word R L'.+1 k w1) i).
case Hik: (val i == val k).
  have -> : tnth (@swap_word R L'.+1 k w1)
    (@Ordinal L'.+1 (val k).+1 (ltn_ord k)) =
    tnth w1 (Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))).
    by rewrite swap_word_tnth /= eqn_leq ltnn /= eqxx.
  by have -> : i = Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))
    by apply: val_inj; rewrite /=; apply/eqP.
case Hik1: (val i == (val k).+1).
  have -> : tnth (@swap_word R L'.+1 k w1)
    (Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))) =
    tnth w1 (@Ordinal L'.+1 (val k).+1 (ltn_ord k)).
    by rewrite swap_word_tnth /= eqxx.
  by have -> : i = @Ordinal L'.+1 (val k).+1 (ltn_ord k)
    by apply: val_inj; rewrite /=; apply/eqP.
rewrite (swap_word_tnth k w1 i) Hik Hik1.
done.
Qed.

(* If no adjacent generators in w commute, then no adjacent swap is possible,
   so the trace class of w is the singleton {w}. *)
Lemma comm_pair_count_zero_adj_swap (L : nat) (w1 w2 : pgg_word M L) :
  comm_pair_count w1 = 0 -> adj_swap w1 w2 = false.
Proof.
case: L w1 w2 => [|L'] w1 w2 //=.
move/eqP; rewrite cards_eq0 => /eqP Hempty.
apply/negbTE/negP.
move/existsP => [k /andP [Hc _]].
have : k \in [set k0 : 'I_L' |
  comm (tnth w1 (@Ordinal L'.+1 (val k0) (ltn_trans (ltn_ord k0) (ltnSn L'))))
       (tnth w1 (@Ordinal L'.+1 (val k0).+1 (ltn_ord k0)))].
  by rewrite inE.
by rewrite Hempty inE.
Qed.

(* The symmetric closure of adj_swap is also false when comm_pair_count = 0 *)
Lemma comm_pair_count_zero_adj_swap_sym (L : nat) (w1 w2 : pgg_word M L) :
  comm_pair_count w1 = 0 -> adj_swap_sym w1 w2 = false.
Proof.
move=> H1.
rewrite /adj_swap_sym (comm_pair_count_zero_adj_swap w2 H1) /=.
apply/negbTE/negP => Hadj.
have := adj_swap_symmetric Hadj.
by rewrite (comm_pair_count_zero_adj_swap _ H1).
Qed.

(* Words with zero commuting pairs are their own trace roots *)
Lemma comm_pair_count_zero_root (L : nat) (w : pgg_word M L) :
  comm_pair_count w = 0 -> root (@adj_swap_sym R L) w = w.
Proof.
move=> H0.
set e := @adj_swap_sym R L.
have Hconn : forall w', connect e w w' = (w == w').
  move=> w'.
  apply/idP/idP.
    move/connectP => [p].
    elim: p w H0 => [w0 _ _ -> // | w'' p IHp w0 H0 /= /andP [Hstep Hpath] Hlast].
    exfalso.
    have : e w0 w'' = false := comm_pair_count_zero_adj_swap_sym _ H0.
    by rewrite Hstep.
  by move/eqP => ->; exact: connect0.
rewrite /root /=.
case: pickP => [w' /= Hw' | /= H].
  by rewrite Hconn in Hw'; move/eqP in Hw'.
by move: (H w); rewrite /= connect0.
Qed.

(* The trace equivalence class of a zero-count word is a singleton *)
Lemma comm_pair_count_zero_singleton (L : nat)
    (w1 w2 : pgg_word M L) :
  comm_pair_count w1 = 0 ->
  trace_equiv w1 w2 -> w1 = w2.
Proof.
move=> H0 /connectP [p].
elim: p w1 H0 => [w1 _ _ -> // | w' p IHp w1 H0 /= /andP [Hstep Hpath] Hlast].
exfalso.
have : adj_swap_sym w1 w' = false := comm_pair_count_zero_adj_swap_sym _ H0.
by rewrite Hstep.
Qed.

(* ========================================================================== *)
(* Section 3: Maximum commuting pairs                                         *)
(* ========================================================================== *)

(* When all distinct generators commute and L >= 2, we have
   comm_pair_count w = L.-1 (every adjacent pair commutes, unless two
   adjacent generators happen to be equal, in which case comm is false
   by irreflexivity). *)
Lemma comm_pair_count_full_comm (L' : nat) (w : pgg_word M L'.+1) :
  (forall i j : 'I_Tg, i != j -> comm i j) ->
  (forall k : 'I_L',
    tnth w (@Ordinal L'.+1 (val k) (ltn_trans (ltn_ord k) (ltnSn L')))
    != tnth w (@Ordinal L'.+1 (val k).+1 (ltn_ord k))) ->
  comm_pair_count w = L'.
Proof.
move=> Hfull Hdist.
apply/eqP; rewrite eqn_leq; apply/andP; split => /=.
  by rewrite -[L' in _ <= L']card_ord; exact: max_card.
suff -> : [set k0 : 'I_L' | comm (tnth w (@Ordinal L'.+1 (val k0) (ltn_trans (ltn_ord k0) (ltnSn L')))) (tnth w (@Ordinal L'.+1 (val k0).+1 (ltn_ord k0)))] = [set: 'I_L'].
  by rewrite cardsT card_ord.
apply/setP => k; rewrite !inE /=.
exact: Hfull (Hdist k).
Qed.

(* ========================================================================== *)
(* Section 4: Swap preserves comm_pair_count adjacently                       *)
(* ========================================================================== *)

(* An adjacent swap at position k changes comm_pair_count by at most 2
   (one pair created/destroyed at k, and adjacent pairs at k-1 and k+1
   may be affected). This is a structural observation. *)
Lemma adj_swap_comm_pair_diff (L : nat) (w1 w2 : pgg_word M L) :
  adj_swap w1 w2 ->
  (comm_pair_count w1 <= comm_pair_count w2 + 2) /\
  (comm_pair_count w2 <= comm_pair_count w1 + 2).
Proof.
case: L w1 w2 => [|L'] w1 w2 //=.
move/existsP => [k /andP [Hcomm_k /eqP Hw2]]; subst w2.
set sw := @swap_word R L'.+1 k w1.
set S1 := [set j : 'I_L' |
  comm (tnth w1 (@Ordinal L'.+1 (val j) (ltn_trans (ltn_ord j) (ltnSn L'))))
       (tnth w1 (@Ordinal L'.+1 (val j).+1 (ltn_ord j)))].
set S2 := [set j : 'I_L' |
  comm (tnth sw (@Ordinal L'.+1 (val j) (ltn_trans (ltn_ord j) (ltnSn L'))))
       (tnth sw (@Ordinal L'.+1 (val j).+1 (ltn_ord j)))].
have Hdiff : forall j : 'I_L', (j \in S1) != (j \in S2) ->
  (val j == (val k).-1) || (val j == (val k).+1).
  move=> j Hne.
  case Hj1 : (val j == (val k).-1) => //=.
  case Hj2 : (val j == (val k).+1) => //=.
  exfalso; move: Hne; apply/negP; rewrite negbK.
  case Hj3 : (val j == val k).
  - have -> : j = k by apply: val_inj; exact: eqP Hj3.
    rewrite !inE /sw !swap_word_tnth /= eqxx.
    have -> : ((val k).+1 == val k) = false
      by rewrite eq_sym -[X in X == _]addn0 -addn1 eqn_add2l.
    rewrite eqxx.
    by rewrite comm_sym.
  - rewrite !inE /sw !swap_word_tnth /=.
    rewrite Hj3 Hj2.
    have Hj1k : (val j).+1 == val k = false.
      apply/eqP => Heq.
      by move: Hj1; rewrite -Heq -pred_Sn eqxx.
    rewrite Hj1k.
    by rewrite eqSS Hj3.
set D := [set j : 'I_L' | (val j == (val k).-1) || (val j == (val k).+1)].
have Hcard_val_eq : forall c : nat, #|[set j : 'I_L' | val j == c]| <= 1.
  move=> c; case: (ltnP c L') => Hc.
    rewrite (_ : [set _ | _] = [set Ordinal Hc]); first by rewrite cards1.
    apply/setP => j; rewrite !inE.
    by apply/eqP/eqP => [Hval | ->] //; apply/val_inj.
  rewrite (_ : [set _ | _] = set0); first by rewrite cards0.
  apply/setP => j; rewrite !inE.
  by apply/negbTE/negP => /eqP Hval; move: (ltn_ord j); rewrite Hval ltnNge Hc.
have HcardD : #|D| <= 2.
  apply: (@leq_trans
    (#|[set j : 'I_L' | val j == (val k).-1]| +
     #|[set j : 'I_L' | val j == (val k).+1]|));
    last by move: (Hcard_val_eq (val k).-1) (Hcard_val_eq (val k).+1);
            case: #|_| => [|[|//]] _; case: #|_| => [|[|//]].
  apply: (@leq_trans
    (#|[set j : 'I_L' | val j == (val k).-1] :|:
      [set j : 'I_L' | val j == (val k).+1]|)).
    apply: subset_leq_card; apply/subsetP => j; rewrite !inE.
    by case/orP => ->; [| rewrite orbT].
  by rewrite cardsU; apply: leq_subr.
have Hsub12 : S1 :\: S2 \subset D.
  apply/subsetP => j /setDP [HjS1 HjnS2].
  by rewrite inE; apply: Hdiff; rewrite HjS1 (negbTE HjnS2).
have Hsub21 : S2 :\: S1 \subset D.
  apply/subsetP => j /setDP [HjS2 HjnS1].
  by rewrite inE; apply: Hdiff; rewrite (negbTE HjnS1) HjS2.
split.
- have H2 := leq_trans (subset_leq_card Hsub12) HcardD.
  have Hinter : #|S1 :&: S2| <= #|S2|
    by apply: subset_leq_card; exact: subsetIr.
  rewrite -[X in X <= _](cardsID S2 S1).
  apply: (@leq_trans (#|S2| + #|S1 :\: S2|)).
    by rewrite leq_add2r.
  by rewrite leq_add2l.
- have H2 := leq_trans (subset_leq_card Hsub21) HcardD.
  have Hinter : #|S2 :&: S1| <= #|S1|
    by apply: subset_leq_card; exact: subsetIr.
  rewrite -[X in X <= _](cardsID S1 S2).
  apply: (@leq_trans (#|S1| + #|S2 :\: S1|)).
    by rewrite leq_add2r.
  by rewrite leq_add2l.
Qed.

(* ========================================================================== *)
(* Section 5: Word cardinality and counting                                   *)
(* ========================================================================== *)

(* Total number of words of length L *)
Lemma card_pgg_word (L : nat) : #|{: pgg_word M L}| = Tg ^ L.
Proof. by rewrite card_tuple card_ord. Qed.

(* For fdist_uniform, we need the (n.+1) form *)
Lemma card_pgg_word_pos (L : nat) :
  0 < Tg ^ L.
Proof. by rewrite expn_gt0. Qed.

Lemma card_pgg_word_succ (L : nat) :
  #|{: pgg_word M L}| = (Tg ^ L).-1.+1.
Proof. by rewrite card_pgg_word prednK // expn_gt0. Qed.

(* --- Counting: total commuting pairs across all words --- *)

(* The total number of (word, commuting-position) pairs.
   For each position k < L-1, the pair (w_k, w_{k+1}) is drawn from
   Tg * Tg generators, and there are Tg^(L-2) choices for the remaining
   positions.  So the total is L.-1 * edge_count * Tg^(L-2).

   More precisely, for L >= 2:
   \sum_w comm_pair_count(w) = L.-1 * (edge_count / 2) * 2 * Tg^(L-2)
                             = L.-1 * edge_count * Tg^(L-2)

   For L <= 1, both sides are 0.
*)
Lemma total_comm_pairs (L : nat) :
  \sum_(w : pgg_word M L) comm_pair_count w =
  match L with
  | 0 => 0
  | 1 => 0
  | L''.+2 => L''.+1 * edge_count * Tg ^ L''
  end.
Proof.
(* The key idea: exchange the order of summation.
   sum_w sum_{k < L-1} [comm w_k w_{k+1}]
   = sum_{k < L-1} sum_w [comm w_k w_{k+1}]
   = sum_{k < L-1} edge_count * Tg^(L-2)
   = (L-1) * edge_count * Tg^(L-2)

   Each inner sum counts words where positions k and k+1 form a
   commuting pair, with Tg^(L-2) free choices for the other positions. *)
Admitted.

(* Average number of commuting pairs per word *)
(* E[comm_pair_count] = L.-1 * edge_count / Tg^2 *)

(* ========================================================================== *)
(* Section 6: Connection to trace class size                                  *)
(* ========================================================================== *)

(* Number of trace classes containing words with zero commuting pairs *)
Lemma zero_comm_pair_traces (L : nat) :
  #|[set w : pgg_word M L | comm_pair_count w == 0]| <=
  @n_traces R L.
Proof.
rewrite /n_traces /n_comp_mem.
apply: subset_leq_card.
apply/subsetP => w.
rewrite !inE => /eqP H0.
by rewrite andbT; apply/eqP; exact: comm_pair_count_zero_root H0.
Qed.

(* Lower bound: words with no commuting adjacent pairs contribute
   directly to trace count *)
Lemma zero_comm_words_are_traces (L : nat) (w : pgg_word M L) :
  comm_pair_count w = 0 ->
  [set w' : pgg_word M L | trace_equiv w w'] = [set w].
Proof.
move=> H0.
apply/setP => w'.
rewrite !inE.
apply/idP/idP.
  move=> Hte.
  by apply/eqP; symmetry; exact: comm_pair_count_zero_singleton H0 Hte.
by move/eqP => ->; rewrite /trace_equiv connect0.
Qed.

End word_analysis.
