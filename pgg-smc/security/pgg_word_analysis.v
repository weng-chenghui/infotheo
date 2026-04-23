(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div binomial fingraph path.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.

(******************************************************************************)
(* PGG: Commuting Pair Analysis for RAAG Words                               *)
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

(** edge_count_sym — the edge-count cardinality is unchanged when the commutation pair is read backwards.
    Kind: helper.
    Why: lets downstream fibre-counting arguments swap the two coordinates freely when enumerating commuting ordered pairs.
    Used by: total_comm_pairs. *)
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

(** comm_pair_count_zero_adj_swap — a word with no commuting adjacent pairs admits no adjacent swap.
    Kind: helper.
    Why: bridges the numerical count of commuting adjacencies and the structural adjacency-swap predicate that drives trace equivalence.
    Used by: comm_pair_count_zero_adj_swap_sym, comm_pair_count_zero_root.
    Naming: six components read as "count of commuting pairs is zero implies no adjacent swap"; shorter names collide with the symmetric variant below, so each semantic fragment is retained. *)
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

(** comm_pair_count_zero_adj_swap_sym — symmetric-closure version of comm_pair_count_zero_adj_swap.
    Kind: helper.
    Why: the trace-equivalence relation uses the symmetric closure of adj_swap, so the zero-count obstruction is lifted to that relation.
    Used by: comm_pair_count_zero_root, comm_pair_count_zero_singleton.
    Naming: seven components are the symmetric companion of comm_pair_count_zero_adj_swap; the trailing _sym is the standard MathComp symmetry marker. *)
Lemma comm_pair_count_zero_adj_swap_sym (L : nat) (w1 w2 : pgg_word M L) :
  comm_pair_count w1 = 0 -> adj_swap_sym w1 w2 = false.
Proof.
move=> H1.
rewrite /adj_swap_sym (comm_pair_count_zero_adj_swap w2 H1) /=.
apply/negbTE/negP => Hadj.
have := adj_swap_symmetric Hadj.
by rewrite (comm_pair_count_zero_adj_swap _ H1).
Qed.

(** comm_pair_count_zero_root — a zero-count word is its own trace-class representative.
    Kind: helper.
    Why: establishes a canonical form for zero-commuting-pair words, used when counting the contribution of such words to the total trace count.
    Used by: zero_comm_pair_traces.
    Naming: five components "count of commuting pairs is zero implies root"; each token plays a distinct semantic role in the statement. *)
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

(** comm_pair_count_zero_singleton — trace-equivalent words with zero commuting pairs are identical.
    Kind: helper.
    Why: zero-commuting-pair words have singleton trace classes, which is exactly the cardinality bound that feeds the trace-count argument.
    Used by: zero_comm_words_are_traces.
    Naming: five components capture subject / property / value / consequence; renaming would lose the parallel with comm_pair_count_zero_root and break the family's readability. *)
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

(** comm_pair_count_full_comm — when all distinct generators commute and adjacent generators in the word are distinct, the count hits its maximum L-1.
    Kind: helper.
    Why: upper-bound saturation lemma for the edge-count argument; provides the tight case that makes the mean-value estimate non-trivial.
    Used by: total_comm_pairs and downstream mixing estimates.
    Naming: five components "count of commuting pairs in the full-commuting regime"; the _full_comm qualifier is the standard way to mark the saturation hypothesis. *)
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

(** adj_swap_comm_pair_diff — an adjacent swap shifts the commuting-pair count by at most 2 in each direction.
    Kind: helper.
    Why: bi-directional Lipschitz control of comm_pair_count under a single swap, needed for telescoping arguments across trace equivalence chains.
    Used by: downstream mixing estimates that track how comm_pair_count evolves along a trace-equivalence walk.
    Naming: five components "swap at adjacent positions yields a commuting-pair difference"; each token names a distinct quantity, and the companion name in pgg_raag.v already uses this pattern. *)
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

(** card_pgg_word_succ — word-cardinality rewritten in successor form for fdist_uniform.
    Kind: helper.
    Why: fdist_uniform expects a cardinality of the form n.+1; this lemma packages card_pgg_word with prednK to discharge that shape.
    Used by: uniform word-distribution constructions in the security pipeline. *)
Lemma card_pgg_word_succ (L : nat) :
  #|{: pgg_word M L}| = (Tg ^ L).-1.+1.
Proof. by rewrite card_pgg_word prednK // expn_gt0. Qed.

(* --- Uniform fiber counting for tuples --- *)

(* For two distinct positions i, j in an (m.+2)-tuple over T, the number
   of tuples with prescribed values at i and j is #|T|^m. *)

Section fiber_count.
Variable T : finType.
Variable m : nat.
Variables (fi fj : 'I_m.+2).
Hypothesis Hfij : fi != fj.

Let fib (a b : T) :=
  [set w : m.+2.-tuple T | (tnth w fi == a) && (tnth w fj == b)].

Let tsp (w : m.+2.-tuple T) (a b : T) : m.+2.-tuple T :=
  [tuple if k == fi then a
         else if k == fj then b
         else tnth w k | k < m.+2].

Let tnth_tsp (w : m.+2.-tuple T) (a b : T) (k : 'I_m.+2) :
  tnth (tsp w a b) k =
  if k == fi then a else if k == fj then b else tnth w k.
Proof. by rewrite /tsp tnth_mktuple. Qed.

Let tsp_id (w : m.+2.-tuple T) :
  tsp w (tnth w fi) (tnth w fj) = w.
Proof.
apply: eq_from_tnth => k; rewrite tnth_tsp.
by case: (k =P fi) => [-> | _] //; case: (k =P fj) => [-> | _].
Qed.

Let tsp_compose (w : m.+2.-tuple T) (a b a' b' : T) :
  tsp (tsp w a b) a' b' = tsp w a' b'.
Proof.
apply: eq_from_tnth => k; rewrite !tnth_tsp.
by case: (k =P fi) => // _; case: (k =P fj).
Qed.

Let tsp_in_fib (w : m.+2.-tuple T) (a b : T) :
  tsp w a b \in fib a b.
Proof.
rewrite inE !tnth_tsp eqxx /=.
by rewrite ifN ?eqxx //; rewrite eq_sym.
Qed.

Let fib_leq (a b a' b' : T) : #|fib a b| <= #|fib a' b'|.
Proof.
have Hinj : {in fib a b &, injective (fun w => tsp w a' b')}.
  move=> w1 w2 Hw1 Hw2 Heq.
  have Hsp1 : tsp w1 a b = w1.
    by move: Hw1; rewrite inE => /andP [/eqP Hi /eqP Hj]; rewrite -Hi -Hj tsp_id.
  have Hsp2 : tsp w2 a b = w2.
    by move: Hw2; rewrite inE => /andP [/eqP Hi /eqP Hj]; rewrite -Hi -Hj tsp_id.
  have := congr1 (fun w => tsp w a b) Heq.
  by rewrite !tsp_compose Hsp1 Hsp2.
rewrite -(card_in_imset Hinj).
apply: subset_leq_card.
by apply/subsetP => w /imsetP [w' Hw' ->]; exact: tsp_in_fib.
Qed.

(** fiber_count_card — the number of (m+2)-tuples with prescribed values at two distinct positions is |T|^m.
    Kind: helper.
    Why: exact cardinality for fibres of the two-position projection, reused as the inner count in the edge-count pushforward argument.
    Used by: total_comm_pairs and the pushforward counting in pgg_mixing. *)
Lemma fiber_count_card (a b : T) :
  #|fib a b| = #|T| ^ m.
Proof.
have fib_eq : forall a0 b0 a1 b1 : T, #|fib a0 b0| = #|fib a1 b1|
  by move=> *; apply/eqP; rewrite eqn_leq !fib_leq.
have Htotal : \sum_(p : (T * T)%type) #|fib p.1 p.2| = #|{: m.+2.-tuple T}|.
  rewrite -sum1_card
    (partition_big (fun w : m.+2.-tuple T => (tnth w fi, tnth w fj))
      xpredT) //=.
  apply: eq_bigr => [[a0 b0]] _.
  rewrite -sum1_card; apply: eq_bigl => w.
  by rewrite inE xpair_eqE.
rewrite (eq_bigr (fun _ => #|fib a b|)) in Htotal;
  last by move=> [a' b'] _; exact: fib_eq.
rewrite sum_nat_const card_tuple card_prod in Htotal.
have Hpos : 0 < #|T| by apply/card_gt0P; exists a.
rewrite !expnS mulnA in Htotal.
by move/eqP: Htotal; rewrite eqn_pmul2l ?muln_gt0 ?Hpos // => /eqP.
Qed.

End fiber_count.

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
case: L => [|[|L'']].
- by rewrite big1.
- rewrite big1 // => w _.
  rewrite /comm_pair_count /=.
  by rewrite (_ : #|_| = 0) //; apply: eq_card0 => -[].
- (* L = L''.+2: exchange summation, partition by pair, count fibers *)
  (* Step 1: Rewrite comm_pair_count as a sum over positions *)
  transitivity (\sum_(w : pgg_word M L''.+2) \sum_(k < L''.+1)
    (comm (tnth w (@Ordinal L''.+2 (val k)
                    (ltn_trans (ltn_ord k) (ltnSn L''.+1))))
          (tnth w (@Ordinal L''.+2 (val k).+1 (ltn_ord k))) : nat)).
  { apply: eq_bigr => w _ /=.
    rewrite -sum1_card big_mkcond /=.
    apply: eq_bigr => k _.
    by rewrite inE; case: (comm _ _). }
  (* Step 2: Exchange order of summation *)
  rewrite exchange_big /=.
  (* Step 3: For each position k, partition by the pair at k,k+1 *)
  transitivity (\sum_(k < L''.+1) (edge_count * Tg ^ L'')).
  { apply: eq_bigr => k _.
    set k0 : 'I_L''.+2 := @Ordinal L''.+2 (val k)
      (ltn_trans (ltn_ord k) (ltnSn L''.+1)).
    set k1 : 'I_L''.+2 := @Ordinal L''.+2 (val k).+1 (ltn_ord k).
    have Hk01 : k0 != k1.
      by apply/eqP => Heq; have := congr1 val Heq => /= /n_Sn.
    rewrite (partition_big (fun w : L''.+2.-tuple 'I_Tg =>
      (tnth w k0, tnth w k1)) xpredT) //=.
    (* Replace inner sums with (comm p.1 p.2) * fiber_size *)
    transitivity (\sum_(p : ('I_Tg * 'I_Tg)%type)
      (comm p.1 p.2 : nat) *
      #|[set w : L''.+2.-tuple 'I_Tg |
          (tnth w k0 == p.1) && (tnth w k1 == p.2)]|).
    { apply: eq_bigr => [[a b]] _.
      case Hab : (comm a b).
      - rewrite mul1n -sum1_card.
        apply: eq_big => w.
          by rewrite inE xpair_eqE.
        by rewrite xpair_eqE => /andP [/eqP -> /eqP ->]; rewrite Hab.
      - rewrite mul0n big1 // => w.
        by rewrite xpair_eqE => /andP [/eqP -> /eqP ->]; rewrite Hab. }
    (* Each fiber has size Tg^L'' *)
    transitivity (\sum_(p : ('I_Tg * 'I_Tg)%type)
      (comm p.1 p.2 : nat) * Tg ^ L'').
    { apply: eq_bigr => [[a b]] _.
      congr (_ * _).
      rewrite (@fiber_count_card _ _ _ _ Hk01).
      by rewrite card_ord. }
    (* Factor out Tg^L'' and identify edge_count *)
    rewrite -big_distrl /=; congr (_ * _).
    symmetry; rewrite /edge_count -sum1_card big_mkcond /=.
    by apply: eq_bigr => -[a b] _; rewrite inE; case: (comm a b). }
  (* Step 4: L''.+1 copies of edge_count * Tg^L'' *)
  by rewrite big_const_ord iter_addn_0 mulnC -mulnA.
Qed.

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

(** zero_comm_words_are_traces — the trace class of a zero-commuting-pair word is the singleton containing that word.
    Kind: helper.
    Why: converts the singleton result of comm_pair_count_zero_singleton into a set-level identity, which is the shape consumed by the subset bound on n_traces.
    Used by: zero_comm_pair_traces and downstream trace-count estimates.
    Naming: five components "zero commuting pairs make the words trace-class representatives"; each token names a semantic fragment and shorter names would collide with the _singleton variant. *)
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
