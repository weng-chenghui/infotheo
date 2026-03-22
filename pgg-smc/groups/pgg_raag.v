(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop fingraph path binomial.
From Stdlib Require Import Wf_nat.
From pgg_smc Require Import pgg_interface pgg_weval_inj.

(******************************************************************************)
(* PGG: RAAG (Right-Angled Artin Group) Search Space Theory                  *)
(* Group presentation: <s_1,...,s_Tg | s_i s_j = s_j s_i for (i,j) in E(Gamma)>  *)
(*                                                                            *)
(* A commutation graph on Tg generators determines which pairs of generators  *)
(* commute.  Two words are trace-equivalent if one can be obtained from the   *)
(* other by swapping adjacent commuting generators.  The number of trace      *)
(* equivalence classes (traces) satisfies:                                    *)
(*                                                                            *)
(*   search_space L <= n_traces L <= Tg^L                                     *)
(*                                                                            *)
(* Empty graph (no commutations) -> n_traces = Tg^L (free case)               *)
(* Complete graph (all commute) -> n_traces = 'C(L+Tg-1, Tg-1) (abelian)     *)
(*                                                                            *)
(* Part 1: Nat-level computable trace count (for vm_compute)                  *)
(*   foata_depth_at comm prev x == depth of x given preceding (depth,val)     *)
(*   foata_pairs comm prev w == compute (depth, value) pairs left to right    *)
(*   dv_leq p1 p2 == lexicographic (depth, value) order                       *)
(*   foata_nf comm w == Foata normal form (canonical trace representative)    *)
(*   n_traces_natB Tg L comm == number of distinct Foata normal forms         *)
(*                                                                            *)
(* Part 2: Abstract trace equivalence (MathComp level)                        *)
(*   swap_word k w == swap positions k and k+1 in word w                      *)
(*   adj_swap comm w1 w2 == w2 is obtained from w1 by one adjacent swap      *)
(*   trace_equiv comm w1 w2 == reflexive-transitive-symmetric closure         *)
(*   n_traces comm L == number of trace equivalence classes                   *)
(*                                                                            *)
(* Part 3: Key lemmas                                                         *)
(*   word_eval_adj_swap : adjacent commuting swap preserves word_eval         *)
(*   word_eval_trace : trace-equivalent words evaluate equally                *)
(*   search_space_le_traces : search_space L <= n_traces L                    *)
(*   raag_weval_inj : word_eval injective on trace classes                    *)
(*   raag_weval_inj_search_space : raag_weval_inj -> search_space = n_traces  *)
(*   search_space_chain : search_space L <= n_traces L <= Tg^L                *)
(*                                                                            *)
(* Part 4: Extreme cases                                                      *)
(*   empty_comm_traces : no commutations -> n_traces = Tg^L                   *)
(*   full_comm_traces : all commute -> n_traces = 'C(L+Tg-1, Tg-1)           *)
(*                                                                            *)
(* Part 5: Nat-level reflection                                               *)
(*   n_traces_of_natB : connects nat-level computation to abstract n_traces   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Part 1: Nat-level computable trace count                                   *)
(* ========================================================================== *)

(* Foata normal form: canonical representative of trace equivalence classes.
   1. Compute (depth, value) pairs left-to-right.
   2. Sort by (depth, value) lexicographic order.
   3. Project to values. *)

(* Depth of element x given preceding (depth, value) pairs:
   max{d+1 : (d,v) in prev, ~comm v x}, or 0 if all commute. *)
Definition foata_depth_at (comm : nat -> nat -> bool)
    (prev : seq (nat * nat)) (x : nat) : nat :=
  foldl (fun acc dv => if comm dv.2 x then acc else maxn acc dv.1.+1) 0 prev.

(* Compute (depth, value) pairs left to right *)
Fixpoint foata_pairs (comm : nat -> nat -> bool)
    (prev : seq (nat * nat)) (w : seq nat) : seq (nat * nat) :=
  match w with
  | [::] => prev
  | x :: rest =>
    let d := foata_depth_at comm prev x in
    foata_pairs comm (rcons prev (d, x)) rest
  end.

(* Lexicographic order on (depth, value) pairs *)
Definition dv_leq (p1 p2 : nat * nat) : bool :=
  (p1.1 < p2.1) || ((p1.1 == p2.1) && (p1.2 <= p2.2)).

(* Foata normal form *)
Definition foata_nf (comm : nat -> nat -> bool) (w : seq nat) : seq nat :=
  [seq p.2 | p <- sort dv_leq (foata_pairs comm [::] w)].

Definition n_traces_natB (Tg L : nat) (comm : nat -> nat -> bool) : nat :=
  size (undup (map (foata_nf comm) (all_words Tg L))).

(* Extensionality: foata_nf depends only on crel values at word elements *)
Lemma foata_depth_at_ext comm1 comm2 prev x :
  (forall a, a \in [seq p.2 | p <- prev] -> comm1 a x = comm2 a x) ->
  foata_depth_at comm1 prev x = foata_depth_at comm2 prev x.
Proof.
rewrite /foata_depth_at.
elim: prev 0 => [|[d v] prev IH] acc //= Heq.
rewrite Heq; last by rewrite mem_head.
apply: IH => a Ha.
by apply: Heq; rewrite /= inE Ha orbT.
Qed.

Lemma foata_pairs_ext comm1 comm2 prev w :
  (forall a b, a \in [seq p.2 | p <- prev] ++ w ->
               b \in [seq p.2 | p <- prev] ++ w ->
               comm1 a b = comm2 a b) ->
  foata_pairs comm1 prev w = foata_pairs comm2 prev w.
Proof.
elim: w prev => [|x w IH] prev //= Heq.
have Hdepth : foata_depth_at comm1 prev x = foata_depth_at comm2 prev x.
  apply: foata_depth_at_ext => a Ha.
  apply: Heq.
  - by rewrite mem_cat Ha.
  - by rewrite mem_cat inE eqxx orbT.
rewrite Hdepth.
apply: IH => a b.
rewrite map_rcons cat_rcons => Ha' Hb'.
exact: Heq.
Qed.

Lemma foata_nf_ext comm1 comm2 w :
  (forall a b, a \in w -> b \in w -> comm1 a b = comm2 a b) ->
  foata_nf comm1 w = foata_nf comm2 w.
Proof.
move=> Heq; rewrite /foata_nf.
congr (map _ (sort _ _)).
by apply: foata_pairs_ext => a b /=; exact: Heq.
Qed.

Lemma leq_sum_sub (I : finType) (P Q : pred I) (f : I -> nat) :
  (forall i, P i -> Q i) ->
  \sum_(i | P i) f i <= \sum_(i | Q i) f i.
Proof.
move=> HPQ.
rewrite big_mkcond [X in _ <= X]big_mkcond.
apply: leq_sum => i _.
case HP : (P i) => //=.
by rewrite (HPQ i HP).
Qed.

(* ========================================================================== *)
(* RAAG mixin + structure                                                     *)
(* ========================================================================== *)

HB.mixin Record isRAAG0 (T : PGGTypes) of GeneratedMonodromyRepr T := {
  raag_comm : rel 'I_(@pgg_ngens' T).+1 ;
  raag_comm_sym : symmetric raag_comm ;
  raag_comm_irrefl : irreflexive raag_comm ;
  raag_Hcomm : forall i j : 'I_(@pgg_ngens' T).+1,
    raag_comm i j ->
    (tnth (@pgg_sigmas T) i * tnth (@pgg_sigmas T) j =
     tnth (@pgg_sigmas T) j * tnth (@pgg_sigmas T) i)%g ;
  raag_gen_inj :
    injective (fun i : 'I_(@pgg_ngens' T).+1 => tnth (@pgg_sigmas T) i) ;
}.

#[short(type=RAAGType)]
HB.structure Definition RAAG :=
  { T of isMonodromyRepr T & hasGenerators T & isRAAG0 T }.

HB.factory Record isRAAG (T : PGGTypes) of GeneratedMonodromyRepr T := {
  raag_comm : rel 'I_(@pgg_ngens' T).+1 ;
  raag_comm_sym : symmetric raag_comm ;
  raag_comm_irrefl : irreflexive raag_comm ;
  raag_Hcomm : forall i j : 'I_(@pgg_ngens' T).+1,
    raag_comm i j ->
    (tnth (@pgg_sigmas T) i * tnth (@pgg_sigmas T) j =
     tnth (@pgg_sigmas T) j * tnth (@pgg_sigmas T) i)%g ;
  raag_gen_inj :
    injective (fun i : 'I_(@pgg_ngens' T).+1 => tnth (@pgg_sigmas T) i) ;
}.

HB.builders Context T of isRAAG T.
  HB.instance Definition _ := @isRAAG0.Build T
    raag_comm raag_comm_sym raag_comm_irrefl raag_Hcomm raag_gen_inj.
HB.end.

(* ========================================================================== *)
(* Part 2: Abstract trace equivalence                                         *)
(* ========================================================================== *)

Section raag_theory.

Variable R : RAAGType.
Let gT := pgg_gT R.
Let M : GeneratedMonodromyReprType := R.
Let Tg := (@pgg_ngens' R).+1.
Let sigmas := @pgg_sigmas R.
Let comm : rel 'I_Tg := @raag_comm R.
Let comm_sym : symmetric comm := @raag_comm_sym R.
Let comm_irrefl : irreflexive comm := @raag_comm_irrefl R.
Let Hcomm : forall i j : 'I_Tg,
  comm i j -> (tnth sigmas i * tnth sigmas j = tnth sigmas j * tnth sigmas i)%g
  := @raag_Hcomm R.

(* --- swap_word: swap positions k and k+1 in a word --- *)

Definition swap_word (L : nat) (k : 'I_L.-1) (w : pgg_word M L)
    : pgg_word M L :=
  match L as L0 return 'I_L0.-1 -> pgg_word M L0 -> pgg_word M L0 with
  | 0 => fun k _ => [tuple]
  | L'.+1 => fun k w =>
    let kL : val k < L'.+1 := ltn_trans (ltn_ord k) (ltnSn L') in
    let k1L : (val k).+1 < L'.+1 := ltn_ord k in
    mktuple (fun i : 'I_L'.+1 =>
      if val i == val k then tnth w (Ordinal k1L)
      else if val i == (val k).+1 then tnth w (Ordinal kL)
      else tnth w i)
  end k w.

Lemma swap_word_tnth L' (k : 'I_L') (w : pgg_word M L'.+1)
    (i : 'I_L'.+1) :
  tnth (@swap_word L'.+1 k w) i =
  if val i == val k then
    tnth w (@Ordinal L'.+1 (val k).+1 (ltn_ord k))
  else if val i == (val k).+1 then
    tnth w (@Ordinal L'.+1 (val k) (ltn_trans (ltn_ord k) (ltnSn L')))
  else tnth w i.
Proof. by rewrite /swap_word tnth_mktuple. Qed.

(* --- adj_swap: one adjacent commuting swap --- *)

Definition adj_swap (L : nat) : rel (pgg_word M L) :=
  match L as L0 return rel (pgg_word M L0) with
  | 0 => fun _ _ => false
  | L'.+1 => fun w1 w2 =>
    [exists k : 'I_L',
      comm (tnth w1 (@Ordinal L'.+1 (val k) (ltn_trans (ltn_ord k) (ltnSn L'))))
           (tnth w1 (@Ordinal L'.+1 (val k).+1 (ltn_ord k : val k < L'))) &&
      (w2 == @swap_word L'.+1 k w1)]
  end.

Definition adj_swap_sym (L : nat) (w1 w2 : pgg_word M L) : bool :=
  adj_swap w1 w2 || adj_swap w2 w1.

Definition trace_equiv (L : nat) : rel (pgg_word M L) :=
  connect (adj_swap_sym (L:=L)).

Definition n_traces (L : nat) : nat :=
  n_comp (adj_swap_sym (L:=L)) {: pgg_word M L}.

(* ========================================================================== *)
(* Part 3: Key lemmas                                                         *)
(* ========================================================================== *)

(* Swapping adjacent commuting generators preserves word_eval *)
Lemma word_eval_adj_swap L (w1 w2 : pgg_word M L) :
  adj_swap w1 w2 -> word_eval w1 = word_eval w2.
Proof.
case: L w1 w2 => [|L'] w1 w2; first by [].
move/existsP => [k /andP [Hc /eqP ->]].
rewrite /word_eval.
set kv := val k.
set ik : 'I_L'.+1 := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')).
set ik1 : 'I_L'.+1 := @Ordinal L'.+1 kv.+1 (ltn_ord k : kv < L').
(* The two products differ only at positions k and k+1 *)
(* Use a helper: swapping adjacent commuting factors in a product *)
suff Hprod : forall (n : nat) (f g : 'I_n -> gT)
  (j : 'I_n) (j1 : 'I_n),
  val j1 = (val j).+1 ->
  (forall i, i != j -> i != j1 -> f i = g i) ->
  g j = f j1 -> g j1 = f j ->
  (f j * f j1 = f j1 * f j)%g ->
  (\prod_(i < n) f i = \prod_(i < n) g i)%g.
  apply: (Hprod _ _ _ ik ik1 (erefl _)).
  - move=> i Hi1 Hi2; rewrite swap_word_tnth.
    have Hne1 : val i != kv.
      by apply: contra_neq Hi1 => Hvi; apply: val_inj.
    have Hne2 : val i != kv.+1.
      by apply: contra_neq Hi2 => Hvi; apply: val_inj.
    by rewrite (negbTE Hne1) (negbTE Hne2).
  - by rewrite swap_word_tnth /= eqxx.
  - rewrite swap_word_tnth /=.
    have -> : (kv.+1 == kv) = false.
      by apply/negbTE; rewrite -[X in _ != X]addn0 -addn1 eqn_add2l.
    by rewrite eqxx.
  - exact: Hcomm Hc.
(* Prove Hprod: swap adjacent commuting elements in a product.
   Convert to nat-indexed bigop, split into three segments, apply commutativity *)
move=> {w1 k kv ik ik1 Hc} n f g j j1 Hj1 Hfg Hgj Hgj1 Hcomm_fg.
have Hjne : j != j1.
  by apply/eqP => /(congr1 val) /=; rewrite Hj1 => /n_Sn.
have Hj1n : (val j).+2 <= n.
  by move: (ltn_ord j1); rewrite -Hj1.
have Hkn : val j <= n := leq_trans (leqnSn _) (leq_trans (leqnSn _) Hj1n).
have Hkk2 : val j <= (val j).+2 := leqW (leqnSn _).
(* Wrap f, g into nat-indexed functions via Ordinal *)
set f' := fun i : nat => match ltnP i n with
  | LtnNotGeq h => f (Ordinal h) | _ => 1%g end.
set g' := fun i : nat => match ltnP i n with
  | LtnNotGeq h => g (Ordinal h) | _ => 1%g end.
have Hf'E : forall i0 : 'I_n, f' (val i0) = f i0.
  move=> i0; rewrite /f'; case: ltnP => h0.
    by congr f; apply: val_inj.
  by exfalso; move: (ltn_ord i0); rewrite ltnNge h0.
have Hg'E : forall i0 : 'I_n, g' (val i0) = g i0.
  move=> i0; rewrite /g'; case: ltnP => h0.
    by congr g; apply: val_inj.
  by exfalso; move: (ltn_ord i0); rewrite ltnNge h0.
transitivity (\prod_(0 <= i < n) f' i)%g.
  rewrite big_mkord; apply: eq_bigr => i _; by rewrite Hf'E.
transitivity (\prod_(0 <= i < n) g' i)%g; last first.
  rewrite big_mkord; apply: eq_bigr => i _; by rewrite Hg'E.
(* Now work with nat-indexed products *)
(* Split [0, n) = [0, j) ++ [j, j+2) ++ [j+2, n) *)
have Hsplit : forall h : nat -> gT,
  (\prod_(0 <= i < n) h i =
   \prod_(0 <= i < val j) h i *
   (\prod_(val j <= i < (val j).+2) h i *
    \prod_((val j).+2 <= i < n) h i))%g.
  move=> h.
  rewrite (@big_cat_nat _ _ _ (val j) _ _ xpredT h (leq0n _) Hkn).
  by congr (_ * _)%g; rewrite (@big_cat_nat _ _ _ (val j).+2 _ _ xpredT h Hkk2 Hj1n).
rewrite !Hsplit.
congr (_ * _)%g.
  (* Before: [0, j) — f' and g' agree *)
  apply: eq_big_nat => i /andP [_ Hi2].
  have Hin : i < n := ltn_trans (ltn_trans Hi2 (ltnSn _)) Hj1n.
  have -> : f' i = f (Ordinal Hin) := Hf'E (Ordinal Hin).
  have -> : g' i = g (Ordinal Hin) := Hg'E (Ordinal Hin).
  apply: Hfg.
    rewrite -val_eqE /=; apply/eqP => Habs.
    by move: Hi2; rewrite Habs ltnNge leqnn.
  rewrite -val_eqE /=; apply/eqP => Habs.
  by move: Hi2; rewrite Habs Hj1 ltnNge leqnSn.
congr (_ * _)%g.
  (* Middle: [j, j+2) *)
  rewrite (@big_nat_recl _ _ _ (val j).+1 (val j) _ (leqnSn _)).
  rewrite big_nat1.
  rewrite [RHS](@big_nat_recl _ _ _ (val j).+1 (val j) _ (leqnSn _)).
  rewrite big_nat1.
  have Hjn : val j < n := leq_ltn_trans (leqnSn _) Hj1n.
  have Hj1n' : (val j).+1 < n := Hj1n.
  have -> : f' (val j) = f (Ordinal Hjn) := Hf'E (Ordinal Hjn).
  have -> : g' (val j) = g (Ordinal Hjn) := Hg'E (Ordinal Hjn).
  have -> : f' (val j).+1 = f (Ordinal Hj1n') := Hf'E (Ordinal Hj1n').
  have -> : g' (val j).+1 = g (Ordinal Hj1n') := Hg'E (Ordinal Hj1n').
  have Heqj : Ordinal Hjn = j by apply: val_inj.
  have Heqj1 : Ordinal Hj1n' = j1 by apply: val_inj; exact: esym Hj1.
  by rewrite Heqj Heqj1 Hgj Hgj1 Hcomm_fg.
(* After: [j+2, n) — f' and g' agree *)
apply: eq_big_nat => i /andP [Hi1 Hi2].
have -> : f' i = f (Ordinal Hi2) := Hf'E (Ordinal Hi2).
have -> : g' i = g (Ordinal Hi2) := Hg'E (Ordinal Hi2).
apply: Hfg.
  rewrite -val_eqE /=; apply/eqP => Habs.
  by move: Hi1; rewrite Habs leqNgt ltnS leqnSn.
rewrite -val_eqE /=; apply/eqP => Habs.
by move: Hi1; rewrite Habs Hj1 ltnn.
Qed.

Lemma word_eval_trace L (w1 w2 : pgg_word M L) :
  trace_equiv w1 w2 -> word_eval w1 = word_eval w2.
Proof.
rewrite /trace_equiv => /connectP [p].
elim: p w1 => [w1 _ -> // | w' p IH w1 /= /andP [Hstep Hpath] Hlast].
have Heq : word_eval w1 = word_eval w'.
  case/orP: Hstep => H.
    exact: word_eval_adj_swap H.
  by symmetry; exact: word_eval_adj_swap H.
by rewrite Heq; exact: IH Hpath Hlast.
Qed.

(* adj_swap_sym is symmetric *)
Lemma adj_swap_sym_sym L : symmetric (@adj_swap_sym L).
Proof. by move=> w1 w2; rewrite /adj_swap_sym orbC. Qed.

(* Search space bounded by number of traces *)
Lemma search_space_le_traces L : @search_space M L <= n_traces L.
Proof.
rewrite /search_space /achievable /n_traces.
have Hsym := sym_connect_sym (@adj_swap_sym_sym L).
set e := adj_swap_sym (L:=L).
suff Hsub : [set word_eval w | w : pgg_word M L] \subset
            [set word_eval r | r in predI (roots e) (mem {: pgg_word M L})].
  exact: leq_trans (subset_leq_card Hsub) (leq_imset_card _ _).
apply/subsetP => b /imsetP [x _ ->].
apply/imsetP; exists (root e x).
  by rewrite !inE roots_root // andbT.
exact: word_eval_trace (connect_root _ x).
Qed.

(* RAAG word-eval injectivity: word_eval injective on trace classes *)
Definition raag_weval_inj (L : nat) : Prop :=
  forall w1 w2 : pgg_word M L, word_eval w1 = word_eval w2 -> trace_equiv w1 w2.

Lemma raag_weval_inj_search_space L :
  raag_weval_inj L -> @search_space M L = n_traces L.
Proof.
move=> Hraag.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  exact: search_space_le_traces.
(* n_traces <= search_space: word_eval is injective on roots *)
rewrite /search_space /achievable /n_traces.
set e := adj_swap_sym (L:=L).
have Hsym := sym_connect_sym (@adj_swap_sym_sym L).
set D := predI (roots e) (mem {: pgg_word M L}).
suff Hinj : {in D &, injective (@word_eval M L)}.
  have <- : #|[set word_eval r | r in D]| = n_comp e {: pgg_word M L}.
    by rewrite (card_in_imset Hinj).
  apply: subset_leq_card.
  apply/subsetP => b /imsetP [r Hr ->].
  by apply/imsetP; exists r => //; move: Hr; rewrite !inE andbT.
move=> r1 r2 Hr1 Hr2 Heq.
move: Hr1 Hr2; rewrite /D !inE !andbT => /eqP Hr1 /eqP Hr2.
have Hconn := Hraag _ _ Heq.
rewrite /trace_equiv /e in Hconn.
by move/(rootP Hsym) in Hconn; rewrite Hr1 Hr2 in Hconn.
Qed.

(* Upper bound: n_traces <= Tg^L *)
Lemma n_traces_le_words L : n_traces L <= Tg ^ L.
Proof.
rewrite /n_traces.
apply: leq_trans (max_card _) _.
by rewrite card_tuple card_ord.
Qed.

Lemma search_space_chain L :
  (@search_space M L <= n_traces L) && (n_traces L <= Tg ^ L).
Proof.
by apply/andP; split; [exact: search_space_le_traces | exact: n_traces_le_words].
Qed.

(* ========================================================================== *)
(* Part 4: Extreme cases                                                      *)
(* ========================================================================== *)

(* Empty comm -> n_traces = Tg^L (free case) *)
Lemma empty_comm_adj_swap L (w1 w2 : pgg_word M L) :
  (forall i j : 'I_Tg, ~~ comm i j) -> adj_swap w1 w2 = false.
Proof.
move=> Hempty.
case: L w1 w2 => [|L'] w1 w2 //=.
apply/negbTE/negP.
move/existsP => [k /andP [Hc _]].
set a := tnth w1 (Ordinal (ltn_trans (ltn_ord k) (ltnSn L'))).
set b := tnth w1 (@Ordinal L'.+1 (val k).+1 (ltn_ord k)).
by move: (Hempty a b); rewrite Hc.
Qed.

Lemma empty_comm_traces L :
  (forall i j : 'I_Tg, ~~ comm i j) -> n_traces L = Tg ^ L.
Proof.
move=> Hempty.
rewrite /n_traces.
have Hno : adj_swap_sym (L:=L) =2 (fun _ _ => false).
  by move=> w1 w2; rewrite /adj_swap_sym !empty_comm_adj_swap.
suff -> : n_comp (adj_swap_sym (L:=L)) {: pgg_word M L} =
          #|{: pgg_word M L}|.
  by rewrite card_tuple card_ord.
rewrite /n_comp_mem.
(* When the relation is empty, connect is just eq, so every element is a root *)
have Hconnect : forall w1 w2 : pgg_word M L,
  connect (adj_swap_sym (L:=L)) w1 w2 = (w1 == w2).
  move=> w1 w2.
  apply/idP/idP.
    move/connectP => [p].
    case: p => [_ -> | w' p /= /andP [Hstep _] _].
      by rewrite eqxx.
    by rewrite Hno in Hstep.
  by move/eqP => ->; apply: connect0.
(* Now: roots = predT, since root x = x for all x *)
have Hroots : forall w : pgg_word M L,
  root (adj_swap_sym (L:=L)) w = w.
  move=> w; rewrite /root.
  case: pickP => [w' /= Hw | /= H].
    by move: Hw; rewrite Hconnect => /eqP ->.
  by move: (H w); rewrite /= Hconnect eqxx.
rewrite (eq_card (B := {: pgg_word M L})).
  by rewrite card_tuple card_ord.
move=> w /=; rewrite !inE andbT /roots /=.
by rewrite Hroots eqxx.
Qed.

(* --- Helper: adj_swap preserves perm_eq --- *)
Lemma swap_word_perm L' (k : 'I_L') (w : pgg_word M L'.+1) :
  perm_eq (val (@swap_word L'.+1 k w)) (val w).
Proof.
set ik : 'I_L'.+1 := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')).
set ik1 : 'I_L'.+1 := @Ordinal L'.+1 (val k).+1 (ltn_ord k).
apply/tuple_permP.
exists (tperm ik ik1).
suff -> : @swap_word L'.+1 k w = [tuple tnth w (tperm ik ik1 i) | i < L'.+1] by [].
apply: eq_from_tnth => i.
rewrite tnth_mktuple (swap_word_tnth k w i).
rewrite permE /=.
case: (val i =P val k) => [Heq | Hne].
  have -> : i = ik by apply: val_inj.
  by rewrite eqxx.
case: (val i =P (val k).+1) => [Heq1 | Hne1].
  have -> : i = ik1 by apply: val_inj.
  have Hne_ik : ik1 != ik.
    by rewrite -val_eqE /= neq_ltn ltnSn orbT.
  by rewrite (negbTE Hne_ik) eqxx.
have Hnik : (i == ik) = false.
  by apply/negbTE/eqP => /(congr1 val) /=; exact: Hne.
have Hnik1 : (i == ik1) = false.
  by apply/negbTE/eqP => /(congr1 val) /=; exact: Hne1.
by rewrite Hnik Hnik1.
Qed.

Lemma adj_swap_perm L (w1 w2 : pgg_word M L) :
  adj_swap w1 w2 -> perm_eq (val w1) (val w2).
Proof.
case: L w1 w2 => [|L'] w1 w2 //=.
move/existsP => [k /andP [_ /eqP ->]].
by rewrite perm_sym; exact: swap_word_perm.
Qed.

Lemma trace_perm L (w1 w2 : pgg_word M L) :
  trace_equiv w1 w2 -> perm_eq (val w1) (val w2).
Proof.
rewrite /trace_equiv => /connectP [p].
elim: p w1 => [w1 _ -> | w' p IH w1 /= /andP [Hstep Hpath] Hlast] //.
have Heq : perm_eq (val w1) (val w').
  case/orP: Hstep => H.
    exact: adj_swap_perm H.
  by rewrite perm_sym; exact: adj_swap_perm H.
exact: perm_trans Heq (IH _ Hpath Hlast).
Qed.

(* --- Helper: unsorted sequence has adjacent descent --- *)
Lemma not_sorted_descent (s : seq nat) :
  (1 < size s)%N -> ~~ sorted leq s ->
  exists i : nat, (i.+1 < size s)%N /\
    (nth 0 s i > nth 0 s i.+1)%N.
Proof.
elim: s => [|a s' IH] // Hsz Hns.
case: s' IH Hsz Hns => [|b s'] IH // _ /=.
rewrite negb_and => /orP [Hab | Hab].
  exists 0; split => //.
  by rewrite ltnNge (negbTE Hab).
case: s' IH Hab => [_ | c s'' IH Hab] //.
have Hsz' : (1 < (size s'').+2)%N by [].
have [i [Hi1 Hi2]] := IH Hsz' Hab.
by exists i.+1; split.
Qed.

(* --- Helper: inversion count for well-founded induction --- *)
Definition inv_count L (w : pgg_word M L) : nat :=
  \sum_(i : 'I_L) \sum_(j : 'I_L | val i < val j)
    (val (tnth w j) < val (tnth w i)).

Lemma inv_count_zero_sorted L (w : pgg_word M L) :
  (inv_count w == 0) = sorted leq (map val (val w)).
Proof.
set s := map val (val w).
have Hsz : size s = L by rewrite /s size_map size_tuple.
apply/idP/idP.
- (* no inversions -> sorted *)
  move=> /eqP Hzero.
  apply/(sortedP 0) => i; rewrite Hsz => HiL.
  have Hi'L : (i < L)%N := ltn_trans (ltnSn i) HiL.
  rewrite leqNgt; apply/negP => Hlt.
  suff : (0 < inv_count w)%N by rewrite Hzero.
  rewrite /inv_count.
  rewrite (bigD1 (Ordinal Hi'L)) //=.
  apply: leq_trans; last exact: leq_addr.
  rewrite (bigD1 (Ordinal HiL)) /=; last by rewrite ltnSn.
  apply: leq_trans; last exact: leq_addr.
  rewrite !(tnth_nth ord0).
  suff -> : (val (nth ord0 (val w) i.+1) < val (nth ord0 (val w) i)) = true by [].
  move: Hlt; rewrite /s !(nth_map ord0) ?size_tuple //.
- (* sorted -> no inversions *)
  move=> Hs.
  have Hno : forall (i j : 'I_L), val i < val j ->
    ~~ (val (tnth w j) < val (tnth w i)).
    move=> [i Hi] [j Hj] /= Hij.
    rewrite -leqNgt !(tnth_nth ord0).
    have := sorted_leq_nth leq_trans leqnn 0 Hs.
    move=> Hmono.
    have Hi' : i \in [pred n | n < size s] by rewrite inE /s size_map size_tuple.
    have Hj' : j \in [pred n | n < size s] by rewrite inE /s size_map size_tuple.
    have := Hmono i j Hi' Hj' (ltnW Hij).
    rewrite /s !(nth_map ord0) ?size_tuple //.
  rewrite /inv_count.
  apply/eqP; apply: big1 => [[i Hi]] _ /=.
  apply: big1 => [[j Hj]] /= Hij.
  have := Hno (Ordinal Hi) (Ordinal Hj) Hij.
  by move/negbTE ->.
Qed.

(* Swapping an adjacent descent decreases inv_count *)
Lemma inv_count_swap_lt L' (k : 'I_L') (w : pgg_word M L'.+1) :
  let ik := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')) in
  let ik1 := @Ordinal L'.+1 (val k).+1 (ltn_ord k) in
  val (tnth w ik) > val (tnth w ik1) ->
  inv_count (@swap_word L'.+1 k w) < inv_count w.
Proof.
move=> /= Hdesc.
set ik : 'I_L'.+1 := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')).
set ik1 : 'I_L'.+1 := @Ordinal L'.+1 (val k).+1 (ltn_ord k).
set sw := @swap_word L'.+1 k w.
have Hik_ne : ik != ik1.
  by apply/eqP => /(congr1 val) /= /n_Sn.
have Hik_succ : val ik1 = (val ik).+1 by rewrite /ik1 /ik.
have Hval_ik1 : forall (x : 'I_L'.+1),
  val x = (val k).+1 -> x = ik1.
  move=> x Hx; apply: ord_inj.
  by have : val x = val ik1 by rewrite /ik1 /=.
have Hswt : forall i : 'I_L'.+1, tnth sw i = tnth w (tperm ik ik1 i).
  move=> i; rewrite /sw swap_word_tnth.
  case Hi : (val i == val k).
    have Hieq : i = ik by apply: val_inj; exact: (eqP Hi).
    by rewrite Hieq tpermL.
  case Hi1 : (val i == (val k).+1).
    by rewrite (Hval_ik1 i (eqP Hi1)) tpermR.
  rewrite tpermD //.
  + by apply/eqP => Heq; move: Hi; rewrite -Heq /= eqxx.
  + by apply/eqP => Heq; move: Hi1; rewrite -Heq /= eqxx.
rewrite /inv_count.
set tp := (tperm ik ik1 : 'I_L'.+1 -> 'I_L'.+1).
have Hinj_tp : injective tp by exact: perm_inj.
have HtpK : cancel tp tp by move=> x; rewrite /tp tpermK.
suff -> : \sum_(i < L'.+1) \sum_(j < L'.+1 | val i < val j)
    (val (tnth sw j) < val (tnth sw i)) =
  \sum_(i < L'.+1) \sum_(j < L'.+1 | val (tp i) < val (tp j))
    (val (tnth w j) < val (tnth w i)).
  rewrite [X in X < _](bigD1 ik) //= [X in _ < X](bigD1 ik) //=.
  apply: (@leq_ltn_trans
    (\sum_(j < L'.+1 | val (tp ik) < val (tp j))
      (val (tnth w j) < val (tnth w ik)) +
     \sum_(i < L'.+1 | i != ik)
      \sum_(j < L'.+1 | val i < val j) (val (tnth w j) < val (tnth w i)))).
  + rewrite leq_add2l.
    apply: leq_sum => i Hine.
    case Hine1 : (i == ik1).
    * rewrite (eqP Hine1) /tp tpermR.
      rewrite (bigD1 ik) /=; last by rewrite tpermL.
      rewrite ltnNge (ltnW Hdesc) /=.
      apply: eq_leq; apply: eq_bigl => j.
      case Hj_ik : (j == ik).
        rewrite (eqP Hj_ik) andbF.
        suff -> : ((val k).+1 < val ik) = false by [].
        by rewrite ltnNge /= leqnSn.
      case Hj_ik1 : (j == ik1).
        by rewrite (eqP Hj_ik1) /tp tpermR /= !ltnn.
      rewrite /tp tpermD //;
        [|by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik
         |by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik1].
      rewrite /= andbT.
      symmetry; rewrite ltn_neqAle eq_sym.
      suff -> : (j != k.+1 :> nat) = true by [].
      apply/eqP => Habs.
      by move: Hj_ik1; rewrite (Hval_ik1 j Habs) eqxx.
    * apply: eq_leq; apply: eq_bigl => j.
      have Hnik : ik != i by rewrite eq_sym.
      have Hnik1 : ik1 != i.
        by apply/eqP => Habs; move: Hine1; rewrite -Habs eqxx.
      case Hj_ik : (j == ik).
        rewrite (eqP Hj_ik) /tp tpermL.
        rewrite tpermD //.
        change ((val i < val ik1) = (val i < val ik)).
        rewrite Hik_succ ltnS leq_eqVlt.
        by have -> : (val i == val ik) = (i == ik) by []; rewrite (negbTE Hine).
      case Hj_ik1 : (j == ik1).
        rewrite (eqP Hj_ik1) /tp tpermR.
        rewrite tpermD //.
        change ((val i < val ik) = (val i < val ik1)).
        symmetry.
        rewrite Hik_succ ltnS leq_eqVlt.
        by have -> : (val i == val ik) = (i == ik) by []; rewrite (negbTE Hine).
      rewrite /tp tpermD //.
      rewrite tpermD //.
      - by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik.
      - by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik1.
  + rewrite ltn_add2r /tp tpermL.
    rewrite [X in _ < X](bigD1 ik1) //=.
    rewrite Hdesc /= add1n.
    apply: leq_ltn_trans; last exact: ltnSn.
    apply: eq_leq; apply: eq_bigl => j.
    case Hj_ik : (j == ik).
      by rewrite (eqP Hj_ik) /tp tpermL /= ltnn ltnn.
    case Hj_ik1 : (j == ik1).
      by rewrite (eqP Hj_ik1) /tp tpermR /= andbF ltnNge leqnSn.
    rewrite /tp tpermD //;
      [|by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik
       |by apply/eqP => Habs; rewrite Habs eqxx in Hj_ik1].
    rewrite /= andbT ltn_neqAle.
    suff -> : (k.+1 != j :> nat) = true by [].
    apply/eqP => Habs.
    suff : j = ik1 by move=> Hj; move: Hj_ik1; rewrite Hj eqxx.
    apply: ord_inj; have : val j = val ik1 by rewrite /ik1 /=.
    done.
transitivity (\sum_(i < L'.+1) \sum_(j < L'.+1 | val i < val j)
    (val (tnth w (tp j)) < val (tnth w (tp i)))).
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite !Hswt.
rewrite (reindex_inj Hinj_tp).
apply: eq_bigr => i _.
rewrite HtpK (reindex_inj Hinj_tp).
apply: eq_bigr => j _.
by rewrite HtpK.
Qed.

(* --- Full comm: every word connects to a sorted word --- *)
Lemma full_comm_connect_sorted L
    (Hfull : forall i j : 'I_Tg, i != j -> comm i j)
    (w : pgg_word M L) :
  exists sw : pgg_word M L,
    sorted leq (map val (val sw)) /\ connect (adj_swap_sym (L:=L)) w sw.
Proof.
move: w.
apply: (well_founded_induction_type
  (Wf_nat.well_founded_ltof _ (@inv_count L))).
move=> w IH.
case Hsorted : (sorted leq (map val (val w))).
  by exists w; split => //; exact: connect0.
case: L w IH Hsorted => [|L'] w IH Hsorted.
  by rewrite (tuple0 w) in Hsorted.
have Hns : ~~ sorted leq (map val (val w)) by rewrite Hsorted.
have HL' : (1 < L'.+1)%N.
  case: L' w IH Hsorted {Hns} => [|L''] // w _ Hsorted.
  by case/tupleP: w Hsorted => x w; rewrite /= (tuple0 w).
have Hsz : (1 < size (map val (val w)))%N.
  by rewrite size_map size_tuple.
have [i [Hi Hdesc]] := not_sorted_descent Hsz Hns.
rewrite size_map size_tuple in Hi.
set ki := @Ordinal L' i Hi.
set ik : 'I_L'.+1 := Ordinal (ltn_trans (ltn_ord ki) (ltnSn L')).
set ik1 : 'I_L'.+1 := @Ordinal L'.+1 (val ki).+1 (ltn_ord ki).
(* Convert descent to tnth form *)
have Hdesc_tnth : val (tnth w ik1) < val (tnth w ik).
  rewrite !(tnth_nth ord0) /=.
  have -> : nth ord0 w i.+1 = nth ord0 (val w) i.+1 by [].
  have -> : nth ord0 w i = nth ord0 (val w) i by [].
  suff Hconv : forall j, j < size (val w) ->
    nth 0 [seq val i0 | i0 <- val w] j = val (nth ord0 (val w) j).
    by rewrite -!Hconv ?size_tuple //; exact: ltn_trans (ltnSn i) Hi.
  by move=> j Hj; rewrite (nth_map ord0).
set sw := @swap_word L'.+1 ki w.
have Hadj : adj_swap_sym w sw.
  rewrite /adj_swap_sym.
  apply/orP; left; apply/existsP; exists ki; apply/andP; split; last by exact/eqP.
  apply: Hfull.
  apply/eqP => Heq; move: Hdesc_tnth; rewrite Heq ltnn //.
have Hlt : Wf_nat.ltof _ (@inv_count L'.+1) sw w.
  rewrite /Wf_nat.ltof.
  by apply/ltP; apply: inv_count_swap_lt.
have [sw' [Hsw' Hconn]] := IH sw Hlt.
exists sw'; split => //.
exact: connect_trans (connect1 Hadj) Hconn.
Qed.

(* Full comm -> n_traces = 'C(L + Tg.-1, Tg.-1) (abelian case) *)
Lemma full_comm_traces L :
  (forall i j : 'I_Tg, i != j -> comm i j) ->
  n_traces L = 'C(L + Tg.-1, Tg.-1).
Proof.
move=> Hfull.
rewrite /n_traces.
set e := adj_swap_sym (L:=L).
have Hsym := sym_connect_sym (@adj_swap_sym_sym L).
set SW := [set t : pgg_word M L | sorted leq (map val (val t))].
suff Heq : n_comp e {: pgg_word M L} = #|SW|.
  rewrite Heq /SW.
  have -> : [set t : pgg_word M L | sorted leq [seq val i | i <- val t]] =
            [set t : L.-tuple 'I_Tg | sorted leq [seq val i | i <- t]].
    by [].
  by rewrite card_sorted_tuples -(bin_sub (leq_addr Tg.-1 L)) addKn.
pose oleq := (fun x y : 'I_Tg => val x <= val y).
have oleq_total : total oleq by move=> x y; exact: leq_total.
have oleq_trans : transitive oleq by move=> x y z; exact: leq_trans.
have oleq_anti : antisymmetric oleq by move=> x y /anti_leq /val_inj.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  (* n_comp <= #|SW|: roots inject into sorted words *)
  set D := [set x : pgg_word M L | roots e x].
  have sort_sz : forall w : pgg_word M L, size (sort oleq (val w)) == L.
    by move=> w0; rewrite size_sort size_tuple.
  set sf := fun w : pgg_word M L => Tuple (sort_sz w).
  have HnD : n_comp e {: pgg_word M L} = #|D|.
    rewrite /n_comp_mem; apply: eq_card => x; rewrite !inE andbT //.
  suff Hinj : {in D &, injective sf}.
    suff Hsub : [set sf r | r in D] \subset SW.
      rewrite HnD -(card_in_imset Hinj).
      exact: subset_leq_card Hsub.
    apply/subsetP => _ /imsetP [r Hr ->].
    rewrite inE /sf /= sorted_map.
    change (sorted oleq (sort oleq r)).
    by apply: sort_sorted => x y; exact: leq_total.
  move=> r1 r2 Hr1 Hr2 Hsf.
  move: Hr1 Hr2; rewrite /D !inE => /eqP Hr1 /eqP Hr2.
  have Hpe : perm_eq (val r1) (val r2).
    apply/(perm_sortP oleq_total oleq_trans oleq_anti).
    by move: Hsf => /(congr1 val) /=.
  suff Hconn : connect e r1 r2 by move/(rootP Hsym) in Hconn; rewrite Hr1 Hr2 in Hconn.
  have [sw1 [Hs1 Hc1]] := full_comm_connect_sorted Hfull r1.
  have [sw2 [Hs2 Hc2]] := full_comm_connect_sorted Hfull r2.
  have Hpe1 := trace_perm Hc1.
  have Hpe2 := trace_perm Hc2.
  have Hpe12 : perm_eq (val sw1) (val sw2).
    apply: (perm_trans (y:=val r1)); first by rewrite perm_sym.
    exact: (perm_trans (y:=val r2) Hpe Hpe2).
  have Hs1' : sorted oleq (val sw1) by rewrite -sorted_map.
  have Hs2' : sorted oleq (val sw2) by rewrite -sorted_map.
  have Heqsw : sw1 = sw2.
    apply: val_inj; exact: (sorted_eq oleq_trans oleq_anti Hs1' Hs2' Hpe12).
  rewrite Heqsw in Hc1.
  apply: (connect_trans Hc1); rewrite Hsym; exact Hc2.
(* #|SW| <= n_comp: different sorted words are in different components *)
(* Inject sorted words into roots via root e *)
set rf := fun sw : pgg_word M L => root e sw.
suff Hinj2 : {in SW &, injective rf}.
  rewrite -(card_in_imset Hinj2).
  apply: subset_leq_card.
  apply/subsetP => _ /imsetP [sw Hsw ->].
  by rewrite /rf !inE roots_root // andbT.
move=> sw1 sw2 Hsw1 Hsw2 Hrf.
move: Hsw1 Hsw2; rewrite !inE => Hs1 Hs2.
have Hconn : connect e sw1 sw2 by apply/(rootP Hsym); rewrite /rf in Hrf.
have Hpe := trace_perm Hconn.
have Hs1' : sorted oleq (val sw1) by rewrite -sorted_map.
have Hs2' : sorted oleq (val sw2) by rewrite -sorted_map.
by apply: val_inj; exact: (sorted_eq oleq_trans oleq_anti Hs1' Hs2' Hpe).
Qed.

Lemma full_comm_trace_iff_perm L (w1 w2 : pgg_word M L) :
  (forall i j : 'I_Tg, i != j -> comm i j) ->
  trace_equiv w1 w2 <-> perm_eq (val w1) (val w2).
Proof.
move=> Hfull; split; first exact: trace_perm.
move=> Hpe.
pose oleq := (fun x y : 'I_Tg => val x <= val y).
have oleq_trans : transitive oleq by move=> x y z; exact: leq_trans.
have oleq_anti : antisymmetric oleq by move=> x y /anti_leq /val_inj.
have [sw1 [Hs1 Hc1]] := full_comm_connect_sorted Hfull w1.
have [sw2 [Hs2 Hc2]] := full_comm_connect_sorted Hfull w2.
have Hpe1 := trace_perm Hc1.
have Hpe2 := trace_perm Hc2.
have Hpe12 : perm_eq (val sw1) (val sw2).
  apply: (perm_trans (y:=val w1)); first by rewrite perm_sym.
  exact: (perm_trans (y:=val w2) Hpe Hpe2).
have Hs1' : sorted oleq (val sw1) by rewrite -sorted_map.
have Hs2' : sorted oleq (val sw2) by rewrite -sorted_map.
have Heqsw : sw1 = sw2.
  apply: val_inj; exact: (sorted_eq oleq_trans oleq_anti Hs1' Hs2' Hpe12).
rewrite Heqsw in Hc1.
apply: (connect_trans Hc1).
by rewrite (sym_connect_sym (@adj_swap_sym_sym L)); exact Hc2.
Qed.

(* Independent set lower bound on traces *)

Lemma indep_adj_swap_false (I : {set 'I_Tg}) L (w1 w2 : pgg_word M L) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  (forall k : 'I_L, tnth w1 k \in I) ->
  adj_swap w1 w2 = false.
Proof.
move=> Hindep HI.
case: L w1 w2 HI => [|L'] w1 w2 HI //=.
apply/negbTE/negP.
move/existsP => [k /andP [Hc _]].
set ik : 'I_L'.+1 := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')).
set ik1 : 'I_L'.+1 := @Ordinal L'.+1 (val k).+1 (ltn_ord k).
have Hi : tnth w1 ik \in I := HI ik.
have Hj : tnth w1 ik1 \in I := HI ik1.
case/boolP: (tnth w1 ik == tnth w1 ik1) => Heq.
  by move/eqP in Heq; rewrite Heq comm_irrefl in Hc.
by move: (Hindep _ _ Hi Hj Heq); rewrite Hc.
Qed.

Lemma indep_set_traces_lb (I : {set 'I_Tg}) (L : nat) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  #|I| ^ L <= n_traces L.
Proof.
move=> Hindep.
rewrite /n_traces.
set e := adj_swap_sym (L:=L).
have Hsym := sym_connect_sym (@adj_swap_sym_sym L).
(* I-word: a word where all entries are in I *)
set Iword := fun w : pgg_word M L =>
  [forall k : 'I_L, tnth w k \in I].
(* adj_swap is false from any I-word *)
have Hadj_false : forall (w1 w2 : pgg_word M L),
  Iword w1 -> adj_swap w1 w2 = false.
  move=> w1 w2 H1.
  have H1' : forall k : 'I_L, tnth w1 k \in I.
    by move/forallP: H1.
  exact: indep_adj_swap_false Hindep H1'.
(* adj_swap_sym is false between I-words *)
have Hno : forall w1 w2 : pgg_word M L,
  Iword w1 -> Iword w2 -> e w1 w2 = false.
  move=> w1 w2 H1 H2.
  by rewrite /e /adj_swap_sym !(Hadj_false _ _ H1) !(Hadj_false _ _ H2).
(* No word connects to an I-word via e unless it's equal *)
have Hconn_eq : forall w1 w2 : pgg_word M L,
  Iword w1 -> connect e w1 w2 -> w1 = w2.
  move=> w1 w2 H1 /connectP [p].
  elim: p w1 H1 => [w1 _ _ -> // | w' p IHp w1 H1 /= /andP [Hstep Hpath] Hlast].
  exfalso.
  have : e w1 w' = false.
    rewrite /e /adj_swap_sym (Hadj_false _ _ H1) /=.
    apply/negbTE/negP => Hadj.
    have H2 : Iword w'.
      apply/forallP => k.
      have Hpe := adj_swap_perm Hadj.
      have Hmem : tnth w' k \in val w' := mem_tnth k w'.
      have : tnth w' k \in val w1.
        by rewrite -(perm_mem Hpe).
      by move/tnthP => [j Hj]; rewrite Hj; exact: (forallP H1).
    by rewrite (Hadj_false _ _ H2) in Hadj.
  by rewrite Hstep.
(* Each I-word is its own root *)
have Hconn_I : forall w1 w2 : pgg_word M L,
  Iword w1 -> connect e w1 w2 = (w1 == w2).
  move=> w1 w2 H1.
  apply/idP/idP.
    by move=> Hc; apply/eqP; exact: Hconn_eq.
  by move/eqP => ->; exact: connect0.
have Hroot_self : forall w : pgg_word M L,
  Iword w -> root e w = w.
  move=> w Hw; rewrite /root /=.
  case: pickP => [w' /= Hw' | /= H].
    by rewrite Hconn_I // in Hw'; move/eqP in Hw'.
  by move: (H w); rewrite /= connect0.
(* Inject I-words into roots *)
pose IT := {x : 'I_Tg | x \in I}.
pose valI := (fun x : IT => sval x : 'I_Tg).
set f := fun (t : L.-tuple IT) => map_tuple valI t : pgg_word M L.
have valI_inj : injective valI.
  by move=> x y /val_inj.
have Hf_inj : injective f.
  move=> t1 t2 Heq.
  apply: eq_from_tnth => i.
  have := congr1 (fun w => tnth w i) Heq.
  rewrite /f !tnth_map.
  by move/valI_inj.
have Hf_Iword : forall t, Iword (f t).
  move=> t; apply/forallP => k.
  rewrite /f tnth_map /valI.
  exact: valP (tnth t k).
(* #|I|^L = #|{: L.-tuple IT}| <= #{roots} = n_traces *)
have HcardIT : #|{: IT}| = #|I|.
  rewrite card_sig; apply: eq_card => x.
  by rewrite !inE.
rewrite -HcardIT -card_tuple.
set S := [set f t | t : L.-tuple IT].
have HS_card : #|S| = #|{: L.-tuple IT}|.
  by rewrite card_imset.
rewrite -HS_card.
apply: subset_leq_card.
apply/subsetP => _ /imsetP [t _ ->].
rewrite !inE andbT /roots /=.
by rewrite Hroot_self ?eqxx //; exact: Hf_Iword.
Qed.

Lemma word_eval_perm_eq L (w1 w2 : pgg_word M L) :
  (forall i j : 'I_Tg, i != j -> comm i j) ->
  perm_eq (val w1) (val w2) -> word_eval w1 = word_eval w2.
Proof.
move=> Hfull Hperm.
apply: word_eval_trace.
by apply/(full_comm_trace_iff_perm _ _ Hfull).
Qed.

(* Independent set generators have singleton trace classes:
   no two distinct I-words are trace-equivalent. *)

Lemma indep_set_singleton_traces (I : {set 'I_Tg}) (L : nat)
    (w1 w2 : pgg_word M L) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  (forall k : 'I_L, tnth w1 k \in I) ->
  (forall k : 'I_L, tnth w2 k \in I) ->
  trace_equiv w1 w2 -> w1 = w2.
Proof.
move=> Hindep H1 H2 Hte.
set e := adj_swap_sym (L:=L).
have Hadj_false : forall (wa wb : pgg_word M L),
  (forall k : 'I_L, tnth wa k \in I) -> adj_swap wa wb = false.
  move=> wa wb HI.
  exact: indep_adj_swap_false Hindep HI.
suff Hsuff : forall wa wb : pgg_word M L,
  (forall k : 'I_L, tnth wa k \in I) -> connect e wa wb -> wa = wb.
  by exact: Hsuff.
move=> wa wb HI /connectP [p].
elim: p wa HI => [wa _ _ -> // | w' p IHp wa HI /= /andP [Hstep Hpath] Hlast].
exfalso.
have : e wa w' = false.
  rewrite /e /adj_swap_sym (Hadj_false _ _ HI) /=.
  apply/negbTE/negP => Hadj.
  have HI' : forall k : 'I_L, tnth w' k \in I.
    move=> k.
    have Hpe := adj_swap_perm Hadj.
    have Hmem : tnth w' k \in val w' := mem_tnth k w'.
    have : tnth w' k \in val wa by rewrite -(perm_mem Hpe).
    by move/tnthP => [j Hj]; rewrite Hj; exact: HI.
  by rewrite (Hadj_false _ _ HI') in Hadj.
by rewrite Hstep.
Qed.

(* Charney's theorem (finite analog): independent set generators
   with raag_weval_inj give word_eval injectivity on I-words *)
Lemma indep_set_word_eval_inj (I : {set 'I_Tg}) (L : nat) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  raag_weval_inj L ->
  forall (w1 w2 : pgg_word M L),
    (forall k : 'I_L, tnth w1 k \in I) ->
    (forall k : 'I_L, tnth w2 k \in I) ->
    word_eval w1 = word_eval w2 -> w1 = w2.
Proof.
move=> Hindep Hrl w1 w2 H1 H2 Heval.
apply: (indep_set_singleton_traces Hindep H1 H2).
exact: Hrl.
Qed.

End raag_theory.

(* ========================================================================== *)
(* Derived results for any RAAGType                                           *)
(* ========================================================================== *)

Section raag_derived.
Variable R : RAAGType.
Let Tg := (@pgg_ngens' R).+1.

Lemma raag_weval_inj1 : @weval_inj R 1.
Proof. exact: gen_inj_weval_inj1 (@raag_gen_inj R). Qed.

Lemma raag_search_space_1 : @search_space R 1 = Tg.
Proof. exact: weval_inj_search_space raag_weval_inj1. Qed.
End raag_derived.

(* ========================================================================== *)
(* Part 5: Nat-level reflection                                               *)
(* ========================================================================== *)

Section raag_gen_reflect.

Variable R : RAAGType.
Let Tg := (@pgg_ngens' R).+1.

Variable comm_nat : nat -> nat -> bool.

Hypothesis Hcomm_nat : forall i j : 'I_Tg,
  @raag_comm R i j = comm_nat (val i) (val j).

Definition comm_ord : rel 'I_Tg := fun i j => comm_nat (val i) (val j).

Let M : GeneratedMonodromyReprType := R.

(* ------------------------------------------------------------------ *)
(* Helper: foldl maxn shift lemma                                      *)
(* ------------------------------------------------------------------ *)

Let foldl_maxn_shift (s : seq nat) (a : nat) :
  foldl maxn a s = maxn a (foldl maxn 0 s).
Proof.
elim: s a => [|b s IH] a /=; first by rewrite maxn0.
by rewrite (IH (maxn a b)) (IH (maxn 0 b)) max0n maxnA.
Qed.

(* ------------------------------------------------------------------ *)
(* foata_depth_at as bigop — permutation-invariant                     *)
(* ------------------------------------------------------------------ *)

Let foata_depth_at_bigop (crel : nat -> nat -> bool) prev x :
  foata_depth_at crel prev x =
  \max_(dv <- prev | ~~ crel dv.2 x) dv.1.+1.
Proof.
rewrite /foata_depth_at.
suff Hgen : forall acc,
  foldl (fun a dv => if crel dv.2 x then a else maxn a dv.1.+1) acc prev =
  maxn acc (\max_(dv <- prev | ~~ crel dv.2 x) dv.1.+1).
  by rewrite Hgen max0n.
elim: prev => [|dv prev IH] acc /=; first by rewrite big_nil maxn0.
by rewrite big_cons; case: (crel dv.2 x) => /=; rewrite IH -?maxnA.
Qed.

Let foata_depth_at_perm (crel : nat -> nat -> bool) prev1 prev2 x :
  perm_eq prev1 prev2 ->
  foata_depth_at crel prev1 x = foata_depth_at crel prev2 x.
Proof. by move=> Hp; rewrite !foata_depth_at_bigop; apply: perm_big. Qed.

(* ------------------------------------------------------------------ *)
(* foata_pairs structural lemmas                                       *)
(* ------------------------------------------------------------------ *)

Let foata_pairs_split' (crel : nat -> nat -> bool) prev w1 w2 :
  foata_pairs crel prev (w1 ++ w2) =
  foata_pairs crel (foata_pairs crel prev w1) w2.
Proof. by elim: w1 prev => [|x w1 IH] prev //=. Qed.

Let foata_pairs_vals (crel : nat -> nat -> bool) prev w :
  map snd (foata_pairs crel prev w) = map snd prev ++ w.
Proof.
elim: w prev => [|x w IH] prev /=; first by rewrite cats0.
by rewrite IH map_rcons -cats1 -catA.
Qed.

Let size_foata_pairs' (crel : nat -> nat -> bool) prev w :
  size (foata_pairs crel prev w) = size prev + size w.
Proof.
elim: w prev => [|x w IH] prev /=; first by rewrite addn0.
by rewrite IH size_rcons addSnnS.
Qed.

Let foata_depth_comm_rcons (crel : nat -> nat -> bool) prev d a b :
  crel a b ->
  foata_depth_at crel (rcons prev (d, a)) b =
  foata_depth_at crel prev b.
Proof.
move=> Hab; rewrite !foata_depth_at_bigop -cats1 big_cat /=.
by rewrite big_cons big_nil Hab /= maxn0.
Qed.

Let foata_pairs_prefix (crel : nat -> nat -> bool) prev w :
  take (size prev) (foata_pairs crel prev w) = prev.
Proof.
elim: w prev => [|x w IH] prev //=.
  by rewrite take_size.
have := IH (rcons prev (foata_depth_at crel prev x, x)).
rewrite size_rcons => HIH.
rewrite -(take_takel _ (leqnSn (size prev))) HIH.
by rewrite -cats1 take_size_cat.
Qed.

Let nth_foata_pairs_val (crel : nat -> nat -> bool) prev w k :
  k < size w ->
  (nth (0, 0) (foata_pairs crel prev w) (size prev + k)).2 = nth 0 w k.
Proof.
elim: w prev k => [|x w IH] prev k //=.
case: k => [|k] Hk /=.
  rewrite addn0; set prev' := rcons prev _.
  have Hlt : size prev < size prev' by rewrite /prev' size_rcons.
  rewrite -(nth_take (0,0) Hlt) (foata_pairs_prefix crel prev' w).
  by rewrite /prev' nth_rcons ltnn eqxx.
by rewrite -(IH (rcons prev (foata_depth_at crel prev x, x)) k Hk)
           size_rcons addSnnS.
Qed.

Let nth_foata_pairs_depth (crel : nat -> nat -> bool) prev w k :
  k < size w ->
  (nth (0, 0) (foata_pairs crel prev w) (size prev + k)).1 =
  foata_depth_at crel (foata_pairs crel prev (take k w)) (nth 0 w k).
Proof.
elim: w prev k => [|x w IH] prev k //=.
case: k => [|k] Hk /=.
  rewrite addn0 /=; set prev' := rcons prev _.
  have Hlt : size prev < size prev' by rewrite /prev' size_rcons.
  rewrite -(nth_take (0,0) Hlt) (foata_pairs_prefix crel prev' w).
  by rewrite /prev' nth_rcons ltnn eqxx.
by rewrite -(IH (rcons prev (foata_depth_at crel prev x, x)) k Hk)
           size_rcons addSnnS.
Qed.

(* foata_pairs with permuted prefix gives permuted output *)
Let foata_pairs_perm_prefix (crel : nat -> nat -> bool) p1 p2 w :
  perm_eq p1 p2 ->
  perm_eq (foata_pairs crel p1 w) (foata_pairs crel p2 w).
Proof.
elim: w p1 p2 => [|x w IH] p1 p2 Hp //=.
apply: IH; rewrite (foata_depth_at_perm _ _ Hp) -!cats1; exact: perm_cat Hp (perm_refl _).
Qed.

(* Swapping adjacent commuting elements preserves foata_pairs multiset *)
Let foata_pairs_swap_adj (crel : nat -> nat -> bool) prev a b w :
  crel a b -> crel b a ->
  perm_eq (foata_pairs crel prev (a :: b :: w))
          (foata_pairs crel prev (b :: a :: w)).
Proof.
move=> Hab Hba /=.
rewrite (foata_depth_comm_rcons _ _ Hab) (foata_depth_comm_rcons _ _ Hba).
apply: foata_pairs_perm_prefix.
by rewrite -!cats1 -!catA perm_cat2l perm_catC.
Qed.

(* ------------------------------------------------------------------ *)
(* dv_leq properties                                                   *)
(* ------------------------------------------------------------------ *)

Let dv_leq_trans : transitive dv_leq.
Proof.
move=> [d2 v2] [d1 v1] [d3 v3]; rewrite /dv_leq /=.
move/orP => [H1|/andP [/eqP H1 H2]]; move/orP => [H3|/andP [/eqP H3 H4]].
- by apply/orP; left; exact: ltn_trans H1 H3.
- by apply/orP; left; rewrite -H3.
- by apply/orP; left; rewrite H1.
- by apply/orP; right; apply/andP; split;
    [rewrite H1 H3|exact: leq_trans H2 H4].
Qed.

Let dv_leq_anti : antisymmetric dv_leq.
Proof.
move=> [d1 v1] [d2 v2]; rewrite /dv_leq /=.
move/andP => [/orP [H1|/andP [/eqP H1 H2]] /orP [H3|/andP [/eqP H3 H4]]].
- by have := ltn_trans H1 H3; rewrite ltnn.
- by exfalso; rewrite H3 ltnn in H1.
- by exfalso; rewrite H1 ltnn in H3.
- by congr pair; [rewrite H1 | apply/anti_leq/andP].
Qed.

Let dv_leq_total : total dv_leq.
Proof.
move=> [d1 v1] [d2 v2]; rewrite /dv_leq /=.
by case: ltngtP => //= E; rewrite ?E ?eqxx /= ?leq_total ?orbT.
Qed.

Let sort_perm_eq_dv (s1 s2 : seq (nat * nat)) :
  perm_eq s1 s2 -> sort dv_leq s1 = sort dv_leq s2.
Proof.
move=> Hp.
have Hs1 := sort_sorted dv_leq_total s1.
have Hs2 := sort_sorted dv_leq_total s2.
have Hp' : perm_eq (sort dv_leq s1) (sort dv_leq s2).
  by rewrite (perm_sort _ s1) perm_sym (perm_sort _ s2) perm_sym.
exact: (sorted_eq dv_leq_trans dv_leq_anti Hs1 Hs2 Hp').
Qed.

(* foata_nf invariant under adjacent commuting swap *)
Let foata_nf_swap_adj (crel : nat -> nat -> bool) a b (w1 w2 : seq nat) :
  crel a b -> crel b a ->
  foata_nf crel (w1 ++ a :: b :: w2) = foata_nf crel (w1 ++ b :: a :: w2).
Proof.
move=> Hab Hba; rewrite /foata_nf !foata_pairs_split'.
congr (map snd); apply: sort_perm_eq_dv.
exact: foata_pairs_swap_adj.
Qed.

(* ------------------------------------------------------------------ *)
(* Key depth property: non-commuting predecessor forces higher depth   *)
(* ------------------------------------------------------------------ *)

Let foata_depth_noncomm_lb (crel : nat -> nat -> bool) prev d v x :
  ~~ crel v x -> (d, v) \in prev ->
  d.+1 <= foata_depth_at crel prev x.
Proof.
move=> Hnc Hin; rewrite foata_depth_at_bigop.
exact: (leq_bigmax_seq (d, v) Hin Hnc).
Qed.

(* Adjacent out-of-order pair in foata_pairs implies commutativity *)
Let foata_descent_comm' (crel : nat -> nat -> bool) prev w k :
  k.+1 < size w ->
  ~~ dv_leq (nth (0, 0) (foata_pairs crel prev w) (size prev + k))
             (nth (0, 0) (foata_pairs crel prev w) (size prev + k.+1)) ->
  crel (nth 0 w k) (nth 0 w k.+1).
Proof.
move=> Hk; rewrite /dv_leq negb_or -!ltnNge => /andP [Hlt _].
apply/negPn/negP => Hnc.
have Hk' := ltn_trans (ltnSn k) Hk.
have Hdep : (nth (0, 0) (foata_pairs crel prev w) (size prev + k.+1)).1 >=
  ((nth (0, 0) (foata_pairs crel prev w) (size prev + k)).1).+1.
  rewrite (nth_foata_pairs_depth crel prev Hk).
  rewrite (nth_foata_pairs_depth crel prev Hk').
  rewrite (take_nth 0 Hk') -cats1 (foata_pairs_split' crel) /=.
  apply: foata_depth_noncomm_lb; first exact: Hnc.
  by rewrite mem_rcons inE eqxx.
by have := leq_ltn_trans Hdep Hlt; rewrite ltnn.
Qed.

(* When foata_pairs is sorted, foata_nf = identity *)
Let foata_nf_sorted (crel : nat -> nat -> bool) w :
  sorted dv_leq (foata_pairs crel [::] w) -> foata_nf crel w = w.
Proof.
move=> Hs; rewrite /foata_nf.
set ps := foata_pairs crel [::] w.
have Hpe : perm_eq ps (sort dv_leq ps) by rewrite perm_sym perm_sort.
have Heq := sorted_eq dv_leq_trans dv_leq_anti Hs (sort_sorted dv_leq_total ps) Hpe.
rewrite -Heq; exact: foata_pairs_vals.
Qed.

(* Unsorted seq has adjacent descent *)
Let not_sorted_descent' (s : seq (nat * nat)) :
  1 < size s -> ~~ sorted dv_leq s ->
  exists k : nat, k.+1 < size s /\
    ~~ dv_leq (nth (0, 0) s k) (nth (0, 0) s k.+1).
Proof.
elim: s => [|a [|b s'] IH] //= _.
rewrite negb_and => /orP [H|H].
  by exists 0; rewrite H.
have Hs : 1 < size (b :: s').
  by case: (s') H => //= c s'' _; rewrite ltnS.
have [k [Hk Hd]] := IH Hs H.
by exists k.+1.
Qed.

(* ------------------------------------------------------------------ *)
(* Word split and swap at nat level                                    *)
(* ------------------------------------------------------------------ *)

Let w_split_nat (k : nat) (w : seq nat) :
  k.+1 < size w ->
  w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
Proof.
move=> Hk.
have Hk' : k < size w := ltn_trans (ltnSn k) Hk.
rewrite -{1}[w](cat_take_drop k).
rewrite (drop_nth 0 Hk').
by rewrite (drop_nth 0 Hk).
Qed.

(* ------------------------------------------------------------------ *)
(* Foata inversion count and decrease under swap                       *)
(* ------------------------------------------------------------------ *)

Let foata_inv (crel : nat -> nat -> bool) (w : seq nat) : nat :=
  let ps := foata_pairs crel [::] w in
  \sum_(i < size w) \sum_(j < size w | i < j)
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).

Let foata_inv_zero (crel : nat -> nat -> bool) w :
  foata_inv crel w = 0 ->
  sorted dv_leq (foata_pairs crel [::] w).
Proof.
rewrite /foata_inv => Hzero.
apply/(sortedP (0,0)) => i; rewrite size_foata_pairs' /= add0n => Hi.
apply/negPn/negP => Hneg.
suff : 0 < \sum_(i0 < size w) \sum_(j0 < size w | i0 < j0)
  (~~ dv_leq (nth (0, 0) (foata_pairs crel [::] w) i0)
             (nth (0, 0) (foata_pairs crel [::] w) j0)) by rewrite Hzero.
have Hi' : i < size w := ltn_trans (ltnSn i) Hi.
rewrite (bigD1 (Ordinal Hi')) //=.
apply: leq_trans; last exact: leq_addr.
rewrite (bigD1 (Ordinal Hi)) //=.
apply: leq_trans; last exact: leq_addr.
by rewrite Hneg.
Qed.

(* foata_pairs structure after swap:
   nth of foata_pairs for swap_nat k w equals nth of foata_pairs for w
   with positions k and k+1 exchanged *)
Let foata_pairs_swap_nth (crel : nat -> nat -> bool) w k :
  (forall a b, crel a b -> crel b a) ->
  k.+1 < size w ->
  crel (nth 0 w k) (nth 0 w k.+1) ->
  let sw := take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w in
  let ps := foata_pairs crel [::] w in
  let ps' := foata_pairs crel [::] sw in
  (forall i, i < size w ->
    nth (0, 0) ps' i =
    if i == k then nth (0, 0) ps k.+1
    else if i == k.+1 then nth (0, 0) ps k
    else nth (0, 0) ps i) /\
  size sw = size w.
Proof.
move=> Hcsym Hk Hc /=.
set sw := take k w ++ _ :: _ :: _.
set ps := foata_pairs crel [::] w.
set ps' := foata_pairs crel [::] sw.
have Hsz : size sw = size w.
  rewrite /sw size_cat /= size_drop (size_takel (ltnW (ltn_trans (ltnSn k) Hk))).
  by rewrite -addn2 addnCA addn2 subnK.
split => // i Hi.
(* Decompose w and sw through foata_pairs_split' *)
have Hw : w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
  exact: w_split_nat.
(* ps = foata_pairs [::] w = foata_pairs P (a :: b :: suffix)
   ps' = foata_pairs [::] sw = foata_pairs P (b :: a :: suffix)
   where P = foata_pairs [::] (take k w), a = nth 0 w k, b = nth 0 w k.+1 *)
set P := foata_pairs crel [::] (take k w).
set a := nth 0 w k.
set b := nth 0 w k.+1.
set suffix := drop k.+2 w.
have Hps : ps = foata_pairs crel P (a :: b :: suffix).
  by rewrite /ps Hw foata_pairs_split'.
have Hps' : ps' = foata_pairs crel P (b :: a :: suffix).
  by rewrite /ps' /sw foata_pairs_split'.
(* The depth of a from prefix P *)
set da := foata_depth_at crel P a.
set db := foata_depth_at crel P b.
(* By commutativity, depth is the same whether we process a or b first *)
have Hdb' : foata_depth_at crel (rcons P (da, a)) b = db.
  by rewrite foata_depth_comm_rcons.
have Hda' : foata_depth_at crel (rcons P (db, b)) a = da.
  by rewrite foata_depth_comm_rcons // Hcsym.
(* After processing [a; b] vs [b; a], the prefixes are permutations *)
set P_ab := rcons (rcons P (da, a)) (db, b).
set P_ba := rcons (rcons P (db, b)) (da, a).
have Hpab : perm_eq P_ab P_ba.
  rewrite /P_ab /P_ba; apply/seq.permP => p.
  rewrite -cats1 -[rcons P (da, a)]cats1 -cats1 -[rcons P (db, b)]cats1.
  by rewrite count_cat count_cat count_cat count_cat /= addn0 addn0 addnAC.
(* For i < k: nth ps i and nth ps' i are the same (both in P) *)
have HszP : size P = k.
  by rewrite size_foata_pairs' /= add0n size_take (ltn_trans (ltnSn k) Hk).
(* The foata_pairs for suffix use the same prefix multiset,
   so they produce the same depths at each position *)
(* Actually, the trickier part: for suffix positions j,
   foata_pairs P_ab suffix and foata_pairs P_ba suffix
   produce the SAME pair at each position (not just permuted),
   because foata_depth_at is perm-invariant and we process
   suffix elements left-to-right the same way. *)
have Hsuffix_eq : forall j, j < size suffix ->
  nth (0, 0) (foata_pairs crel P_ab suffix) (size P_ab + j) =
  nth (0, 0) (foata_pairs crel P_ba suffix) (size P_ba + j).
  (* By induction on suffix, using foata_depth_at_perm *)
  elim: suffix P_ab P_ba Hpab {Hps Hps'} => [|x suf IH] Pab Pba Hpab j Hj //.
  case: j Hj => [|j] Hj /=.
    rewrite addn0 addn0.
    set dab := foata_depth_at crel Pab x.
    set dba := foata_depth_at crel Pba x.
    set Pab' := rcons Pab (dab, x).
    set Pba' := rcons Pba (dba, x).
    have Hlt_ab : size Pab < size Pab' by rewrite /Pab' size_rcons.
    have Hlt_ba : size Pba < size Pba' by rewrite /Pba' size_rcons.
    rewrite -(nth_take (0,0) Hlt_ab) (foata_pairs_prefix crel Pab' suf).
    rewrite -(nth_take (0,0) Hlt_ba) (foata_pairs_prefix crel Pba' suf).
    rewrite /Pab' /Pba' nth_rcons nth_rcons ltnn ltnn eqxx eqxx.
    by rewrite /dab /dba (foata_depth_at_perm _ _ Hpab).
  have Hpab' : perm_eq (rcons Pab (foata_depth_at crel Pab x, x))
                       (rcons Pba (foata_depth_at crel Pba x, x)).
    rewrite (foata_depth_at_perm _ _ Hpab) -cats1 -(cats1 Pba).
    exact: perm_cat Hpab _.
  have -> : size Pab + j.+1 =
    size (rcons Pab (foata_depth_at crel Pab x, x)) + j
    by rewrite size_rcons addSnnS.
  have -> : size Pba + j.+1 =
    size (rcons Pba (foata_depth_at crel Pba x, x)) + j
    by rewrite size_rcons addSnnS.
  exact: IH.
(* Now assemble: for i < k, i = k, i = k+1, i > k+1 *)
case: (ltnP i k) => Hik.
  (* i < k: both in prefix P *)
  have -> : (i == k) = false by apply/negbTE; rewrite ltn_eqF.
  have -> : (i == k.+1) = false by apply/negbTE; rewrite ltn_eqF // ltnS ltnW.
  have Hi_lt_P : i < size P by rewrite HszP.
  transitivity (nth (0, 0) P i); last first.
    have -> : nth (0,0) ps i = nth (0,0) (take (size P) ps) i by rewrite nth_take.
    by rewrite Hps (foata_pairs_prefix crel P (a :: b :: suffix)).
  have -> : nth (0,0) ps' i = nth (0,0) (take (size P) ps') i by rewrite nth_take.
  by rewrite Hps' (foata_pairs_prefix crel P (b :: a :: suffix)).
(* i >= k *)
case Heqk : (i == k).
  (* i = k *)
  rewrite (eqP Heqk).
  (* ps' at k = (db, b) = ps at k.+1 *)
  have HszPba : k < size P_ba by rewrite /P_ba !size_rcons HszP.
  have HszPab : k.+1 < size P_ab by rewrite /P_ab !size_rcons HszP.
  rewrite Hps' /= Hda'.
  rewrite -(nth_take (0,0) HszPba) (foata_pairs_prefix crel P_ba suffix).
  rewrite /P_ba !nth_rcons !size_rcons HszP ltnSn ltnn eqxx /=.
  rewrite Hps /= Hdb'.
  rewrite -(nth_take (0,0) HszPab) (foata_pairs_prefix crel P_ab suffix).
  by rewrite /P_ab !nth_rcons !size_rcons HszP ltnn eqxx.
have Hik' : k < i by rewrite ltn_neqAle eq_sym Heqk Hik.
case Heqk1 : (i == k.+1).
  (* i = k+1: ps' at k+1 = (da, a) = ps at k *)
  rewrite (eqP Heqk1).
  have HszPba1 : k.+1 < size P_ba by rewrite /P_ba !size_rcons HszP.
  have HszPabk : k < size P_ab by rewrite /P_ab !size_rcons HszP.
  rewrite Hps' /= Hda'.
  rewrite -(nth_take (0,0) HszPba1) (foata_pairs_prefix crel P_ba suffix).
  rewrite /P_ba !nth_rcons !size_rcons HszP ltnn eqxx /=.
  rewrite Hps /= Hdb'.
  rewrite -(nth_take (0,0) HszPabk) (foata_pairs_prefix crel P_ab suffix).
  by rewrite /P_ab !nth_rcons !size_rcons HszP ltnSn ltnn eqxx.
(* i > k+1: in the suffix *)
have Hik1 : k.+1 < i by rewrite ltn_neqAle eq_sym Heqk1 Hik'.
have Hsuf_i : i - k.+2 < size suffix.
  by rewrite size_drop ltn_sub2rE.
(* i > k+1: positions in the suffix are unchanged *)
have HszPab2 : size P_ab = k.+2 by rewrite /P_ab !size_rcons HszP.
have HszPba2 : size P_ba = k.+2 by rewrite /P_ba !size_rcons HszP.
have Hi_eq : i = size P_ab + (i - k.+2).
  by rewrite HszPab2 addnC subnK.
have Hi_ba : i = size P_ba + (i - k.+2).
  by rewrite HszPba2 addnC subnK.
have Hps_ab : ps = foata_pairs crel P_ab suffix.
  by rewrite Hps /= Hdb'.
have Hps'_ba : ps' = foata_pairs crel P_ba suffix.
  by rewrite Hps' /= Hda'.
have Hsuf_eq_i := Hsuffix_eq _ Hsuf_i.
have Hki : k.+2 <= i by [].
have Hki2 : k.+2 + (i - k.+2) = i by rewrite addnC subnK.
rewrite HszPab2 HszPba2 Hki2 in Hsuf_eq_i.
by rewrite Hps'_ba Hps_ab.
Qed.

Let foata_inv_swap_lt (crel : nat -> nat -> bool) w k :
  (forall a b, crel a b -> crel b a) ->
  k.+1 < size w ->
  crel (nth 0 w k) (nth 0 w k.+1) ->
  ~~ dv_leq (nth (0, 0) (foata_pairs crel [::] w) k)
             (nth (0, 0) (foata_pairs crel [::] w) k.+1) ->
  foata_inv crel (take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w) <
  foata_inv crel w.
Proof.
move=> Hcsym Hk Hc Hdesc.
set sw := take k w ++ _ :: _ :: _.
have [Hnth Hsz] := foata_pairs_swap_nth Hcsym Hk Hc.
set ps := foata_pairs crel [::] w.
set ps' := foata_pairs crel [::] sw.
rewrite /foata_inv Hsz.
(* The inverted pair at (k, k+1) is fixed.
   All other pairs have the same inversion status.
   So the sum decreases by exactly 1. *)
(* Define f(i,j) = ~~ dv_leq (ps i) (ps j) for the original *)
(* Define f'(i,j) = ~~ dv_leq (ps' i) (ps' j) for the swap *)
(* We have: ps' i = ps (tp i) where tp = transposition of k, k+1 *)
(* So f'(i,j) = f(tp i, tp j) *)
(* The sum of f'(i,j) over i < j = sum of f(tp i, tp j) over i < j *)
(* = sum of f(i', j') over (tp i', tp j') with i' < j' ... no *)
(* Actually: reindex i -> tp i, j -> tp j. Since tp is a bijection on 'I_n,
   and for i < j with (i,j) != (k,k+1), we have tp i < tp j or tp j < tp i. *)
(* The key: for all (i,j) with i < j, f'(i,j) = f(tp i, tp j).
   Since tp just swaps k <-> k+1, we have:
   - If neither i nor j is k or k+1: tp i = i, tp j = j, so f'(i,j) = f(i,j)
   - If i = k, j = k+1: f'(k,k+1) = f(k+1,k) = ~~ dv_leq (ps k+1) (ps k)
     But dv_leq is total, so ~~ dv_leq (ps k+1) (ps k) = ~~ (dv_leq (ps k+1) (ps k))
     And since ~~ dv_leq (ps k) (ps k+1) (= Hdesc), by totality dv_leq (ps k+1) (ps k),
     so f'(k,k+1) = 0. While f(k,k+1) = 1 (= Hdesc). So we save 1.
   - If i = k, j != k+1: f'(k,j) = f(k+1,j). And for j > k+1, this is the same pair.
   - Etc. The point is that the sum is preserved except at (k,k+1) which decreases by 1.
*)
(* To formalize: split the double sum, show each part matches except (k,k+1) *)
(* This is mechanical but long. Let me do it directly. *)
have Hk' : k < size w := ltn_trans (ltnSn k) Hk.
have Hk1 : k.+1 < size w := Hk.
(* Show: \sum_i \sum_{j > i} f'(i,j) + 1 <= \sum_i \sum_{j > i} f(i,j) *)
(* Equivalently: \sum_i \sum_{j > i} f'(i,j) < \sum_i \sum_{j > i} f(i,j) *)
(* Strategy: show f'(i,j) <= f(tp i, tp j) for all i<j,
   with strict inequality at (k,k+1) *)
(* Actually let me use a different approach: rewrite f' in terms of f *)
suff Hlt_sum : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps' i) (nth (0, 0) ps' j)) <
  \sum_(i < size w) \sum_(j < size w | i < j)
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).
  exact: Hlt_sum.
(* Rewrite ps' using Hnth *)
have Hnth_eq : forall i : 'I_(size w),
  nth (0, 0) ps' i =
  nth (0, 0) ps (if val i == k then k.+1 else if val i == k.+1 then k else val i).
  move=> [i Hi] /=; rewrite Hnth //.
  case: (i == k) => //; case: (i == k.+1) => //.
(* The double sum with ps' = double sum with ps composed with transposition *)
(* Let tp : nat -> nat = fun i => if i == k then k.+1 else if i == k.+1 then k else i *)
set tp := fun i : nat => if i == k then k.+1 else if i == k.+1 then k else i.
have Htp_inv : forall i, tp (tp i) = i.
  move=> i; rewrite /tp.
  case Hi : (i == k).
    by rewrite (eqP Hi) gtn_eqF // eqxx.
  case Hi1 : (i == k.+1).
    by rewrite (eqP Hi1) eqxx.
  by rewrite Hi Hi1.
have Htp_inj : injective tp.
  by move=> i j Hij; rewrite -(Htp_inv i) -(Htp_inv j) Hij.
(* Step A: LHS = sum with f(tp i, tp j) *)
have Heq_tp : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps' i) (nth (0, 0) ps' j)) =
  \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps (tp i)) (nth (0, 0) ps (tp j))).
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite !Hnth_eq.
rewrite Heq_tp.
have Hfix : dv_leq (nth (0, 0) ps k.+1) (nth (0, 0) ps k).
  by move: (dv_leq_total (nth (0, 0) ps k) (nth (0, 0) ps k.+1));
     rewrite (negbTE Hdesc).
(* Build ordinal-level transposition *)
set ik : 'I_(size w) := Ordinal Hk'.
set ik1 : 'I_(size w) := Ordinal Hk.
have Hik_ne : ik != ik1.
  by apply/eqP => /(congr1 val) /= /n_Sn.
have Htp_bnd : forall i, i < size w -> tp i < size w.
  move=> i Hi; rewrite /tp.
  case: (i == k) => //; case: (i == k.+1) => //.
set tp_ord := fun i : 'I_(size w) => Ordinal (Htp_bnd _ (ltn_ord i)) : 'I_(size w).
have Htp_ord_val : forall i : 'I_(size w), val (tp_ord i) = tp (val i).
  by move=> [i Hi].
have Htp_ord_inv : forall i, tp_ord (tp_ord i) = i.
  move=> i; apply: ord_inj; rewrite !Htp_ord_val; exact: Htp_inv.
have Htp_ord_inj : injective tp_ord.
  by move=> i j Hij; rewrite -(Htp_ord_inv i) -(Htp_ord_inv j) Hij.
(* Rewrite LHS using reindex *)
(* First, show tp_ord ik = ik1 and tp_ord ik1 = ik *)
have Htp_ik : tp_ord ik = ik1.
  by apply: ord_inj; rewrite Htp_ord_val /tp /= eqxx.
have Htp_ik1 : tp_ord ik1 = ik.
  by apply: ord_inj; rewrite Htp_ord_val /tp /= gtn_eqF // eqxx.
have Hval_ik : forall j : 'I_(size w), val j = k -> j = ik.
  by move=> j' /= Hj'; apply: ord_inj.
have Hval_ik1 : forall j : 'I_(size w), val j = k.+1 -> j = ik1.
  by move=> j' /= Hj'; apply: ord_inj.
(* Step B: Reindex to get reindexed_sum *)
have Hreindex : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps (tp i)) (nth (0, 0) ps (tp j))) =
  \sum_(i < size w) \sum_(j < size w | tp (val i) < tp (val j))
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).
  have Htp_tp_ord : forall i : 'I_(size w),
    tp (val (tp_ord i)) = val i.
    by move=> i0; rewrite Htp_ord_val Htp_inv.
  rewrite (reindex_inj Htp_ord_inj).
  apply: eq_bigr => i _.
  rewrite (reindex_inj Htp_ord_inj).
  apply: eq_bigr => j _.
  congr (~~ dv_leq (nth _ ps _) (nth _ ps _)); exact: Htp_tp_ord.
rewrite Hreindex.
(* Step C: Show reindexed_sum < orig_sum *)
(* Strategy: big_mkcond + ltn_sum (pointwise <= with strict < at (ik,ik1)).
   The only pair where tp reverses ordering is (ik1, ik),
   but f(ik1, ik) = ~~ dv_leq ps[k+1] ps[k] = 0 (by Hfix), so the term is 0. *)
(* Helper: ltn_sum - strict inequality from pointwise *)
have ltn_sum_aux : forall (I : finType) (f0 g0 : I -> nat) (i0 : I),
    (forall i, f0 i <= g0 i) -> f0 i0 < g0 i0 ->
    \sum_i f0 i < \sum_i g0 i.
  move=> I f0 g0 i0 Hle Hlt.
  rewrite (bigD1 i0) // [X in _ < X](bigD1 i0) //.
  have Hle_rest : \sum_(i | i != i0) f0 i <= \sum_(i | i != i0) g0 i.
    by apply: leq_sum => i _; exact: Hle.
  apply: (@leq_ltn_trans (f0 i0 + \sum_(i | i != i0) g0 i)).
    by rewrite leq_add2l.
  by rewrite ltn_add2r.
(* Helper: tp computation lemmas *)
have tpk : tp k = k.+1 by rewrite /tp eqxx.
have tpk1 : tp k.+1 = k by rewrite /tp (gtn_eqF (ltnSn k)) eqxx.
have tp_oth : forall m, m != k -> m != k.+1 -> tp m = m.
  by move=> m /negbTE Hm /negbTE Hm1; rewrite /tp Hm Hm1.
(* Helper: the only pair where tp reverses ordering is (k+1, k) *)
have tp_swap_only : forall i j : nat,
    tp i < tp j -> ~~ (i < j) -> i = k.+1 /\ j = k.
  move=> i0 j0 Htp0 Horig0.
  have [Hik0|Hik0] := boolP (i0 == k); have [Hjk0|Hjk0] := boolP (j0 == k).
  - by move: Htp0; rewrite (eqP Hik0) (eqP Hjk0) tpk ltnn.
  - have [Hjk1|Hjk1] := boolP (j0 == k.+1).
    + by move: Htp0; rewrite (eqP Hik0) (eqP Hjk1) tpk tpk1 ltnNge leqnSn.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hik0).
      move: Htp0; rewrite (eqP Hik0) tpk (@tp_oth j0 Hjk0 Hjk1) => Hlt0.
      exact: ltn_trans (ltnSn k) Hlt0.
  - have [Hik10|Hik10] := boolP (i0 == k.+1).
    + by rewrite (eqP Hik10) (eqP Hjk0).
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hjk0).
      move: Htp0; rewrite (eqP Hjk0) tpk (@tp_oth i0 Hik0 Hik10) => Hlt0.
      by rewrite ltn_neqAle Hik0 -ltnS.
  - have [Hik10|Hik10] := boolP (i0 == k.+1); have [Hjk1|Hjk1] := boolP (j0 == k.+1).
    + by move: Htp0; rewrite (eqP Hik10) (eqP Hjk1) tpk1 ltnn.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hik10).
      move: Htp0; rewrite (eqP Hik10) tpk1 (@tp_oth j0 Hjk0 Hjk1) => Hlt0.
      rewrite ltn_neqAle eq_sym Hjk1 /=.
      exact: Hlt0.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hjk1).
      move: Htp0; rewrite (eqP Hjk1) tpk1 (@tp_oth i0 Hik0 Hik10) => Hlt0.
      exact: ltn_trans Hlt0 (ltnSn k).
    + exfalso; move/negP: Horig0; apply.
      by move: Htp0; rewrite (@tp_oth i0 Hik0 Hik10) (@tp_oth j0 Hjk0 Hjk1).
(* Pointwise: [tp i < tp j] * f(i,j) <= [i < j] * f(i,j) *)
have Hpw : forall i j : 'I_(size w),
  (if tp (val i) < tp (val j)
   then ~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j) : nat else 0) <=
  (if val i < val j
   then ~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j) : nat else 0).
  move=> i0 j0.
  case Horig0 : (val i0 < val j0) => /=.
    by case : (tp (val i0) < tp (val j0)).
  have [Htp0|Htp0] := boolP (tp (val i0) < tp (val j0)) => //.
  have [Hi0 Hj0] := @tp_swap_only (val i0) (val j0) Htp0 (negbT Horig0).
  have -> : i0 = ik1 by apply: ord_inj.
  have -> : j0 = ik by apply: ord_inj.
  by rewrite /= Hfix.
(* Strict at (ik, ik1) *)
have Hstrict : (if tp (val ik) < tp (val ik1)
    then ~~ dv_leq (nth (0, 0) ps ik) (nth (0, 0) ps ik1) : nat else 0) <
  (if val ik < val ik1
    then ~~ dv_leq (nth (0, 0) ps ik) (nth (0, 0) ps ik1) : nat else 0).
  rewrite /= tpk tpk1 ltnSn (negbTE Hdesc) /=.
  by have -> : k.+1 < k = false by rewrite ltnNge leqnSn.
(* Final: big_mkcond + ltn_sum twice *)
rewrite [X in X < _]big_mkcond [X in _ < X]big_mkcond.
apply: (@ltn_sum_aux _ _ _ ik).
  move=> i0.
  rewrite [X in X <= _]big_mkcond [X in _ <= X]big_mkcond.
  exact: leq_sum (fun j0 _ => Hpw i0 j0).
rewrite [X in X < _]big_mkcond [X in _ < X]big_mkcond.
apply: (@ltn_sum_aux _ _ _ ik1).
  move=> j0.
  exact: Hpw ik j0.
exact: Hstrict.
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness: foata_nf(w) reachable via adjacent commuting swaps      *)
(* ------------------------------------------------------------------ *)

(* We prove: for any word w (with entries < some bound),
   w is trace-equivalent to foata_nf(w).
   Here trace-equiv at nat level means obtainable by adjacent commuting swaps. *)

Let foata_nf_sound (crel : nat -> nat -> bool) w :
  (forall a b, crel a b -> crel b a) ->
  exists ws : seq (seq nat),
    last w ws = foata_nf crel w /\
    forall i, i < size ws ->
      let w0 := nth [::] (w :: ws) i in
      let w1 := nth [::] (w :: ws) i.+1 in
      exists k, k.+1 < size w0 /\
        crel (nth 0 w0 k) (nth 0 w0 k.+1) /\
        crel (nth 0 w0 k.+1) (nth 0 w0 k) /\
        w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0.
Proof.
move=> Hcsym.
move: w.
apply: (well_founded_induction_type
  (Wf_nat.well_founded_ltof _ (foata_inv crel))).
move=> w IH.
case Hs : (sorted dv_leq (foata_pairs crel [::] w)).
  exists [::]; split; first by rewrite /= foata_nf_sorted.
  by move=> i.
(* Not sorted: find adjacent descent *)
have Hsz : 1 < size w.
  case Hw : (size w) => [|[|n]] //.
  1,2: exfalso; move/negP: Hs; apply;
       by case: w Hw IH => [|a [|b w']] //=.
have Hszfp : 1 < size (foata_pairs crel [::] w)
  by rewrite size_foata_pairs' /= add0n.
have [k0 [Hk0 Hk0d]] := not_sorted_descent' Hszfp (negbT Hs).
rewrite size_foata_pairs' /= add0n in Hk0.
have Hcomm : crel (nth 0 w k0) (nth 0 w k0.+1).
  exact: foata_descent_comm' Hk0 Hk0d.
set sw := take k0 w ++ nth 0 w k0.+1 :: nth 0 w k0 :: drop k0.+2 w.
have Hnf : foata_nf crel sw = foata_nf crel w.
  rewrite /sw.
  transitivity (foata_nf crel (take k0 w ++ nth 0 w k0 :: nth 0 w k0.+1 :: drop k0.+2 w)).
    apply foata_nf_swap_adj; [exact: Hcsym | exact: Hcomm].
  congr (foata_nf crel). symmetry; exact: w_split_nat.
have Hlt : @Wf_nat.ltof _ (foata_inv crel) sw w.
  rewrite /Wf_nat.ltof /sw; apply/ltP.
  exact: foata_inv_swap_lt Hcsym Hk0 Hcomm Hk0d.
have [ws [Hlast Hsteps]] := IH sw Hlt.
exists (sw :: ws); split.
  by rewrite /= Hlast Hnf.
case => [|i] Hi /=.
  exists k0; repeat split => //; exact: Hcsym.
exact: Hsteps.
Qed.

(* ------------------------------------------------------------------ *)
(* Lift nat-level trace equivalence to ordinal level                   *)
(* ------------------------------------------------------------------ *)

(* comm_nat symmetry from raag_comm_sym *)
Let comm_nat_sym : forall a b : nat,
  a < Tg -> b < Tg -> comm_nat a b -> comm_nat b a.
Proof.
move=> a b Ha Hb Hab.
rewrite -(@Hcomm_nat (Ordinal Hb) (Ordinal Ha)).
by rewrite (@raag_comm_sym R) Hcomm_nat.
Qed.

(* Bridge: nat-level swap chain -> ordinal-level trace_equiv *)
(* Given a chain of nat-level adjacent commuting swaps where all
   entries are ordinal values (< Tg), produce ordinal-level trace_equiv *)

Let nat_swap_chain_to_trace_equiv L (ws : seq (seq nat)) (w0 : @pgg_word M L) :
  (forall i, i <= size ws ->
    let wi := nth (map val (tval w0)) (map val (tval w0) :: ws) i in
    size wi = L /\ all (fun j => j < Tg) wi) ->
  (forall i, i < size ws ->
    let wi := nth [::] (map val (tval w0) :: ws) i in
    let wi1 := nth [::] (map val (tval w0) :: ws) i.+1 in
    exists k, k.+1 < size wi /\
      comm_nat (nth 0 wi k) (nth 0 wi k.+1) /\
      comm_nat (nth 0 wi k.+1) (nth 0 wi k) /\
      wi1 = take k wi ++ nth 0 wi k.+1 :: nth 0 wi k :: drop k.+2 wi) ->
  forall wf : @pgg_word M L,
    map val (tval wf) = last (map val (tval w0)) ws ->
    @trace_equiv R L w0 wf.
Proof.
elim: ws w0 => [|w1 ws IH] w0 Hbd Hstep wf Hlast /=.
  (* No steps *)
  rewrite /= in Hlast.
  suff -> : w0 = wf by exact: connect0.
  by apply: val_inj; apply: (inj_map val_inj); rewrite Hlast.
(* One step from w0 to w1, then w1 to wf *)
have [k [Hk [Hc1 [Hc2 Hw1]]]] := Hstep 0 (ltn0Sn _).
simpl in Hw1.
(* Build the ordinal word for w1 *)
have [Hsz1 Hbd1] := Hbd 1 (ltn0Sn _).
simpl in Hsz1, Hbd1.
(* Step 1: Build the ordinal word w1_ord from w1 *)
pose mk_ord := fun x =>
  match Sumbool.sumbool_of_bool (x < Tg) with
  | left pf => @Ordinal Tg x pf
  | right _ => @Ordinal Tg 0 (ltn0Sn _)
  end.
have Hmk_val : forall x, x < Tg -> val (mk_ord x) = x.
  move=> x Hx; rewrite /mk_ord.
  by case: (Sumbool.sumbool_of_bool _) => pf //=; rewrite pf in Hx.
pose w1_seq := map mk_ord w1 : seq 'I_Tg.
have Hsz_w1_seq : size w1_seq = L by rewrite /w1_seq size_map.
pose w1_ord : @pgg_word M L := Tuple (introT eqP Hsz_w1_seq).
have Hval_eq : map val (tval w1_ord) = w1.
  rewrite /w1_ord /= /w1_seq -map_comp.
  suff H : forall s, all (fun j => j < Tg) s ->
    map (val \o mk_ord) s = s.
    exact: H.
  elim => //= x xs IH' /andP [Hx Hxs].
  by rewrite /= Hmk_val // IH'.
(* Step 2: Apply IH to go from w1_ord to wf *)
have Hk_bound : k < L.-1.
  have Hsz0 : size (map val (tval w0)) = L
    by rewrite size_map size_tuple.
  by move: Hk; rewrite /= Hsz0 -ltn_predRL.
suff Hconn : trace_equiv w0 w1_ord.
  apply: connect_trans Hconn _.
  apply: (IH w1_ord) => //.
  - move=> [|i'] Hi /=.
    + (* i = 0: goal has map val (tval w1_ord), hyp has w1 *)
      have /= := Hbd 1 (ltn0Sn _).
      by rewrite Hval_eq.
    + (* i > 0: both access ws[i'] *)
      have Hi2 : i'.+2 <= size (w1 :: ws) by rewrite /= ltnS.
      have /= := Hbd i'.+2 Hi2.
      rewrite (set_nth_default (map val (tval w1_ord)) _ Hi).
      by rewrite (set_nth_default (map val (tval w0)) _ Hi).
  - move=> [|i'] Hi /=.
    + (* i = 0 *)
      have /= := Hstep 1 Hi.
      by rewrite Hval_eq.
    + (* i > 0: both access ws *)
      exact: Hstep i'.+2 Hi.
  - by rewrite /= Hval_eq.
(* Step 3: Prove trace_equiv w0 w1_ord via one adj_swap step *)
apply: connect1; rewrite /adj_swap_sym; apply/orP; left.
(* Need L = L'.+1 for adj_swap to be nontrivial *)
clear wf Hlast IH.
destruct L as [|L']; first by rewrite /= in Hk.
(* adj_swap on L'.+1 *)
apply/existsP; exists (Ordinal Hk_bound).
apply/andP; split.
  (* Commutativity: raag_comm (tnth w0 k) (tnth w0 k.+1) *)
  (* Goal: raag_comm (tnth w0 k_ord) (tnth w0 k1_ord) *)
  rewrite Hcomm_nat !(tnth_nth ord0).
  (* Now goal: comm_nat (val (nth ord0 w0 k')) (val (nth ord0 w0 k1')) *)
  simpl.
  have -> : val (nth ord0 (tval w0) k) = nth 0 (map val (tval w0)) k.
    rewrite (nth_map ord0) ?size_tuple //.
    by rewrite ltnS ltnW.
  have -> : val (nth ord0 (tval w0) k.+1) = nth 0 (map val (tval w0)) k.+1.
    by rewrite (nth_map ord0) ?size_tuple.
  simpl in Hc1; exact: Hc1.
(* Equality: w1_ord = swap_word k w0 *)
apply/eqP; apply: eq_from_tnth => i.
rewrite swap_word_tnth; apply: val_inj.
(* Key facts about tnth and nth *)
have Hw1_tnth : forall j : 'I_L'.+1,
  val (tnth w1_ord j) = nth 0 w1 (val j).
  move=> j.
  have Hj : val j < size (tval w1_ord).
    by rewrite size_tuple; exact: ltn_ord.
  transitivity (nth 0 (map val (tval w1_ord)) (val j)).
    rewrite (nth_map ord0 _ _ Hj).
    congr (val _).
    by rewrite (tnth_nth ord0).
  by rewrite Hval_eq.
have Hw0_tnth : forall j : 'I_L'.+1,
  val (tnth w0 j) = nth 0 (map val (tval w0)) (val j).
  move=> j; rewrite (tnth_nth (tnth w0 j)) /=.
  by rewrite (nth_map (tnth w0 j)) ?size_tuple.
set mw0 := map val (tval w0).
have Hsz_mw0 : size mw0 = L'.+1
  by rewrite /mw0 size_map size_tuple.
have Hk_lt : k < L'.+1
  by exact: ltn_trans (ltn_ord (Ordinal Hk_bound)) (ltnSn L').
rewrite Hw1_tnth Hw1.
(* Now: nth 0 (take k mw0 ++ ...) (val i) vs tnth w0 (swap pattern) *)
case: ifP => [/eqP Hi_k | Hne1].
  (* i = k *)
  rewrite Hi_k nth_cat size_take Hsz_mw0 Hk_lt ltnn subnn /=.
  by rewrite Hw0_tnth.
case: ifP => [/eqP Hi_k1 | Hne2].
  (* i = k.+1 *)
  rewrite Hi_k1 nth_cat size_take Hsz_mw0 Hk_lt.
  rewrite ltnNge leqnSn /= subSn // subnn /=.
  by rewrite Hw0_tnth.
(* i != k and i != k.+1 *)
(* Hne1 : (val i == val k) = false, Hne2 : (val i == (val k).+1) = false *)
rewrite nth_cat size_take Hsz_mw0 Hk_lt.
case: (ltnP (val i) k) => Hik.
  (* i < k *)
  by rewrite nth_take // Hw0_tnth.
(* i >= k, ltnP already resolved val i < k to false *)
have Hik_strict : k < val i.
  by rewrite ltn_neqAle Hik andbT eq_sym Hne1.
have Hik_ge2 : k.+1 < val i.
  by rewrite ltn_neqAle Hik_strict andbT eq_sym Hne2.
have Hsub : val i - k = (val i - k.+2).+2.
  set d := val i - k.+2.
  have Hvi : val i = d + k.+2 by rewrite /d subnK.
  by rewrite Hvi -addSnnS -addSnnS addnK.
rewrite /= Hsub /= nth_drop addnC subnK //.
by rewrite Hw0_tnth.
Qed.

(* ------------------------------------------------------------------ *)
(* fnf: Foata normal form on ordinal words                             *)
(* ------------------------------------------------------------------ *)

Definition fnf (L : nat) (w : @pgg_word M L) : seq nat :=
  foata_nf comm_nat (map val (tval w)).

Lemma val_tnth_nth n (w : n.-tuple 'I_Tg) (i : 'I_n) :
  val (tnth w i) = nth 0 (map val (tval w)) (val i).
Proof.
rewrite (tnth_nth (tnth w i)) /=.
by rewrite (nth_map (tnth w i)) ?size_tuple.
Qed.

(* Invariance: adj_swap w1 w2 -> fnf w1 = fnf w2 *)
Let fnf_adj_swap L (w1 w2 : @pgg_word M L) :
  @adj_swap R L w1 w2 -> fnf w1 = fnf w2.
Proof.
case: L w1 w2 => [|L'] w1 w2 //=.
move/existsP => [k /andP [Hc /eqP ->]].
rewrite /fnf /=.
set ik := Ordinal (ltn_trans (ltn_ord k) (ltnSn L')).
set ik1 := @Ordinal L'.+1 (val k).+1 (ltn_ord k).
have Hcomm1 : comm_nat (val (tnth w1 ik)) (val (tnth w1 ik1)).
  by rewrite -Hcomm_nat.
have Hcomm2 : comm_nat (val (tnth w1 ik1)) (val (tnth w1 ik)).
  by rewrite -Hcomm_nat raag_comm_sym.
set mw := map val (tval w1).
set a := val (tnth w1 ik).
set b := val (tnth w1 ik1).
(* Goal: foata_nf comm_nat (map val (tval (swap_word k w1))) = foata_nf comm_nat mw *)
(* Key: decompose mw = pre ++ [a; b] ++ suf *)
(*      and swap_word gives pre ++ [b; a] ++ suf *)
set pre := take (val k) mw.
set suf := drop (val k).+2 mw.
have Ha : a = nth 0 mw (val k) by rewrite /a /mw val_tnth_nth /ik.
have Hb : b = nth 0 mw (val k).+1 by rewrite /b /mw val_tnth_nth /ik1.
have Hsz : size mw = L'.+1 by rewrite /mw size_map size_tuple.
have Hklt : (val k).+1 < size mw by rewrite Hsz; exact: ltn_ord.
have Hklt' : val k < size mw by exact: ltn_trans (ltnSn _) Hklt.
have Hmw : mw = pre ++ a :: b :: suf.
  rewrite /pre /suf Ha Hb.
  have -> : nth 0 mw (val k) :: nth 0 mw (val k).+1 :: drop (val k).+2 mw
            = drop (val k) mw.
    rewrite (drop_nth 0 Hklt') /=; congr (_ :: _).
    rewrite (drop_nth 0 Hklt) /=.
    by rewrite -addn2 -drop_drop drop_drop addnC.
  by rewrite cat_take_drop.
(* The swap_word swaps a and b *)
suff Hsw : map val (tval (@swap_word M L'.+1 k w1)) = pre ++ b :: a :: suf.
  by rewrite Hsw {1}Hmw; exact: foata_nf_swap_adj.
(* Prove swap_word produces the swapped version *)
apply: (@eq_from_nth _ 0).
  rewrite size_map size_tuple.
  have -> : size (pre ++ b :: a :: suf) = size (pre ++ a :: b :: suf).
    by rewrite !size_cat.
  by rewrite -Hmw Hsz.
move=> i; rewrite size_map size_tuple => Hi.
rewrite (nth_map (tnth w1 ik)) ?size_tuple //.
have -> : nth (tnth w1 ik) (tval (@swap_word M L'.+1 k w1)) i =
          tnth (@swap_word M L'.+1 k w1) (Ordinal Hi).
  by rewrite (tnth_nth (tnth w1 ik) (@swap_word M L'.+1 k w1) (Ordinal Hi)).
rewrite swap_word_tnth.
rewrite nth_cat /pre size_takel; last exact: ltnW Hklt'.
case Hik_eq : (i == val k).
  (* i = k: swap gives tnth w1 ik1, target is b *)
  move/eqP: Hik_eq => ->.
  by rewrite ltnn subnn /=.
case Hik1_eq : (i == (val k).+1).
  (* i = k+1: swap gives tnth w1 ik, target is a *)
  move/eqP: Hik1_eq => ->.
  by rewrite ltnNge leqnSn /= subSnn /=.
(* i <> k, i <> k+1: swap gives tnth w1 i, target is original *)
case: ifP => Hilt.
  (* i < k: in pre part *)
  by rewrite nth_take // val_tnth_nth.
(* i >= k: in suf part, i - val k >= 2 *)
have Hge : val k <= i by rewrite leqNgt Hilt.
have Higt : val k < i by rewrite ltn_neqAle eq_sym Hik_eq Hge.
have Hik1gt : (val k).+1 < i.
  by rewrite ltn_neqAle eq_sym Hik1_eq.
have Hige2 : 2 <= i - val k.
  rewrite leq_subRL; last by apply: ltnW; apply: ltnW; exact: Hik1gt.
  by rewrite addnC.
(* RHS: nth 0 (b :: a :: suf) (i - val k) *)
(* suf = drop (val k).+2 mw *)
(* Rewrite using cat: [:: b, a & suf] = [:: b; a] ++ suf *)
have -> : nth 0 (b :: a :: suf) (i - val k) = nth 0 ([:: b; a] ++ suf) (i - val k) by [].
rewrite nth_cat /=.
have -> : (i - val k < 2) = false by rewrite ltnNge Hige2.
rewrite /suf nth_drop.
have -> : (val k).+2 + (i - val k - 2) = i.
  by rewrite -subnDA -(addn2 (val k)) subnKC // addn2.
by rewrite val_tnth_nth.
Qed.

Let fnf_trace L (w1 w2 : @pgg_word M L) :
  @trace_equiv R L w1 w2 -> fnf w1 = fnf w2.
Proof.
rewrite /trace_equiv => /connectP [p].
elim: p w1 => [w1 _ -> | w' p IH w1 /= /andP [Hstep Hpath] Hlast] //.
have Heq : fnf w1 = fnf w'.
  case/orP: Hstep => H.
    exact: fnf_adj_swap H.
  by symmetry; exact: fnf_adj_swap H.
by rewrite Heq; exact: IH Hpath Hlast.
Qed.

(* Separation: fnf w1 = fnf w2 -> trace_equiv w1 w2 *)
Let fnf_sep L (w1 w2 : @pgg_word M L) :
  fnf w1 = fnf w2 -> @trace_equiv R L w1 w2.
Proof.
move=> Hnf_eq.
(* Define symmetric bounded wrapper for comm_nat *)
set comm_b := fun a b : nat => [&& a < Tg, b < Tg & comm_nat a b].
have Hcb_sym : forall a b, comm_b a b -> comm_b b a.
  move=> a b; rewrite /comm_b => /and3P [Ha Hb Hab].
  by rewrite Ha Hb comm_nat_sym.
(* comm_b agrees with comm_nat on in-range values *)
have Hcb_eq : forall a b, a < Tg -> b < Tg -> comm_b a b = comm_nat a b.
  by move=> a b Ha Hb; rewrite /comm_b Ha Hb.
(* foata_nf comm_b = foata_nf comm_nat on ordinal words *)
have Hword_bd : forall (w : @pgg_word M L),
  all (fun x => x < Tg) (map val (tval w)).
  move=> w; apply/allP => x /mapP [o _ ->]; exact: ltn_ord.
have Hfnf_b : forall (w : @pgg_word M L),
  foata_nf comm_b (map val (tval w)) = fnf w.
  move=> w; rewrite /fnf; apply: foata_nf_ext => a b Ha Hb.
  have Ha' : a < Tg by move: (allP (Hword_bd w) _ Ha).
  have Hb' : b < Tg by move: (allP (Hword_bd w) _ Hb).
  exact: Hcb_eq.
(* Get swap chains using comm_b (which is symmetric) *)
have [ws1 [Hlast1 Hsteps1]] :=
  foata_nf_sound (map val (tval w1)) Hcb_sym.
have [ws2 [Hlast2 Hsteps2]] :=
  foata_nf_sound (map val (tval w2)) Hcb_sym.
(* Adjacent swaps preserve size and bounds *)
have Hswap_sz : forall s k, k.+1 < size s ->
  size (take k s ++ nth 0 s k.+1 :: nth 0 s k :: drop k.+2 s) = size s.
  move=> s k0 Hk0.
  rewrite size_cat size_take (ltn_trans (ltnSn k0) Hk0) /=.
  rewrite size_drop.
  have Hk0' : k0.+2 <= size s by [].
  by rewrite -addSnnS -addSnnS subnKC.
have Hswap_bd : forall s k, k.+1 < size s ->
  all (fun x => x < Tg) s ->
  all (fun x => x < Tg) (take k s ++ nth 0 s k.+1 :: nth 0 s k :: drop k.+2 s).
  move=> s k0 Hk0 Hall.
  rewrite all_cat /=; apply/andP; split.
    by apply/allP => x Hx; apply (allP Hall); exact: mem_take Hx.
  rewrite (allP Hall (nth 0 s k0.+1)); last exact: mem_nth.
  rewrite (allP Hall (nth 0 s k0)) /=; last exact: mem_nth (ltn_trans (ltnSn k0) Hk0).
  by apply/allP => x Hx; apply (allP Hall); exact: mem_drop Hx.
(* Chain invariant: each word has size L and all values < Tg *)
(* Helper to bridge nth default values *)
have nth_def_cons : forall (x0 : seq nat) ws w i,
  i < size ws -> nth x0 (w :: ws) i.+1 = nth [::] (w :: ws) i.+1.
  move=> x0 ws' w' i' Hi'; apply: set_nth_default; rewrite /= ltnS; exact: Hi'.
have nth_def_cons0 : forall (x0 : seq nat) ws w i,
  i <= size ws -> nth x0 (w :: ws) i = nth [::] (w :: ws) i.
  move=> x0 ws' w' [|i'] Hi' //.
  apply: set_nth_default; rewrite /= ltnS; exact: Hi'.
have Hchain_inv1 : forall i, i <= size ws1 ->
  let wi := nth (map val (tval w1)) (map val (tval w1) :: ws1) i in
  size wi = L /\ all (fun j => j < Tg) wi.
  elim => [|i IH] Hi.
    by rewrite /= size_map size_tuple.
  have Hi' : i < size ws1 := Hi.
  have [Hszi Hbdi] := IH (ltnW Hi').
  have [k0 [Hk0 [_ [_ Heqw]]]] := Hsteps1 i Hi'.
  rewrite (nth_def_cons _ _ _ _ Hi') (nth_def_cons0 _ _ _ _ (ltnW Hi')) in Hszi Hbdi |- *.
  rewrite Heqw; split.
  - by rewrite Hswap_sz.
  - by exact: Hswap_bd.
have Hchain_inv2 : forall i, i <= size ws2 ->
  let wi := nth (map val (tval w2)) (map val (tval w2) :: ws2) i in
  size wi = L /\ all (fun j => j < Tg) wi.
  elim => [|i IH] Hi.
    by rewrite /= size_map size_tuple.
  have Hi' : i < size ws2 := Hi.
  have [Hszi Hbdi] := IH (ltnW Hi').
  have [k0 [Hk0 [_ [_ Heqw]]]] := Hsteps2 i Hi'.
  rewrite (nth_def_cons _ _ _ _ Hi') (nth_def_cons0 _ _ _ _ (ltnW Hi')) in Hszi Hbdi |- *.
  rewrite Heqw; split.
  - by rewrite Hswap_sz.
  - by exact: Hswap_bd.
(* comm_b swaps are also comm_nat swaps *)
have Hsteps1_nat : forall i, i < size ws1 ->
  let wi := nth [::] (map val (tval w1) :: ws1) i in
  let wi1 := nth [::] (map val (tval w1) :: ws1) i.+1 in
  exists k, k.+1 < size wi /\
    comm_nat (nth 0 wi k) (nth 0 wi k.+1) /\
    comm_nat (nth 0 wi k.+1) (nth 0 wi k) /\
    wi1 = take k wi ++ nth 0 wi k.+1 :: nth 0 wi k :: drop k.+2 wi.
  move=> i Hi.
  have [k0 [Hk0 [Hc1 [Hc2 Hw]]]] := Hsteps1 i Hi.
  exists k0; repeat split => //.
  - by move: Hc1; rewrite /comm_b => /and3P [_ _ ?].
  - by move: Hc2; rewrite /comm_b => /and3P [_ _ ?].
have Hsteps2_nat : forall i, i < size ws2 ->
  let wi := nth [::] (map val (tval w2) :: ws2) i in
  let wi1 := nth [::] (map val (tval w2) :: ws2) i.+1 in
  exists k, k.+1 < size wi /\
    comm_nat (nth 0 wi k) (nth 0 wi k.+1) /\
    comm_nat (nth 0 wi k.+1) (nth 0 wi k) /\
    wi1 = take k wi ++ nth 0 wi k.+1 :: nth 0 wi k :: drop k.+2 wi.
  move=> i Hi.
  have [k0 [Hk0 [Hc1 [Hc2 Hw]]]] := Hsteps2 i Hi.
  exists k0; repeat split => //.
  - by move: Hc1; rewrite /comm_b => /and3P [_ _ ?].
  - by move: Hc2; rewrite /comm_b => /and3P [_ _ ?].
(* Build ordinal word for the common normal form *)
(* last ws1 = foata_nf comm_b (map val w1) = fnf w1 = fnf w2
                                            = foata_nf comm_b (map val w2) = last ws2 *)
have Hcommon : last (map val (tval w1)) ws1 = last (map val (tval w2)) ws2.
  by rewrite Hlast1 Hlast2 Hfnf_b Hfnf_b Hnf_eq.
(* Build ordinal word for the normal form *)
have [Hsznf Hbdnf] := Hchain_inv1 (size ws1) (leqnn _).
rewrite nth_last /= in Hsznf Hbdnf.
set nf_list := last (map val (tval w1)) ws1 in Hsznf Hbdnf.
pose mk_ord := fun x =>
  match Sumbool.sumbool_of_bool (x < Tg) with
  | left pf => @Ordinal Tg x pf
  | right _ => @Ordinal Tg 0 (ltn0Sn _)
  end.
have Hmk_val : forall x, x < Tg -> val (mk_ord x) = x.
  move=> x Hx; rewrite /mk_ord.
  by case: (Sumbool.sumbool_of_bool _) => pf //=; rewrite pf in Hx.
pose nf_seq := map mk_ord nf_list : seq 'I_Tg.
have Hsz_nf : size nf_seq = L by rewrite /nf_seq size_map.
pose wf : @pgg_word M L := Tuple (introT eqP Hsz_nf).
have Hval_wf : map val (tval wf) = nf_list.
  rewrite /wf /= /nf_seq -map_comp.
  suff H : forall s, all (fun j => j < Tg) s ->
    map (val \o mk_ord) s = s.
    exact: H.
  elim => //= x xs IH /andP [Hx Hxs].
  by rewrite /= Hmk_val // IH.
(* w1 ~ wf via ws1 chain *)
have Hte1 : @trace_equiv R L w1 wf.
  apply: (nat_swap_chain_to_trace_equiv Hchain_inv1 Hsteps1_nat).
  exact: Hval_wf.
(* w2 ~ wf via ws2 chain *)
have Hte2 : @trace_equiv R L w2 wf.
  have Hchain_inv2' : forall i, i <= size ws2 ->
    let wi := nth (map val (tval w2)) (map val (tval w2) :: ws2) i in
    size wi = L /\ all (fun j => j < Tg) wi.
    exact: Hchain_inv2.
  apply: (nat_swap_chain_to_trace_equiv Hchain_inv2' Hsteps2_nat).
  by rewrite -Hcommon.
(* Compose: w1 ~ wf ~ w2 *)
apply: connect_trans Hte1 _.
rewrite (sym_connect_sym (@adj_swap_sym_sym R L)).
exact: Hte2.
Qed.

(* ------------------------------------------------------------------ *)
(* all_words <-> enum tuples bijection                                 *)
(* ------------------------------------------------------------------ *)

Let all_words_uniq' : forall Tg' L, uniq (all_words Tg' L).
Proof.
move=> Tg'; elim=> [|L' IH] //=.
apply: allpairs_uniq; first exact: iota_uniq.
- exact: IH.
- by move=> [a1 b1] [a2 b2] /= _ _ [-> ->].
Qed.

Let all_words_mem' : forall Tg' L (w : seq nat),
  w \in all_words Tg' L <-> (size w = L /\ all (fun i => i < Tg') w).
Proof.
move=> Tg' L w; split.
- elim: L w => [|L IH] w /=.
  + by rewrite mem_seq1 => /eqP ->.
  + move/flattenP => [s /mapP [i Hi ->] /mapP [w' Hw' ->]].
    rewrite mem_iota add0n in Hi.
    have [Hsz Hbd] := IH w' Hw'.
    have /andP [_ Hi'] := Hi.
    by rewrite /= Hsz Hi' Hbd.
- elim: L w => [|L IH] w /=.
  + by move=> [/size0nil -> _].
  + case: w => [|a w'] /=.
      by move=> [].
    move=> [/= [Hsz] /andP [Ha Hbd]].
    apply/flattenP; exists (map (cons a) (all_words Tg' L)).
      by apply/mapP; exists a => //; rewrite mem_iota add0n.
    apply/mapP; exists w' => //. exact (IH w' (conj Hsz Hbd)).
Qed.

Let all_words_perm_tuples L :
  perm_eq (all_words Tg L)
          (map (fun w : @pgg_word M L => map val (tval w))
               (enum {: @pgg_word M L})).
Proof.
apply: uniq_perm.
- exact: all_words_uniq'.
- rewrite map_inj_uniq; first exact: enum_uniq.
  by move=> w1 w2 /(inj_map val_inj) /val_inj.
- move=> w; apply/idP/idP.
  + move/all_words_mem' => [Hsz Hbd].
    apply/mapP.
    pose ow := pmap (insub : nat -> option 'I_Tg) w.
    have Hpmap_sz : forall s, all (fun x => x < Tg) s ->
        size (pmap (insub : nat -> option 'I_Tg) s) = size s.
      by elim => //= a s IH /andP [Ha Hs]; rewrite insubT //= IH.
    have Hsz_ow : size ow == L by rewrite /ow Hpmap_sz // Hsz.
    have Hpmap_map : forall s, all (fun x => x < Tg) s ->
        map val (pmap (insub : nat -> option 'I_Tg) s) = s.
      by elim => //= a s IH /andP [Ha Hs]; rewrite insubT //= IH.
    have Hmap : map val ow = w by rewrite /ow Hpmap_map.
    by exists (Tuple Hsz_ow); [rewrite mem_enum | rewrite /= Hmap].
  + move/mapP => [t _ ->].
    apply/all_words_mem'; split.
      by rewrite size_map size_tuple.
    by apply/allP => x /mapP [o _ ->]; exact: ltn_ord.
Qed.

(* ------------------------------------------------------------------ *)
(* Abstract canonical form counting                                    *)
(* ------------------------------------------------------------------ *)

Let n_comp_canonical (T : finType) (S : eqType) (e : rel T) (f : T -> S)
  (Hsym : connect_sym e)
  (Hinv : forall x y : T, connect e x y -> f x = f y)
  (Hsep : forall x y : T, f x = f y -> connect e x y) :
  n_comp e T = size (undup (map f (enum T))).
Proof.
have Hnc : n_comp e T = size (filter (roots e) (enum T)).
  rewrite /n_comp_mem cardE /enum_mem /=.
  congr size.
  rewrite filter_predI filter_predT //.
rewrite Hnc.
suff Hperm : perm_eq (map f (filter (roots e) (enum T)))
                      (undup (map f (enum T))).
  by rewrite -(perm_size Hperm) size_map.
apply: uniq_perm.
- rewrite map_inj_in_uniq; first by apply: filter_uniq; exact: enum_uniq.
  move=> x y.
  rewrite !mem_filter => /andP [Hx _] /andP [Hy _].
  move=> Hfxy.
  move: Hx Hy; rewrite /roots /= => /eqP Hx /eqP Hy.
  have Hc := Hsep _ _ Hfxy.
  by rewrite -Hx -Hy (rootP Hsym Hc).
- exact: undup_uniq.
- move=> s; rewrite mem_undup; apply/mapP/mapP.
  + move=> [x Hx ->].
    have Hxe : x \in enum T.
      by rewrite mem_filter in Hx; case/andP: Hx.
    exact: (ex_intro2 _ _ x Hxe (erefl (f x))).
  + move=> [x Hx ->].
    exists (root e x).
      rewrite mem_filter mem_enum andbT /roots /= root_root //.
    exact: Hinv (connect_root e x).
Qed.

Let size_undup_perm_eq (S : eqType) (s1 s2 : seq S) :
  perm_eq s1 s2 -> size (undup s1) = size (undup s2).
Proof.
move=> Hp; apply/eqP; rewrite eqn_leq; apply/andP; split;
  apply: (uniq_leq_size (s2:=undup _) (undup_uniq _)) => x;
  by rewrite !mem_undup (perm_mem Hp).
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem                                                        *)
(* ------------------------------------------------------------------ *)

Lemma n_traces_of_natB (L : nat) :
  n_traces_natB Tg L comm_nat = @n_traces R L.
Proof.
rewrite /n_traces_natB.
(* Step 1: replace all_words with map to_nat (enum tuples) *)
have Hstep1 : size (undup (map (foata_nf comm_nat) (all_words Tg L))) =
  size (undup (map (fnf (L:=L)) (enum {: @pgg_word M L}))).
  apply: size_undup_perm_eq.
  have Hpe := all_words_perm_tuples L.
  have Hpe' := perm_map (foata_nf comm_nat) Hpe.
  suff -> : map (fnf (L:=L)) (enum {: @pgg_word M L}) =
    map (foata_nf comm_nat)
      (map (fun w : @pgg_word M L => map val (tval w))
           (enum {: @pgg_word M L}))
    by exact: Hpe'.
  rewrite -map_comp; apply: eq_map => w /=.
  by rewrite /fnf.
rewrite Hstep1.
(* Step 2: apply canonical form counting *)
symmetry; apply: n_comp_canonical.
- exact: sym_connect_sym (@adj_swap_sym_sym R L).
- exact: fnf_trace.
- exact: fnf_sep.
Qed.

End raag_gen_reflect.