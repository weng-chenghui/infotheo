(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop fingraph path binomial.
From Stdlib Require Import Wf_nat.
From pgg_smc Require Import pgg_interface pgg_lfree.

(******************************************************************************)
(* PGG-SMC: RAAG (Right-Angled Artin Group) Search Space Theory              *)
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
(*   trace_norm_pass_aux comm fuel carry rest == bubble carry rightward        *)
(*   trace_norm_pass comm w == one pass of partial bubble sort                *)
(*   trace_norm comm w == iterate trace_norm_pass to fixpoint                 *)
(*   n_traces_natB Tg L comm == number of distinct trace-normal forms         *)
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
(*   raag_lfree : word_eval injective on trace classes                        *)
(*   raag_lfree_search_space : raag_lfree -> search_space = n_traces          *)
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

(* One pass: bubble carry element rightward through rest, swapping when
   carry > y and comm carry y.  Uses fuel (= size rest) for termination. *)
Fixpoint trace_norm_pass_aux (comm : nat -> nat -> bool) (fuel : nat)
    (carry : nat) (rest : seq nat) : seq nat * bool :=
  match fuel, rest with
  | _, [::] => ([:: carry], false)
  | 0, _ => (carry :: rest, false)
  | fuel'.+1, y :: rest' =>
    if comm carry y && (y < carry) then
      let '(w', _) := trace_norm_pass_aux comm fuel' carry rest' in
      (y :: w', true)
    else
      let '(w', c) := trace_norm_pass_aux comm fuel' y rest' in
      (carry :: w', c)
  end.

Definition trace_norm_pass (comm : nat -> nat -> bool) (w : seq nat)
    : seq nat * bool :=
  match w with
  | [::] => ([::], false)
  | x :: rest => trace_norm_pass_aux comm (size rest) x rest
  end.

(* Iterate trace_norm_pass until stable, bounded by fuel *)
Fixpoint trace_norm_iter (comm : nat -> nat -> bool) (fuel : nat)
    (w : seq nat) : seq nat :=
  match fuel with
  | 0 => w
  | fuel'.+1 =>
    let '(w', changed) := trace_norm_pass comm w in
    if changed then trace_norm_iter comm fuel' w'
    else w'
  end.

Definition trace_norm (comm : nat -> nat -> bool) (w : seq nat) : seq nat :=
  trace_norm_iter comm (size w * size w) w.

Definition n_traces_natB (Tg L : nat) (comm : nat -> nat -> bool) : nat :=
  size (undup (map (trace_norm comm) (all_words Tg L))).

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

(* RAAG L-freeness: word_eval injective on trace classes *)
Definition raag_lfree (L : nat) : Prop :=
  forall w1 w2 : pgg_word M L, word_eval w1 = word_eval w2 -> trace_equiv w1 w2.

Lemma raag_lfree_search_space L :
  raag_lfree L -> @search_space M L = n_traces L.
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
   with raag_lfree give word_eval injectivity on I-words *)
Lemma indep_set_word_eval_inj (I : {set 'I_Tg}) (L : nat) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  raag_lfree L ->
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

Lemma raag_lfree1 : @lfree R 1.
Proof. exact: gen_inj_lfree1 (@raag_gen_inj R). Qed.

Lemma raag_search_space_1 : @search_space R 1 = Tg.
Proof. exact: lfree_search_space raag_lfree1. Qed.
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

Lemma n_traces_of_natB (L : nat) :
  n_traces_natB Tg L comm_nat = @n_traces R L.
Proof.
(* Requires proving that trace_norm produces canonical representatives of
   trace equivalence classes, i.e., two words are trace-equivalent iff they
   have the same trace_norm.  Soundness (each swap preserves trace_equiv) is
   straightforward; completeness needs confluence of trace_norm, which follows
   from Newman's lemma (local confluence + termination → confluence) — the
   combinatorial infrastructure for this is not yet in the codebase.
   This is a reflection lemma for vm_compute convenience only; all mathematical
   results (search_space_le_traces, full_comm_traces, etc.) are proved without it. *)
Admitted.

End raag_gen_reflect.
