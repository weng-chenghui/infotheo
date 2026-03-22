(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.

(******************************************************************************)
(*                                                                            *)
(*            Assignment Graphs and Edge Coverage for PGG                     *)
(*                                                                            *)
(* This file defines assignment graphs and edge coverage for the              *)
(* (k,T)-threshold ramp scheme in PGG.                                       *)
(*                                                                            *)
(* An assignment graph captures which pairs of players share a                *)
(* component. Edge coverage determines how much information a coalition       *)
(* can reconstruct.                                                           *)
(*                                                                            *)
(*  AssignmentGraph T == a symmetric, irreflexive graph on 'I_T              *)
(*  covered_edges C G == edges of G where both endpoints lie in C             *)
(*  secure_edges C G  == edges of G NOT fully covered by C                    *)
(*  recoverable_bits C G == number of covered edges (halved for undirected)   *)
(*  cycle_graph T     == T-cycle: player i shares with player (i+1) mod T    *)
(*  complete_graph T  == complete graph: all player-pairs share a component   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Helper lemmas for modular arithmetic, proved before ring_scope
   to avoid scope conflicts with ssrnat rewrite lemmas. *)

Lemma succ_mod_neq (n m : nat) : (0 < m -> n < m.+1 ->
  (n + 1) %% m.+1 <> n)%N.
Proof.
move=> Hm Hn.
case: (ltnP (n + 1) m.+1) => Hcase.
- rewrite modn_small // => Habs.
  have : n < n + 1 by rewrite addn1.
  by rewrite Habs ltnn.
- have Hnm : n = m.
    apply/eqP; rewrite eqn_leq -ltnS Hn /=.
    by rewrite -(leq_add2r 1) !addn1 ltnS in Hcase.
  subst n; rewrite addn1 modnn => H0.
  by rewrite H0 ltnn in Hm.
Qed.

Lemma succ_mod_cycle2_ord (T : nat) (i j : 'I_T.+1) :
  (1 < T)%N ->
  j = inZp (i + 1) ->
  i = inZp (j + 1) ->
  False.
Proof.
move=> HT Hj Hi.
have Hvi := congr1 val Hi.
have Hvj := congr1 val Hj.
simpl in Hvi, Hvj.
set iv := val i in Hvi Hvj.
set jv := val j in Hvi Hvj.
have HiT := ltn_ord i : (iv < T.+1)%N.
have HjT := ltn_ord j : (jv < T.+1)%N.
case: (ltnP (iv + 1)%N T.+1) => Hcase1.
  have jv_eq : (jv = iv + 1)%N by rewrite Hvj modn_small.
  case: (ltnP (iv + 1 + 1)%N T.+1) => Hcase2.
    have iv_eq : (iv = iv + 1 + 1)%N.
      transitivity ((jv + 1) %% T.+1)%N; first exact: Hvi.
      by rewrite jv_eq modn_small.
    have : (iv < iv + 1 + 1)%N by rewrite !addn1.
    by rewrite -iv_eq ltnn.
  have iv11_T : (iv + 1 + 1 = T.+1)%N.
    apply/eqP; rewrite eqn_leq Hcase2 andbT.
    rewrite !addn1; rewrite !addn1 in Hcase1; exact: Hcase1.
  have iv_eq : (iv = 0)%N.
    transitivity ((jv + 1) %% T.+1)%N; first exact: Hvi.
    by rewrite jv_eq iv11_T modnn.
  have : (T.+1 = 2)%N by rewrite -iv11_T iv_eq.
  move=> /eqP; rewrite eqSS => /eqP HT1.
  by rewrite HT1 ltnn in HT.
have iv_T : (iv = T)%N.
  apply/eqP; rewrite eqn_leq -ltnS HiT /=.
  by rewrite -(leq_add2r 1) !addn1 ltnS in Hcase1.
have jv_eq : (jv = 0)%N by rewrite Hvj iv_T addn1 modnn.
have iv_eq : (iv = 1)%N.
  rewrite Hvi jv_eq add0n modn_small //; exact: ltnW.
by rewrite iv_eq in iv_T; rewrite -iv_T ltnn in HT.
Qed.

Import GRing.Theory.

Local Open Scope ring_scope.

(* ========================================================================= *)
(* Section 1: Assignment Graph                                               *)
(* ========================================================================= *)

Section AssignmentGraphDef.

Variable T : nat.

Record AssignmentGraph := mkAG {
  ag_edges : {set 'I_T * 'I_T};
  ag_sym : forall i j, (i, j) \in ag_edges -> (j, i) \in ag_edges;
  ag_irrefl : forall i, (i, i) \notin ag_edges;
}.

End AssignmentGraphDef.

(* ========================================================================= *)
(* Section 2: Edge Coverage                                                  *)
(* ========================================================================= *)

Section EdgeCoverage.

Variable T : nat.
Variable G : AssignmentGraph T.

(** Edges where both endpoints are in coalition C. *)
Definition covered_edges (C : {set 'I_T}) : {set 'I_T * 'I_T} :=
  [set e in ag_edges G | (e.1 \in C) && (e.2 \in C)].

(** Edges NOT fully covered by C. *)
Definition secure_edges (C : {set 'I_T}) : {set 'I_T * 'I_T} :=
  ag_edges G :\: covered_edges C.

(** Number of covered directed edges, halved for undirected count. *)
Definition recoverable_bits (C : {set 'I_T}) : nat :=
  #|covered_edges C| %/ 2.

End EdgeCoverage.

(* ========================================================================= *)
(* Section 3: Monotonicity Lemmas                                            *)
(* ========================================================================= *)

Section Monotonicity.

Variable T : nat.
Variable G : AssignmentGraph T.

Lemma covered_mono (C C' : {set 'I_T}) :
  C \subset C' -> covered_edges G C \subset covered_edges G C'.
Proof.
move=> Hsub; apply/subsetP => e.
rewrite /covered_edges !inE.
move=> /andP[He /andP[H1 H2]].
rewrite He /=; apply/andP; split;
  exact: (subsetP Hsub).
Qed.

Lemma covered_full (C : {set 'I_T}) :
  C = setT -> covered_edges G C = ag_edges G.
Proof.
move=> ->; apply/setP => e; rewrite /covered_edges !inE.
by case: (e \in ag_edges G) => //=; rewrite !in_setT.
Qed.

Lemma secure_subset (C : {set 'I_T}) :
  secure_edges G C \subset ag_edges G.
Proof. by apply/subsetP => e; rewrite /secure_edges !inE => /andP[]. Qed.

Lemma covered_secure_partition (C : {set 'I_T}) :
  covered_edges G C :|: secure_edges G C = ag_edges G.
Proof.
apply/setP => e; rewrite /covered_edges /secure_edges !inE.
case Hedge : (e \in ag_edges G) => //=.
by case: (e.1 \in C); case: (e.2 \in C).
Qed.

Lemma secure_singleton (C : {set 'I_T}) :
  #|C| = 1 -> covered_edges G C = set0.
Proof.
move=> Hcard; apply/setP => [[i j]] /=; rewrite /covered_edges !inE /=.
case Hedge : ((i, j) \in ag_edges G) => //=.
apply/negP => /andP[H1 H2].
have /cards1P[x Hx] : #|C| == 1 by rewrite Hcard.
move: H1 H2; rewrite Hx !in_set1 => /eqP Hi /eqP Hj.
subst i j.
by move/negP: (ag_irrefl G x).
Qed.

Lemma covered_edges0 : covered_edges G set0 = set0.
Proof.
apply/setP => e; rewrite /covered_edges !inE.
by case: (e \in ag_edges G).
Qed.

End Monotonicity.

(* ========================================================================= *)
(* Section 4: Concrete Instances                                             *)
(* ========================================================================= *)

Section CycleGraph.

Variable T' : nat.
Hypothesis HT : (0 < T')%N.
Let T := T'.+1.

(** Cycle graph: party i is connected to party (i+1) mod T
    and party (i-1) mod T. Directed edges in both directions. *)

Definition cycle_edge_set : {set 'I_T * 'I_T} :=
  [set e : 'I_T * 'I_T |
    (e.2 == inZp (e.1 + 1)) || (e.1 == inZp (e.2 + 1))].

Lemma cycle_sym (i j : 'I_T) :
  (i, j) \in cycle_edge_set -> (j, i) \in cycle_edge_set.
Proof. by rewrite !inE /= orbC. Qed.

Lemma cycle_irrefl (i : 'I_T) : (i, i) \notin cycle_edge_set.
Proof.
rewrite inE /= orbb; apply/negP => /eqP /(congr1 val) /= Hmod.
exact: (succ_mod_neq HT (ltn_ord i) (esym Hmod)).
Qed.

Definition cycle_graph : AssignmentGraph T :=
  mkAG cycle_sym cycle_irrefl.

(** Forward and backward edge decomposition for counting. *)

Definition fwd_edges : {set 'I_T * 'I_T} :=
  [set ((i : 'I_T), inZp (i + 1)) | i : 'I_T].

Definition bwd_edges : {set 'I_T * 'I_T} :=
  [set (inZp ((i : 'I_T) + 1), (i : 'I_T)) | i : 'I_T].

Lemma cycle_edge_set_union : cycle_edge_set = fwd_edges :|: bwd_edges.
Proof.
apply/setP => [[a b]]; rewrite !inE /=.
apply/idP/idP.
- case/orP => /eqP H.
  + apply/orP; left; apply/imsetP; exists a => //.
    by apply/eqP; rewrite xpair_eqE eqxx /= H.
  + apply/orP; right; apply/imsetP; exists b => //.
    by apply/eqP; rewrite xpair_eqE eqxx andbT H.
- case/orP => /imsetP[i _ /eqP]; rewrite xpair_eqE => /andP[/eqP Ha /eqP Hb];
  subst a b; apply/orP.
  + by left; exact: eqxx.
  + by right; exact: eqxx.
Qed.

Lemma fwd_card : #|fwd_edges| = T.
Proof.
rewrite card_imset ?card_ord //.
by move=> i j /eqP; rewrite xpair_eqE => /andP[/eqP H _].
Qed.

Lemma bwd_card : #|bwd_edges| = T.
Proof.
rewrite card_imset ?card_ord //.
by move=> i j /eqP; rewrite xpair_eqE => /andP[_ /eqP].
Qed.

Lemma fwd_bwd_disjoint : (1 < T')%N -> [disjoint fwd_edges & bwd_edges].
Proof.
move=> HT2.
apply/pred0P => [[a b]] /=.
apply/negP => /andP[/imsetP[i _ Hab1] /imsetP[j _ Hab2]].
have Ha1 : a = i by move: Hab1 => [].
have Hb1 : b = inZp (i + 1) :> 'I_T by move: Hab1 => [].
have Ha2 : a = inZp (j + 1) :> 'I_T by move: Hab2 => [].
have Hb2 : b = j by move: Hab2 => [].
have Hij : i = inZp (j + 1) :> 'I_T by rewrite -Ha1 -Ha2.
have Hji : j = inZp (i + 1) :> 'I_T by rewrite -Hb2 -Hb1.
exact: (succ_mod_cycle2_ord HT2 Hji Hij).
Qed.

Lemma cycle_edges_count : (1 < T')%N -> #|ag_edges cycle_graph| = 2 * T.
Proof.
move=> HT2.
rewrite /= cycle_edge_set_union cardsU.
rewrite fwd_card bwd_card.
have /eqP -> : fwd_edges :&: bwd_edges == set0.
  by rewrite setI_eq0; exact: fwd_bwd_disjoint.
by rewrite cards0 subn0 addnn -mul2n.
Qed.

End CycleGraph.

Section CompleteGraph.

Variable T' : nat.
Let T := T'.+2.

Definition complete_edge_set : {set 'I_T * 'I_T} :=
  [set e : 'I_T * 'I_T | e.1 != e.2].

Lemma complete_sym (i j : 'I_T) :
  (i, j) \in complete_edge_set -> (j, i) \in complete_edge_set.
Proof. by rewrite !inE eq_sym. Qed.

Lemma complete_irrefl (i : 'I_T) : (i, i) \notin complete_edge_set.
Proof. by rewrite inE eqxx. Qed.

Definition complete_graph : AssignmentGraph T :=
  mkAG complete_sym complete_irrefl.

Lemma complete_edges_count :
  #|ag_edges complete_graph| = T * T.-1.
Proof.
have Hcompl : ~: complete_edge_set = [set e : 'I_T * 'I_T | e.1 == e.2].
  by apply/setP => e; rewrite !inE negbK.
have Hdiag : #|[set e : 'I_T * 'I_T | e.1 == e.2]| = T.
  pose f (i : 'I_T) : 'I_T * 'I_T := (i, i).
  have Hinj : injective f by move=> i j [].
  have -> : [set e : 'I_T * 'I_T | e.1 == e.2] = f @: [set: 'I_T].
    apply/setP => [[i j]]; rewrite inE /=.
    apply/eqP/imsetP.
    - move=> Hij; exists i; first by rewrite inE.
      by rewrite /f /=; case: j / Hij.
    - by move=> [k _ /= [-> ->]].
  by rewrite card_imset // cardsT card_ord.
have := cardsC complete_edge_set.
rewrite Hcompl Hdiag card_prod !card_ord.
(* #|complete_edge_set| + T = T * T -> #|complete_edge_set| = T * T.-1 *)
set n := #|complete_edge_set| => Hsum.
have Harith : (T * T.-1 + T = T * T)%N by rewrite /T mulnS addnC.
by apply/eqP; rewrite -(eqn_add2r T) Hsum Harith.
Qed.

Lemma complete_covered_full (C : {set 'I_T}) :
  C = setT -> covered_edges complete_graph C = ag_edges complete_graph.
Proof. exact: covered_full. Qed.

End CompleteGraph.
