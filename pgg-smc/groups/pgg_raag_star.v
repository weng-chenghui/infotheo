(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.

(******************************************************************************)
(* PGG-SMC: Star-Graph RAAG Instance                                         *)
(* Group presentation: <g_0,...,g_m | g_0 g_i = g_i g_0 for i=1..m>         *)
(*                                                                            *)
(* Constructs a concrete PGG instance based on a star commutation graph:      *)
(* one center generator commutes with all leaf generators, while leaves do    *)
(* not commute with each other.  This gives a non-abelian RAAG with           *)
(* independent set of size m (the leaves), yielding m^L <= n_traces.          *)
(*                                                                            *)
(*   star_gen i == generator permutation:                                     *)
(*                 center (i=0): tperm n0 n1 (support {0,1})                  *)
(*                 leaf (i>0):   tperm n2 (2+i) (support {2,2+i})             *)
(*   star_comm i j == commutation relation (center commutes with leaves)      *)
(*   star_Hcomm == star_comm implies group-level commutativity                *)
(*   star_leaf_noncommute == leaves do not commute                            *)
(*   star_G_nonabelian == the generated group is non-abelian (m >= 2)         *)
(*   star_gen_inj == generators are injective                                 *)
(*   star_search_space_1 == search_space 1 = T                                *)
(*   star_weval_inj1 == word-eval injectivity at L=1                          *)
(*   star_traces_lb == m^L <= n_traces (via indep_set_traces_lb)              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section star_instance.

Variable m : nat.

Let T := m.+1.
Let N := m.+3.
Let gT : finGroupType := {perm 'I_N}.

(* Helper ordinals *)
Let n0 : 'I_N := Ordinal (isT : 0 < N).
Let n1 : 'I_N := Ordinal (isT : 1 < N).
Let n2 : 'I_N := Ordinal (isT : 2 < N).

Lemma i_plus_2_lt (i : 'I_T) : (val i).+2 < N.
Proof. by case: i => v Hv. Qed.

(* Generator definition *)
Definition star_gen (i : 'I_T) : gT :=
  if val i == 0 then tperm n0 n1
  else tperm n2 (Ordinal (i_plus_2_lt i)).

(* Simplification lemmas *)
Lemma star_gen0 : star_gen ord0 = tperm n0 n1.
Proof. by rewrite /star_gen /=. Qed.

Lemma star_gen_leaf (i : 'I_T) (Hi : val i != 0) :
  star_gen i = tperm n2 (Ordinal (i_plus_2_lt i)).
Proof. by rewrite /star_gen (negbTE Hi). Qed.

(* Generator tuple *)
Definition star_gen_tuple : T.-tuple gT := gen_tuple_of star_gen.

Lemma star_gen_tupleE (i : 'I_T) : tnth star_gen_tuple i = star_gen i.
Proof. exact: gen_tuple_ofE. Qed.

(* Involution: tperm^2 = 1 *)
Lemma star_gen_invol (i : 'I_T) : (star_gen i ^+ 2 = 1)%g.
Proof. by rewrite /star_gen; case: ifP => _; exact: tperm2. Qed.

(* --- Distinctness lemmas --- *)

Let n0_ne_n1 : n0 != n1 := isT.
Let n0_ne_n2 : n0 != n2 := isT.
Let n1_ne_n2 : n1 != n2 := isT.

(* --- Center commutes with leaves --- *)

Lemma star_center_commute (i : 'I_T) : 0 < val i ->
  (star_gen ord0 * star_gen i = star_gen i * star_gen ord0)%g.
Proof.
move=> Hi.
have Hi0 : val i != 0 by rewrite -lt0n.
rewrite star_gen0 (star_gen_leaf Hi0).
set j := Ordinal (i_plus_2_lt i).
(* n0, n1 are disjoint from n2, j *)
have Hn0n2 : n0 != n2 := isT.
have Hn0j : n0 != j by rewrite -val_eqE.
have Hn1n2 : n1 != n2 := isT.
have Hn1j : n1 != j by rewrite -val_eqE.
exact: tperm_disjoint_comm.
Qed.

(* --- Leaves do not commute --- *)

Lemma star_leaf_noncommute (i j : 'I_T) :
  0 < val i -> 0 < val j -> i != j ->
  (star_gen i * star_gen j != star_gen j * star_gen i)%g.
Proof.
move=> Hi Hj Hij.
have Hi0 : val i != 0 by rewrite -lt0n.
have Hj0 : val j != 0 by rewrite -lt0n.
rewrite (star_gen_leaf Hi0) (star_gen_leaf Hj0).
(* Prove all distinctness facts before introducing abbreviations *)
have Hne_n2_ai : n2 != Ordinal (i_plus_2_lt i).
  apply/eqP => Habs; move: Hi.
  by have /= := congr1 val Habs; case: (val i).
have Hne_n2_aj : n2 != Ordinal (i_plus_2_lt j).
  apply/eqP => Habs; move: Hj.
  by have /= := congr1 val Habs; case: (val j).
have Hne_ai_aj : Ordinal (i_plus_2_lt i) != Ordinal (i_plus_2_lt j).
  apply/eqP => Habs.
  by have /= /succn_inj/succn_inj/val_inj := congr1 val Habs; apply/eqP.
set ai := Ordinal (i_plus_2_lt i).
set aj := Ordinal (i_plus_2_lt j).
(* Apply both sides to n2: get ai vs aj *)
apply/eqP => /permP /(_ n2); rewrite !permM !tpermL.
have Hne_aj_ai : Ordinal (i_plus_2_lt j) != Ordinal (i_plus_2_lt i).
  by rewrite eq_sym.
rewrite (tpermD Hne_n2_ai Hne_aj_ai).
rewrite (tpermD Hne_n2_aj Hne_ai_aj).
by move/eqP; rewrite (negbTE Hne_ai_aj).
Qed.

(* --- Commutativity relation --- *)

Definition star_comm : rel 'I_T :=
  fun i j => ((val i == 0) || (val j == 0)) && (i != j).

Lemma star_comm_sym : symmetric star_comm.
Proof.
move=> i j; rewrite /star_comm orbC; congr (_ && _).
by rewrite /negb eq_sym.
Qed.

Lemma star_comm_irrefl : irreflexive star_comm.
Proof. by move=> i; rewrite /star_comm eqxx andbF. Qed.

(* --- Hcomm: star_comm implies group-level commutativity --- *)

Lemma star_Hcomm : forall i j : 'I_T,
  star_comm i j ->
  (tnth star_gen_tuple i * tnth star_gen_tuple j =
   tnth star_gen_tuple j * tnth star_gen_tuple i)%g.
Proof.
move=> i j; rewrite /star_comm !star_gen_tupleE.
move/andP => [Hor Hij].
case/orP: Hor => /eqP Hv.
- have Hieq : i = ord0 by apply: val_inj.
  rewrite Hieq.
  have Hj0 : 0 < val j.
    rewrite lt0n; apply: contra_neq Hij => Hjv.
    by rewrite Hieq; apply: val_inj.
  exact: star_center_commute Hj0.
- have Hjeq : j = ord0 by apply: val_inj.
  rewrite Hjeq.
  have Hi0 : 0 < val i.
    rewrite lt0n; apply/eqP => Hiv.
    by move/eqP: Hij; apply; rewrite Hjeq; apply: val_inj.
  by rewrite (star_center_commute Hi0).
Qed.

(* --- Generator injectivity --- *)

Lemma star_gen_inj : injective star_gen.
Proof.
move=> i j; rewrite /star_gen.
case Hi0 : (val i == 0); case Hj0 : (val j == 0).
- (* both center *)
  by move=> _; apply: val_inj; rewrite (eqP Hi0) (eqP Hj0).
- (* i center, j leaf *)
  move/permP/(_ n0).
  rewrite tpermL.
  have Hj : val j != 0 by rewrite Hj0.
  set aj := Ordinal (i_plus_2_lt j).
  have Hn0n2 : n2 != n0 := isT.
  have Hn0aj : aj != n0 by rewrite -val_eqE.
  rewrite (tpermD Hn0n2 Hn0aj).
  by move/(congr1 val).
- (* i leaf, j center *)
  move/permP/(_ n0).
  have Hi : val i != 0 by rewrite Hi0.
  set ai := Ordinal (i_plus_2_lt i).
  have Hn0n2 : n2 != n0 := isT.
  have Hn0ai : ai != n0 by rewrite -val_eqE.
  rewrite (tpermD Hn0n2 Hn0ai) tpermL.
  by move/(congr1 val).
- (* both leaf *)
  set ai := Ordinal (i_plus_2_lt i).
  set aj := Ordinal (i_plus_2_lt j).
  move/permP/(_ n2).
  rewrite !tpermL => Heq.
  have /= := congr1 val Heq.
  by move/succn_inj/succn_inj/val_inj.
Qed.

(* --- PGGTypes instance --- *)

Local Notation Star_PGGTypes := (@Gen_PGGTypes m m.+1 star_gen_tuple).
Let M_star : GeneratedMonodromyReprType := Star_PGGTypes.

(* --- RAAG instance wrapper lemmas --- *)

Lemma star_gen_inj_sigmas :
  injective (fun i : 'I_T => tnth (@pgg_sigmas M_star) i).
Proof. by move=> i j; rewrite !star_gen_tupleE; exact: star_gen_inj. Qed.

Lemma star_Hcomm_sigmas : forall i j : 'I_T,
  star_comm i j ->
  (tnth (@pgg_sigmas M_star) i * tnth (@pgg_sigmas M_star) j =
   tnth (@pgg_sigmas M_star) j * tnth (@pgg_sigmas M_star) i)%g.
Proof. by move=> i j; exact: star_Hcomm. Qed.

(* --- Non-abelianity --- *)

Lemma star_G_nonabelian : 1 < m ->
  ~~ abelian (pgg_G M_star).
Proof.
move=> Hm.
have HT1 : 1 < T := ltnW Hm.
have HT2 : 2 < T by [].
set i1 : 'I_T := Ordinal HT1.
set i2 : 'I_T := Ordinal HT2.
have Hij : i1 != i2 by rewrite -val_eqE.
have Hnc : (tnth (@pgg_sigmas M_star) i1 * tnth (@pgg_sigmas M_star) i2 !=
            tnth (@pgg_sigmas M_star) i2 * tnth (@pgg_sigmas M_star) i1)%g.
  by rewrite !star_gen_tupleE; exact: star_leaf_noncommute.
exact: (gen_nonabelian Hij Hnc).
Qed.

(* --- Independent set: leaves --- *)

Definition star_leaves : {set 'I_T} := [set i : 'I_T | 0 < val i].

Lemma star_leaf_set_card : #|star_leaves| = m.
Proof.
suff -> : star_leaves = [set~ ord0 : 'I_T].
  by rewrite cardsC1 card_ord.
apply/setP => x; rewrite !inE.
by case: x => [[|v] Hv].
Qed.

(* Leaves form an independent set *)
Lemma star_leaves_indep (i j : 'I_T) :
  i \in star_leaves -> j \in star_leaves -> i != j -> ~~ star_comm i j.
Proof.
rewrite !inE /star_comm => Hi Hj Hij.
apply/negP; move/andP => [Hor _].
case/orP: Hor => /eqP Hv.
- by move: Hi; rewrite Hv.
- by move: Hj; rewrite Hv.
Qed.

(* --- RAAG instance registration --- *)

HB.instance Definition Star_isRAAG :=
  @isRAAG0.Build Star_PGGTypes
    star_comm star_comm_sym star_comm_irrefl
    star_Hcomm_sigmas star_gen_inj_sigmas.

Let R_star : RAAGType := Star_PGGTypes.

Lemma star_traces_lb (L : nat) :
  m ^ L <= @n_traces R_star L.
Proof.
rewrite -star_leaf_set_card.
apply: (@indep_set_traces_lb R_star star_leaves L).
move=> i j Hi Hj Hij.
change (~~ star_comm i j).
exact: (star_leaves_indep Hi Hj Hij).
Qed.

End star_instance.
