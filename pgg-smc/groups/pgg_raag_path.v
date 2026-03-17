(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.

(******************************************************************************)
(* PGG-SMC: Path-Graph RAAG Instance                                         *)
(* Group presentation: <g_0,...,g_m | g_i g_j = g_j g_i for |i-j| >= 2>     *)
(*                                                                            *)
(* T = m+1 generators on N = m+2 sheets.  Generator i = tperm i (i+1).       *)
(* Generators commute iff |i-j| >= 2 (disjoint supports).                    *)
(*                                                                            *)
(*   path_gen i == tperm (ordinal i) (ordinal (i+1))                          *)
(*   path_comm i j == |i-j| >= 2                                              *)
(*   path_gen_inj == generators are injective                                 *)
(*   path_weval_inj1 == word-eval injectivity at L=1 (via gen_inj_weval_inj1) *)
(*   path_G_nonabelian == non-abelian for m >= 1 (via gen_nonabelian)         *)
(*   path_traces_lb == 2^L <= n_traces (adjacent pair forms indep set)        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section path_instance.

Variable m : nat.

Let T := m.+1.
Let N := m.+2.
Let gT : finGroupType := {perm 'I_N}.

(* Ordinal constructors *)
Definition path_lo (i : 'I_T) : 'I_N :=
  Ordinal (ltn_trans (ltn_ord i) (ltnSn _)).

Definition path_hi (i : 'I_T) : 'I_N :=
  Ordinal (ltn_ord i : (val i).+1 < N).

(* Generator: tperm i (i+1) *)
Definition path_gen (i : 'I_T) : gT := tperm (path_lo i) (path_hi i).

(* Generator tuple *)
Definition path_gen_tuple : T.-tuple gT := gen_tuple_of path_gen.

Lemma path_gen_tupleE (i : 'I_T) : tnth path_gen_tuple i = path_gen i.
Proof. exact: gen_tuple_ofE. Qed.

(* --- Generator injectivity --- *)

Lemma path_gen_inj : injective path_gen.
Proof.
move=> i j; rewrite /path_gen => /permP Heq.
(* Evaluate at path_lo i: tperm maps i to i+1 *)
have H1 := Heq (path_lo i).
rewrite tpermL in H1.
(* Evaluate at path_hi i: tperm maps i+1 to i *)
have H2 := Heq (path_hi i).
rewrite tpermR in H2.
(* From H1: tperm j (j+1) (i) = i+1
   From H2: tperm j (j+1) (i+1) = i
   The tperm j (j+1) permutation moves exactly {j, j+1}.
   If i is not in {j, j+1}, H1 gives i = i+1, contradiction.
   So i = j or i = j+1. Similarly i+1 = j or i+1 = j+1. *)
have [Hlo_eq | Hne1] := eqVneq (path_lo i) (path_lo j).
  by apply: val_inj; have /= := congr1 val Hlo_eq.
have [Heq1 | Hne2] := eqVneq (path_lo i) (path_hi j).
  (* path_lo i = path_hi j, so val i = (val j).+1 *)
  rewrite -Heq1 tpermR in H1.
  (* Now H1 : path_lo j = path_hi i *)
  exfalso.
  have /= V1 : val i = (val j).+1 := congr1 val Heq1.
  have /= V2 : (val i).+1 = val j := congr1 val H1.
  suff Habs : (val j).+2 = val j.
    by have : val j < (val j).+2 by []; rewrite Habs ltnn.
  by rewrite -V1 V2.
(* i not in {j, j+1}: tperm fixes i, so H1 gives i = i+1, absurd *)
exfalso.
have Hne1' : path_lo j != path_lo i by rewrite eq_sym.
have Hne2' : path_hi j != path_lo i by rewrite eq_sym.
rewrite (tpermD Hne1' Hne2') in H1.
have : path_hi i != path_lo i by rewrite -val_eqE /= gtn_eqF // ltnSn.
by rewrite H1 eqxx.
Qed.

(* --- PGGTypes instance --- *)

Local Notation Path_PGGTypes := (@Gen_PGGTypes m m path_gen_tuple).
Let M_path : GeneratedMonodromyReprType := Path_PGGTypes.

(* --- Commutativity relation --- *)

Definition path_comm : rel 'I_T :=
  fun i j => (1 < (val i - val j) + (val j - val i))%N.

Lemma path_comm_sym : symmetric path_comm.
Proof. by move=> i j; rewrite /path_comm addnC. Qed.

Lemma path_comm_irrefl : irreflexive path_comm.
Proof. by move=> i; rewrite /path_comm subnn. Qed.

Lemma path_comm_dist2 (i j : 'I_T) :
  path_comm i j ->
  (val i - val j) + (val j - val i) >= 2.
Proof. by []. Qed.

Lemma path_dist_neq (a b : nat) : (a - b) + (b - a) >= 2 -> a != b.
Proof. by case: (a =P b) => [-> | //]; rewrite subnn. Qed.

Lemma path_dist_neqS (a b : nat) : (a - b) + (b - a) >= 2 -> a != b.+1.
Proof.
move=> Hge; apply/eqP => Hab; rewrite Hab in Hge.
have H1 : b.+1 - b = 1 by rewrite subSn ?leqnn // subnn.
have H2 : b - b.+1 = 0 by apply/eqP; rewrite subn_eq0.
by rewrite H1 H2 addn0 in Hge.
Qed.

Lemma path_Hcomm : forall i j : 'I_T,
  path_comm i j ->
  (tnth path_gen_tuple i * tnth path_gen_tuple j =
   tnth path_gen_tuple j * tnth path_gen_tuple i)%g.
Proof.
move=> i j Hc; rewrite !path_gen_tupleE /path_gen.
have Hdist := path_comm_dist2 Hc.
have Hdist' : (val j - val i) + (val i - val j) >= 2 by rewrite addnC.
apply: tperm_disjoint_comm; rewrite -val_eqE /=.
- exact: path_dist_neq Hdist.
- exact: path_dist_neqS Hdist.
- by rewrite eq_sym; exact: path_dist_neqS Hdist'.
- by rewrite eqSS; exact: path_dist_neq Hdist.
Qed.

(* --- RAAG instance wrapper lemmas --- *)

Lemma path_gen_inj_sigmas :
  injective (fun i : 'I_T => tnth (@pgg_sigmas M_path) i).
Proof. by move=> i j; rewrite !path_gen_tupleE; exact: path_gen_inj. Qed.

Lemma path_Hcomm_sigmas : forall i j : 'I_T,
  path_comm i j ->
  (tnth (@pgg_sigmas M_path) i * tnth (@pgg_sigmas M_path) j =
   tnth (@pgg_sigmas M_path) j * tnth (@pgg_sigmas M_path) i)%g.
Proof. by move=> i j; exact: path_Hcomm. Qed.

(* --- Non-abelianity (via generic) --- *)

Lemma path_adj_noncommute (Hm : 0 < m) :
  let i0 : 'I_T := Ordinal (isT : 0 < T) in
  let i1 : 'I_T := Ordinal (Hm : 1 < T) in
  (path_gen i0 * path_gen i1 != path_gen i1 * path_gen i0)%g.
Proof.
rewrite /=.
set i0 : 'I_T := Ordinal (isT : 0 < T).
set i1 : 'I_T := Ordinal (Hm : 1 < T).
rewrite /path_gen.
apply/eqP => /permP /(_ (path_lo i0)).
rewrite !permM.
have H01 : path_lo i0 != path_lo i1 by rewrite -val_eqE.
have H02 : path_lo i0 != path_hi i1 by rewrite -val_eqE.
have Hne01' : path_lo i1 != path_lo i0 by rewrite eq_sym.
have Hne02' : path_hi i1 != path_lo i0 by rewrite eq_sym.
rewrite (tpermD Hne01' Hne02') !tpermL.
have H_hi0_lo1 : path_hi i0 = path_lo i1 by apply: val_inj.
rewrite H_hi0_lo1 tpermL.
by move/(congr1 val).
Qed.

Lemma path_G_nonabelian : 0 < m ->
  ~~ abelian (pgg_G Path_PGGTypes).
Proof.
move=> Hm.
set i0 : 'I_T := Ordinal (isT : 0 < T).
set i1 : 'I_T := Ordinal (Hm : 1 < T).
have Hij : i0 != i1 by rewrite -val_eqE.
have Hnc : (tnth (@pgg_sigmas M_path) i0 * tnth (@pgg_sigmas M_path) i1 !=
            tnth (@pgg_sigmas M_path) i1 * tnth (@pgg_sigmas M_path) i0)%g.
  by rewrite !path_gen_tupleE; exact: path_adj_noncommute.
exact: (gen_nonabelian Hij Hnc).
Qed.

(* --- Independent set: any adjacent pair {i, i+1} --- *)

Lemma path_indep_pair (Hm : 0 < m) :
  let I : {set 'I_T} := [set Ordinal (isT : 0 < T); Ordinal (Hm : 1 < T)] in
  forall i j : 'I_T, i \in I -> j \in I -> i != j -> ~~ path_comm i j.
Proof.
move=> /= i j; rewrite !inE => /orP [] /eqP -> /orP [] /eqP -> // _ /=;
  rewrite /path_comm /=;
  by rewrite (eqP (subn_eq0 (isT : 0 <= 1))) add0n addn0.
Qed.

(* --- RAAG instance registration --- *)

HB.instance Definition Path_isRAAG :=
  @isRAAG0.Build Path_PGGTypes
    path_comm path_comm_sym path_comm_irrefl
    path_Hcomm_sigmas path_gen_inj_sigmas.

Let R_path : RAAGType := Path_PGGTypes.

Lemma path_traces_lb (L : nat) : 0 < m ->
  2 ^ L <= @n_traces R_path L.
Proof.
move=> Hm.
set I : {set 'I_T} := [set Ordinal (isT : 0 < T); Ordinal (Hm : 1 < T)].
have Hcard : #|I| = 2.
  by rewrite cards2 -val_eqE.
rewrite -Hcard.
apply: (@indep_set_traces_lb R_path I L).
move=> i j Hi Hj Hij.
change (~~ path_comm i j).
exact: (@path_indep_pair Hm i j Hi Hj Hij).
Qed.

End path_instance.
