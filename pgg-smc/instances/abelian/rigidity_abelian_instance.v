(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Abelian (Disjoint Transpositions) Algebraic Rigidity Instance              *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the abelian group     *)
(* Z/2Z x Z/2Z acting on 4 sheets via two disjoint transpositions            *)
(* sigma_1 = (0 1) and sigma_2 = (2 3).                                      *)
(*                                                                            *)
(* This instance demonstrates:                                                *)
(*   - Abelian (commutative) generators with L = 1                           *)
(*   - All generators commute, so round complexity = 1 in RAAG sense          *)
(*   - Group = {id, (01), (23), (01)(23)} with |G| = 4                       *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 2 (generators), N = 4 (sheets), L = 1, depth = 1                  *)
(*   epsilon_DPI = 2 * (4! - 2) / 4! = 44/24                                *)
(*                                                                            *)
(* Note: a tighter endpoint bound is achievable by direct computation.        *)
(* For s=0: endpoint dist is {0 -> 1/2, 1 -> 1/2}, giving epsilon = 1.0.    *)
(* The DPI bound (44/24 ~ 1.83) is conservative.                             *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   abel_sigmas_distinct : generators are distinct permutations             *)
(*   abel_weval_inj1 : word-eval injectivity at L=1                          *)
(*   abel_security_witness_direct_1 : SecurityWitness (via endpoint_inj)     *)
(*   abel_rigidity : AlgebraicRigidity (security + threshold)                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Generator Definitions                                                  *)
(******************************************************************************)

(* Two disjoint transpositions on 'I_4:
   sigma_1 = (0 1) : swaps sheets 0 and 1
   sigma_2 = (2 3) : swaps sheets 2 and 3
   These commute because their supports are disjoint. *)

Definition abel_s1 : {perm 'I_4} :=
  tperm (Ordinal (n:=4) (isT : (0 < 4)%N))
        (Ordinal (n:=4) (isT : (1 < 4)%N)).

Definition abel_s2 : {perm 'I_4} :=
  tperm (Ordinal (n:=4) (isT : (2 < 4)%N))
        (Ordinal (n:=4) (isT : (3 < 4)%N)).

Definition abel_sigmas : 2.-tuple {perm 'I_4} :=
  [tuple abel_s1; abel_s2].

(* Generators are distinct permutations *)
Lemma abel_s1_neq_s2 : abel_s1 != abel_s2.
Proof.
apply/eqP => Habs.
have := congr1 (fun sigma : {perm 'I_4} =>
  sigma (Ordinal (n:=4) (isT : (0 < 4)%N))) Habs.
by rewrite /abel_s1 tpermL /abel_s2 tpermD.
Qed.

Lemma abel_sigmas_distinct :
  injective (fun i : 'I_2 => tnth abel_sigmas i).
Proof.
move=> i j Heq; apply val_inj.
move: Heq; rewrite /abel_sigmas (tnth_nth abel_s1) (tnth_nth abel_s1).
case: i => [[|[|i]] Hi] //; case: j => [[|[|j]] Hj] //= Habs;
  exfalso; move/eqP: abel_s1_neq_s2; apply;
  first [exact: Habs | exact: esym Habs].
Qed.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section abel_security.

Variable R : realType.

Let M_abel := @Gen_PGGTypes 1 2 abel_sigmas.
Let R_abel : GeneratedMonodromyReprType := M_abel.

(* Word-eval injectivity at L=1: follows from generator injectivity *)
Lemma abel_weval_inj1 : @weval_inj M_abel 1.
Proof. exact: gen_inj_weval_inj1 abel_sigmas_distinct. Qed.

(* Direct endpoint SecurityWitness at L=1.
   Epsilon = 2*(4-2)/4 = 1.0, tighter than DPI bound 44/24 ≈ 1.83.
   Proof: (01) and (23) have disjoint support, so they map every sheet
   to distinct values. *)
Lemma abel_perm_endpoint_inj1 :
  forall s : 'I_4,
  {in @achievable M_abel 1 &,
   injective (fun sigma : {perm 'I_4} => sigma s)}.
Proof.
move=> s x y Hx Hy Hf; move: Hf.
rewrite /achievable in Hx Hy.
case/imsetP: Hx => wx _ ->.
case/imsetP: Hy => wy _ ->.
rewrite /word_eval !big_ord_recr !big_ord0 /= !mul1g => Hf.
move: (tnth wx ord_max) (tnth wy ord_max) Hf => i j.
rewrite /pgg_sigmas /abel_sigmas !(tnth_nth abel_s1) /=.
case: i => [[|[|i]] Hi]; case: j => [[|[|j]] Hj] //=;
  rewrite /abel_s1 /abel_s2;
  case: s => [[|[|[|[|s]]]] Hs] //= => Hf;
  by have := congr1 val Hf; rewrite !permE.
Qed.

Definition abel_security_witness_direct_1 : SecurityWitness R R_abel :=
  security_witness_endpoint_inj R abel_weval_inj1 abel_perm_endpoint_inj1.

End abel_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section abel_rigidity.

Variable R : realType.

Let R_abel : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 1 2 abel_sigmas.

(* Group nontriviality *)
Hypothesis HG_abel : (1 < #|pgg_G R_abel|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = 4 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_abel).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT R_abel -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_abel -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_abel ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition abel_covering : CoveringScheme R_abel :=
  genus0_covering HG_abel qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis abel_genus0_pgl :
  (#|pgg_G R_abel| <= pgl_bound R_abel)%N.

Definition abel_threshold_witness : ThresholdWitness R_abel :=
  @MkThresholdWitness R_abel abel_covering (fun _ => abel_genus0_pgl).

Definition abel_rigidity : AlgebraicRigidity R R_abel :=
  @MkAlgebraicRigidity R R_abel
    (abel_security_witness_direct_1 R)
    abel_threshold_witness.

(* Derived properties *)

Lemma abel_complexity (L : nat) :
  (@search_space R_abel L <= #|pgg_G R_abel|)%N.
Proof. exact: search_space_leG. Qed.

Lemma abel_tradeoff :
  let cs := tw_covering (ar_threshold abel_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_abel| <= pgl_bound R_abel)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_abel abel_covering
                                     (fun _ => abel_genus0_pgl)).
Qed.

End abel_rigidity.
