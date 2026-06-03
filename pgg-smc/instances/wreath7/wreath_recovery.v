(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: recovery core and covering scheme for Z_7 wr S_2                      *)
(*                                                                            *)
(* The T > k ramp. Two piles of seven cards, each carrying sum_mod on 'I_7    *)
(* (a perfect, position-symmetric secret sharing). The binary product glues   *)
(* them into one ThresholdScheme 'I_14 'I_14 with                             *)
(*   ts_T = 7 + 7 = 14,   ts_k = min 7 7 = 7,   gap = ts_T - ts_k = 7 > 0.     *)
(* The gap is born from the product (ts_T sums, ts_k is the min).             *)
(*                                                                            *)
(* Reconstruction is invariant only under the abelian core Z_7^2 =            *)
(* <<cut1, cut2>> of within-pile cuts (each preserves the pile partition),    *)
(* via product_sum_mod_perm_compatible. The pile swap wswap is NOT a recovery *)
(* symmetry, only a security/anonymity move, so it is excluded from           *)
(* cs_recon_symmetry. This is the cs_recon_symmetry decoupling in action.     *)
(*                                                                            *)
(* cd_genus = 4 is gap-bound bookkeeping (2 * 4 = 8 >= gap 7), not a curve     *)
(* genus; the Riemann-Hurwitz field cd_hurwitz holds for any group order.     *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
Require Import pgg_interface.
From pgg_smc Require Import pgg_wreath.
From pgg_reconstruct Require Import pgg_sharing_framework product_threshold
                                    covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Recovery core: the product of two perfect per-pile schemes             *)
(******************************************************************************)

(** pile7 — the per-pile perfect secret sharing on seven cards.
    Kind: instance.
    Why: each pile carries sum_mod on 'I_7 (ts_T = ts_k = 7); its
    reconstruction is a symmetric sum, invariant under any within-pile cut. *)
Definition pile7 : ThresholdScheme 'I_7 'I_7 := @sum_mod_scheme 5 6.

(** wreath2_scheme — the two-pile product on the 14-card deck.
    Kind: instance.
    Why: the recovery scheme of the wreath instance; its T > k gap is the
    privacy/recoverability headline. *)
Definition wreath2_scheme : ThresholdScheme 'I_14 'I_14 :=
  @product_scheme 5 5 pile7 pile7.

(** wreath2_T, wreath2_k, wreath2_gap — the T > k ramp, by computation.
    Kind: helper.
    Why: the recoverability headline (ts_T = 14 > ts_k = 7, gap 7).
    Used by: rigidity_wreath_instance (the vm_compute demos). *)
Lemma wreath2_T : ts_T wreath2_scheme = 14.
Proof. by []. Qed.

Lemma wreath2_k : ts_k wreath2_scheme = 7.
Proof. by []. Qed.

Lemma wreath2_gap : ts_k wreath2_scheme < ts_T wreath2_scheme.
Proof. by []. Qed.

(******************************************************************************)
(** * The reconstruction-symmetry core Z_7^2 preserves the pile partition    *)
(******************************************************************************)

(** ppred — predicate: a deck permutation keeps pile-1 cards in pile 1.
    Kind: helper.
    Why: the pile-preserving condition that product_sum_mod_perm_compatible
    needs; pile-preserving perms form a group containing the cuts.
    Used by: pp_group, wcore_pp. *)
Definition ppred (p : {perm 'I_14}) : bool :=
  [forall j : 'I_14, (val j < 7) ==> (val (p j) < 7)].

(** ppred_cut1, ppred_cut2 — each within-pile cut preserves pile 1.
    Kind: helper.
    Why: generators of the core lie in the pile-preserving group.
    Used by: wcore_sub_pp. *)
Lemma ppred_cut1 : ppred cut1.
Proof.
apply/forallP => j; apply/implyP; rewrite /cut1;
  case: j => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]] Hj;
  rewrite ?permM ?permE /=; by [].
Qed.

Lemma ppred_cut2 : ppred cut2.
Proof.
apply/forallP => j; apply/implyP; rewrite /cut2;
  case: j => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]] Hj;
  rewrite ?permM ?permE /=; by [].
Qed.

(** pp_group — pile-preserving permutations form a group.
    Kind: helper.
    Why: lets gen_subG lift pile preservation from the two generators to the
    whole core <<cut1, cut2>>.
    Used by: wcore_sub_pp. *)
Lemma pp_group : group_set [set p : {perm 'I_14} | ppred p].
Proof.
apply/group_setP; split.
  by rewrite inE /ppred; apply/forallP => j; apply/implyP => Hj; rewrite perm1.
move=> x y; rewrite !inE /ppred => /forallP Hx /forallP Hy.
apply/forallP => j; apply/implyP => Hj; rewrite permM.
by apply: (implyP (Hy (x j))); apply: (implyP (Hx j)).
Qed.

(** ppgrp — the pile-preserving permutations as a group object.
    Kind: instance.
    Why: target of the gen_subG containment for the core. *)
Definition ppgrp : {group {perm 'I_14}} := Group pp_group.

(** wcore — the abelian reconstruction-symmetry core Z_7^2 = <<cut1, cut2>>.
    Kind: instance.
    Why: the subgroup on which reconstruction is invariant; the within-pile
    cuts, NOT the pile swap. The load-bearing use of cs_recon_symmetry. *)
Definition wcore : {group pgg_gT M_wreath} := <<[set cut1; cut2]>>%G.

(** cut2_in_G — the second cut lies in the wreath group.
    Kind: helper.
    Why: completes the generator memberships for wcore_sub.
    Used by: wcore_sub. *)
Lemma cut2_in_G : cut2 \in pgg_G M_wreath.
Proof. have := sigmas_in_G (M := M_wreath) (@Ordinal 3 1 isT). by rewrite (tnth_nth 1%g). Qed.

(** wcore_sub — the core is a subgroup of the security group.
    Kind: helper.
    Why: discharges cs_recon_symmetry_sub.
    Used by: wreath_covering. *)
Lemma wcore_sub : wcore \subset pgg_G M_wreath.
Proof.
rewrite gen_subG; apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->].
  exact: cut1_in_G.
exact: cut2_in_G.
Qed.

(** wcore_sub_pp — the core preserves the pile partition.
    Kind: helper.
    Why: lifts ppred_cut1/ppred_cut2 to the whole generated core via gen_subG.
    Used by: wcore_pp. *)
Lemma wcore_sub_pp : wcore \subset ppgrp.
Proof.
rewrite gen_subG; apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->].
  exact: ppred_cut1.
exact: ppred_cut2.
Qed.

(** wcore_pp — every core element keeps pile-1 cards in pile 1.
    Kind: helper.
    Why: the preserves_pile1 hypothesis of product_sum_mod_perm_compatible.
    Used by: wreath_recon_inv. *)
Lemma wcore_pp (g : pgg_gT M_wreath) :
  g \in wcore -> forall i : 'I_14, (val i < 7)%N -> (val (g i) < 7)%N.
Proof.
move=> Hg i Hi.
have Hp : ppred g by move/(subsetP wcore_sub_pp): Hg; rewrite inE.
by apply: (implyP (forallP Hp i)).
Qed.

(******************************************************************************)
(** * Covering data (genus-4 bookkeeping) and the covering scheme            *)
(******************************************************************************)

(** wreath_ramif, wreath_hurwitz — the bare-nat side conditions of CoveringData.
    Kind: helper.
    Why: cd_genus = 4 is gap bookkeeping; cd_hurwitz holds for any group order
    once total_ramif = 2*|G| + 6.
    Used by: wreath_cdata. *)
Lemma wreath_ramif : (6 <= 2 * #|pgg_G M_wreath| + 6)%N.
Proof. by rewrite leq_addl. Qed.

Lemma wreath_hurwitz :
  2 * 4 + 2 * #|pgg_G M_wreath| =
  #|pgg_G M_wreath| * (2 * 0) + (2 * #|pgg_G M_wreath| + 6) + 2.
Proof. by rewrite muln0 muln0 add0n -addnA addnC. Qed.

(** wreath_cdata — the covering data with bookkeeping genus 4.
    Kind: instance.
    Why: cd_genus = 4 satisfies 2 * 4 >= gap 7 for cs_gap; not a curve genus. *)
Definition wreath_cdata : CoveringData M_wreath :=
  @MkCoveringData M_wreath 0 6 (2 * #|pgg_G M_wreath| + 6) 4
    wreath_ramif wreath_hurwitz.

(** wreath_scheme_T — the scheme's T' matches the declared cs_T'.
    Kind: helper.
    Why: discharges cs_scheme_T.
    Used by: wreath_covering. *)
Lemma wreath_scheme_T : ts_T' wreath2_scheme = 13.
Proof. by []. Qed.

(** wreath_recon_inv — reconstruction is invariant under the abelian core.
    Kind: main.
    Why: the cs_recon_invariant of the covering, via
    product_sum_mod_perm_compatible fed wcore_pp. The pile swap is excluded.
    Used by: wreath_covering. *)
Lemma wreath_recon_inv :
  ts_recon_perm_invariant (gT := pgg_gT M_wreath) (G := wcore)
    wreath2_scheme (fun g : pgg_gT M_wreath => g).
Proof.
apply: (@product_sum_mod_perm_compatible 5 5 6 6 (pgg_gT M_wreath) wcore
          (fun g : pgg_gT M_wreath => g)).
exact: wcore_pp.
Qed.

(** wreath_gap — the gap field: ts_T <= ts_k + 2 * genus, i.e. 14 <= 7 + 8.
    Kind: helper.
    Why: discharges cs_gap.
    Used by: wreath_covering. *)
Lemma wreath_gap :
  ts_T wreath2_scheme <= ts_k wreath2_scheme + 2 * cd_genus wreath_cdata.
Proof. by []. Qed.

(** wreath_covering — the curve-free covering scheme for Z_7 wr S_2.
    Kind: main.
    Why: packages the recovery scheme, the genus-4 bookkeeping, and the
    abelian-core recon-invariance into one CoveringScheme. The security group
    is the full wreath pgg_G M_wreath; the recon-symmetry is only wcore. *)
Definition wreath_covering : CoveringScheme M_wreath :=
  @MkCoveringScheme M_wreath
    wreath_cdata 13 wreath2_scheme wreath_scheme_T
    (fun g : pgg_gT M_wreath => g)
    wcore wcore_sub wreath_recon_inv wreath_gap.
