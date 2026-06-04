(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Cryptographically-secure CombinatorialRigidity for Z_7 wr S_2              *)
(*                                                                            *)
(* The S_5 instance carries TWO rigidity records: s5_rigidity (the fiber       *)
(* security witness, eps = 6/5 at L = 1) and s5_rigidity_cryptographically_    *)
(* secure (the spectral Schreier witness, eps -> 0). This file gives the       *)
(* wreath the same upgrade: a CombinatorialRigidity whose security witness is   *)
(* the vanishing spectral asymptotic (wreath_security_witness_asymptotic),     *)
(* instead of the L = 1 fiber bound (eps = 11/7) carried by wreath_rigidity.    *)
(*                                                                            *)
(* Because the wreath cuts are 7-cycles, the spectral witness lives on the     *)
(* inverse-closed presentation M_wreath_sym (see wreath_mixing.v), so the       *)
(* covering must move there too. The covering, the genus-4 bookkeeping, the     *)
(* abelian-core recon-invariance, and the order inequality all transfer from    *)
(* M_wreath verbatim: M_wreath_sym is the SAME group (wreath_sym_same_group),   *)
(* on the SAME 14-card deck, with the SAME threshold scheme wreath2_scheme.     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import pgg_wreath wreath_recovery wreath_mixing.
From pgg_reconstruct Require Import pgg_sharing_framework product_threshold
                                    covering_scheme cover_tradeoff
                                    combinatorial_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section wreath_crypto_rigidity.

Variable R : realType.

(** wreath_sym_deck — the symmetric-presentation deck has 14 cards.
    Kind: helper. Why: feeds the pgl bound. Used by: wreath_pgl_lt_card_sym. *)
Lemma wreath_sym_deck : (pgg_N' M_wreath_sym).+1 = 14.
Proof. by []. Qed.

(** wreath_ramif_sym, wreath_hurwitz_sym — the nat side conditions of the
    covering data at M_wreath_sym (mirror of wreath_ramif / wreath_hurwitz).
    Kind: helper. Why: discharge the CoveringData obligations. Used by:
    wreath_cdata_sym. *)
Lemma wreath_ramif_sym : (6 <= 2 * #|pgg_G M_wreath_sym| + 6)%N.
Proof. by rewrite leq_addl. Qed.

Lemma wreath_hurwitz_sym :
  2 * 4 + 2 * #|pgg_G M_wreath_sym| =
  #|pgg_G M_wreath_sym| * (2 * 0) + (2 * #|pgg_G M_wreath_sym| + 6) + 2.
Proof. by rewrite muln0 muln0 add0n -addnA addnC. Qed.

(** wreath_cdata_sym — the covering data (bookkeeping genus 4) at M_wreath_sym.
    Kind: instance. Why: the genus side of the covering, retyped at the
    symmetric presentation. *)
Definition wreath_cdata_sym : CoveringData M_wreath_sym :=
  @MkCoveringData M_wreath_sym 0 6 (2 * #|pgg_G M_wreath_sym| + 6) 4
    wreath_ramif_sym wreath_hurwitz_sym.

(** wreath_scheme_T_sym — the scheme's party count matches cs_T'.
    Kind: helper. Why: discharges cs_scheme_T. Used by: wreath_covering_sym. *)
Lemma wreath_scheme_T_sym : ts_T' wreath2_scheme = 13.
Proof. by []. Qed.

(** wreath_recon_inv_sym — reconstruction is invariant under the abelian core,
    at M_wreath_sym (same statement and proof as wreath_recon_inv).
    Kind: main. Why: the cs_recon_invariant of the transferred covering. The
    deck, scheme, core, and permutation predicate are unchanged. Used by:
    wreath_covering_sym. *)
Lemma wreath_recon_inv_sym :
  ts_recon_perm_invariant (gT := pgg_gT M_wreath_sym) (G := wcore)
    wreath2_scheme (fun g : pgg_gT M_wreath_sym => g).
Proof.
apply: (@product_sum_mod_perm_compatible 5 5 6 6 (pgg_gT M_wreath_sym) wcore
          (fun g : pgg_gT M_wreath_sym => g)).
exact: wcore_pp.
Qed.

(** wreath_gap_sym — the gap field 14 <= 7 + 2*4 at M_wreath_sym.
    Kind: helper. Why: discharges cs_gap. Used by: wreath_covering_sym. *)
Lemma wreath_gap_sym :
  ts_T wreath2_scheme <= ts_k wreath2_scheme + 2 * cd_genus wreath_cdata_sym.
Proof. by []. Qed.

(** wcore_sub_sym — the abelian core lies in the symmetric group, via the
    group equality wreath_sym_same_group.
    Kind: helper. Why: discharges the cs recon-symmetry subset obligation.
    Used by: wreath_covering_sym. *)
Lemma wcore_sub_sym : wcore \subset pgg_G M_wreath_sym.
Proof. rewrite wreath_sym_same_group; exact: wcore_sub. Qed.

(** wreath_covering_sym — the curve-free covering scheme at M_wreath_sym.
    Kind: main. Why: the recovery side of the cryptographically-secure rigidity,
    transferred from wreath_covering to the spectral presentation. *)
Definition wreath_covering_sym : CoveringScheme M_wreath_sym :=
  @MkCoveringScheme M_wreath_sym
    wreath_cdata_sym 13 wreath2_scheme wreath_scheme_T_sym
    (fun g : pgg_gT M_wreath_sym => g)
    wcore wcore_sub_sym wreath_recon_inv_sym wreath_gap_sym.

(** wreath_genus_gt0_sym — the recovery gap is positive (genus 4).
    Kind: helper. Why: discharges cr_genus_gt0. Used by:
    wreath_rigidity_cryptographically_secure. *)
Lemma wreath_genus_gt0_sym : (0 < cd_genus (cs_data wreath_covering_sym))%N.
Proof. by []. Qed.

(** wreath_pgl_lt_card_sym — the order inequality at M_wreath_sym: the group
    (98) exceeds the curve bound (60).
    Kind: main. Why: discharges cr_pgl_lt_card; pgl_bound depends only on the
    14-card deck, and the group order transfers via wreath_sym_same_group. *)
Lemma wreath_pgl_lt_card_sym :
  (pgl_bound M_wreath_sym < #|pgg_G M_wreath_sym|)%N.
Proof.
by rewrite pgl_bound_unfold wreath_sym_deck wreath_sym_same_group card_wreath.
Qed.

(** wreath_rigidity_cryptographically_secure — the wreath rigidity carrying the
    vanishing spectral witness, the parity of s5_rigidity_cryptographically_
    secure.
    Kind: instance.
    Why: certifies the wreath with the strong (asymptotic, eps -> 0) security
    witness rather than the L = 1 fiber bound of wreath_rigidity, together with
    the transferred covering, positive genus, and order inequality. The word
    length 285 mirrors the S_5 40-bit choice. *)
Definition wreath_rigidity_cryptographically_secure :
    CombinatorialRigidity R M_wreath_sym :=
  @MkCombinatorialRigidity R M_wreath_sym
    (wreath_security_witness_asymptotic R 285)
    wreath_covering_sym wreath_genus_gt0_sym wreath_pgl_lt_card_sym.

End wreath_crypto_rigidity.
