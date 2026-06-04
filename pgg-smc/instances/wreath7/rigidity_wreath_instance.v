(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: the CombinatorialRigidity instance for Z_7 wr S_2 and its protocol    *)
(*                                                                            *)
(* Bundles the three requirements into a single record and proves the         *)
(* headline order inequality and end-to-end protocol correctness:             *)
(*                                                                            *)
(*   wreath_pgl_lt_card   pgl_bound M_wreath = 60 < 98 = |G|  (security)       *)
(*   cd_genus = 4 > 0, gap ts_T-ts_k = 7                      (recoverability) *)
(*   wreath_rigidity      the CombinatorialRigidity value                      *)
(*   wreath_protocol_correct   recovery from G-stable starts under a cut       *)
(*                                                                            *)
(* The order inequality with a positive gap is the positive dual of s5_nogo:  *)
(* the wreath realises what no genus-zero curve can (cf. cr_large_group_with_  *)
(* gap). Unlike every prior instance, the PGGInterface is concrete            *)
(* (ord_tuple 14) and G_stable is proven, not assumed.                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import pgg_weval_inj pgg_wreath wreath_recovery
                            wreath_security wreath_program.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff combinatorial_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section rigidity_wreath.

Variable R : realType.

(** wreath_pgl_lt_card — the order inequality: the group exceeds the curve bound.
    Kind: main.
    Why: structural security headline. pgl_bound(deck 14) = maxn 28 60 = 60, and
    |G| = 98 (card_wreath), so 60 < 98. The single use of the card_wreath axiom. *)
Lemma wreath_pgl_lt_card : (pgl_bound M_wreath < #|pgg_G M_wreath|)%N.
Proof. by rewrite pgl_bound_unfold wreath_deck card_wreath. Qed.

(** wreath_genus_gt0 — the recovery gap is positive (bookkeeping genus 4).
    Kind: helper.
    Why: discharges cr_genus_gt0; with the order inequality it is the dual of
    s5_nogo. Used by: wreath_rigidity. *)
Lemma wreath_genus_gt0 : (0 < cd_genus (cs_data wreath_covering))%N.
Proof. by []. Qed.

(** wreath_rigidity — the CombinatorialRigidity value for Z_7 wr S_2.
    Kind: main.
    Why: certifies security (the quantitative witness), recovery (the covering
    with its gap), the positive genus, and the order inequality, in one record. *)
Definition wreath_rigidity : CombinatorialRigidity R M_wreath :=
  @MkCombinatorialRigidity R M_wreath
    (wreath_security_witness R) wreath_covering wreath_genus_gt0 wreath_pgl_lt_card.

(** wreath_order_inequality_and_gap — large group AND positive gap together.
    Kind: main.
    Why: the headline conjunction s5_nogo forbids for any genus-zero curve,
    obtained here from the wreath's CombinatorialRigidity. *)
Lemma wreath_order_inequality_and_gap :
  (pgl_bound M_wreath < #|pgg_G M_wreath|)%N /\
  (0 < cd_genus (cs_data (cr_covering wreath_rigidity)))%N.
Proof. exact: (cr_large_group_with_gap wreath_rigidity). Qed.

(******************************************************************************)
(*     Concrete interface and end-to-end protocol correctness                 *)
(******************************************************************************)

(** wreath_PI — the concrete two-pile-of-seven starting interface.
    Kind: instance.
    Why: the 14 starting card positions, in order. No prior instance built a
    concrete PGGInterface; the identity start tuple makes G_stable reflexivity. *)
Lemma wreath_starts_uniq : uniq (ord_tuple 14).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

Definition wreath_PI : PGGInterface M_wreath :=
  @MkPGGI M_wreath 13 (ord_tuple 14) wreath_starts_uniq.

(** wreath_HT — the scheme and interface party counts agree (both 13).
    Kind: helper.
    Why: the cast witness; kept as erefl so the tuple casts reduce away. *)
Definition wreath_HT : ts_T' wreath2_scheme = pi_T' wreath_PI := erefl.

(** wreath_G_stable — the monodromy permutes the starts as the share permutation.
    Kind: main.
    Why: the structural condition of protocol correctness, proven (not assumed).
    With starts = ord_tuple 14 and pgg_rho the identity inclusion, both sides
    equal g i. Closes the audit gap that G_stable was always a hypothesis. *)
Lemma wreath_G_stable :
  forall g, g \in wcore ->
  forall i : 'I_(ts_T' wreath2_scheme).+1,
    @pgg_rho M_wreath g
      (tnth (cast_tuple (esym (congr1 S wreath_HT)) (pi_starts wreath_PI)) i) =
    tnth (cast_tuple (esym (congr1 S wreath_HT)) (pi_starts wreath_PI)) (g i).
Proof.
move=> g Hg i.
by rewrite /pgg_rho /= !tnth_ord_tuple.
Qed.

(** wreath_protocol_correct — recovery of the dealt endpoints returns the secret.
    Kind: main.
    Why: the end-to-end protocol guarantee. For any hidden element P of the
    abelian core, reconstructing the revealed endpoints recovers the secret,
    via the generic pgg_hidden_invariant_perm fed the proven G_stable and the
    covering's recon-invariance. *)
Lemma wreath_protocol_correct (s : 'I_14) (P : pgg_gT M_wreath) :
  P \in wcore ->
  ts_valid wreath2_scheme s
    (cast_tuple (esym (congr1 S wreath_HT)) (pi_starts wreath_PI)) ->
  @pgg_recon_endpoints M_wreath wreath_PI wreath2_scheme wreath_HT P = s.
Proof.
move=> PG Hvalid.
apply: (@pgg_hidden_invariant_perm M_wreath wreath_PI wreath2_scheme wreath_HT
          wcore s P (fun g : pgg_gT M_wreath => g) wcore_sub wreath_G_stable PG
          Hvalid).
exact: wreath_recon_inv.
Qed.

(******************************************************************************)
(*     vm_compute demonstrations                                              *)
(******************************************************************************)

(** wreath_demo_* — the headline numbers, by computation.
    Kind: example.
    Why: the T > k ramp, the pgl bound, the order inequality, non-abelianness,
    surfaced as concrete checks. *)
Lemma wreath_demo_T : ts_T wreath2_scheme = 14.
Proof. by []. Qed.

Lemma wreath_demo_k : ts_k wreath2_scheme = 7.
Proof. by []. Qed.

Lemma wreath_demo_gap : (ts_k wreath2_scheme < ts_T wreath2_scheme)%N.
Proof. by []. Qed.

Lemma wreath_demo_pgl : pgl_bound M_wreath = 60.
Proof. by rewrite pgl_bound_unfold wreath_deck. Qed.

Lemma wreath_demo_nonabelian : ~~ abelian (pgg_G M_wreath).
Proof. exact: wreath_nonabelian. Qed.

(******************************************************************************)
(*     Complexity bounds (S_5-parity derived lemmas)                          *)
(******************************************************************************)

(** wreath_complexity — the brute-force search space is bounded by the group.
    Kind: helper.
    Why: the S_5-parity bound (mirror of s5_complexity); the L-round search
    space never exceeds |G| = 98. Used by: tightness arguments for the wreath. *)
Lemma wreath_complexity (L : nat) :
  (@search_space M_wreath L <= #|pgg_G M_wreath|)%N.
Proof. exact: search_space_leG. Qed.

(* No wreath analogue of s5_search_chain: that chain bounds search_space by
   n_traces (Cartier-Foata traces), which is defined for a RAAGType. Z_7 wr S_2
   is NOT a right-angled Artin group (cut1 has order 7, so the group has
   torsion, whereas RAAGs are torsion-free), so the trace machinery does not
   apply. The generic group bound wreath_complexity above is the part that
   transfers. *)

End rigidity_wreath.
