(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abel_profile: the abelian (insecure) plug of the shared program            *)
(*                                                                            *)
(* Relocated from the wreath7 contrast file. The plug uses a sum-mod scheme on *)
(* the 4 abelian sheets with the identity content readout, the abelian         *)
(* monodromy pgg_rho, and a reconstruction invariance proved by the same       *)
(* group-agnostic argument as s5_sum_mod_perm_compatible. The differentiator   *)
(* from the secure plugs is the GROUP (commuting generators), not the scheme.  *)
(*                                                                            *)
(* The protocol interface of the profile is abel_PI, the four-seat interface   *)
(* whose starting layout is the four card positions in canonical order. Its    *)
(* seat count pi_T' = 3 is the share count ts_T' abel_ts of the sum-mod scheme *)
(* the plug carries, so an ExecutionPlug over this profile has its seat/share  *)
(* bridge at erefl. The two-generator value Gen_PGG_2 abel_sigmas keeps its    *)
(* group-level role of naming the two generators and is not the mp_PI of any   *)
(* protocol profile: its pi_T' is 1, so the bridge 1 = 3 has no proof.         *)
(*                                                                            *)
(* The file also carries the concrete description of the generated group: the  *)
(* two generators are disjoint transpositions, so they are commuting           *)
(* involutions and the group they generate is the Klein four-group             *)
(* {1, s1, s2, s1 s2}, of order four and abelian.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_ts             == the sum-mod threshold scheme on the four sheets    *)
(*   abel_plug           == the abelian reconstruction plug                    *)
(*   abel_PI             == the four-seat abelian protocol interface           *)
(*   abel_profile        == the abelian MonodromyProfile                       *)
(*   abel_G4             == the set {1, s1, s2, s1 s2} of permutations         *)
(*                                                                            *)
(* Key results, one entry per @main declaration:                              *)
(*   profile_k_abel      == the plug's privacy threshold is four               *)
(*   abel_gens_commute   == the two generators commute                         *)
(*   abel_G4_group_set   == abel_G4 is a subgroup                              *)
(*   abel_pgg_GE         == the generated group is abel_G4                     *)
(*   abel_G4_card        == abel_G4 has four elements                          *)
(*   abel_pgg_G_card     == the generated group has four elements              *)
(*   abel_G_abelian      == the generated group is abelian                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_abelian.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_ts, abel_plug and abel_profile are built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(** abel_ts — sum-mod threshold scheme on the 4 abelian sheets, one share per
    sheet (k = 4). Kind: instance. What: @sum_mod_scheme 2 3 : ThresholdScheme
    'I_4 'I_4 (ts_T' = 3, so the share-index space 'I_4 matches the sheet space
    that the abelian monodromy pgg_rho permutes). Why: the plain scheme for the
    abelian plug; the differentiator from the secure plugs is the group, not the
    scheme. Used-by: abel_plug.
    @intent: sum_mod_scheme at two sheets' worth of successor numerals, giving
    four shares over 'I_4. *)
Definition abel_ts : ThresholdScheme 'I_4 'I_4 := @sum_mod_scheme 2 3.

(** abel_sum_mod_perm_compatible — sum-mod reconstruction is invariant under the
    abelian monodromy. Kind: helper. What: ts_recon_perm_invariant over
    pgg_G (Gen_PGGTypes abel_sigmas) for abel_ts and pgg_rho. Why: the
    rp_recon_invariant field of abel_plug; the proof is the group-agnostic
    single-reindex argument shared with s5_sum_mod_perm_compatible. Used-by:
    abel_plug.
    Naming: the name spells the scheme (sum_mod), the transported structure
    (perm) and the property (compatible), matching the sibling
    s5_sum_mod_perm_compatible; no MathComp suffix names this shape.
    @composes: abel_plug *)
Lemma abel_sum_mod_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G (@Gen_PGGTypes 1 2 abel_sigmas)) _ _ abel_ts
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)).
Proof.
move=> g s shares Hg Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry.
rewrite (reindex_inj (@perm_inj _ (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas) g))).
by apply: eq_bigr.
Qed.

(** abel_plug — the abelian reconstruction plug. Kind: instance. What: abel_ts +
    id content + abelian monodromy + abel_sum_mod_perm_compatible. Why: routes
    the abelian (insecure) example through the general MonodromyProfile program.
    Used-by: abel_profile.
    @intent: MkReconPlug at abel_M with scheme abel_ts, identity content
    readout, monodromy pgg_rho and invariance abel_sum_mod_perm_compatible. *)
Definition abel_plug : ReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) 'I_4 :=
  @MkReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) 'I_4 abel_ts id
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)) abel_sum_mod_perm_compatible.

(** abel_starts_uniq — the four canonical starting card positions are
    distinct.
    @composes: abel_PI *)
Lemma abel_starts_uniq : uniq (ord_tuple 4).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** abel_PI — the four-seat abelian protocol interface.
    @intent: MkPGGI at abel_M with pi_T' = 3 and the four card positions
    0, 1, 2, 3 in canonical order as the starting layout. *)
Definition abel_PI : PGGInterface abel_M :=
  @MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq.

(** abel_profile — plug the abelian Z_2 x Z_2 (N = 4), paired with sum-mod.
    Kind: instance. What: the MonodromyProfile bundling the group, the secret
    type 'I_4, the four-seat interface abel_PI and abel_plug. Why: the insecure
    plug; commuting generators, k = 4, the contrast to the secure plugs. The
    seat count of abel_PI is the share count of abel_ts, so the seat/share
    bridge of an execution over this profile is erefl; the two-generator value
    Gen_PGG_2 abel_sigmas has seat count 1 and is not used here.
    Used-by: abelian_exec, contrast demos.
    @intent: MkMonodromyProfile at the abelian group, the secret type 'I_4,
    the four-seat interface abel_PI and abel_plug. *)
Definition abel_profile : MonodromyProfile :=
  @MkMonodromyProfile abel_M 'I_4 abel_PI abel_plug.

(** profile_k_abel — the abelian plug's privacy threshold is 4 (one share per
    sheet).
    @main bound: contrast character against the S_5 plug's k = 5, read off
    the shared profile_k. *)
Lemma profile_k_abel : profile_k abel_profile = 4.
Proof. by []. Qed.

(** abel_gens_commute — the abelian plug's generators commute.
    Kind: main. What: commute abel_s1 abel_s2. Why: the structural root of the
    insecure character (commuting shuffles do not mix, eps floors), the opposite
    of the non-abelian secure plugs. Used-by: abelian security narrative.
    @main architecture: commute abel_s1 abel_s2, the two generators being
    disjoint transpositions of the four sheets. *)
Lemma abel_gens_commute : commute abel_s1 abel_s2.
Proof.
apply/permP => x; rewrite !permM /abel_s1 /abel_s2.
by case: x => -[|[|[|[|x]]]] Hx; rewrite ?permE.
Qed.

(******************************************************************************)
(*     The Klein four-group generated by the two disjoint transpositions      *)
(******************************************************************************)

(** abel_G4 — the four-element set {1, s1, s2, s1 s2}.
    @intent: the concrete carrier of the group generated by the two disjoint
    transpositions, the support of the uniform distribution the abelian
    shuffle-analysis models are compared against. *)
Definition abel_G4 : {set {perm 'I_4}} :=
  [set 1%g; abel_s1; abel_s2; (abel_s1 * abel_s2)%g].

(** abel_s1K — the first generator is an involution.
    @composes: abel_G4_group_set *)
Lemma abel_s1K : (abel_s1 * abel_s1 = 1)%g.
Proof. exact: tperm2. Qed.

(** abel_s2K — the second generator is an involution.
    @composes: abel_G4_group_set *)
Lemma abel_s2K : (abel_s2 * abel_s2 = 1)%g.
Proof. exact: tperm2. Qed.

(** abel_s21 — the two generators commute, in product form.
    @composes: abel_G4_group_set *)
Lemma abel_s21 : (abel_s2 * abel_s1)%g = (abel_s1 * abel_s2)%g.
Proof. exact: esym abel_gens_commute. Qed.

(** abel_s1_s1s2 — s1 (s1 s2) = s2.
    @composes: abel_G4_group_set *)
Lemma abel_s1_s1s2 : (abel_s1 * (abel_s1 * abel_s2))%g = abel_s2.
Proof. by rewrite mulgA abel_s1K mul1g. Qed.

(** abel_s2_s1s2 — s2 (s1 s2) = s1.
    @composes: abel_G4_group_set *)
Lemma abel_s2_s1s2 : (abel_s2 * (abel_s1 * abel_s2))%g = abel_s1.
Proof. by rewrite mulgA abel_s21 -mulgA abel_s2K mulg1. Qed.

(** abel_s1s2_s1 — (s1 s2) s1 = s2.
    @composes: abel_G4_group_set *)
Lemma abel_s1s2_s1 : (abel_s1 * abel_s2 * abel_s1)%g = abel_s2.
Proof. by rewrite -mulgA abel_s21 mulgA abel_s1K mul1g. Qed.

(** abel_s1s2_s2 — (s1 s2) s2 = s1.
    @composes: abel_G4_group_set *)
Lemma abel_s1s2_s2 : (abel_s1 * abel_s2 * abel_s2)%g = abel_s1.
Proof. by rewrite -mulgA abel_s2K mulg1. Qed.

(** abel_s1s2K — the product of the two generators is an involution.
    @composes: abel_G4_group_set *)
Lemma abel_s1s2K : (abel_s1 * abel_s2 * (abel_s1 * abel_s2))%g = 1%g.
Proof. by rewrite mulgA abel_s1s2_s1 abel_s2K. Qed.

(** abel_G4_group_set — {1, s1, s2, s1 s2} is a subgroup of the permutations
    of the four sheets.
    @main architecture: group_set abel_G4, the set contains the identity and
    is closed under the group law; the canonical structure below registers it
    as a group. *)
Lemma abel_G4_group_set : group_set abel_G4.
Proof.
apply/group_setP; split; first by rewrite !inE eqxx.
move=> x y; rewrite !inE.
move=> /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->]
       /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->];
  rewrite ?mul1g ?mulg1 ?abel_s1K ?abel_s2K ?abel_s21 ?abel_s1_s1s2
          ?abel_s2_s1s2 ?abel_s1s2_s1 ?abel_s1s2_s2 ?abel_s1s2K
          ?eqxx ?orbT //=.
Qed.

(* abel_G4_group registers abel_G4 as a group, so that the group-theoretic
   notation of fingroup applies to the set spelled out above. *)
Canonical abel_G4_group := group abel_G4_group_set.

(** abel_gen_setE — the generator image set is the pair {s1, s2}.
    @composes: abel_pgg_GE *)
Lemma abel_gen_setE :
  [set tnth abel_sigmas i | i : 'I_2] = [set abel_s1; abel_s2].
Proof.
apply/setP => g; rewrite !inE; apply/imsetP/orP.
  case=> i _ ->; move: i => [[|[|i]] Hi] //=;
    rewrite (tnth_nth abel_s1) /=; [by left | by right].
case=> /eqP ->;
  [exists (Ordinal (isT : (0 < 2)%N)) | exists (Ordinal (isT : (1 < 2)%N))];
  by rewrite // (tnth_nth abel_s1).
Qed.

(** abel_pgg_GE — the generated group is the four-element Klein set.
    @main architecture: pgg_G abel_M = {1, s1, s2, s1 s2} as sets of
    permutations of the four sheets. *)
Lemma abel_pgg_GE : (pgg_G abel_M : {set {perm 'I_4}}) = abel_G4.
Proof.
have -> : (pgg_G abel_M : {set {perm 'I_4}})
        = <<[set tnth abel_sigmas i | i : 'I_2]>>%g by [].
rewrite abel_gen_setE; apply/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite gen_subG; apply/subsetP => g.
  by rewrite !inE => /orP[/eqP->|/eqP->]; rewrite eqxx ?orbT.
apply/subsetP => g; rewrite !inE.
move=> /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->].
- exact: group1.
- by apply: mem_gen; rewrite !inE eqxx.
- by apply: mem_gen; rewrite !inE eqxx orbT.
- by apply: groupM; apply: mem_gen; rewrite !inE eqxx ?orbT.
Qed.

(** abel_perm_eq0 — equal permutations agree at sheet 0.
    @composes: abel_G4_card *)
Lemma abel_perm_eq0 (g h : {perm 'I_4}) : g = h ->
  val (g (Ordinal (isT : (0 < 4)%N))) = val (h (Ordinal (isT : (0 < 4)%N))).
Proof. by move=> ->. Qed.

(** abel_perm_eq2 — equal permutations agree at sheet 2.
    @composes: abel_G4_card *)
Lemma abel_perm_eq2 (g h : {perm 'I_4}) : g = h ->
  val (g (Ordinal (isT : (2 < 4)%N))) = val (h (Ordinal (isT : (2 < 4)%N))).
Proof. by move=> ->. Qed.

(** abel_1_neq_s1 — the identity differs from the first generator.
    @composes: abel_G4_card *)
Lemma abel_1_neq_s1 : (1%g == abel_s1) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite perm1 /abel_s1 !permE.
Qed.

(** abel_1_neq_s2 — the identity differs from the second generator.
    @composes: abel_G4_card *)
Lemma abel_1_neq_s2 : (1%g == abel_s2) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq2; rewrite perm1 /abel_s2 !permE.
Qed.

(** abel_1_neq_s1s2 — the identity differs from the generator product.
    @composes: abel_G4_card *)
Lemma abel_1_neq_s1s2 : (1%g == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0;
   rewrite perm1 permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s1_neq_s2E — the two generators differ.
    @composes: abel_G4_card *)
Lemma abel_s1_neq_s2E : (abel_s1 == abel_s2) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s1_neq_s1s2 — the first generator differs from the product.
    @composes: abel_G4_card *)
Lemma abel_s1_neq_s1s2 : (abel_s1 == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq2; rewrite permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s2_neq_s1s2 — the second generator differs from the product.
    @composes: abel_G4_card *)
Lemma abel_s2_neq_s1s2 : (abel_s2 == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_G4_card — the four listed permutations are pairwise distinct.
    @main architecture: #|abel_G4| = 4, the cardinality the uniform
    distribution on the generated group is normalised by. *)
Lemma abel_G4_card : #|abel_G4| = 4.
Proof.
rewrite /abel_G4 -!setUA !cardsU1 !inE cards1.
by rewrite abel_1_neq_s1 abel_1_neq_s2 abel_1_neq_s1s2 abel_s1_neq_s2E
           abel_s1_neq_s1s2 abel_s2_neq_s1s2.
Qed.

(** abel_G4_card_gt0 — the generated group is nonempty.
    @composes: abel_group_uniform *)
Lemma abel_G4_card_gt0 : (0 < #|abel_G4|)%N.
Proof. by rewrite abel_G4_card. Qed.

(** abel_pgg_G_card — the monodromy group has four elements.
    @main architecture: #|pgg_G abel_M| = 4. *)
Lemma abel_pgg_G_card : #|pgg_G abel_M| = 4.
Proof. by rewrite abel_pgg_GE abel_G4_card. Qed.

(** abel_G_abelian — the generated group is abelian.
    @main architecture: abelian (pgg_G abel_M), the hypothesis of
    abelian_word_eval and freq_vec_det. *)
Lemma abel_G_abelian : abelian (pgg_G abel_M).
Proof.
have -> : (pgg_G abel_M : {set {perm 'I_4}})
        = <<[set tnth abel_sigmas i | i : 'I_2]>>%g by [].
rewrite abel_gen_setE abelian_gen.
apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->];
  apply/centP => y; rewrite !inE => /orP[/eqP->|/eqP->] //;
  [exact: abel_gens_commute | exact: esym abel_gens_commute].
Qed.
