(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_abel_profile: the four-seat abelian interface and the Klein group    *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 4.5,     *)
(* 6.3 and 9.1. The landed abel_profile carries Gen_PGG_2 abel_sigmas, a      *)
(* two-generator interface whose pi_T' is 1, while abel_ts is a four-share    *)
(* sum-mod scheme whose ts_T' is 3, so the ExecutionPlug seat/share bridge    *)
(* would have to prove 1 = 3. This file records the failure, builds the       *)
(* four-seat interface abel_PI and the revised profile abel_profileP, and     *)
(* proves the Klein-group facts the negative probe consumes.                  *)
(*                                                                            *)
(* Probe claims:                                                              *)
(*   abel_old_bridge_absent == the landed profile admits no seat/share bridge *)
(*   abel_PI                == the four-seat interface, pi_T' = 3             *)
(*   abel_profileP          == the revised coherent profile                   *)
(*   abel_pgg_GE            == the generated group is {1, s1, s2, s1 s2}      *)
(*   abel_G4_card           == that group has four elements                   *)
(*   abel_G_abelian         == that group is abelian                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** abel_M — the abelian two-generator monodromy template at N = 4.
    @intent: the Gen_PGGTypes form abel_ts, abel_plug and abel_profile carry,
    spelled out as a notation because the instance files keep it inline. *)
Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(******************************************************************************)
(*     The landed profile carries no seat/share bridge                        *)
(******************************************************************************)

(** abel_old_pi_T — the landed profile's interface has two seats.
    @composes: abel_old_bridge_absent *)
Lemma abel_old_pi_T : pi_T' (mp_PI abel_profile) = 1.
Proof. by []. Qed.

(** abel_old_ts_T — the landed profile's scheme has four shares.
    @composes: abel_old_bridge_absent *)
Lemma abel_old_ts_T : ts_T' (rp_scheme (mp_plug abel_profile)) = 3.
Proof. by []. Qed.

(* The two numbers above are the two sides of ep_players_bridge. The commands
   below record the exact rejections:

     The term "erefl" has type
      "pi_T' (mp_PI abel_profile) = pi_T' (mp_PI abel_profile)"
     while it is expected to have type
      "pi_T' (mp_PI abel_profile) = ts_T' (rp_scheme (mp_plug abel_profile))"
     (cannot unify "pi_T' (mp_PI abel_profile)" and
     "ts_T' (rp_scheme (mp_plug abel_profile))").

   and, with the successor numerals forced,

     The term "erefl" has type "1 = 1" while it is expected to have type
      "pi_T' (mp_PI abel_profile) = ts_T' (rp_scheme (mp_plug abel_profile))". *)
Fail Definition abel_old_bridge :
  pi_T' (mp_PI abel_profile) = ts_T' (rp_scheme (mp_plug abel_profile)) := erefl.

Fail Check (erefl 1%N
  : pi_T' (mp_PI abel_profile) = ts_T' (rp_scheme (mp_plug abel_profile))).

(* No dealer_secret_plug exists over the landed profile: its second argument is
   the same bridge. *)
Fail Definition abel_old_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile 'I_4 erefl
    (enum 'I_(pi_T' (mp_PI abel_profile)).+1) erefl
    (fun s _ => tnth (ts_encode abel_ts s)) 150.

(** abel_old_bridge_absent — the landed profile's seat count and share count
    differ.
    @main architecture: pi_T' (mp_PI abel_profile) = 1 and
    ts_T' (rp_scheme (mp_plug abel_profile)) = 3, so no proof of
    ep_players_bridge exists at abel_profile. *)
Lemma abel_old_bridge_absent :
  pi_T' (mp_PI abel_profile) <> ts_T' (rp_scheme (mp_plug abel_profile)).
Proof. by rewrite abel_old_pi_T abel_old_ts_T. Qed.

(******************************************************************************)
(*     The four-seat interface and the revised profile                        *)
(******************************************************************************)

(** abel_starts_uniq — the four canonical starting positions are distinct.
    @composes: abel_PI *)
Lemma abel_starts_uniq : uniq (ord_tuple 4).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** abel_PI — the four-seat abelian interface.
    @intent: MkPGGI at abel_M with pi_T' = 3 and the four card positions
    0, 1, 2, 3 in canonical order as the starting layout. *)
Definition abel_PI : PGGInterface abel_M :=
  @MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq.

(** abel_profileP — the revised abelian profile.
    @intent: MkMonodromyProfile at abel_M, secret type 'I_4, the four-seat
    interface abel_PI and the landed reconstruction plug abel_plug. *)
Definition abel_profileP : MonodromyProfile :=
  @MkMonodromyProfile abel_M 'I_4 abel_PI abel_plug.

(** abel_PI_seat_count — the revised interface has four seats.
    @main architecture: pi_T' abel_PI = 3, so the seat index type is 'I_4. *)
Lemma abel_PI_seat_count : pi_T' abel_PI = 3.
Proof. by []. Qed.

(** abel_bridge — the revised interface and abel_ts agree on the seat count.
    @intent: the ep_players_bridge argument of every ExecutionPlug over
    abel_profileP; it is erefl at 3 = 3. *)
Definition abel_bridge :
  pi_T' (mp_PI abel_profileP) = ts_T' (rp_scheme (mp_plug abel_profileP)) :=
  erefl.

(** abel_profileP_k — the revised profile's threshold character is four.
    @main bound: profile_k abel_profileP = 4, one share per sheet, unchanged
    by the interface revision. *)
Lemma abel_profileP_k : profile_k abel_profileP = 4.
Proof. by []. Qed.

(******************************************************************************)
(*     The Klein four-group generated by the two disjoint transpositions      *)
(******************************************************************************)

(** abel_G4 — the four-element set {1, s1, s2, s1 s2}.
    @intent: the concrete carrier of the group generated by the two disjoint
    transpositions, used as the support of the ideal shuffle distribution. *)
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

(** abel_G4_group_set — {1, s1, s2, s1 s2} is closed under the group law.
    @composes: abel_pgg_GE *)
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
Proof. by apply/negbTE/eqP => /abel_perm_eq0; rewrite perm1 /abel_s1 !permE. Qed.

(** abel_1_neq_s2 — the identity differs from the second generator.
    @composes: abel_G4_card *)
Lemma abel_1_neq_s2 : (1%g == abel_s2) = false.
Proof. by apply/negbTE/eqP => /abel_perm_eq2; rewrite perm1 /abel_s2 !permE. Qed.

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

(** abel_G4_card — the generated group has four elements.
    @main architecture: #|abel_G4| = 4, the cardinality the ideal uniform
    shuffle distribution is normalised by. *)
Lemma abel_G4_card : #|abel_G4| = 4.
Proof.
rewrite /abel_G4 -!setUA !cardsU1 !inE cards1.
by rewrite abel_1_neq_s1 abel_1_neq_s2 abel_1_neq_s1s2 abel_s1_neq_s2E
           abel_s1_neq_s1s2 abel_s2_neq_s1s2.
Qed.

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

Print Assumptions abel_profileP.
Print Assumptions abel_pgg_GE.
Print Assumptions abel_G4_card.
Print Assumptions abel_G_abelian.
Print Assumptions abel_old_bridge_absent.
