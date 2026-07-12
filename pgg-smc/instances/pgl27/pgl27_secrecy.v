(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_secrecy: coalition view independence of the eight-card orbit scheme  *)
(*                                                                            *)
(* The uniformly shuffled dealt arrangement of the PGL(2,7) orbit scheme has  *)
(* a coalition view independent of the orbit secret for every coalition of at *)
(* most three cards, instantiating the bridge's ttrans_view_indep_gen         *)
(* (reconstruct/transitivity_privacy.v) at t = 3.                             *)
(* The all-decks results remove the fixed-representative scope limit: the     *)
(* dealt deck is uniform over ALL valid decks of the class.                   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_view_indep == the PGL(2,7) coalition view independence at three    *)
(*     cards                                                                  *)
(*   pgl27_view_leakage_le == leakage about the orbit secret is monotone in   *)
(*     the observed position set, for every coalition size                    *)
(*   pgl27_view_dep_k4 == a four-card coalition view is not independent of    *)
(*     the orbit secret, so the privacy threshold three is sharp              *)
(*   pgl27_view_leak_k4 == a four-card coalition shares strictly positive     *)
(*     mutual information with the orbit secret                               *)
(*   pgl27_view_indep_alldecks == all-decks dealer privacy at three cards     *)
(*   pgl27_view_indep_deck == shuffle-free uniform-deck privacy at three      *)
(*     cards                                                                  *)
(*                                                                            *)
(* The secrecy statements concern the pre-reveal execution: after the public  *)
(* reveal every player learns the secret by design.                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

Section pgl27_secrecy.
Local Open Scope proba_scope.
Variable R : realType.

(** pgl27P == the joint law of a uniform orbit secret and a uniform PGL(2,7)
    shuffle.
    @intent: the joint sample space of the eight-card orbit scheme. *)
Definition pgl27P : R.-fdist (bool * pgg_gT pgl27_M)%type :=
  (fdist_uniform card_bool) `x (`U pgl27_G_pos).

(** pgl27_secret == the dealt orbit-class secret component of a sample.
    @intent: the orbit-secret random variable. *)
Definition pgl27_secret : {RV pgl27P -> bool} := fun u => u.1.

(** pgl27_view == the dealt card values a coalition C observes at a sample,
    and ord0 outside C.
    @intent: the coalition observable random variable. *)
Definition pgl27_view (C : {set 'I_8}) : {RV pgl27P -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then
              tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i) else ord0].

(** pgl27_view_indep == any coalition of at most three cards has a view of the
    shuffled dealt arrangement independent of the orbit secret.
    @main security: instance coalition view independence from the bridge. *)
Lemma pgl27_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P |= pgl27_view C _|_ pgl27_secret.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R (fdist_uniform card_bool) pgl27_G_pos
  orbit_encode C HC orbit_encode_deck).
Qed.

Local Open Scope ring_scope.
Local Open Scope entropy_scope.

(** pgl27_view_leakage_le == the mutual information a coalition shares with the
    orbit secret is monotone under coalition inclusion, for every coalition
    size including above the privacy threshold.
    @main bound: instance leakage is monotone in the observed position set. *)
Lemma pgl27_view_leakage_le (C C' : {set 'I_8}) : C' \subset C ->
  `I(pgl27_secret ; pgl27_view C') <= `I(pgl27_secret ; pgl27_view C).
Proof.
move=> HCC'.
exact: (@coalition_view_mutual_info_le (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool) pgl27_G_pos
  orbit_encode C C' HCC').
Qed.

(** pgl27_leak_coalition == the four heart seats, the positions carrying a
    card of code below four in the identity deal.
    @intent: the size-four coalition witnessing sharpness of the privacy
    threshold three. *)
Definition pgl27_leak_coalition : {set 'I_8} := [set i | (val i < 4)%N].

(** pgl27_view_dep_k4 == a four-card coalition whose view of the shuffled
    dealt arrangement is not independent of the orbit secret.
    @main security: the privacy threshold three is sharp, a coalition of four
    cards already depends on the orbit secret. *)
Lemma pgl27_view_dep_k4 :
  #|pgl27_leak_coalition| = 4 /\
  ~ pgl27P |= pgl27_secret _|_ pgl27_view pgl27_leak_coalition.
Proof.
pose v0 : {ffun 'I_8 -> 'I_8} :=
  [ffun i => if (val i < 4)%N then i else ord0].
have Hhs : heart_set (orbit_encode false) = pgl27_leak_coalition.
  apply/setP => x; rewrite /heart_set /pgl27_leak_coalition !inE /is_heart.
  by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
have Hsc : subset_class pgl27_leak_coalition = false.
  by rewrite -Hhs; exact: (orbit_encodeK false).
have Hview_false : pgl27_view pgl27_leak_coalition (false, 1%g) = v0.
  rewrite /pgl27_view /v0; apply/ffunP => i.
  rewrite !ffunE /pgl27_leak_coalition inE /= perm1.
  have Hid : tnth (orbit_encode false) i = i.
    by apply/val_inj; case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
  by rewrite Hid.
have Hview_true : forall g, g \in pgg_G pgl27_M ->
    pgl27_view pgl27_leak_coalition (true, g) <> v0.
  move=> g gG Hveq.
  set d := [tuple tnth (orbit_encode true) (@pgg_rho pgl27_M g i) | i < 8].
  have Hud : uniq d.
    by rewrite -[uniq d]/(deck_ok d) (deck_stable g (orbit_encode true) gG)
       orbit_encode_deck.
  have Hinj : injective (tnth d) by apply/tuple_uniqP.
  have Hpin : forall i, i \in pgl27_leak_coalition -> tnth d i = i.
    move=> i; rewrite /pgl27_leak_coalition inE => Hi.
    move/ffunP/(_ i): Hveq.
    rewrite !ffunE /pgl27_leak_coalition inE Hi /= => Heq.
    by rewrite /d tnth_mktuple.
  have Hheart : heart_set d = pgl27_leak_coalition.
    apply/setP => x; rewrite /heart_set inE; apply/idP/idP.
      move=> Hx.
      have Hc : tnth d x \in pgl27_leak_coalition.
        by rewrite /pgl27_leak_coalition inE.
      by move: (Hpin _ Hc) => /Hinj Hdx; rewrite -Hdx.
    move=> Hx; rewrite (Hpin _ Hx); move: Hx.
    by rewrite /pgl27_leak_coalition !inE /is_heart.
  move: (orbit_class_invariant g (orbit_encode true) gG).
  by rewrite orbit_encodeK -/d /orbit_class Hheart Hsc.
have Hzero :
    `Pr[ [% pgl27_secret, pgl27_view pgl27_leak_coalition] = (true, v0) ] = 0.
  apply/eqP; apply/negPn; apply/negP => /pfwd1_neq0 [[s g] [Hmem Hpos]].
  have gG : g \in pgg_G pgl27_M.
    apply: contraLR Hpos => gN.
    rewrite /pgl27P fdist_prodE /=
      (@fdist_uniform_supp_notin R _ (pgg_G pgl27_M) pgl27_G_pos g gN) mulr0.
    by apply/negP => /lt0r_neq0; rewrite eqxx.
  move: Hmem; rewrite inE /= xpair_eqE => /andP[/eqP Hs /eqP Hv].
  by apply: (Hview_true g gG); rewrite -Hs.
have HP1 : forall b : bool, 0 < pgl27P (b, 1%g).
  move=> b; rewrite /pgl27P fdist_prodE /=; apply: mulr_gt0.
    by rewrite fdist_uniformE invr_gt0 ltr0n card_bool.
  rewrite (@fdist_uniform_supp_in R _ (pgg_G pgl27_M) pgl27_G_pos 1%g
    (group1 _)).
  by rewrite invr_gt0 ltr0n; exact: pgl27_G_pos.
have Hpt : 0 < `Pr[ pgl27_secret = true ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (true, 1%g); split; last exact: HP1.
  by rewrite inE.
have Hpv : 0 < `Pr[ (pgl27_view pgl27_leak_coalition) = v0 ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (false, 1%g); split; last exact: HP1.
  by rewrite inE /= Hview_false.
split.
  rewrite /pgl27_leak_coalition -sum1dep_card big_mkcond /=.
  by do 8 rewrite big_ord_recl; rewrite big_ord0.
move=> Hind; move: (Hind true v0) => Heq.
move: (mulr_gt0 Hpt Hpv); rewrite -Heq Hzero.
by move/lt0r_neq0; rewrite eqxx.
Qed.

(** pgl27_view_leak_k4 == a four-card coalition sharing strictly positive
    mutual information with the orbit secret.
    @main security: above the privacy threshold three the coalition view of
    the shuffled dealt arrangement leaks the orbit secret. *)
Lemma pgl27_view_leak_k4 :
  #|pgl27_leak_coalition| = 4 /\
  0 < `I(pgl27_secret ; pgl27_view pgl27_leak_coalition).
Proof.
split; first exact: (proj1 pgl27_view_dep_k4).
rewrite lt0r; apply/andP; split; last exact: mutual_info_ge0.
apply/eqP => HI0.
exact: (proj2 pgl27_view_dep_k4) (mutual_info_RV0_indep HI0).
Qed.

(** pgl27_class_decks_pos — both orbit classes are realised by valid decks,
    so each class-conditional uniform deck law is well defined.
    @composes: pgl27_view_indep_alldecks *)
Lemma pgl27_class_decks_pos (s : bool) :
  (0 < #|class_decks orbit_class deck_ok s|)%N.
Proof.
apply/card_gt0P; exists (orbit_encode s).
by rewrite inE orbit_encode_deck orbit_encodeK eqxx.
Qed.

(** pgl27_view_indep_alldecks — a dealer dealing a uniform valid deck of the
    secret's class followed by the uniform PGL(2,7) shuffle gives every
    coalition of at most three cards a view independent of the orbit secret.
    @main security: all-decks dealer coalition privacy at three cards. *)
Lemma pgl27_view_indep_alldecks (C : {set 'I_8}) : (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos (R:=R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
        pgl27_class_decks_pos.
Proof.
move=> HC.
exact: (ttrans_view_indep_alldecks pgl27_3transitive
  (fdist_uniform card_bool) pgl27_G_pos (fun sh H => H)
  pgl27_class_decks_pos HC).
Qed.

(** pgl27_view_indep_deck — a dealer dealing a uniform valid deck of the
    secret's class gives, with no further shuffle, every coalition of at most
    three cards a view independent of the orbit secret.
    @main security: representative-free all-decks privacy at three cards. *)
Lemma pgl27_view_indep_deck (C : {set 'I_8}) : (#|C| <= 3)%N ->
  uniform_deckP (fdist_uniform card_bool) (R:=R) pgl27_class_decks_pos
  |= uniform_deck_view (fdist_uniform card_bool) pgl27_class_decks_pos C
  _|_ ((fun u => u.1)
        : {RV (uniform_deckP (fdist_uniform card_bool)
                 pgl27_class_decks_pos) -> bool}).
Proof.
move=> HC.
exact: (ttrans_view_indep_deck pgl27_3transitive
  (fdist_uniform card_bool) pgl27_G_pos (fun sh H => H)
  orbit_class_invariant deck_stable pgl27_class_decks_pos HC).
Qed.

End pgl27_secrecy.
