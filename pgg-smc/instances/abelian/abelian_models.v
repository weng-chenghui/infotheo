(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abelian_models: the two abelian shuffle models and their exact distance    *)
(*                                                                            *)
(* Two probability models sit on the identity-content plug abel_shuffle_plug. *)
(* The ideal one is the uniform distribution on the four-element generated    *)
(* group; the actual one is the pushforward of the uniform distribution on    *)
(* generator words of length L + 1 through the abelian word evaluator.        *)
(*                                                                            *)
(* Both generators are involutions and they commute, so a word evaluates to a *)
(* group element determined by the parity of its count of the first letter. A *)
(* word of positive length therefore reaches exactly one parity class of two  *)
(* elements, each carrying mass one half, and never the other two elements of *)
(* the group. The full-L1 distance from the group uniform is 1 at every       *)
(* positive length. The complete four-endpoint reader abel_reader is globally *)
(* injective, so that distance is unchanged at the executed observation.      *)
(*                                                                            *)
(* Every distance below is stated in the repository's full-L1 convention:     *)
(* var_dist P Q is the sum over the carrier of the absolute differences, with *)
(* no factor one half.                                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_group_uniform  == the ideal model, uniform on the generated group   *)
(*   abel_word_dist      == the actual model at word length L + 1             *)
(*   abel_parity_mass    == the word mass of the odd first-letter class       *)
(*   abel_letter_flip    == the swap of the two generator indices             *)
(*   abel_flip           == the word map swapping the first letter            *)
(*   abel_ideal_adapter  == the SampleAdapter of the ideal model              *)
(*   abel_actual_adapter == the SampleAdapter of the actual model             *)
(*   abel_sample_reader  == the endpoint vector read at a sample point        *)
(*                                                                            *)
(* Key results, one entry per @main declaration:                              *)
(*   abel_word_evalE     == a word's value from its two letter parities       *)
(*   abel_word_eval_odd, abel_word_eval_even == the parity class at each      *)
(*                          length parity                                     *)
(*   abel_flip_freq      == the first-letter flip inverts the class           *)
(*   abel_word_group_dist == full-L1 distance 1 at every positive length      *)
(*   abel_executed_distance == the same distance after the endpoint reader    *)
(*   abel_executed_observation_distance == the same distance at the two       *)
(*                          models' own sample spaces                         *)
(*   abel_word_group_dist0 == the length-zero distance is 1 + 1/2, not 1      *)
(*   abel_ideal_cut_dist, abel_actual_cut_dist == the two cut distributions   *)
(*   abel_sample_reader_dist == the reader pushforward of the cut             *)
(*                          distribution                                      *)
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
From pgg_smc Require Import abel_profile abelian_exec.
From pgg_smc Require Import pgg_analysis_status.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_profile is built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(******************************************************************************)
(*     The parity invariant of an abelian word                                *)
(******************************************************************************)

(** expg_invol — an involution's powers alternate between it and the identity.
    @composes: abel_word_evalE *)
Lemma expg_invol (gT : finGroupType) (g : gT) : (g * g = 1)%g ->
  forall n, (g ^+ n)%g = (if odd n then g else 1)%g.
Proof.
move=> Hg; elim=> [|n IHn]; first by rewrite expg0.
by rewrite expgS IHn /=; case: (odd n); rewrite ?Hg ?mulg1.
Qed.

(** abel_sigma0 — the first generator of the abelian tuple.
    @composes: abel_word_evalE *)
Lemma abel_sigma0 : tnth (@pgg_sigmas abel_M) ord0 = abel_s1.
Proof. by rewrite (tnth_nth abel_s1). Qed.

(** abel_sigma1 — the second generator of the abelian tuple.
    @composes: abel_word_evalE *)
Lemma abel_sigma1 : tnth (@pgg_sigmas abel_M) (lift ord0 ord0) = abel_s2.
Proof. by rewrite (tnth_nth abel_s1). Qed.

(** abel_word_evalE — a word's value is the product of the two generators
    raised to the parities of their counts.
    @main architecture: word_eval w = (if odd (freq_vec w 0) then s1 else 1) *
    (if odd (freq_vec w 1) then s2 else 1). The two generators commute, which
    collapses the word to a product of powers, and each is an involution,
    which collapses each power to its exponent's parity. *)
Lemma abel_word_evalE (n : nat) (w : pgg_word abel_M n) :
  @word_eval abel_M n w
  = ((if odd (@freq_vec abel_M n w ord0) then abel_s1 else 1)
     * (if odd (@freq_vec abel_M n w (lift ord0 ord0)) then abel_s2 else 1))%g.
Proof.
rewrite (abelian_word_eval w abel_G_abelian).
rewrite big_ord_recl big_ord_recl big_ord0 mulg1.
by rewrite abel_sigma0 abel_sigma1 (expg_invol abel_s1K) (expg_invol abel_s2K).
Qed.

(** abel_freq_parity — the two letter counts of a length-n word have parities
    summing to the parity of n.
    @composes: abel_word_eval_odd, abel_word_eval_even *)
Lemma abel_freq_parity (n : nat) (w : pgg_word abel_M n) :
  odd (@freq_vec abel_M n w (lift ord0 ord0))
  = odd n (+) odd (@freq_vec abel_M n w ord0).
Proof.
have H := freq_vec_sum w.
move: H; rewrite big_ord_recl big_ord_recl big_ord0 addn0 => H.
have K : odd (@freq_vec abel_M n w ord0)
         (+) odd (@freq_vec abel_M n w (lift ord0 ord0)) = odd n
  by rewrite -oddD H.
by rewrite -K addbAC addbb.
Qed.

(** abel_word_eval_odd — an odd-length word evaluates to a generator.
    @main architecture: word_eval w = if odd (freq_vec w 0) then s1 else s2,
    for odd n; the two values a word of odd length can take. *)
Lemma abel_word_eval_odd (n : nat) (w : pgg_word abel_M n) : odd n ->
  @word_eval abel_M n w
  = if odd (@freq_vec abel_M n w ord0) then abel_s1 else abel_s2.
Proof.
move=> Hn; rewrite abel_word_evalE abel_freq_parity Hn.
by case: (odd (@freq_vec abel_M n w ord0)); rewrite /= ?mulg1 ?mul1g.
Qed.

(** abel_word_eval_even — an even-length word evaluates to the identity or the
    generator product.
    @main architecture: word_eval w = if odd (freq_vec w 0) then s1 s2 else 1,
    for even n; the two values a word of even length can take. *)
Lemma abel_word_eval_even (n : nat) (w : pgg_word abel_M n) : ~~ odd n ->
  @word_eval abel_M n w
  = if odd (@freq_vec abel_M n w ord0) then (abel_s1 * abel_s2)%g else 1%g.
Proof.
move/negbTE => Hn; rewrite abel_word_evalE abel_freq_parity Hn.
by case: (odd (@freq_vec abel_M n w ord0)); rewrite /= ?mulg1 ?mul1g.
Qed.

(******************************************************************************)
(*     The first-letter flip, an involution inverting the class               *)
(******************************************************************************)

(** abel_letter_flip — the swap of the two generator indices.
    @intent: the involution of 'I_2 exchanging 0 and 1. *)
Definition abel_letter_flip (x : 'I_2) : 'I_2 :=
  if x == ord0 then Ordinal (isT : (1 < 2)%N) else ord0.

(** abel_letter_flipK — the letter swap is an involution.
    @composes: abel_flipK *)
Lemma abel_letter_flipK : involutive abel_letter_flip.
Proof. by move=> x; apply: val_inj; move: x => [[|[|x]] Hx]. Qed.

(** abel_flip — the word map swapping the first letter.
    @intent: the map on positive-length words that replaces the letter at
    position 0 by the other generator index and keeps every other letter. *)
Definition abel_flip (n : nat) (w : pgg_word abel_M n.+1)
    : pgg_word abel_M n.+1 :=
  [tuple (if i == ord0 then abel_letter_flip (tnth w i) else tnth w i)
   | i < n.+1].

(** abel_flipK — the first-letter flip is an involution.
    @composes: abel_flip_inj *)
Lemma abel_flipK (n : nat) : involutive (@abel_flip n).
Proof.
move=> w; apply: eq_from_tnth => i; rewrite !tnth_mktuple.
by case Hi : (i == ord0); rewrite ?Hi ?abel_letter_flipK.
Qed.

(** abel_flip_inj — the first-letter flip is a bijection of the word space.
    @composes: abel_parity_mass_flip *)
Lemma abel_flip_inj (n : nat) : injective (@abel_flip n).
Proof. exact: can_inj (@abel_flipK n). Qed.

(** abel_flip_freq — the first-letter flip inverts the parity of the first
    letter's count.
    @main architecture: odd (freq_vec (abel_flip w) 0) = ~~ odd (freq_vec w 0),
    the bijection that makes the two parity classes equinumerous. *)
Lemma abel_flip_freq (n : nat) (w : pgg_word abel_M n.+1) :
  odd (@freq_vec abel_M n.+1 (abel_flip w) ord0)
  = ~~ odd (@freq_vec abel_M n.+1 w ord0).
Proof.
rewrite /freq_vec (cardsD1 ord0) [in RHS](cardsD1 ord0).
have Hd : [set i : 'I_n.+1 | tnth (abel_flip w) i == ord0] :\ ord0
        = [set i : 'I_n.+1 | tnth w i == ord0] :\ ord0.
  apply/setP => i; rewrite !in_setD1 !inE tnth_mktuple.
  by case Hi : (i == ord0) => /=; rewrite ?Hi ?Hi //=.
have H0 : (ord0 \in [set i : 'I_n.+1 | tnth (abel_flip w) i == ord0])
        = ~~ (ord0 \in [set i : 'I_n.+1 | tnth w i == ord0]).
  rewrite !inE tnth_mktuple eqxx /abel_letter_flip.
  by case: (tnth w ord0 == ord0).
rewrite Hd H0.
by case: (ord0 \in [set i : 'I_n.+1 | tnth w i == ord0]) => /=; rewrite ?negbK.
Qed.

(******************************************************************************)
(*     The four group elements, as inequations and memberships                *)
(******************************************************************************)

(** abel_s2_neq_s1E — the second generator differs from the first.
    @composes: abel_word_group_dist *)
Lemma abel_s2_neq_s1E : (abel_s2 == abel_s1) = false.
Proof. by rewrite eq_sym abel_s1_neq_s2E. Qed.

(** abel_s1s2_neq_s1 — the generator product differs from the first generator.
    @composes: abel_word_group_dist *)
Lemma abel_s1s2_neq_s1 : ((abel_s1 * abel_s2)%g == abel_s1) = false.
Proof. by rewrite eq_sym abel_s1_neq_s1s2. Qed.

(** abel_s1s2_neq_s2 — the generator product differs from the second generator.
    @composes: abel_word_group_dist *)
Lemma abel_s1s2_neq_s2 : ((abel_s1 * abel_s2)%g == abel_s2) = false.
Proof. by rewrite eq_sym abel_s2_neq_s1s2. Qed.

(** abel_s1s2_neq_1 — the generator product differs from the identity.
    @composes: abel_word_group_dist *)
Lemma abel_s1s2_neq_1 : ((abel_s1 * abel_s2)%g == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s1s2. Qed.

(** abel_s1_neq_1 — the first generator differs from the identity.
    @composes: abel_word_group_dist *)
Lemma abel_s1_neq_1 : (abel_s1 == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s1. Qed.

(** abel_s2_neq_1 — the second generator differs from the identity.
    @composes: abel_word_group_dist *)
Lemma abel_s2_neq_1 : (abel_s2 == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s2. Qed.

(** abel_in_G4_1 — the identity lies in the generated group.
    @composes: abel_word_group_dist *)
Lemma abel_in_G4_1 : (1%g : {perm 'I_4}) \in abel_G4.
Proof. by rewrite !inE eqxx. Qed.

(** abel_in_G4_s1 — the first generator lies in the generated group.
    @composes: abel_word_group_dist *)
Lemma abel_in_G4_s1 : abel_s1 \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(** abel_in_G4_s2 — the second generator lies in the generated group.
    @composes: abel_word_group_dist *)
Lemma abel_in_G4_s2 : abel_s2 \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(** abel_in_G4_s1s2 — the generator product lies in the generated group.
    @composes: abel_word_group_dist *)
Lemma abel_in_G4_s1s2 : (abel_s1 * abel_s2)%g \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(******************************************************************************)
(*     The two shuffle models and their exact distance                        *)
(******************************************************************************)

Section abel_models.

Variable R : realType.

(** abel_group_uniform — the ideal shuffle model.
    @intent: the uniform distribution on the four-element generated group
    {1, s1, s2, s1 s2}. This is the ideal target the abelian mixing statements
    are taken against: it is the uniform distribution on exactly the
    permutations the protocol's own generators reach, so the distance below
    measures failure to mix inside the reachable group and not the fact that
    the group is smaller than the full symmetric group. *)
Definition abel_group_uniform : R.-fdist {perm 'I_4} :=
  @fdist_uniform_supp R _ _ abel_G4_card_gt0.

(** abel_word_dist — the actual shuffle model at positive word length.
    @intent: the pushforward of the uniform distribution on generator words of
    length L.+1 through the abelian word evaluator; the length is positive by
    construction, the parameter L counting the letters after the first. *)
Definition abel_word_dist (L : nat) : R.-fdist {perm 'I_4} :=
  @rho_from_words R 2 1 L.+1 abel_sigmas.

(** abel_word_distE — the actual model as a fibre sum.
    @composes: abel_word_dist_class *)
Lemma abel_word_distE (L : nat) (g : {perm 'I_4}) :
  abel_word_dist L g
  = \sum_(w : pgg_word abel_M L.+1 | @word_eval abel_M L.+1 w == g)
      (@word_uniform R 1 L.+1) w.
Proof.
rewrite /abel_word_dist /rho_from_words fdistmapE.
by apply: eq_bigl => w; rewrite inE.
Qed.

(** abel_parity_mass — the mass of one parity class of words.
    @intent: the total uniform-word mass of the words whose count of the first
    letter is odd. *)
Definition abel_parity_mass (L : nat) : R :=
  \sum_(w : pgg_word abel_M L.+1 | odd (@freq_vec abel_M L.+1 w ord0))
    (@word_uniform R 1 L.+1) w.

(** abel_parity_mass_flip — the two parity classes carry the same mass.
    @composes: abel_parity_mass_half *)
Lemma abel_parity_mass_flip (L : nat) :
  \sum_(w : pgg_word abel_M L.+1 | ~~ odd (@freq_vec abel_M L.+1 w ord0))
    (@word_uniform R 1 L.+1) w = abel_parity_mass L.
Proof.
rewrite (reindex_inj (@abel_flip_inj L)) /abel_parity_mass.
rewrite (eq_bigl (fun w => odd (@freq_vec abel_M L.+1 w ord0)));
  last by move=> w; rewrite abel_flip_freq negbK.
by apply: eq_bigr => w _; rewrite /word_uniform !fdist_uniformE.
Qed.

(** abel_parity_split — the two parity classes exhaust the word space.
    @composes: abel_parity_mass_half *)
Lemma abel_parity_split (L : nat) :
  abel_parity_mass L
  + \sum_(w : pgg_word abel_M L.+1 | ~~ odd (@freq_vec abel_M L.+1 w ord0))
      (@word_uniform R 1 L.+1) w = 1.
Proof.
rewrite /abel_parity_mass -[RHS](FDist.f1 (@word_uniform R 1 L.+1)).
by rewrite [RHS](bigID (fun w => odd (@freq_vec abel_M L.+1 w ord0))).
Qed.

(** abel_parity_mass_half — each parity class carries mass one half.
    @composes: abel_word_dist_class *)
Lemma abel_parity_mass_half (L : nat) : abel_parity_mass L = 2%:R^-1.
Proof.
have h2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
have H := abel_parity_split L.
rewrite abel_parity_mass_flip in H.
have Hx : abel_parity_mass L * 2%:R = 1 by rewrite mulr_natr mulr2n.
by apply: (mulIf h2); rewrite Hx mulVf.
Qed.

(** abel_word_dist_class — a two-element parity class carries the whole mass,
    one half at each element.
    @composes: abel_word_group_dist *)
Lemma abel_word_dist_class (L : nat) (a b : {perm 'I_4}) :
  (forall w : pgg_word abel_M L.+1,
     @word_eval abel_M L.+1 w
     = if odd (@freq_vec abel_M L.+1 w ord0) then a else b) ->
  a != b ->
  [/\ abel_word_dist L a = 2%:R^-1, abel_word_dist L b = 2%:R^-1 &
      forall c : {perm 'I_4}, c != a -> c != b -> abel_word_dist L c = 0].
Proof.
move=> Hw Hab; split.
- rewrite abel_word_distE -(abel_parity_mass_half L); apply: eq_bigl => w.
  by rewrite Hw; case: (odd _); rewrite ?eqxx // eq_sym (negbTE Hab).
- rewrite abel_word_distE -(abel_parity_mass_half L) -(abel_parity_mass_flip L).
  apply: eq_bigl => w.
  by rewrite Hw; case: (odd _); rewrite ?eqxx // (negbTE Hab).
- move=> c Hca Hcb; rewrite abel_word_distE big_pred0 // => w.
  by rewrite Hw; case: (odd _); rewrite eq_sym ?(negbTE Hca) ?(negbTE Hcb).
Qed.

(******************************************************************************)
(*     The full-L1 sum over the four-element group                            *)
(******************************************************************************)

(** abel_G4_sum — a sum over the generated group is its four terms.
    @composes: abel_var_distE *)
Lemma abel_G4_sum (F : {perm 'I_4} -> R) :
  \sum_(a in abel_G4) F a
  = F 1%g + (F abel_s1 + (F abel_s2 + F (abel_s1 * abel_s2)%g)).
Proof.
rewrite /abel_G4 -!setUA !big_setU1 ?big_set1 //.
- by rewrite inE abel_s2_neq_s1s2.
- by rewrite !inE abel_s1_neq_s2E abel_s1_neq_s1s2.
- by rewrite !inE abel_1_neq_s1 abel_1_neq_s2 abel_1_neq_s1s2.
Qed.

(** abel_two_halves — two halves make one.
    @composes: abel_two_quarters *)
Lemma abel_two_halves : (2%:R:R)^-1 + 2%:R^-1 = 1.
Proof.
have h2 : (2%:R:R) != 0 by rewrite pnatr_eq0.
by rewrite -mulr2n -(mulr_natl (2%:R^-1 : R) 2) mulfV.
Qed.

(** abel_two_quarters — two quarters make one half.
    @composes: abel_four_quarters, abel_norm_half_quarter *)
Lemma abel_two_quarters : (4%:R:R)^-1 + 4%:R^-1 = 2%:R^-1.
Proof.
have h4 : (4%:R:R) = 2%:R * 2%:R by rewrite -natrM.
by rewrite h4 invfM -mulrDl abel_two_halves mul1r.
Qed.

(** abel_four_quarters — four quarters make one.
    @composes: abel_word_group_dist *)
Lemma abel_four_quarters :
  (4%:R:R)^-1 + ((4%:R:R)^-1 + ((4%:R:R)^-1 + (4%:R:R)^-1)) = 1.
Proof. by rewrite addrA !abel_two_quarters abel_two_halves. Qed.

(** abel_norm_zero_quarter — the gap between no mass and a quarter.
    @composes: abel_word_group_dist *)
Lemma abel_norm_zero_quarter : `|(0:R) - 4%:R^-1| = 4%:R^-1.
Proof. by rewrite sub0r normrN ger0_norm // invr_ge0 ler0n. Qed.

(** abel_norm_half_quarter — the gap between a half and a quarter.
    @composes: abel_word_group_dist *)
Lemma abel_norm_half_quarter : `|(2%:R:R)^-1 - 4%:R^-1| = 4%:R^-1.
Proof. by rewrite -abel_two_quarters addrK ger0_norm // invr_ge0 ler0n. Qed.

(** abel_quarter_le1 — a quarter is at most one.
    @composes: abel_word_group_dist0 *)
Lemma abel_quarter_le1 : (4%:R : R)^-1 <= 1.
Proof. by rewrite invf_le1 ?ler1n // ltr0n. Qed.

(** abel_group_uniform_in — the ideal model is a quarter on the group.
    @composes: abel_var_distE *)
Lemma abel_group_uniform_in (g : {perm 'I_4}) :
  g \in abel_G4 -> abel_group_uniform g = 4%:R^-1.
Proof.
move=> Hg; rewrite /abel_group_uniform.
by rewrite (@fdist_uniform_supp_in R _ _ abel_G4_card_gt0 g Hg) abel_G4_card.
Qed.

(** abel_group_uniform_out — the ideal model vanishes off the group.
    @composes: abel_var_distE *)
Lemma abel_group_uniform_out (g : {perm 'I_4}) :
  g \notin abel_G4 -> abel_group_uniform g = 0.
Proof. exact: (@fdist_uniform_supp_notin R _ _ abel_G4_card_gt0 g). Qed.

(** abel_var_distE — the full-L1 distance to the ideal model is the sum of the
    four group-element gaps, for a distribution supported in the group.
    @composes: abel_word_group_dist, abel_word_group_dist0 *)
Lemma abel_var_distE (P : R.-fdist {perm 'I_4}) :
  (forall g, g \notin abel_G4 -> P g = 0) ->
  var_dist P abel_group_uniform
  = `|P 1%g - 4%:R^-1|
    + (`|P abel_s1 - 4%:R^-1|
       + (`|P abel_s2 - 4%:R^-1| + `|P (abel_s1 * abel_s2)%g - 4%:R^-1|)).
Proof.
move=> HP.
rewrite /var_dist (bigID (fun a : {perm 'I_4} => a \in abel_G4)) /=.
rewrite [X in _ + X]big1; last first.
  by move=> g Hg; rewrite HP // abel_group_uniform_out // subrr normr0.
rewrite addr0 (abel_G4_sum (fun a => `|P a - abel_group_uniform a|)).
by rewrite !abel_group_uniform_in // !inE eqxx ?orbT.
Qed.

(******************************************************************************)
(*     The exact distance                                                     *)
(******************************************************************************)

(** abel_word_group_dist — the actual and ideal shuffle models are at full-L1
    distance exactly one, at every positive word length.
    @main security: var_dist (abel_word_dist L) abel_group_uniform = 1, for
    every L : nat, that is at every generator-word length L.+1, in the
    repository's full-L1 convention. This is a fixed-length mixing limitation:
    it says the word model does not reach the uniform distribution on the
    generated group at any finite length, and it is not a statement about
    privacy of any observer. The proof is not commutativity alone: it uses the
    parity invariant of the two commuting involutions, which pins the actual
    model to a two-element parity class of mass one half at each element. *)
Theorem abel_word_group_dist (L : nat) :
  var_dist (abel_word_dist L) abel_group_uniform = 1.
Proof.
case HL : (odd L.+1).
- case: (abel_word_dist_class (fun w => abel_word_eval_odd w HL)
            (negbT abel_s1_neq_s2E)) => H1 H2 H0.
  have Hsupp : forall g, g \notin abel_G4 -> abel_word_dist L g = 0.
    move=> g Hg; apply: H0.
      by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s1.
    by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s2.
  rewrite (abel_var_distE Hsupp) H1 H2.
  rewrite (H0 1%g (negbT abel_1_neq_s1) (negbT abel_1_neq_s2)).
  rewrite (H0 (abel_s1 * abel_s2)%g (negbT abel_s1s2_neq_s1)
              (negbT abel_s1s2_neq_s2)).
  by rewrite !abel_norm_zero_quarter !abel_norm_half_quarter abel_four_quarters.
- case: (abel_word_dist_class (fun w => abel_word_eval_even w (negbT HL))
            (negbT abel_s1s2_neq_1)) => H1 H2 H0.
  have Hsupp : forall g, g \notin abel_G4 -> abel_word_dist L g = 0.
    move=> g Hg; apply: H0.
      by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s1s2.
    by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_1.
  rewrite (abel_var_distE Hsupp) H1 H2.
  rewrite (H0 abel_s1 (negbT abel_s1_neq_s1s2) (negbT abel_s1_neq_1)).
  rewrite (H0 abel_s2 (negbT abel_s2_neq_s1s2) (negbT abel_s2_neq_1)).
  by rewrite !abel_norm_zero_quarter !abel_norm_half_quarter abel_four_quarters.
Qed.

(** abel_executed_distance — the complete four-endpoint observations of the two
    shuffle models are at full-L1 distance exactly one.
    @main security: var_dist (fdistmap abel_reader (abel_word_dist L))
    (fdistmap abel_reader abel_group_uniform) = 1, for every L : nat, in the
    repository's full-L1 convention. This is the static endpoint-vector form of
    the fixed-length mixing limitation: the reader is injective, so reading the
    four endpoints loses none of the distance. *)
Theorem abel_executed_distance (L : nat) :
  var_dist (fdistmap abel_reader (abel_word_dist L))
           (fdistmap abel_reader abel_group_uniform) = 1.
Proof.
by rewrite (var_dist_fdistmap_inj _ _ abel_reader_inj) abel_word_group_dist.
Qed.

(******************************************************************************)
(*     The length-zero exclusion witness                                      *)
(******************************************************************************)

(** abel_word_dist0E — the empty word evaluates to the identity, so the
    length-zero pushforward is the Dirac distribution at the identity.
    @composes: abel_word_group_dist0 *)
Lemma abel_word_dist0E (g : {perm 'I_4}) :
  (@rho_from_words R 2 1 0 abel_sigmas) g = if g == 1%g then 1 else 0.
Proof.
rewrite /rho_from_words fdistmapE.
have Hwe : forall w : pgg_word abel_M 0, @word_eval abel_M 0 w = 1%g.
  by move=> w; rewrite /word_eval big_ord0.
case Hg : (g == 1%g).
  rewrite -[RHS](FDist.f1 (@word_uniform R 1 0)); apply: eq_bigl => w.
  by rewrite !inE /= Hwe eq_sym Hg.
by rewrite big_pred0 // => w; rewrite !inE /= Hwe eq_sym Hg.
Qed.

(** abel_word_group_dist0 — at word length zero the distance is 1 + 1/2, not 1.
    @main bound: var_dist (rho_from_words at length 0) abel_group_uniform =
    1 + 1/2, in the repository's full-L1 convention. This is the excluded-length
    witness of abel_word_group_dist: the positive-length hypothesis of that
    theorem is load-bearing, because the length-zero pushforward is a Dirac
    distribution and not a uniform distribution on a two-element parity
    class. *)
Theorem abel_word_group_dist0 :
  var_dist (@rho_from_words R 2 1 0 abel_sigmas) abel_group_uniform
  = 1 + 2%:R^-1.
Proof.
have Hsupp : forall g, g \notin abel_G4 ->
    (@rho_from_words R 2 1 0 abel_sigmas) g = 0.
  move=> g Hg; rewrite abel_word_dist0E.
  by case Hg1 : (g == 1%g) => //; move: Hg; rewrite (eqP Hg1) abel_in_G4_1.
rewrite (abel_var_distE Hsupp) !abel_word_dist0E eqxx.
rewrite abel_s1_neq_1 abel_s2_neq_1 abel_s1s2_neq_1.
rewrite !abel_norm_zero_quarter ger0_norm;
  last by rewrite subr_ge0 abel_quarter_le1.
by rewrite addrA subrK abel_two_quarters.
Qed.

(******************************************************************************)
(*     The two sample adapters on the shuffle-analysis plug                   *)
(******************************************************************************)

(** abel_ideal_adapter — the ideal shuffle model as a sample adapter.
    @intent: the SampleAdapter over abel_shuffle_plug whose sample carrier is
    the permutation group itself, whose prior is abel_group_uniform, whose run
    argument is the unit and whose cut is the sample point. *)
Definition abel_ideal_adapter : SampleAdapter R abel_shuffle_plug :=
  @MkSampleAdapter R abel_profile abel_shuffle_plug
    {perm 'I_4} abel_group_uniform (fun _ => tt) idfun.

(** abel_actual_adapter — the finite-word shuffle model as a sample adapter.
    @intent: the SampleAdapter over abel_shuffle_plug whose sample carrier is
    the generator words of length L.+1, whose prior is the uniform word
    distribution, whose run argument is the unit and whose cut is the word
    evaluation. *)
Definition abel_actual_adapter (L : nat) : SampleAdapter R abel_shuffle_plug :=
  @MkSampleAdapter R abel_profile abel_shuffle_plug
    (pgg_word abel_M L.+1) (@word_uniform R 1 L.+1)
    (fun _ => tt) (@word_eval abel_M L.+1).

(** abel_fdistmap_id — the identity map leaves a distribution unchanged.
    @composes: abel_ideal_cut_dist *)
Lemma abel_fdistmap_id (P : R.-fdist {perm 'I_4}) : fdistmap idfun P = P.
Proof. by apply/fdist_ext => g; rewrite fdistmapE (big_pred1 g). Qed.

(** abel_ideal_cut_dist — the ideal adapter's cut distribution is the group
    uniform.
    @main architecture: sa_cut_dist abel_ideal_adapter = abel_group_uniform. *)
Lemma abel_ideal_cut_dist : sa_cut_dist abel_ideal_adapter = abel_group_uniform.
Proof. exact: abel_fdistmap_id. Qed.

(** abel_actual_cut_dist — the finite-word adapter's cut distribution is the
    actual shuffle model.
    @main architecture: sa_cut_dist (abel_actual_adapter L) = abel_word_dist L,
    so the exact distance above is a statement about the distribution this
    adapter samples. *)
Lemma abel_actual_cut_dist (L : nat) :
  sa_cut_dist (abel_actual_adapter L) = abel_word_dist L.
Proof. by []. Qed.

(** abel_sample_reader — the complete four-endpoint observation as a function
    of a sample point.
    @intent: abel_reader read at the cut the sample point selects, with carrier
    4.-tuple 'I_4; by abel_shuffle_executed_readerE this is the endpoint list
    the run's verifier collects. *)
Definition abel_sample_reader (sa : SampleAdapter R abel_shuffle_plug)
    (u : sa_sampleT sa) : 4.-tuple 'I_4 :=
  abel_reader (sa_cut u).

(** abel_sample_reader_dist — the executed observation's distribution is the
    reader pushforward of the cut distribution.
    @main architecture: fdistmap (@abel_sample_reader sa) (sa_sampleP sa) =
    fdistmap abel_reader (sa_cut_dist sa), the equality that carries the exact
    distance from the cut layer to the executed observation layer. *)
Lemma abel_sample_reader_dist (sa : SampleAdapter R abel_shuffle_plug) :
  fdistmap (@abel_sample_reader sa) (sa_sampleP sa)
  = fdistmap abel_reader (sa_cut_dist sa).
Proof. by rewrite /sa_cut_dist fdistmap_comp. Qed.

(** abel_executed_observation_distance — the executed four-endpoint
    observations of the two models are at full-L1 distance exactly one.
    @main security: the distance between the reader pushforward of the actual
    adapter's own sample distribution and the reader pushforward of the ideal
    adapter's own sample distribution is 1, for every L : nat, in the
    repository's full-L1 convention. This is the executed form of the
    fixed-length mixing limitation and is the endpoint of the abelian negative
    chain; it is a negative mixing result and not a privacy failure. *)
Theorem abel_executed_observation_distance (L : nat) :
  var_dist
    (fdistmap (@abel_sample_reader (abel_actual_adapter L))
              (sa_sampleP (abel_actual_adapter L)))
    (fdistmap (@abel_sample_reader abel_ideal_adapter)
              (sa_sampleP abel_ideal_adapter)) = 1.
Proof.
rewrite !abel_sample_reader_dist abel_actual_cut_dist abel_ideal_cut_dist.
exact: abel_executed_distance.
Qed.

End abel_models.

(******************************************************************************)
(*     The typed model family of the abelian limitation path                  *)
(******************************************************************************)

(** abel_word_family — the fixed-length word model family, indexed by the
    word length.
    @intent: the AnalysisModelFamily over abel_shuffle_observed sending a
    length L to abel_actual_adapter at that length, the model the mixing
    limitation is stated about. *)
Definition abel_word_family : AnalysisModelFamily abel_shuffle_observed :=
  @MkAnalysisModelFamily abel_shuffle_observed (fun _ => nat)
    (fun R L => @abel_actual_adapter R L).
