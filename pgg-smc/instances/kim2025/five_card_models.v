(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_models: the biased sample models of the five-card instance and   *)
(* the decoded colour reader                                                  *)
(*                                                                            *)
(* The five-card execution plug five_card_exec_plug carries no probability    *)
(* model. This file supplies three sample adapters over it, beside the landed *)
(* uniform one five_card_sample: one biased cut, L repeated biased cuts, and  *)
(* the concrete seven-cut model at bias 1/100. Each is identified by its cut  *)
(* distribution, so a shuffle bound stated at that distribution transfers to  *)
(* the executed run.                                                          *)
(*                                                                            *)
(* The second half reads the executed endpoints as card colours at a list of  *)
(* card positions and identifies that reader with the leakage space's partial *)
(* view ViewA, which carries Kim's input-privacy bound.                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_single_sample     == the sample adapter whose sample space is the    *)
(*                            den Boer leakage space under Kim's biased joint *)
(*                            distribution                                    *)
(*   kim_repeated_sampleT  == the repeated-cut sample space: a committed pair *)
(*                            together with an L-letter word                  *)
(*   kim_repeated_dist     == uniform committed pairs times the weighted word *)
(*                            distribution                                    *)
(*   kim_repeated_sample   == the sample adapter whose cut is the word        *)
(*                            evaluation of the sampled word                  *)
(*   five_card_exec_colour_view == the executed endpoints decoded as colours  *)
(*                            at a list of card positions                     *)
(*   kim_centi_repeated_sample  == kim_repeated_sample at bias 1/100 and word *)
(*                            length 7                                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   kim_single_cut_distE   == the biased model's cut distribution is the     *)
(*                             image of Kim's weight distribution under the   *)
(*                             rotation realization                           *)
(*   kim_repeated_cut_distE == the repeated model's cut distribution is the   *)
(*                             weighted word shuffle at word length L         *)
(*   kim_centi_cut_distE    == the concrete model's cut distribution is the   *)
(*                             marginal bound of the centi certificate bundle *)
(*   five_card_colour_viewE == the decoded executed colour reader agrees with *)
(*                             the leakage-space partial view ViewA           *)
(*   five_card_colour_view_RV_E == the same agreement as an equality of       *)
(*                             random variables on Kim's joint distribution   *)
(*   five_card_colour_view_leak_bound == the executed colour reader carries   *)
(*                             at most kim_leak_bound eps about the inputs    *)
(*                             given the output                               *)
(*   kim_repeated_seat_distE == the repeated model's executed seat            *)
(*                             distribution is the static pushforward         *)
(*                                                                            *)
(* Hypothesis consumption. The five-card layer carries four side conditions   *)
(* on the bias eps and one word length. Each declaration consumes a strict    *)
(* subset:                                                                    *)
(*                                                                            *)
(*   declaration                       lt   gt   spec  small  L               *)
(*   -------------------------------   ---  ---  ----  -----  ---             *)
(*   kim_weight_dist                    x    x     .     .     .              *)
(*   kim_input_dist                     x    x     .     .     .              *)
(*   kim_view / kim_inputs              x    x     .     .     .              *)
(*   kim_secret                         x    x     .     .     .              *)
(*   kim_input_private                  x    x     .     x     .              *)
(*   five_card_profile                  .    .     .     .     .              *)
(*   five_card_exec_plug                .    .     .     .     .              *)
(*   five_card_exec_colour_view         .    .     .     .     .              *)
(*   five_card_colour_view_leak_bound   x    x     .     x     .              *)
(*   kim_single_sample                  x    x     .     .     .              *)
(*   kim_repeated_sample                x    x     .     .     x              *)
(*   fc_kim_security_bundle             x    x     x     .     x              *)
(*                                                                            *)
(* Here lt is eps < 1/5, gt is -(4/5) < eps, spec is |eps| < 4/5 and small is *)
(* 0 < 1/5 - |eps|. The condition small is not implied by lt and gt: at       *)
(* eps = -1/2 both lt and gt hold while 1/5 - |eps| is negative. The program  *)
(* layer rows are empty because five_card_profile and five_card_exec_plug are *)
(* closed terms, so the executed colour reader carries no side condition and  *)
(* five_card_colour_view_leak_bound consumes exactly the three conditions of  *)
(* kim_input_private.                                                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_sample_adapter.
From pgg_smc Require Import pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.
From pgg_smc Require Import five_card_exec kim_input_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section five_card_sample_models.

Variable R : realType.
Variable eps : R.
Hypothesis eps_lt_inv5 : eps < 5%:R^-1.
Hypothesis eps_gt_neg4inv5 : - (4%:R * 5%:R^-1) < eps.
Variable L : nat.

Let mpF : MonodromyProfile := five_card_profile.

(******************************************************************************)
(*     The biased sample models over the five-card plug                       *)
(******************************************************************************)

(* The uniform model is the landed five_card_sample: the den Boer leakage
   space Omega under the uniform distribution P, argument the committed pair
   and cut the sampled rotation. Its cut distribution is
   five_card_sample_cut_distE, and the same distribution read as the den Boer
   member's marginal bound is den_boer_sample_cut_witnessE. Neither is restated
   here. *)

(** kim_single_sample — the one-biased-cut model.
    @intent: the sample layer over five_card_exec_plug whose sample space is the
    den Boer leakage space Omega under Kim's biased joint distribution
    kim_input_dist, the run argument being the committed pair and the cut the
    realized rotation; the carrier and both maps are those of five_card_sample
    and only the distribution differs. *)
Definition kim_single_sample : SampleAdapter R five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug
    five_card_leakage.Omega (kim_input_dist eps_lt_inv5 eps_gt_neg4inv5)
    five_card_sample_arg five_card_sample_cut.

(** kim_repeated_sampleT — the repeated-cut sample space.
    @intent: a committed pair of bits together with an L-letter word over the
    five rotation generators. *)
Definition kim_repeated_sampleT : finType :=
  [the finType of ((bool * bool) * (L.-tuple 'I_5))%type].

(** kim_repeated_dist — the repeated-cut distribution.
    @intent: the product of the uniform distribution on committed pairs with
    the weighted word distribution built from Kim's generator weights. *)
Definition kim_repeated_dist : R.-fdist kim_repeated_sampleT :=
  ((fdist_uniform card_bool2)
   `x (@word_weighted R 4 L
         (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5)))%fdist.

(** kim_repeated_sample — the L-repeated-biased-cut model.
    @intent: the sample layer over five_card_exec_plug whose sample space is
    kim_repeated_sampleT under kim_repeated_dist, the run argument being the
    committed pair and the cut the word evaluation of the sampled word. *)
Definition kim_repeated_sample : SampleAdapter R five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug
    kim_repeated_sampleT kim_repeated_dist
    (fun u => u.1) (fun u => @word_eval FiveCardKim_M L u.2).

(******************************************************************************)
(*     The cut distributions of the models                                    *)
(******************************************************************************)

(** kim_single_snd_weightE — the rotation marginal of Kim's joint distribution
    is Kim's weight distribution.
    @composes: kim_single_cut_distE *)
Lemma kim_single_snd_weightE :
  fdistmap (fun u : five_card_leakage.Omega => u.2)
    (kim_input_dist eps_lt_inv5 eps_gt_neg4inv5)
  = kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5.
Proof.
by rewrite /kim_input_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_single_cut_distE — the one-biased-cut model's cut distribution is the
    image of Kim's weight distribution under the rotation realization.
    @main architecture: sa_cut_dist kim_single_sample = fdistmap (fun k : 'I_5
    => (fc_sigma ^+ k)%g) (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5). *)
Lemma kim_single_cut_distE :
  sa_cut_dist kim_single_sample
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
rewrite /sa_cut_dist /kim_single_sample /= /five_card_sample_cut.
by rewrite -kim_single_snd_weightE fdistmap_comp.
Qed.

(** kim_repeated_snd_wordE — the word marginal of the repeated model's
    distribution is the weighted word distribution.
    @composes: kim_repeated_cut_distE *)
Lemma kim_repeated_snd_wordE :
  fdistmap (fun u : kim_repeated_sampleT => u.2) kim_repeated_dist
  = @word_weighted R 4 L (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
by rewrite /kim_repeated_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_repeated_cut_distE — the repeated-cut model's cut distribution is the
    weighted word shuffle at word length L.
    @main architecture: sa_cut_dist kim_repeated_sample =
    rho_from_words_weighted L fc_kim_sigmas (kim_weight_dist eps_lt_inv5
    eps_gt_neg4inv5). *)
Lemma kim_repeated_cut_distE :
  sa_cut_dist kim_repeated_sample
  = @rho_from_words_weighted R 3 4 L fc_kim_sigmas
      (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
rewrite /sa_cut_dist /kim_repeated_sample /= /rho_from_words_weighted.
by rewrite -kim_repeated_snd_wordE fdistmap_comp.
Qed.

(******************************************************************************)
(*     The executed seat distribution of the repeated model                   *)
(******************************************************************************)

(** kim_repeated_seat_distE — the repeated model's executed seat distribution
    is the pushforward of the static observation.
    @main architecture: sa_seat_dist kim_repeated_sample 0 i = fdistmap
    (sa_static_seat_view kim_repeated_sample five_card_content_obs i)
    kim_repeated_dist; the endpoint hypothesis of sa_seat_distE is discharged
    by five_card_exec_endpoints, which quantifies over every cut and so applies
    at the word-evaluation cut. *)
Lemma kim_repeated_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @sa_seat_dist R mpF five_card_exec_plug kim_repeated_sample 0 i
  = fdistmap (@sa_static_seat_view R mpF five_card_exec_plug
                kim_repeated_sample five_card_content_obs i) kim_repeated_dist.
Proof.
by apply: sa_seat_distE => -[[a b] v]; exact: five_card_exec_endpoints.
Qed.

(******************************************************************************)
(*     The decoded colour reader of the executed endpoints                    *)
(******************************************************************************)

(** five_card_layout_colourE — the dealt layout entry at the monodromy image
    of a seat's start decodes to the colour the leakage space reads there.
    @composes: five_card_endpoint_colourE
    The orientation is cut = fc_sigma ^+ k: the pair denboer_player_trace_shape
    and denboer_player_trace_ok ties the executed layout entry at that cut to
    nth false (arr w) i. *)
Lemma five_card_layout_colourE (a b : bool) (k : 'I_5) (i : 'I_5) :
  decode_bool (tnth (den_boer_layout (a, b))
    (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ k)%g
       (tnth (pi_starts FiveCardKim_PI) i)))
  = nth false (five_card_leakage.arr (a, b, k)) i.
Proof.
rewrite -(denboer_player_trace_shape R a b k i).
rewrite denboer_player_trace_ok /comp_RV decode_encode_bool.
by rewrite /ViewA /thead tnth_map (tnth_nth 0%N).
Qed.

(** five_card_decode_ord0 — the card position ord0 decodes to the club colour.
    @composes: five_card_endpoint_colourE
    This is the value the colour reader returns at a position outside the five
    dealt cards, and it agrees with the default false of ViewA. The equality is
    not closed by computation: decode_bool compares against inord 1, whose
    reduction is blocked by the opaque idP, so the value is read off through
    inordK instead. *)
Lemma five_card_decode_ord0 : decode_bool ord0 = false.
Proof. by rewrite /decode_bool -(inj_eq val_inj) /= inordK. Qed.

(** five_card_exec_colour_view — the executed endpoints decoded as colours
    at a list of card positions.
    @intent: the tuple of decode_bool of the entries of exec_endpoints at the
    positions of A, in the order and with the multiplicity of A, taking the
    default card position ord0, hence the colour false, outside the five dealt
    cards.
    Naming: intentional; _colour_view names the decoded reader, and the entries
    of A are seat indices into the endpoint list rather than seats of the
    profile's index type, so no MathComp suffix denotes it. *)
Definition five_card_exec_colour_view (A : seq nat) (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) : (size A).-tuple bool :=
  map_tuple (fun j => decode_bool
    (nth ord0 (@exec_endpoints mpF five_card_exec_plug ab w0 0) j))
    (in_tuple A).

(** five_card_endpoint_colourE — the decoded executed endpoint at a card
    position is the colour the leakage space reads there, at every position.
    @composes: five_card_colour_viewE
    Positions below five go through five_card_exec_seat_endpointE and
    five_card_layout_colourE; positions from five on are the two default
    values, ord0 on the executed side and false on the leakage side. *)
Lemma five_card_endpoint_colourE (w : five_card_leakage.Omega) (j : nat) :
  decode_bool (nth ord0 (@exec_endpoints mpF five_card_exec_plug
                  w.1 (five_card_group.fc_sigma ^+ w.2)%g 0) j)
  = nth false (five_card_leakage.arr w) j.
Proof.
case: w => -[a b] k /=.
have [Hj|Hj] := ltnP j 5.
  have -> : nth ord0 (@exec_endpoints mpF five_card_exec_plug
      (a, b) (five_card_group.fc_sigma ^+ k)%g 0) j
    = @exec_seat_endpoint mpF five_card_exec_plug
        (a, b) (five_card_group.fc_sigma ^+ k)%g 0 (Ordinal Hj) by [].
  rewrite five_card_exec_seat_endpointE /five_card_content_obs.
  exact: five_card_layout_colourE.
have Hsz : size (@exec_endpoints mpF five_card_exec_plug (a, b)
                   (five_card_group.fc_sigma ^+ k)%g 0) = 5.
  exact: (exec_endpoints_size (five_card_exec_endpoints a b _)).
rewrite [in RHS]nth_default;
  last by rewrite /fc_shuffle size_rot fc_arrange_size.
rewrite nth_default; last by rewrite Hsz.
exact: five_card_decode_ord0.
Qed.

(** five_card_colour_viewE — the executed colour reader is the leakage space's
    partial view, at the rotation cut.
    @main correctness: five_card_exec_colour_view A w.1 (fc_sigma ^+ w.2)%g =
    ViewA R A w, at every position list A and every leakage outcome w. *)
Lemma five_card_colour_viewE (A : seq nat) (w : five_card_leakage.Omega) :
  five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g
  = ViewA R A w.
Proof.
apply: val_inj => /=.
by apply: eq_map => j; exact: five_card_endpoint_colourE.
Qed.

(** five_card_colour_view_RV_E — the executed colour reader is Kim's view
    random variable.
    @main architecture: the function sending a leakage outcome w to
    five_card_exec_colour_view A w.1 (fc_sigma ^+ w.2)%g is
    kim_view eps_lt_inv5 eps_gt_neg4inv5 A as a map from Omega to
    (size A).-tuple bool. *)
Lemma five_card_colour_view_RV_E (A : seq nat) :
  (fun w : five_card_leakage.Omega =>
     five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g)
  = kim_view eps_lt_inv5 eps_gt_neg4inv5 A
    :> (five_card_leakage.Omega -> (size A).-tuple bool).
Proof. by apply: funext => w; rewrite five_card_colour_viewE. Qed.

(******************************************************************************)
(*     Kim's input-privacy bound at the executed colour reader                *)
(******************************************************************************)

Section five_card_input_privacy_transport.

Hypothesis eps_small : 0 < 5%:R^-1 - `|eps|.

(** five_card_colour_view_leak_bound — the executed colour reader carries at
    most kim_leak_bound eps about the inputs given the output.
    @main security: cond_mutual_info of the joint distribution of the inputs,
    the executed colour reader and the secret is at most kim_leak_bound eps.
    Naming: intentional; _leak_bound names the conditional-mutual-information
    bound carried by a reader, matching kim_leak_bound, and no MathComp suffix
    denotes it. *)
Corollary five_card_colour_view_leak_bound (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs eps_lt_inv5 eps_gt_neg4inv5,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret eps_lt_inv5 eps_gt_neg4inv5]) <= kim_leak_bound eps.
Proof. by rewrite five_card_colour_view_RV_E; exact: kim_input_private. Qed.

End five_card_input_privacy_transport.

End five_card_sample_models.

(******************************************************************************)
(*     The concrete seven-cut model at bias 1/100                             *)
(******************************************************************************)

Section five_card_centi_model.

Variable R : realType.

(** kim_centi_repeated_sample — the concrete seven-cut model.
    @intent: kim_repeated_sample at bias 1/100 with Kim's centi constraint pack
    and word length 7. *)
Definition kim_centi_repeated_sample :=
  @kim_repeated_sample R (1 / 100) (kim_centi_lt R) (kim_centi_gt R) 7.

(** kim_centi_witness_rhoE — the centi certificate bundle's marginal bound
    carries the weighted word shuffle at word length 7.
    @composes: kim_centi_cut_distE *)
Lemma kim_centi_witness_rhoE :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R))
  = @rho_from_words_weighted R 3 4 7 fc_kim_sigmas
      (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)).
Proof. by []. Qed.

(** kim_centi_cut_distE — the concrete model's cut distribution is the
    marginal bound of the centi certificate bundle.
    @main architecture: sa_cut_dist kim_centi_repeated_sample = sw_rho_dist
    (scb_bound (kim_security_bundle_centi R)). *)
Lemma kim_centi_cut_distE :
  sa_cut_dist kim_centi_repeated_sample
  = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
Proof.
by rewrite kim_centi_witness_rhoE /kim_centi_repeated_sample
   kim_repeated_cut_distE.
Qed.

(** kim_centi_repeated_seat_distE — the concrete model's executed seat
    distribution is the pushforward of the static observation.
    @intent: kim_repeated_seat_distE instantiated at bias 1/100 and word
    length 7, the seven-cut member of the repeated family. *)
Definition kim_centi_repeated_seat_distE :=
  @kim_repeated_seat_distE R (1 / 100) (kim_centi_lt R) (kim_centi_gt R) 7.

End five_card_centi_model.
