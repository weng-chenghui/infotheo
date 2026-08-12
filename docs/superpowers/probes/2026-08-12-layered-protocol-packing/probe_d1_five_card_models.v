(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_d1_five_card_models: the four five-card sample models, their cut      *)
(* distributions, the decoded colour reader and the hypothesis-vacuity check.  *)
(*                                                                            *)
(* Probe unit D1 of the 2026-08-12 layered-protocol-packing gate: the          *)
(* five-card half of section 15.5 together with section 15.7.  Everything is   *)
(* stated over the landed R-parameterized API of five_card_exec.v,             *)
(* five_card_kim.v, kim_input_privacy.v and five_card_leakage.v.               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_single_sample     == the five-card sample adapter whose sample space  *)
(*                            is the den Boer leakage space under Kim's        *)
(*                            biased joint distribution                        *)
(*   kim_repeated_sampleT  == the repeated-cut sample space, a committed pair  *)
(*                            together with an L-letter word                   *)
(*   kim_repeated_dist     == uniform committed pairs times the weighted word  *)
(*                            distribution                                     *)
(*   kim_repeated_sample   == the sample adapter whose cut is the word         *)
(*                            evaluation of the sampled word                   *)
(*   five_card_exec_colour_view == the executed endpoints of a run, decoded    *)
(*                            as colours at a list of card positions           *)
(*   kim_centi_repeated_sample  == kim_repeated_sample at bias 1/100 and word  *)
(*                            length 7                                         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   kim_single_cut_distE  == the biased sample's cut distribution is the      *)
(*                            image of Kim's weight distribution under the     *)
(*                            rotation realization                             *)
(*   kim_repeated_cut_distE == the repeated sample's cut distribution is the   *)
(*                            weighted word shuffle                            *)
(*   five_card_colour_viewE == the decoded executed colour reader agrees with  *)
(*                            the leakage-space partial view ViewA             *)
(*   five_card_colour_view_RV_E == the same agreement as an equality of        *)
(*                            random variables on Kim's joint distribution     *)
(*   five_card_colour_view_leak_bound == the executed colour reader carries at *)
(*                            most kim_leak_bound eps about the inputs given   *)
(*                            the output                                       *)
(*   kim_repeated_seat_distE == the repeated sample's executed seat            *)
(*                            distribution is the static pushforward           *)
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

Section d1_five_card_models.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(******************************************************************************)
(*     Part 1: the four sample models                                         *)
(******************************************************************************)

(* Model 1, the uniform regression, is the landed five_card_sample: the den
   Boer leakage space Omega under the uniform distribution P, argument the
   committed pair and cut the sampled rotation.  Its cut distribution is the
   landed five_card_sample_cut_distE, and the same distribution read as the
   den Boer member's witness is den_boer_sample_cut_witnessE.  Neither is
   reproved here. *)
Check (five_card_sample Hlt Hgt Hspec L).
Check (@five_card_sample_cut_distE R eps Hlt Hgt Hspec L).
Check (@den_boer_sample_cut_witnessE R eps Hlt Hgt Hspec L).

(** kim_single_sample — model 2, one biased cut.
    @intent: the sample layer over five_card_exec_plug whose sample space is
    the den Boer leakage space Omega under Kim's biased joint distribution
    kim_input_dist, the run argument being the committed pair and the cut the
    realized rotation; the carrier and both maps are those of five_card_sample
    and only the distribution differs. *)
Definition kim_single_sample : SampleAdapter (five_card_exec_plug Hlt Hgt Hspec L) :=
  @MkSampleAdapter R mpF (five_card_exec_plug Hlt Hgt Hspec L)
    five_card_leakage.Omega (kim_input_dist Hlt Hgt)
    five_card_sample_arg (five_card_sample_cut Hlt Hgt Hspec L).

(** kim_repeated_sampleT — model 3's sample space.
    @intent: a committed pair of bits together with an L-letter word over the
    five rotation generators. *)
Definition kim_repeated_sampleT : finType :=
  [the finType of ((bool * bool) * (L.-tuple 'I_5))%type].

(** kim_repeated_dist — model 3's distribution.
    @intent: the product of the uniform distribution on committed pairs with
    the weighted word distribution built from Kim's generator weights. *)
Definition kim_repeated_dist : R.-fdist kim_repeated_sampleT :=
  ((fdist_uniform kim_input_privacy.card_bool2)
   `x (@word_weighted R 4 L (kim_weight_dist Hlt Hgt)))%fdist.

(** kim_repeated_sample — model 3, L repeated biased cuts.
    @intent: the sample layer over five_card_exec_plug whose sample space is
    kim_repeated_sampleT under kim_repeated_dist, the run argument being the
    committed pair and the cut the word evaluation of the sampled word. *)
Definition kim_repeated_sample : SampleAdapter (five_card_exec_plug Hlt Hgt Hspec L) :=
  @MkSampleAdapter R mpF (five_card_exec_plug Hlt Hgt Hspec L)
    kim_repeated_sampleT kim_repeated_dist
    (fun u => u.1) (fun u => @word_eval FiveCardKim_M L u.2).

(******************************************************************************)
(*     Part 2: the cut distributions of the models                            *)
(******************************************************************************)

(** kim_single_snd_weightE — the rotation marginal of Kim's joint distribution
    is Kim's weight distribution.
    @composes: kim_single_cut_distE *)
Lemma kim_single_snd_weightE :
  fdistmap (fun u : five_card_leakage.Omega => u.2) (kim_input_dist Hlt Hgt)
  = kim_weight_dist Hlt Hgt.
Proof.
by rewrite /kim_input_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_single_cut_distE — the one-biased-cut model's cut distribution is the
    image of Kim's weight distribution under the rotation realization.
    @main architecture: sa_cut_dist kim_single_sample = fdistmap
    (fun k : 'I_5 => (fc_sigma ^+ k)%g) (kim_weight_dist Hlt Hgt). *)
Lemma kim_single_cut_distE :
  sa_cut_dist kim_single_sample
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (kim_weight_dist Hlt Hgt).
Proof.
rewrite /sa_cut_dist /kim_single_sample /= /five_card_sample_cut.
by rewrite -kim_single_snd_weightE fdistmap_comp.
Qed.

(** kim_repeated_snd_wordE — the word marginal of the repeated model's
    distribution is the weighted word distribution.
    @composes: kim_repeated_cut_distE *)
Lemma kim_repeated_snd_wordE :
  fdistmap (fun u : kim_repeated_sampleT => u.2) kim_repeated_dist
  = @word_weighted R 4 L (kim_weight_dist Hlt Hgt).
Proof.
by rewrite /kim_repeated_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_repeated_cut_distE — the repeated-cut model's cut distribution is the
    weighted word shuffle at word length L.
    @main architecture: sa_cut_dist kim_repeated_sample =
    rho_from_words_weighted L fc_kim_sigmas (kim_weight_dist Hlt Hgt). *)
Lemma kim_repeated_cut_distE :
  sa_cut_dist kim_repeated_sample
  = @rho_from_words_weighted R 3 4 L fc_kim_sigmas (kim_weight_dist Hlt Hgt).
Proof.
rewrite /sa_cut_dist /kim_repeated_sample /= /rho_from_words_weighted.
by rewrite -kim_repeated_snd_wordE fdistmap_comp.
Qed.

(******************************************************************************)
(*     Part 3: the decoded colour reader                                      *)
(******************************************************************************)

(** d1_layout_colourE — the dealt layout entry at the monodromy image of a
    seat's start decodes to the colour the leakage space reads at that seat.
    @composes: d1_endpoint_colourE
    The orientation is cut = fc_sigma ^+ k: the landed pair
    denboer_player_trace_shape and denboer_player_trace_ok already ties the
    executed layout entry at that cut to nth false (arr w) i.  The opposite
    orientation is refuted by d1_orientation_inv_attempt below. *)
Lemma d1_layout_colourE (a b : bool) (k : 'I_5) (i : 'I_5) :
  decode_bool (tnth (den_boer_layout (a, b))
    (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ k)%g
       (tnth (pi_starts FiveCardKim_PI) i)))
  = nth false (five_card_leakage.arr (a, b, k)) i.
Proof.
rewrite -(denboer_player_trace_shape R a b k i).
rewrite denboer_player_trace_ok /comp_RV decode_encode_bool.
by rewrite /ViewA /thead tnth_map (tnth_nth 0%N).
Qed.

(* The inverse orientation cut = (fc_sigma ^+ k)^-1 does not admit the same
   script.  Harvested from rocq_check on the un-Failed command:

   The RHS of (denboer_player_trace_shape R a b k i)
       (tnth (den_boer_layout (a, b))
          (pgg_rho (fc_sigma ^+ k)%g (tnth (pi_starts FiveCardKim_PI) i)))
   does not match any subterm of the goal *)
Fail Definition d1_orientation_inv_attempt (a b : bool) (k : 'I_5) (i : 'I_5) :
  decode_bool (tnth (den_boer_layout (a, b))
    (@pgg_rho FiveCardKim_M ((five_card_group.fc_sigma ^+ k)^-1)%g
       (tnth (pi_starts FiveCardKim_PI) i)))
  = nth false (five_card_leakage.arr (a, b, k)) i :=
  ltac:(rewrite -(denboer_player_trace_shape R a b k i);
        rewrite denboer_player_trace_ok /comp_RV decode_encode_bool;
        by rewrite /ViewA /thead tnth_map (tnth_nth 0%N)).

(** d1_decode_ord0 — the card position ord0 decodes to the club colour.
    @composes: d1_endpoint_colourE
    This is the value the colour reader returns at a position outside the five
    dealt cards, and it agrees with the default false of ViewA.  The equality
    is not closed by computation: decode_bool compares against inord 1, whose
    reduction is blocked by the opaque idP, so the value is read off through
    inordK instead. *)
Lemma d1_decode_ord0 : decode_bool ord0 = false.
Proof. by rewrite /decode_bool -(inj_eq val_inj) /= inordK. Qed.

(** five_card_exec_colour_view — the executed endpoints decoded as colours at a
    list of card positions.
    @intent: the tuple of decode_bool of the entries of exec_endpoints at the
    positions of A, in the order and with the multiplicity of A, taking the
    default card position ord0 (hence the colour false) outside the five dealt
    cards. *)
Definition five_card_exec_colour_view (A : seq nat) (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) : (size A).-tuple bool :=
  map_tuple (fun j => decode_bool
    (nth ord0 (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L) ab w0 0) j))
    (in_tuple A).

(** d1_endpoint_colourE — the decoded executed endpoint at a card position is
    the colour the leakage space reads there, at every position.
    @composes: five_card_colour_viewE
    Positions below five go through five_card_exec_seat_endpointE and
    d1_layout_colourE; positions from five on are the two default values, ord0
    on the executed side and false on the leakage side. *)
Lemma d1_endpoint_colourE (w : five_card_leakage.Omega) (j : nat) :
  decode_bool (nth ord0 (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L)
                  w.1 (five_card_group.fc_sigma ^+ w.2)%g 0) j)
  = nth false (five_card_leakage.arr w) j.
Proof.
case: w => -[a b] k /=.
have [Hj|Hj] := ltnP j 5.
  have -> : nth ord0 (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L)
      (a, b) (five_card_group.fc_sigma ^+ k)%g 0) j
    = @exec_seat_endpoint R mpF (five_card_exec_plug Hlt Hgt Hspec L)
        (a, b) (five_card_group.fc_sigma ^+ k)%g 0 (Ordinal Hj) by [].
  rewrite five_card_exec_seat_endpointE /five_card_content_obs.
  exact: d1_layout_colourE.
have Hsz : size (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L) (a, b)
                   (five_card_group.fc_sigma ^+ k)%g 0) = 5.
  exact: (exec_endpoints_size (five_card_exec_endpoints Hlt Hgt Hspec L a b _)).
rewrite [in RHS]nth_default; last by rewrite /fc_shuffle size_rot fc_arrange_size.
rewrite nth_default; last by rewrite Hsz.
exact: d1_decode_ord0.
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
by apply: eq_map => j; exact: d1_endpoint_colourE.
Qed.

(** d1_point_dup — the leakage outcome at which the ordered duplicate position
    list is read.
    @intent: the committed pair (true, false) with the identity rotation. *)
Definition d1_point_dup : five_card_leakage.Omega := (true, false, ord0).

(** d1_point_range — the leakage outcome at which the out-of-range position
    list is read.
    @intent: the committed pair (true, false) with the rotation 2. *)
Definition d1_point_range : five_card_leakage.Omega := (true, false, @Ordinal 5 2 isT).

(** d1_colour_view_dup — the colour reader respects the order and the
    multiplicity of its position list.
    @composes: five_card_colour_viewE
    At the outcome d1_point_dup the dealt row is [false; true; true; false;
    true], so the position list [:: 1; 3; 1] reads [:: true; false; true]. *)
Lemma d1_colour_view_dup :
  val (five_card_exec_colour_view [:: 1; 3; 1]%N d1_point_dup.1
         (five_card_group.fc_sigma ^+ d1_point_dup.2)%g)
  = [:: true; false; true].
Proof. by rewrite five_card_colour_viewE. Qed.

(** d1_colour_view_range — the colour reader returns false outside the five
    dealt cards.
    @composes: five_card_colour_viewE
    At the outcome d1_point_range the dealt row is [true; false; true; false;
    true], so the position list [:: 0; 7] reads [:: true; false], the second
    entry being the out-of-range default. *)
Lemma d1_colour_view_range :
  val (five_card_exec_colour_view [:: 0; 7]%N d1_point_range.1
         (five_card_group.fc_sigma ^+ d1_point_range.2)%g)
  = [:: true; false].
Proof. by rewrite five_card_colour_viewE. Qed.

(** five_card_colour_view_RV_E — the executed colour reader is Kim's view
    random variable.
    @main architecture: the function sending a leakage outcome w to
    five_card_exec_colour_view A w.1 (fc_sigma ^+ w.2)%g is kim_view Hlt Hgt A
    as a map from Omega to (size A).-tuple bool. *)
Lemma five_card_colour_view_RV_E (A : seq nat) :
  (fun w : five_card_leakage.Omega =>
     five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g)
  = kim_view Hlt Hgt A :> (five_card_leakage.Omega -> (size A).-tuple bool).
Proof. by apply: funext => w; rewrite five_card_colour_viewE. Qed.

(******************************************************************************)
(*     Part 4: the executed seat distribution of the repeated model           *)
(******************************************************************************)

(** kim_repeated_seat_distE — the repeated model's executed seat distribution
    is the pushforward of the static observation.
    @main architecture: sa_seat_dist kim_repeated_sample 0 i = fdistmap
    (sa_static_seat_view kim_repeated_sample five_card_content_obs i)
    kim_repeated_dist; the endpoint hypothesis of sa_seat_distE is discharged
    by five_card_exec_endpoints, which quantifies over every cut and so applies
    at the word-evaluation cut. *)
Lemma kim_repeated_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @sa_seat_dist R mpF (five_card_exec_plug Hlt Hgt Hspec L) kim_repeated_sample 0 i
  = fdistmap (@sa_static_seat_view R mpF (five_card_exec_plug Hlt Hgt Hspec L)
                kim_repeated_sample five_card_content_obs i) kim_repeated_dist.
Proof. by apply: sa_seat_distE => -[[a b] v]; exact: five_card_exec_endpoints. Qed.

(******************************************************************************)
(*     The transport of Kim's input-privacy bound to the executed reader      *)
(******************************************************************************)

Section d1_transport.

Hypothesis Hsmall : 0 < 5%:R^-1 - `|eps|.

(** five_card_colour_view_leak_bound — the executed colour reader carries at
    most kim_leak_bound eps about the inputs given the output.
    @main security: cond_mutual_info of the joint distribution of the inputs,
    the executed colour reader and the secret is at most kim_leak_bound eps.
    The hypothesis set is Hlt, Hgt and Hsmall; Hspec and L enter only through
    the execution plug the reader is stated over. *)
Corollary five_card_colour_view_leak_bound (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs Hlt Hgt,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret Hlt Hgt]) <= kim_leak_bound eps.
Proof. by rewrite five_card_colour_view_RV_E; exact: kim_input_private. Qed.

End d1_transport.

End d1_five_card_models.

(******************************************************************************)
(*     The concrete seven-cut model at bias 1/100                             *)
(******************************************************************************)

Section d1_concrete.

Variable R : realType.

Let cLt := kim_centi_lt R.
Let cGt := kim_centi_gt R.
Let cSpec := kim_centi_spec R.

(** kim_centi_repeated_sample — model 4, the concrete seven-cut model.
    @intent: kim_repeated_sample at bias 1/100 with Kim's centi constraint pack
    and word length 7. *)
Definition kim_centi_repeated_sample :=
  @kim_repeated_sample R (1 / 100) cLt cGt cSpec 7.

(** kim_centi_witness_rhoE — the centi security witness carries the weighted
    word shuffle at word length 7.
    @composes: kim_centi_cut_distE *)
Lemma kim_centi_witness_rhoE :
  sw_rho_dist (kim_security_witness_centi R)
  = @rho_from_words_weighted R 3 4 7 fc_kim_sigmas (kim_weight_dist cLt cGt).
Proof. by []. Qed.

(** kim_centi_cut_distE — the concrete model's cut distribution is the centi
    security witness's distribution.
    @main architecture: sa_cut_dist kim_centi_repeated_sample = sw_rho_dist
    (kim_security_witness_centi R). *)
Lemma kim_centi_cut_distE :
  sa_cut_dist kim_centi_repeated_sample = sw_rho_dist (kim_security_witness_centi R).
Proof. by rewrite kim_centi_witness_rhoE /kim_centi_repeated_sample
  kim_repeated_cut_distE. Qed.

(** kim_centi_repeated_seat_distE — the concrete model's executed seat
    distribution is the pushforward of the static observation.
    @composes: kim_repeated_seat_distE *)
Definition kim_centi_repeated_seat_distE :=
  @kim_repeated_seat_distE R (1 / 100) cLt cGt cSpec 7.

Check kim_centi_repeated_seat_distE.

End d1_concrete.

(******************************************************************************)
(*     Section 15.7: which theorem consumes which assumption                  *)
(******************************************************************************)

(* The five-card layer carries four side conditions on the bias eps and one
   word length.  Each declaration below consumes a strict subset:

     declaration                    Hlt   Hgt   Hspec  Hsmall   L
     ---------------------------    ----  ----  -----  -------  ----
     kim_weight_dist                 x     x      .       .      .
     kim_input_dist                  x     x      .       .      .
     kim_view / kim_inputs           x     x      .       .      .
     kim_secret                      x     x      .       .      .
     kim_input_private               x     x      .       x      .
     five_card_colour_view_leak_bound x    x      x       x      x
     fc_kim_security_bound           x     x      x       .      x
     fc_kim_security_witness         x     x      x       .      x
     five_card_profile               x     x      x       .      x
     five_card_exec_plug             x     x      x       .      x
     kim_single_sample               x     x      x       .      x
     kim_repeated_sample             x     x      x       .      x

   Hlt is eps < 1/5, Hgt is -(4/5) < eps, Hspec is |eps| < 4/5 and Hsmall is
   0 < 1/5 - |eps|.  Hlt and Hgt are the two weight-positivity conditions;
   Hspec is the spectral-gap condition of the security witness; Hsmall is the
   denominator condition of kim_leak_bound, declared at kim_input_privacy.v
   line 420 and consumed by kim_input_private through kim_div_bound.  Hspec and
   L are absent from kim_input_private itself and enter
   five_card_colour_view_leak_bound only because the executed reader is stated
   over five_card_exec_plug, which carries the whole profile.  The bound
   Hsmall is not implied by Hlt and Hgt: at eps = -1/2 both Hlt and Hgt hold
   while 1/5 - |eps| is negative. *)

Section d1_hypothesis_vacuity.

Variable R : realType.

(** d1_eps0_smallbias — the small-bias condition holds at bias 0.
    @composes: d1_eps0_leak_bound *)
Lemma d1_eps0_smallbias : 0 < 5%:R^-1 - `|0 : R|.
Proof. by rewrite normr0 subr0 invr_gt0 ltr0n. Qed.

(** d1_centi_smallbias — the small-bias condition holds at bias 1/100.
    @composes: d1_centi_leak_bound *)
Lemma d1_centi_smallbias : 0 < 5%:R^-1 - `|1 / 100 : R|.
Proof.
rewrite subr_gt0 ger0_norm; last by rewrite divr_ge0.
exact: (kim_centi_lt R).
Qed.

(* Bias 0: the den Boer member.  Every hypothesis of the five-card layer is
   instantiated by a landed constant. *)

(** d1_eps0_plug — the execution plug at bias 0 and word length 1.
    @intent: five_card_exec_plug fed the den Boer constraint pack. *)
Definition d1_eps0_plug :=
  @five_card_exec_plug R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1.

(** d1_eps0_single — the one-biased-cut model at bias 0.
    @intent: kim_single_sample fed the den Boer constraint pack. *)
Definition d1_eps0_single :=
  @kim_single_sample R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1.

(** d1_eps0_repeated — the repeated-cut model at bias 0.
    @intent: kim_repeated_sample fed the den Boer constraint pack. *)
Definition d1_eps0_repeated :=
  @kim_repeated_sample R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1.

(** d1_eps0_leak_bound — the transported input-privacy bound at bias 0.
    @composes: five_card_colour_view_leak_bound *)
Definition d1_eps0_leak_bound :=
  @five_card_colour_view_leak_bound R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1 d1_eps0_smallbias.

(** d1_eps0_security_bound — the dealing-phase spectral bound at bias 0.
    @composes: fc_kim_security_bound *)
Definition d1_eps0_security_bound :=
  @fc_kim_security_bound R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1.

(* Bias 1/100: Kim's centi member, the same four instantiations. *)

(** d1_centi_plug — the execution plug at bias 1/100 and word length 7.
    @intent: five_card_exec_plug fed Kim's centi constraint pack. *)
Definition d1_centi_plug :=
  @five_card_exec_plug R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
    (kim_centi_spec R) 7.

(** d1_centi_single — the one-biased-cut model at bias 1/100.
    @intent: kim_single_sample fed Kim's centi constraint pack. *)
Definition d1_centi_single :=
  @kim_single_sample R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
    (kim_centi_spec R) 7.

(** d1_centi_repeated — the repeated-cut model at bias 1/100.
    @intent: kim_repeated_sample fed Kim's centi constraint pack. *)
Definition d1_centi_repeated :=
  @kim_repeated_sample R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
    (kim_centi_spec R) 7.

(** d1_centi_leak_bound — the transported input-privacy bound at bias 1/100.
    @composes: five_card_colour_view_leak_bound *)
Definition d1_centi_leak_bound :=
  @five_card_colour_view_leak_bound R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
    (kim_centi_spec R) 7 d1_centi_smallbias.

(** d1_centi_security_bound — the dealing-phase spectral bound at bias 1/100.
    @composes: fc_kim_security_bound *)
Definition d1_centi_security_bound :=
  @fc_kim_security_bound R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
    (kim_centi_spec R) 7.

Check d1_eps0_leak_bound.
Check d1_centi_leak_bound.
Check d1_eps0_security_bound.
Check d1_centi_security_bound.

End d1_hypothesis_vacuity.

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions kim_single_cut_distE.
Print Assumptions kim_repeated_cut_distE.
Print Assumptions five_card_colour_viewE.
Print Assumptions five_card_colour_view_RV_E.
Print Assumptions five_card_colour_view_leak_bound.
Print Assumptions kim_repeated_seat_distE.
Print Assumptions kim_centi_cut_distE.
Print Assumptions d1_colour_view_dup.
Print Assumptions d1_colour_view_range.
