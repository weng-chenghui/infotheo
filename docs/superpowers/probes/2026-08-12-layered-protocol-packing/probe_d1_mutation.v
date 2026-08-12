(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe D1, mutation check: the bias, the cut map, the decoder and the        *)
(* small-bias hypothesis are all load-bearing                                  *)
(*                                                                            *)
(* Section 15.5 claims that the four five-card sample models differ only in    *)
(* their sample distribution and cut map, that the decoded colour reader is    *)
(* the leakage-space partial view, and that the transported input-privacy      *)
(* bound needs the hypotheses section 15.7 lists.  This file checks the four   *)
(* claims that make those statements honest.                                   *)
(*                                                                            *)
(*   M1  the bias is load-bearing.  The uniform model's cut distribution is    *)
(*       the uniform rotation image, and the same script applied to the        *)
(*       biased model against the same uniform image is rejected.  The         *)
(*       rejection is not an artefact of the script: at bias 1/100 the two     *)
(*       distributions are provably distinct                                   *)
(*       (kim_single_cut_dist_neq_uniform), because the one-cut variation      *)
(*       distance is 1/50 under the bias and 0 under the uniform weights.      *)
(*                                                                            *)
(*   M2  the cut map is load-bearing.  Replacing the word evaluation by the    *)
(*       constant identity cut breaks the word-shuffle equation, and the       *)
(*       rejection survives replacing the closing by [] with exact: erefl.     *)
(*                                                                            *)
(*   M3  the decoder is load-bearing.  Replacing decode_bool by the constant   *)
(*       false breaks the agreement with ViewA both in the general form (M3a)  *)
(*       and at the concrete reveal where a heart is dealt (M3b).              *)
(*                                                                            *)
(*   M4  the small-bias hypothesis is load-bearing.  In a section carrying     *)
(*       only the two positivity conditions and the spectral condition, the    *)
(*       transported bound cannot be instantiated, neither by omitting the     *)
(*       hypothesis argument (M4a) nor by leaving it as a hole (M4b).          *)
(*                                                                            *)
(* Each rejection is wrapped in Fail, so the file compiles green exactly when  *)
(* all seven are rejected.  The unmutated twins are declared first as positive *)
(* controls, so a Fail cannot pass by a mistake shared with the honest case.   *)
(*                                                                            *)
(* The message quoted above a Fail is the verbatim diagnostic obtained by      *)
(* removing that one Fail and re-elaborating the declaration under the         *)
(* interactive checker: batch mode does not echo the message of a Fail that    *)
(* succeeds.                                                                   *)
(*                                                                            *)
(* The section d1_copies below repeats the parts of                            *)
(* probe_d1_five_card_models.v that these checks need.  They are copies rather *)
(* than imports because the probe directory carries a dash-bearing name and so *)
(* is not a legal Rocq logical path under the -R flags of rebuild.sh.          *)
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

(******************************************************************************)
(*     The copied part of probe_d1_five_card_models.v                         *)
(******************************************************************************)

Section d1_copies.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** kim_single_sample — model 2, one biased cut.
    @intent: copy of probe_d1_five_card_models.kim_single_sample. *)
Definition kim_single_sample : SampleAdapter (five_card_exec_plug Hlt Hgt Hspec L) :=
  @MkSampleAdapter R mpF (five_card_exec_plug Hlt Hgt Hspec L)
    five_card_leakage.Omega (kim_input_dist Hlt Hgt)
    five_card_sample_arg (five_card_sample_cut Hlt Hgt Hspec L).

(** kim_repeated_sampleT — model 3's sample space.
    @intent: copy of probe_d1_five_card_models.kim_repeated_sampleT. *)
Definition kim_repeated_sampleT : finType :=
  [the finType of ((bool * bool) * (L.-tuple 'I_5))%type].

(** kim_repeated_dist — model 3's distribution.
    @intent: copy of probe_d1_five_card_models.kim_repeated_dist. *)
Definition kim_repeated_dist : R.-fdist kim_repeated_sampleT :=
  ((fdist_uniform kim_input_privacy.card_bool2)
   `x (@word_weighted R 4 L (kim_weight_dist Hlt Hgt)))%fdist.

(** kim_repeated_sample — model 3, L repeated biased cuts.
    @intent: copy of probe_d1_five_card_models.kim_repeated_sample. *)
Definition kim_repeated_sample : SampleAdapter (five_card_exec_plug Hlt Hgt Hspec L) :=
  @MkSampleAdapter R mpF (five_card_exec_plug Hlt Hgt Hspec L)
    kim_repeated_sampleT kim_repeated_dist
    (fun u => u.1) (fun u => @word_eval FiveCardKim_M L u.2).

(** kim_single_snd_weightE — the rotation marginal of Kim's joint distribution.
    @composes: kim_single_cut_distE *)
Lemma kim_single_snd_weightE :
  fdistmap (fun u : five_card_leakage.Omega => u.2) (kim_input_dist Hlt Hgt)
  = kim_weight_dist Hlt Hgt.
Proof.
by rewrite /kim_input_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_single_cut_distE — the one-biased-cut model's cut distribution.
    @composes: kim_single_cut_dist_neq_uniform *)
Lemma kim_single_cut_distE :
  sa_cut_dist kim_single_sample
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (kim_weight_dist Hlt Hgt).
Proof.
rewrite /sa_cut_dist /kim_single_sample /= /five_card_sample_cut.
by rewrite -kim_single_snd_weightE fdistmap_comp.
Qed.

(** kim_repeated_snd_wordE — the word marginal of the repeated model.
    @composes: mu2_control *)
Lemma kim_repeated_snd_wordE :
  fdistmap (fun u : kim_repeated_sampleT => u.2) kim_repeated_dist
  = @word_weighted R 4 L (kim_weight_dist Hlt Hgt).
Proof.
by rewrite /kim_repeated_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** d1_layout_colourE — the dealt layout entry decodes to the leakage colour.
    @composes: d1_endpoint_colourE *)
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

(** d1_decode_ord0 — the card position ord0 decodes to the club colour.
    @composes: d1_endpoint_colourE *)
Lemma d1_decode_ord0 : decode_bool ord0 = false.
Proof. by rewrite /decode_bool -(inj_eq val_inj) /= inordK. Qed.

(** five_card_exec_colour_view — the executed endpoints decoded as colours.
    @intent: copy of probe_d1_five_card_models.five_card_exec_colour_view. *)
Definition five_card_exec_colour_view (A : seq nat) (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) : (size A).-tuple bool :=
  map_tuple (fun j => decode_bool
    (nth ord0 (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L) ab w0 0) j))
    (in_tuple A).

(** d1_endpoint_colourE — the decoded executed endpoint is the leakage colour.
    @composes: five_card_colour_viewE *)
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

(** five_card_colour_viewE — the executed colour reader is the partial view.
    @composes: five_card_colour_view_RV_E *)
Lemma five_card_colour_viewE (A : seq nat) (w : five_card_leakage.Omega) :
  five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g
  = ViewA R A w.
Proof.
apply: val_inj => /=.
by apply: eq_map => j; exact: d1_endpoint_colourE.
Qed.

(** five_card_colour_view_RV_E — the executed colour reader is kim_view.
    @composes: five_card_colour_view_leak_bound *)
Lemma five_card_colour_view_RV_E (A : seq nat) :
  (fun w : five_card_leakage.Omega =>
     five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g)
  = kim_view Hlt Hgt A :> (five_card_leakage.Omega -> (size A).-tuple bool).
Proof. by apply: funext => w; rewrite five_card_colour_viewE. Qed.

Section d1_copies_transport.

Hypothesis Hsmall : 0 < 5%:R^-1 - `|eps|.

(** five_card_colour_view_leak_bound — the transported input-privacy bound.
    @composes: mu4_control *)
Corollary five_card_colour_view_leak_bound (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs Hlt Hgt,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret Hlt Hgt]) <= kim_leak_bound eps.
Proof. by rewrite five_card_colour_view_RV_E; exact: kim_input_private. Qed.

End d1_copies_transport.

End d1_copies.

(** d1_point_range — the leakage outcome at which the out-of-range position
    list is read.
    @intent: the committed pair (true, false) with the rotation 2, at which the
    dealt row is [true; false; true; false; true]. *)
Definition d1_point_range : five_card_leakage.Omega := (true, false, @Ordinal 5 2 isT).

(******************************************************************************)
(*     M1: the bias is load-bearing                                           *)
(******************************************************************************)

(** mu1_control — the uniform model's cut distribution is the uniform rotation
    image, by the landed second-marginal script.
    @composes: mu1_attempt *)
Definition mu1_control (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
  (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat) :
  sa_cut_dist (five_card_sample Hlt Hgt Hspec L)
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)) :=
  ltac:(rewrite /sa_cut_dist /five_card_sample /= /five_card_sample_cut;
        by rewrite -(five_card_sample_snd_uniformE R) fdistmap_comp).

(* M1: the same script claims the biased model's cut distribution is the
   uniform rotation image.  Rejected with

     No applicable tactic.

   which is the closing by [] of the control script refusing the residual
   goal fdistmap (fun u => (fc_sigma ^+ u.2)%g) (kim_input_dist Hlt Hgt) =
   fdistmap ((fun k => (fc_sigma ^+ k)%g) \o snd) (P R). *)
Fail Definition mu1_attempt (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
  (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat) :
  sa_cut_dist (kim_single_sample Hlt Hgt Hspec L)
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)) :=
  ltac:(rewrite /sa_cut_dist /kim_single_sample /= /five_card_sample_cut;
        by rewrite -(five_card_sample_snd_uniformE R) fdistmap_comp).

(** d1_one_letter_rotE — the weighted word shuffle at word length 1 is the
    image of the letter distribution under the rotation realization.
    @composes: kim_single_cut_dist_neq_uniform *)
Lemma d1_one_letter_rotE (R : realType) (W : R.-fdist 'I_5) :
  @rho_from_words_weighted R 3 4 1 fc_kim_sigmas W
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g) W.
Proof.
rewrite rho_from_words_weighted1.
by congr fdistmap; apply: funext => k; exact: fc_kim_sigmasE.
Qed.

(** kim_single_cut_dist_neq_uniform — at bias 1/100 the biased model's cut
    distribution is not the uniform rotation image.
    @main security: the mutated equation of M1 is false, not merely unprovable
    by the control script.  Both sides are the word shuffle at word length 1,
    so equality would carry the one-cut variation distance of the biased weights
    to that of the uniform weights, which are 1/50 (kim_one_cut_centiE) and 0
    (kim_var_dist_exact at bias 0). *)
Lemma kim_single_cut_dist_neq_uniform (R : realType) :
  sa_cut_dist (kim_single_sample (kim_centi_lt R) (kim_centi_gt R)
                 (kim_centi_spec R) 7)
  <> fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
       (fdist_uniform (card_ord 5)).
Proof.
rewrite kim_single_cut_distE -!d1_one_letter_rotE => Heq.
have Hv := @kim_one_cut_centiE R ord0.
rewrite Heq in Hv.
have H0 := @kim_var_dist_exact R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R) 1 ord0.
rewrite /endpoint_dist_weighted kim_weight_uniform_at0 in H0.
rewrite H0 /kim_lambda2 normr0 mulr0 expr1 mulr0 in Hv.
move/eqP: Hv; by rewrite eq_sym div1r invr_eq0 pnatr_eq0.
Qed.

(******************************************************************************)
(*     M2, M3 and M4                                                          *)
(******************************************************************************)

Section d1_mutations.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** mu2_sample — the repeated model with the cut map emptied to the identity.
    @intent: kim_repeated_sample with word_eval replaced by the constant 1. *)
Definition mu2_sample : SampleAdapter (five_card_exec_plug Hlt Hgt Hspec L) :=
  @MkSampleAdapter R mpF (five_card_exec_plug Hlt Hgt Hspec L)
    (kim_repeated_sampleT L) (kim_repeated_dist Hlt Hgt L)
    (fun u => u.1) (fun _ => 1%g).

(** mu2_control — the unmutated repeated model satisfies the word-shuffle
    equation by the marginal script.
    @composes: mu2_attempt *)
Definition mu2_control : sa_cut_dist (kim_repeated_sample Hlt Hgt Hspec L)
  = @rho_from_words_weighted R 3 4 L fc_kim_sigmas (kim_weight_dist Hlt Hgt) :=
  ltac:(rewrite /sa_cut_dist /kim_repeated_sample /= /rho_from_words_weighted;
        by rewrite -(kim_repeated_snd_wordE Hlt Hgt L) fdistmap_comp).

(* M2: the constant cut map does not satisfy the word-shuffle equation.
   Rejected with

     No applicable tactic. *)
Fail Definition mu2_attempt : sa_cut_dist mu2_sample
  = @rho_from_words_weighted R 3 4 L fc_kim_sigmas (kim_weight_dist Hlt Hgt) :=
  ltac:(rewrite /sa_cut_dist /mu2_sample /= /rho_from_words_weighted;
        by rewrite -(kim_repeated_snd_wordE Hlt Hgt L) fdistmap_comp).

(* M2 again with the discriminating closer, so the rejection is not the
   uninformative refusal of by [].  Rejected with

     Cannot apply lemma erefl

   which witnesses that the two distributions are not convertible. *)
Fail Definition mu2_attempt_refl : sa_cut_dist mu2_sample
  = @rho_from_words_weighted R 3 4 L fc_kim_sigmas (kim_weight_dist Hlt Hgt) :=
  ltac:(rewrite /sa_cut_dist /mu2_sample /= /rho_from_words_weighted;
        rewrite -(kim_repeated_snd_wordE Hlt Hgt L) fdistmap_comp; exact: erefl).

(** mu3_colour_view — the colour reader with the decoder emptied to false.
    @intent: five_card_exec_colour_view with decode_bool replaced by the
    constant false. *)
Definition mu3_colour_view (A : seq nat) (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) : (size A).-tuple bool :=
  map_tuple (fun j => (fun _ : 'I_(pgg_N' (mp_M mpF)).+1 => false)
    (nth ord0 (@exec_endpoints R mpF (five_card_exec_plug Hlt Hgt Hspec L) ab w0 0) j))
    (in_tuple A).

(** mu3_control — the unmutated colour reader agrees with the partial view.
    @composes: mu3_attempt *)
Definition mu3_control (A : seq nat) (w : five_card_leakage.Omega) :
  five_card_exec_colour_view Hlt Hgt Hspec L A w.1
    (five_card_group.fc_sigma ^+ w.2)%g = ViewA R A w :=
  ltac:(apply: val_inj => /=;
        by apply: eq_map => j; exact: (d1_endpoint_colourE Hlt Hgt Hspec L w j)).

(** mu3_control_value — at the reveal [:: 0; 7] the unmutated reader returns a
    heart at position 0 and the out-of-range default at position 7.
    @composes: mu3_attempt_value *)
Definition mu3_control_value :
  val (five_card_exec_colour_view Hlt Hgt Hspec L [:: 0; 7]%N d1_point_range.1
        (five_card_group.fc_sigma ^+ d1_point_range.2)%g) = [:: true; false] :=
  ltac:(by rewrite five_card_colour_viewE).

(* M3a: the constant decoder does not agree with the partial view.  Rejected
   with

     Cannot apply lemma (d1_endpoint_colourE Hlt Hgt Hspec L w j) *)
Fail Definition mu3_attempt (A : seq nat) (w : five_card_leakage.Omega) :
  mu3_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g = ViewA R A w :=
  ltac:(apply: val_inj => /=;
        by apply: eq_map => j; exact: (d1_endpoint_colourE Hlt Hgt Hspec L w j)).

(* M3b: the constant decoder loses the heart at position 0 of the reveal the
   control reads.  Rejected with

     No applicable tactic.

   The Timeout guard is kept because the goal mentions exec_endpoints; the
   rejection is immediate, since the constant decoder beta-reduces away the
   interpreter term before the comparison. *)
Fail Timeout 30 Definition mu3_attempt_value :
  val (mu3_colour_view [:: 0; 7]%N d1_point_range.1
        (five_card_group.fc_sigma ^+ d1_point_range.2)%g) = [:: true; false] :=
  ltac:(by []).

(** mu4_control — with the small-bias hypothesis in hand the transported bound
    instantiates.
    @composes: mu4_attempt *)
Definition mu4_control (Hsmall : 0 < 5%:R^-1 - `|eps|) (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs Hlt Hgt,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view Hlt Hgt Hspec L A w.1
         (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret Hlt Hgt]) <= kim_leak_bound eps :=
  ltac:(exact: (five_card_colour_view_leak_bound Hlt Hgt Hspec L Hsmall A)).

(* M4a: in this section, which carries only the two positivity conditions and
   the spectral condition, the transported bound cannot be instantiated by
   omitting the small-bias argument.  Rejected with

     Cannot apply lemma (five_card_colour_view_leak_bound Hlt Hgt Hspec L A) *)
Fail Definition mu4_attempt (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs Hlt Hgt,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view Hlt Hgt Hspec L A w.1
         (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret Hlt Hgt]) <= kim_leak_bound eps :=
  ltac:(exact: (five_card_colour_view_leak_bound Hlt Hgt Hspec L A)).

(* M4b: nor by leaving the small-bias argument as a hole, since the section has
   no proof of it to elaborate the hole with.  Rejected with

     No applicable tactic. *)
Fail Definition mu4_attempt_hole (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs Hlt Hgt,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view Hlt Hgt Hspec L A w.1
         (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret Hlt Hgt]) <= kim_leak_bound eps :=
  ltac:(exact: (five_card_colour_view_leak_bound Hlt Hgt Hspec L _ A)).

End d1_mutations.

Print Assumptions kim_single_cut_dist_neq_uniform.
Print Assumptions mu1_control.
Print Assumptions mu2_control.
Print Assumptions mu3_control.
Print Assumptions mu3_control_value.
Print Assumptions mu4_control.
