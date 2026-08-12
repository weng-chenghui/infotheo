(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_f_five_card_facade: the provisional five-card typed facade.          *)
(*                                                                            *)
(* Probe unit F of the 2026-08-12 layered-protocol-packing gate: section      *)
(* 15.8, phase H1 of section 13.  The five-card analysis cone in the seven    *)
(* fixed source sections of section 13.1:                                     *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* Section 7 is empty for this development and is documented as empty rather  *)
(* than omitted, per the section 13.5 acceptance rule.  A separate bound      *)
(* sub-block sits beside section 6 and carries the endpoint marginal bounds,  *)
(* which are NOT privacy statements.                                          *)
(*                                                                            *)
(* Import discipline matches probe_f_pgl27_facade: the type vocabulary is     *)
(* Require Export'ed, the five-card instance cone is Require Import'ed only.  *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: everything an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Export boolp reals.
From infotheo Require Export ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Export variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_sample_adapter.
From pgg_reconstruct Require Export algebraic_rigidity.

(* Imported instance cone: not re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.
From pgg_smc Require Import five_card_exec kim_input_privacy.
From lpp_probe Require Import probe_d1_five_card_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(* fa_five_card_profile: the probability-independent five-card program profile.
   @intent: alias of five_card_profile; production is the parameterless core,
   and the den_boer and kim compatibility names reduce to it. *)
Definition fa_five_card_profile := @five_card_profile.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(******************************************************************************)

(* fa_five_card_exec_plug: the five-card execution plug over that profile.
   @intent: alias of five_card_exec_plug, the shared piSMC run. *)
Definition fa_five_card_exec_plug := @five_card_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Six carriers, kept distinct: a message list for the raw traces, 'I_5 for   *)
(* the finite content readers, bool * bool for the dealer pair, a card        *)
(* position list for the verifier, and (size A).-tuple bool for the decoded   *)
(* colour sequence.                                                           *)
(******************************************************************************)

(* fa_five_card_player_raw_trace: one seat's raw executed trace.
   @intent: alias of five_card_exec_player_raw_trace. *)
Definition fa_five_card_player_raw_trace := @five_card_exec_player_raw_trace.

(* fa_five_card_coalition_raw_trace: a coalition's raw executed traces.
   @intent: alias of five_card_exec_coalition_raw_trace. *)
Definition fa_five_card_coalition_raw_trace :=
  @five_card_exec_coalition_raw_trace.

(* fa_five_card_input_raw_trace: an input party's raw executed trace.
   @intent: alias of five_card_exec_input_raw_trace. *)
Definition fa_five_card_input_raw_trace := @five_card_exec_input_raw_trace.

(* fa_five_card_input_trace: the input party's finite content reader, a random
   variable with carrier 'I_5.
   @intent: alias of five_card_exec_input_trace. *)
Definition fa_five_card_input_trace := @five_card_exec_input_trace.

(* fa_five_card_dealer_raw_trace: the dealer's raw executed trace.
   @intent: alias of five_card_exec_dealer_raw_trace. *)
Definition fa_five_card_dealer_raw_trace := @five_card_exec_dealer_raw_trace.

(* fa_five_card_dealer_trace: the dealer's finite content reader, a random
   variable with carrier bool * bool.
   @intent: alias of five_card_exec_dealer_trace. *)
Definition fa_five_card_dealer_trace := @five_card_exec_dealer_trace.

(* fa_five_card_verifier_endpoints: the generic endpoint observer at the
   five-card plug, carrier a list of dealt card positions.  The section 7.8
   exec_verifier_trace twin is production work landed in probe unit A.
   @intent: exec_endpoints specialized at five_card_exec_plug. *)
Definition fa_five_card_verifier_endpoints (R : realType) (eps : R)
    (Hlt : eps < 5%:R^-1) (Hgt : - (4%:R * 5%:R^-1) < eps)
    (Hspec : `|eps| < 4%:R / 5%:R) (L : nat) :=
  @exec_endpoints R (five_card_profile Hlt Hgt Hspec L)
    (five_card_exec_plug Hlt Hgt Hspec L).

(* fa_five_card_content_trace: one seat's finite content reader, a random
   variable with carrier 'I_5; the observer of the den Boer trace results.
   @intent: alias of five_card_exec_trace. *)
Definition fa_five_card_content_trace := @five_card_exec_trace.

(* fa_five_card_colour_view: the decoded sequence observer required by the Kim
   bridge, carrier (size A).-tuple bool at a list A of card positions.
   @intent: alias of five_card_exec_colour_view of probe unit D1. *)
Definition fa_five_card_colour_view := @five_card_exec_colour_view.

(* fa_five_card_secret: the dealt Boolean secret a AND b as a random variable.
   @intent: alias of five_card_leakage.Secret. *)
Definition fa_five_card_secret := @five_card_leakage.Secret.

(* fa_five_card_prior: the uniform prior on the den Boer leakage space.
   @intent: alias of five_card_leakage.P, the distribution the finite content
   readers are random variables on. *)
Definition fa_five_card_prior := @five_card_leakage.P.

(******************************************************************************)
(* ===== 4. Models ===== *)
(******************************************************************************)

(* fa_five_card_sample: the uniform one-cut sample model.
   @intent: alias of five_card_sample. *)
Definition fa_five_card_sample := @five_card_sample.

(* fa_kim_single_sample: the single-biased one-cut sample model.
   @intent: alias of kim_single_sample of probe unit D1. *)
Definition fa_kim_single_sample := @kim_single_sample.

(* fa_kim_repeated_sample: the repeated-biased L-cut sample model.
   @intent: alias of kim_repeated_sample of probe unit D1. *)
Definition fa_kim_repeated_sample := @kim_repeated_sample.

(* fa_kim_centi_repeated_sample: the seven-cut model at bias one hundredth.
   @intent: alias of kim_centi_repeated_sample of probe unit D1. *)
Definition fa_kim_centi_repeated_sample := @kim_centi_repeated_sample.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(******************************************************************************)

(* fa_five_card_exec_correct: termination, endpoint count and recovery.
   @intent: alias of five_card_exec_correct. *)
Definition fa_five_card_exec_correct := @five_card_exec_correct.

(* fa_five_card_exec_recovers: the derived run decodes to a AND b.
   @intent: alias of five_card_exec_recovers. *)
Definition fa_five_card_exec_recovers := @five_card_exec_recovers.

(******************************************************************************)
(* ===== 6. Security ===== *)
(******************************************************************************)

(* fa_five_card_exec_trace_secrecy: the conditional entropy of the secret given
   seat zero's executed content trace equals its entropy.
   @intent: alias of five_card_exec_trace_secrecy. *)
Definition fa_five_card_exec_trace_secrecy := @five_card_exec_trace_secrecy.

(* fa_five_card_exec_input_trace_secrecy: the same for an input party's trace,
   at every party index j.  The statement is a constant-conditioning result:
   the input rows of the executed trace are empty, so the conditioning variable
   is constant and the equality holds for every j including out-of-range ones.
   @intent: alias of five_card_exec_input_trace_secrecy. *)
Definition fa_five_card_exec_input_trace_secrecy :=
  @five_card_exec_input_trace_secrecy.

(* fa_five_card_exec_dealer_pair_centropy0: the committed pair is determined by
   the dealer's executed trace.
   @intent: alias of five_card_exec_dealer_pair_centropy0. *)
Definition fa_five_card_exec_dealer_pair_centropy0 :=
  @five_card_exec_dealer_pair_centropy0.

(* fa_five_card_exec_dealer_trace_centropy0: the secret is determined by the
   dealer's executed trace.
   @intent: alias of five_card_exec_dealer_trace_centropy0. *)
Definition fa_five_card_exec_dealer_trace_centropy0 :=
  @five_card_exec_dealer_trace_centropy0.

(* fa_five_card_colour_view_leak_bound: the Kim input-privacy bridge, bounding
   the conditional mutual information the decoded colour sequence carries about
   the inputs given the output.
   @intent: alias of five_card_colour_view_leak_bound of probe unit D1. *)
Definition fa_five_card_colour_view_leak_bound :=
  @five_card_colour_view_leak_bound.

(******************************************************************************)
(* ===== bound (not security) ===== *)
(*                                                                            *)
(* These are ENDPOINT MARGINAL BOUNDS in the sense of section 13.2: each says *)
(* how far one seat's endpoint distribution is from uniform after L cuts.     *)
(* None of them is a privacy or security statement, none of them quantifies   *)
(* over a coalition view, and none of them may be used as the witness of a    *)
(* Security-bridged path; probe_f_mutation.v exhibits the type mismatch.      *)
(******************************************************************************)

(* fa_fc_kim_security_bound: the spectral endpoint marginal bound at word
   length L, an @main bound result.
   @intent: alias of fc_kim_security_bound. *)
Definition fa_fc_kim_security_bound := @fc_kim_security_bound.

(* fa_kim_deal_centi_lt: the seven-cut endpoint marginal bound at bias one
   hundredth, strictly below 2^-40, an @main bound result.
   @intent: alias of kim_deal_centi_lt. *)
Definition fa_kim_deal_centi_lt := @kim_deal_centi_lt.

(* fa_kim_security_witness_centi: the certificate the seven-cut bound is read
   off, carrying the weighted word shuffle at word length seven.
   @intent: alias of kim_security_witness_centi. *)
Definition fa_kim_security_witness_centi := @kim_security_witness_centi.

(* fa_kim_lambda2: the second eigenvalue bound of the biased cut.
   @intent: alias of kim_lambda2, the constant of fa_fc_kim_security_bound. *)
Definition fa_kim_lambda2 := @kim_lambda2.

(* fa_kim_leak_bound: the mutual-information bound of the Kim input-privacy
   result, the constant of fa_five_card_colour_view_leak_bound.
   @intent: alias of kim_leak_bound. *)
Definition fa_kim_leak_bound := @kim_leak_bound.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(*                                                                            *)
(* No transfer-layer result exists for the five-card development; the section *)
(* is intentionally empty per the H1 acceptance rule "empty capability        *)
(* sections explicitly documented".  The generic bound                        *)
(* var_dist_fdistmap_transfer of probe unit E applies to any pair of readers, *)
(* but the five-card development has no ideal-distribution equality to feed   *)
(* its second hypothesis, so nothing is aliased here.                         *)
(******************************************************************************)

(******************************************************************************)
(*     Type retention                                                         *)
(*                                                                            *)
(* Same instrument and same caveat as probe_f_pgl27_facade: the value-level   *)
(* check Check (erefl : fa = landed) diverges on every alias whose body        *)
(* reaches the piSMC interpreter, so the type-level checker is used           *)
(* throughout and every line is Timeout-guarded.                              *)
(******************************************************************************)

(* alias_same_type — the two arguments share one type.
   @intent: the type-level half of the facade retention check; Local so that
   the manifest re-exporting both facades sees no duplicate name. *)
Local Definition alias_same_type (T : Type) (x y : T) : Type := T.

Timeout 60 Check (erefl : fa_five_card_profile = @five_card_profile).

Timeout 60 Check (alias_same_type fa_five_card_profile (@five_card_profile)).
Timeout 60 Check (alias_same_type fa_five_card_exec_plug
  (@five_card_exec_plug)).
Timeout 60 Check (alias_same_type fa_five_card_player_raw_trace
  (@five_card_exec_player_raw_trace)).
Timeout 60 Check (alias_same_type fa_five_card_coalition_raw_trace
  (@five_card_exec_coalition_raw_trace)).
Timeout 60 Check (alias_same_type fa_five_card_input_raw_trace
  (@five_card_exec_input_raw_trace)).
Timeout 60 Check (alias_same_type fa_five_card_input_trace
  (@five_card_exec_input_trace)).
Timeout 60 Check (alias_same_type fa_five_card_dealer_raw_trace
  (@five_card_exec_dealer_raw_trace)).
Timeout 60 Check (alias_same_type fa_five_card_dealer_trace
  (@five_card_exec_dealer_trace)).
Timeout 60 Check (alias_same_type fa_five_card_content_trace
  (@five_card_exec_trace)).
Timeout 60 Check (alias_same_type fa_five_card_colour_view
  (@five_card_exec_colour_view)).
Timeout 60 Check (alias_same_type fa_five_card_secret
  (@five_card_leakage.Secret)).
Timeout 60 Check (alias_same_type fa_five_card_prior (@five_card_leakage.P)).
Timeout 60 Check (alias_same_type fa_five_card_sample (@five_card_sample)).
Timeout 60 Check (alias_same_type fa_kim_single_sample (@kim_single_sample)).
Timeout 60 Check (alias_same_type fa_kim_repeated_sample
  (@kim_repeated_sample)).
Timeout 60 Check (alias_same_type fa_kim_centi_repeated_sample
  (@kim_centi_repeated_sample)).
Timeout 60 Check (alias_same_type fa_five_card_exec_correct
  (@five_card_exec_correct)).
Timeout 60 Check (alias_same_type fa_five_card_exec_recovers
  (@five_card_exec_recovers)).
Timeout 60 Check (alias_same_type fa_five_card_exec_trace_secrecy
  (@five_card_exec_trace_secrecy)).
Timeout 60 Check (alias_same_type fa_five_card_exec_input_trace_secrecy
  (@five_card_exec_input_trace_secrecy)).
Timeout 60 Check (alias_same_type fa_five_card_exec_dealer_pair_centropy0
  (@five_card_exec_dealer_pair_centropy0)).
Timeout 60 Check (alias_same_type fa_five_card_exec_dealer_trace_centropy0
  (@five_card_exec_dealer_trace_centropy0)).
Timeout 60 Check (alias_same_type fa_five_card_colour_view_leak_bound
  (@five_card_colour_view_leak_bound)).
Timeout 60 Check (alias_same_type fa_fc_kim_security_bound
  (@fc_kim_security_bound)).
Timeout 60 Check (alias_same_type fa_kim_deal_centi_lt (@kim_deal_centi_lt)).
Timeout 60 Check (alias_same_type fa_kim_security_witness_centi
  (@kim_security_witness_centi)).
Timeout 60 Check (alias_same_type fa_kim_lambda2 (@kim_lambda2)).
Timeout 60 Check (alias_same_type fa_kim_leak_bound (@kim_leak_bound)).
Timeout 60 Check (alias_same_type fa_five_card_verifier_endpoints
  (fun (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
     (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R)
     (L : nat) =>
   @exec_endpoints R (five_card_profile Hlt Hgt Hspec L)
     (five_card_exec_plug Hlt Hgt Hspec L))).

(******************************************************************************)
(*     One written type per section                                           *)
(******************************************************************************)

(* 1 Program *)
Timeout 60 Check (fa_five_card_profile :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> `|eps| < 4%:R / 5%:R ->
    nat -> MonodromyProfile R).

(* 2 Execution *)
Timeout 60 Check (fa_five_card_exec_plug :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    ExecutionPlug (fa_five_card_profile Hlt Hgt Hspec L)).

(* 3 Observers: the decoded colour sequence keeps its (size A).-tuple bool
   carrier and its card-position index domain. *)
Timeout 60 Check (fa_five_card_colour_view :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat)
    (A : seq nat),
    bool * bool -> pgg_gT FiveCardKim_M -> (size A).-tuple bool).

(* 4 Models: the sample adapter keeps its dependent index on the plug. *)
Timeout 60 Check (fa_five_card_sample :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    SampleAdapter (fa_five_card_exec_plug Hlt Hgt Hspec L)).
Timeout 60 Check (fa_kim_centi_repeated_sample :
  forall R : realType,
    SampleAdapter (fa_five_card_exec_plug (kim_centi_lt R) (kim_centi_gt R)
                     (kim_centi_spec R) 7)).

(* 5 Correctness *)
Timeout 60 Check (fa_five_card_exec_recovers :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat)
    (a b : bool) (w0 : pgg_gT FiveCardKim_M),
    w0 \in pgg_G FiveCardKim_M ->
    exec_decode (fa_five_card_exec_plug Hlt Hgt Hspec L)
      (exec_endpoints_size (five_card_exec_endpoints Hlt Hgt Hspec L a b w0))
    = a && b).

(* 6 Security: the den Boer trace result keeps its observer and both sides. *)
Timeout 60 Check (fa_five_card_exec_trace_secrecy :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    `H( (fa_five_card_secret R)
      | (@fa_five_card_content_trace R eps Hlt Hgt Hspec L ord0))
    = `H `p_ (fa_five_card_secret R)).

(* bound: the spectral endpoint marginal bound keeps its constant. *)
Timeout 60 Check (fa_fc_kim_security_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    `|eps| < 4%:R / 5%:R ->
    forall (L : nat) (s : 'I_5),
      var_dist (endpoint_dist_weighted L fc_kim_sigmas (kim_weight_dist Hlt Hgt) s)
               (fdist_uniform (card_ord 5))
      <= Num.ExtraDef.sqrtr 5%:R * fa_kim_lambda2 eps ^+ L).

(* 7 Transfer: nothing to check, by construction. *)

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions fa_five_card_profile.
Print Assumptions fa_five_card_exec_recovers.
Print Assumptions fa_five_card_exec_trace_secrecy.
Print Assumptions fa_five_card_colour_view_leak_bound.
Print Assumptions fa_kim_deal_centi_lt.
