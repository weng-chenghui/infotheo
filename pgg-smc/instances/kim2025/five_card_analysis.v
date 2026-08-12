(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_analysis: the typed facade of the five-card instance             *)
(*                                                                            *)
(* The facade presents the five-card analysis cone through one alias per      *)
(* public value, inside Module FiveCardAnalysis, in seven fixed source        *)
(* sections:                                                                  *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* A bound sub-block sits beside section 6 and carries the endpoint marginal  *)
(* bounds of the repeated and seven-cut models. Those are not privacy or      *)
(* security statements and are not aliased under the security heading.        *)
(* Section 7 is empty for this development and is documented as empty rather  *)
(* than omitted.                                                              *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the             *)
(*     five_card_, den_boer_ and kim_ prefixes of their targets;              *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the five-card instance cone is Require Import'ed only.  *)
(*                                                                            *)
(* Check table against the phase-H1 minimum list of the five-card facade:     *)
(*                                                                            *)
(*   probability-independent program profile  -> profile, den_boer_profile    *)
(*   execution plug                           -> exec_plug                    *)
(*   ObservedExecution value                  -> observed, den_boer_observed  *)
(*   participant observer                     -> player_raw_trace,            *)
(*                                               content_trace                *)
(*   coalition observer                       -> coalition_raw_trace          *)
(*   input-party observer                     -> input_raw_trace, input_trace *)
(*   dealer observer                          -> dealer_raw_trace,            *)
(*                                               dealer_trace                 *)
(*   verifier observer                        -> verifier_trace,              *)
(*                                               verifier_endpoints           *)
(*   decoded sequence observer (Kim bridge)   -> colour_view                  *)
(*   uniform sample model                     -> uniform_sample               *)
(*   single-biased sample model               -> single_biased_sample         *)
(*   repeated-biased sample model             -> repeated_sample              *)
(*   seven-cut sample model                   -> centi_sample                 *)
(*   execution correctness and recovery       -> exec_correct, exec_recovers, *)
(*                                               observed_recovers            *)
(*   exact-security bridge                    -> marginal_bound, perfect      *)
(*   entropy bridges                          -> dealer_pair_centropy0,       *)
(*                                               dealer_trace_centropy0,      *)
(*                                               input_trace_secrecy          *)
(*   trace bridge                             -> exec_trace_secrecy           *)
(*   input-privacy bridge                     -> colour_view_leak_bound       *)
(*   repeated and seven-cut endpoint bounds   -> endpoint_bound,              *)
(*                                               deal_centi_lt (bound block)  *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: every constant an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Export boolp reals.
From infotheo Require Export ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Export variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Export pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Export pgg_analysis_status.
From pgg_reconstruct Require Export algebraic_rigidity.

(* Imported instance cone: loaded, never re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.
From pgg_smc Require Import five_card_exec kim_input_privacy five_card_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Module FiveCardAnalysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(*                                                                            *)
(* The den Boer profile is the five-card profile itself: den_boer_profile     *)
(* reduces to five_card_profile by conversion, so the two aliases below name  *)
(* one program and the equality holds by erefl.                               *)
(******************************************************************************)

(** profile — the probability-independent five-card program profile.
    @intent: alias of five_card_profile. *)
Definition profile := five_card_profile.

(** den_boer_profile — the same program under the den Boer name.
    @intent: alias of den_boer_profile.den_boer_profile. *)
Definition den_boer_profile := den_boer_profile.den_boer_profile.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(******************************************************************************)

(** exec_plug — the execution plug over that profile, carrying the shared
    piSMC run.
    @intent: alias of five_card_exec_plug. *)
Definition exec_plug := five_card_exec_plug.

(** verifier_trace — the verifier's raw executed trace, a message list read
    at the verifier process of the run.
    @intent: exec_verifier_trace specialized at five_card_exec_plug. *)
Definition verifier_trace :=
  @exec_verifier_trace five_card_profile five_card_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Six carriers, kept distinct: a message list for the raw traces, the card   *)
(* position 'I_5 for the participant and input-party content readers,         *)
(* bool * bool for the dealer content reader, a list of card positions for    *)
(* the verifier endpoints, (size A).-tuple bool for the decoded colour        *)
(* sequence, and bool for the evaluated secret.                               *)
(******************************************************************************)

(** player_raw_trace — one seat's raw executed trace, a message list.
    @intent: alias of five_card_exec_player_raw_trace. *)
Definition player_raw_trace := @five_card_exec_player_raw_trace.

(** coalition_raw_trace — a coalition's raw executed traces, a finfun of
    message lists indexed by seats.
    @intent: alias of five_card_exec_coalition_raw_trace. *)
Definition coalition_raw_trace := @five_card_exec_coalition_raw_trace.

(** input_raw_trace — an input party's raw executed trace, a message list
    indexed by the party index.
    @intent: alias of five_card_exec_input_raw_trace. *)
Definition input_raw_trace := @five_card_exec_input_raw_trace.

(** input_trace — an input party's finite content reader, a random variable
    with carrier 'I_5.
    @intent: alias of five_card_exec_input_trace. *)
Definition input_trace := @five_card_exec_input_trace.

(** dealer_raw_trace — the dealer's raw executed trace, a message list.
    @intent: alias of five_card_exec_dealer_raw_trace. *)
Definition dealer_raw_trace := @five_card_exec_dealer_raw_trace.

(** dealer_trace — the dealer's finite content reader, a random variable with
    carrier bool * bool.
    @intent: alias of five_card_exec_dealer_trace. *)
Definition dealer_trace := @five_card_exec_dealer_trace.

(** verifier_endpoints — the executed endpoint list of the run, the dealt
    card positions the verifier reads.
    @intent: exec_endpoints specialized at five_card_exec_plug. *)
Definition verifier_endpoints :=
  @exec_endpoints five_card_profile five_card_exec_plug.

(** content_trace — one seat's finite content reader, a random variable with
    carrier 'I_5.
    @intent: alias of five_card_exec_trace. *)
Definition content_trace := @five_card_exec_trace.

(** colour_view — the decoded colour sequence at a list of seat indices into
    the endpoint list, carrier (size A).-tuple bool.
    @intent: alias of five_card_exec_colour_view, the observer of the Kim
    input-privacy bridge. *)
Definition colour_view := @five_card_exec_colour_view.

(** secret — the evaluated secret a AND b read as a random variable.
    @intent: alias of five_card_leakage.Secret. *)
Definition secret := @five_card_leakage.Secret.

(** prior — the uniform distribution on the den Boer sample space the finite
    content readers are random variables on.
    @intent: alias of five_card_leakage.P. *)
Definition prior := @five_card_leakage.P.

(** observed — the observed execution of the profile and plug: the run, its
    static observation and the value it recovers.
    @intent: alias of five_card_observed. *)
Definition observed := five_card_observed.

(** den_boer_observed — the same observed execution under the den Boer name.
    @intent: alias of five_card_exec.den_boer_observed. *)
Definition den_boer_observed := five_card_exec.den_boer_observed.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* Each model is followed by the equations that identify its cut and seat     *)
(* distributions, so that a security statement about a named distribution     *)
(* can be attached to a named executed observer.                              *)
(******************************************************************************)

(** uniform_sample — the uniform one-cut model.
    @intent: alias of five_card_sample. *)
Definition uniform_sample := @five_card_sample.

(** single_biased_sample — the single-biased one-cut model at Kim's input
    distribution.
    @intent: alias of kim_single_sample. *)
Definition single_biased_sample := @kim_single_sample.

(** repeated_sample — the repeated-biased model at word length L.
    @intent: alias of kim_repeated_sample. *)
Definition repeated_sample := @kim_repeated_sample.

(** centi_sample — the seven-cut model at bias one hundredth.
    @intent: alias of kim_centi_repeated_sample. *)
Definition centi_sample := @kim_centi_repeated_sample.

(** sample_cut_distE — the uniform model's cut distribution is the uniform
    rotation.
    @intent: alias of five_card_sample_cut_distE. *)
Definition sample_cut_distE := @five_card_sample_cut_distE.

(** sample_cut_witnessE — the uniform model's cut distribution is the shuffle
    of the den Boer marginal bound.
    @intent: alias of den_boer_sample_cut_witnessE. *)
Definition sample_cut_witnessE := @den_boer_sample_cut_witnessE.

(** witness_rotationE — the den Boer marginal bound's shuffle is the uniform
    rotation.
    @intent: alias of den_boer_witness_rotationE. *)
Definition witness_rotationE := @den_boer_witness_rotationE.

(** single_cut_distE — the single-biased model's cut distribution is the
    biased rotation.
    @intent: alias of kim_single_cut_distE. *)
Definition single_cut_distE := @kim_single_cut_distE.

(** repeated_cut_distE — the repeated model's cut distribution is the
    weighted word shuffle at word length L.
    @intent: alias of kim_repeated_cut_distE. *)
Definition repeated_cut_distE := @kim_repeated_cut_distE.

(** repeated_seat_distE — the repeated model's executed seat distribution is
    the pushforward of the static observation.
    @intent: alias of kim_repeated_seat_distE. *)
Definition repeated_seat_distE := @kim_repeated_seat_distE.

(** centi_cut_distE — the seven-cut model's cut distribution is the marginal
    bound of the seven-cut certificate bundle.
    @intent: alias of kim_centi_cut_distE. *)
Definition centi_cut_distE := @kim_centi_cut_distE.

(** centi_witness_rhoE — the seven-cut certificate bundle's marginal bound
    carries the weighted word shuffle at word length seven.
    @intent: alias of kim_centi_witness_rhoE. *)
Definition centi_witness_rhoE := @kim_centi_witness_rhoE.

(** centi_repeated_seat_distE — the seven-cut model's executed seat
    distribution is the pushforward of the static observation.
    @intent: alias of kim_centi_repeated_seat_distE. *)
Definition centi_repeated_seat_distE := @kim_centi_repeated_seat_distE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(******************************************************************************)

(** exec_correct — termination, endpoint count and recovery together.
    @intent: alias of five_card_exec_correct. *)
Definition exec_correct := @five_card_exec_correct.

(** exec_recovers — the executed run decodes to a AND b.
    @intent: alias of five_card_exec_recovers. *)
Definition exec_recovers := @five_card_exec_recovers.

(** observed_recovers — the observed run decodes to a AND b.
    @intent: alias of five_card_observed_recovers. *)
Definition observed_recovers := @five_card_observed_recovers.

(** procs_biasE — the process list of the run is one list, so the equation it
    once carried between two biases is the self-equality of that list; the
    bias-independence content now lives in the type of the profile, which
    mentions no bias.
    @intent: alias of five_card_exec_procs_biasE. *)
Definition procs_biasE := @five_card_exec_procs_biasE.

(******************************************************************************)
(* ===== 6. Security ===== *)
(******************************************************************************)

(** exec_trace_secrecy — the conditional entropy of the secret given seat
    zero's executed content trace equals its entropy.
    @intent: alias of five_card_exec_trace_secrecy. *)
Definition exec_trace_secrecy := @five_card_exec_trace_secrecy.

(** input_trace_secrecy — the same equality for an input party's content
    trace, at every party index. The input rows of the executed trace are
    empty, so the conditioning variable is constant and the equality holds at
    every index including out-of-range ones. It is an architecture statement
    about where the input parties appear in the run, not a privacy bound
    against an adversary who reads their trace.
    @intent: alias of five_card_exec_input_trace_secrecy. *)
Definition input_trace_secrecy := @five_card_exec_input_trace_secrecy.

(** dealer_pair_centropy0 — the committed pair is determined by the dealer's
    executed content trace.
    @intent: alias of five_card_exec_dealer_pair_centropy0. *)
Definition dealer_pair_centropy0 := @five_card_exec_dealer_pair_centropy0.

(** dealer_trace_centropy0 — the secret is determined by the dealer's
    executed content trace.
    @intent: alias of five_card_exec_dealer_trace_centropy0. *)
Definition dealer_trace_centropy0 := @five_card_exec_dealer_trace_centropy0.

(** colour_viewE — the executed colour view at a rotation cut is the Kim
    static view, pointwise on the den Boer sample space.
    @intent: alias of five_card_colour_viewE. *)
Definition colour_viewE := @five_card_colour_viewE.

(** colour_view_RV_E — the same equality as an equality of random variables.
    @intent: alias of five_card_colour_view_RV_E. *)
Definition colour_view_RV_E := @five_card_colour_view_RV_E.

(** colour_view_leak_bound — the conditional mutual information the decoded
    colour sequence carries about the inputs given the output is at most
    kim_leak_bound eps, under Kim's biased input distribution.
    @intent: alias of five_card_colour_view_leak_bound. *)
Definition colour_view_leak_bound := @five_card_colour_view_leak_bound.

(** marginal_bound — the shuffle marginal bound of the uniform model.
    @intent: alias of den_boer_marginal_bound. *)
Definition marginal_bound := @den_boer_marginal_bound.

(** perfect — the epsilon of that marginal bound is zero.
    @intent: alias of den_boer_perfect. *)
Definition perfect := @den_boer_perfect.

(******************************************************************************)
(* ===== bound (endpoint marginal, not security) ===== *)
(*                                                                            *)
(* Each alias below bounds the distance from uniform of ONE seat's endpoint   *)
(* distribution after L cuts. None quantifies over a coalition view, none     *)
(* mentions a second secret, and none may witness a security-bridged          *)
(* analysis path. They are endpoint marginal bounds and are recorded as       *)
(* such in the analysis manifest.                                            *)
(******************************************************************************)

(** kim_bundle — the certificate bundle of the repeated model at word length
    L, carrying its endpoint marginal bound.
    @intent: alias of fc_kim_security_bundle. *)
Definition kim_bundle := @fc_kim_security_bundle.

(** centi_bundle — the certificate bundle of the seven-cut model at bias one
    hundredth.
    @intent: alias of kim_security_bundle_centi. *)
Definition centi_bundle := @kim_security_bundle_centi.

(** endpoint_bound — the spectral endpoint marginal bound at word length L:
    one seat's endpoint distribution is within sqrt 5 times the L-th power of
    the second eigenvalue of the uniform distribution.
    @intent: alias of fc_kim_security_bound. *)
Definition endpoint_bound := @fc_kim_security_bound.

(** deal_centi_lt — the seven-cut endpoint marginal bound at bias one
    hundredth is strictly below 2^-40.
    @intent: alias of kim_deal_centi_lt. *)
Definition deal_centi_lt := @kim_deal_centi_lt.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(*                                                                            *)
(* This section carries NO transfer theorem. No transfer-layer result exists  *)
(* for the five-card development: the generic bound                           *)
(* var_dist_fdistmap_transfer applies to any pair of readers, but the         *)
(* five-card development has no ideal distribution equality to discharge its  *)
(* second hypothesis, so there is nothing to alias and nothing is             *)
(* manufactured to fill the section. What the section does carry is a typed   *)
(* transfer status for each analysis path, one alias for the two exact-cut    *)
(* paths, which share their status, and one for the repeated-cut path.        *)
(******************************************************************************)

(** exec_transfer_status — the transfer status of the two exact-cut paths, the
    uniform one and the single-biased one.
    @intent: StaticExecutedOnly, the paths carrying their landed static
    results to their executed observers and no ideal-to-finite theorem. *)
Definition exec_transfer_status : TransferStatus := StaticExecutedOnly.

(** repeated_transfer_status — the transfer status of the repeated-cut path.
    @intent: NoModelComparison, the path carrying endpoint marginal bounds
    only. *)
Definition repeated_transfer_status : TransferStatus := NoModelComparison.

End FiveCardAnalysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, whose   *)
(* bodies do not reach the piSMC interpreter. On every other alias the        *)
(* value-level form Check (erefl : alias = landed) DIVERGES: the unifier      *)
(* unfolds past the alias into exec_participant_trace and evaluates           *)
(* run_interp. Those aliases are retained by spelled type ascriptions, one    *)
(* representative per section and one for the bound sub-block. Every line is  *)
(* Timeout-guarded.                                                           *)
(******************************************************************************)

Timeout 60 Check (erefl : FiveCardAnalysis.profile = five_card_profile).
Timeout 60 Check
  (erefl : FiveCardAnalysis.den_boer_profile = FiveCardAnalysis.profile).

(* 1 Program *)
Timeout 60 Check (FiveCardAnalysis.profile : MonodromyProfile).

(* 2 Execution *)
Timeout 60 Check (FiveCardAnalysis.exec_plug :
  ExecutionPlug FiveCardAnalysis.profile).

(* 3 Observers: the decoded colour sequence keeps its (size A).-tuple bool
   carrier and its seat-index domain. *)
Timeout 60 Check (FiveCardAnalysis.colour_view :
  forall A : seq nat,
    bool * bool -> pgg_gT FiveCardKim_M -> (size A).-tuple bool).

(* 4 Models: the seven-cut adapter keeps its dependent index on the plug. *)
Timeout 60 Check (FiveCardAnalysis.centi_sample :
  forall R : realType, SampleAdapter R FiveCardAnalysis.exec_plug).

(* 5 Correctness: recovery keeps its group-membership hypothesis and its
   evaluated conjunction. *)
Timeout 60 Check (FiveCardAnalysis.observed_recovers :
  forall (x : bool * bool) (w0 : pgg_gT FiveCardKim_M),
    w0 \in pgg_G FiveCardKim_M ->
    exec_decode FiveCardAnalysis.exec_plug
      (OE.oe_endpoints_size FiveCardAnalysis.observed x w0) = x.1 && x.2).

(* 6 Security: the den Boer trace result keeps its observer and both sides. *)
Timeout 60 Check (FiveCardAnalysis.exec_trace_secrecy :
  forall R : realType,
    `H( (FiveCardAnalysis.secret R)
      | (FiveCardAnalysis.content_trace R ord0))
    = `H `p_ (FiveCardAnalysis.secret R)).

(* bound: the spectral endpoint marginal bound keeps its constant. *)
Timeout 60 Check (FiveCardAnalysis.endpoint_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    `|eps| < 4%:R / 5%:R ->
    forall (L : nat) (s : 'I_5),
      var_dist
        (endpoint_dist_weighted L fc_kim_sigmas (kim_weight_dist Hlt Hgt) s)
        (fdist_uniform (card_ord 5))
      <= Num.Def.sqrtr 5%:R * kim_lambda2 eps ^+ L).

(* 7 Transfer: no theorem to check, by construction; the two typed statuses
   are pinned at their constructors. *)
Timeout 60 Check
  (erefl : FiveCardAnalysis.exec_transfer_status = StaticExecutedOnly).
Timeout 60 Check
  (erefl : FiveCardAnalysis.repeated_transfer_status = NoModelComparison).
