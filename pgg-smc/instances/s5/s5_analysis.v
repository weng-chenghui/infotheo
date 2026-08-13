(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_analysis: the typed facade of the five-seat S_5 instance                *)
(*                                                                            *)
(* The facade presents the S_5 analysis cone through one alias per public     *)
(* value, inside Module S5Analysis, in seven fixed source sections:           *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* The instance carries two analysis paths over one profile. The              *)
(* deterministic path deals a position and proves recovery; the randomized    *)
(* path deals an additive sharing of a tape secret and carries the executed   *)
(* secrecy results. Aliases naming a plug or a model of the randomized path   *)
(* are prefixed rand_, and those of the finite-word endpoint model word_. As  *)
(* at the other instance facades, the prefix exec_ marks a result read at an  *)
(* executed observer rather than the deterministic path: the two section-6    *)
(* aliases are executed results of the randomized path, and the retention     *)
(* check of section 6 spells rand_exec_plug and rand_sample into its type.    *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the s5_ prefix  *)
(*     of their targets;                                                      *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the S_5 instance cone is Require Import'ed only.        *)
(*                                                                            *)
(* Section 6 states exact secrecy results of the randomized path only. The    *)
(* endpoint marginal bound of the finite-word model is a separate sub-block   *)
(* after section 6: it bounds one seat's endpoint distribution, it is         *)
(* conditional on s5_rayleigh_Q2_R, and it is not a privacy statement.        *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: every constant an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg.
From mathcomp Require Export boolp reals zmodp matrix.
From infotheo Require Export realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Export pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Export pgg_collusion_bound pgg_randomized_sharing.
From pgg_smc Require Export pgg_canonical_sharing.
From pgg_smc Require Export pgg_analysis_status.

(* Imported instance cone: loaded, never re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_smc Require Import pgg_leakage_witness pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_raag_s5 pgg_raag_path s5_profile s5_run.
From pgg_smc Require Import s5_secrecy s5_trace s5_mixing.
From pgg_smc Require Import s5_exec s5_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Module S5Analysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(** profile — the probability-independent five-seat program profile.
    @intent: alias of s5_profile. *)
Definition profile := s5_profile.

(** profile_k — the profile's privacy threshold is five: fewer than five
    shares cannot distinguish two secrets.
    @intent: alias of profile_k_s5. *)
Definition profile_k := profile_k_s5.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(*                                                                            *)
(* Two plugs over the one profile. Their run arguments differ: the dealt      *)
(* position 'I_5 for the deterministic plug and the sampler tape             *)
(* 'rV['Z_5]_5 for the randomized plug. Their process lists are not claimed   *)
(* equal.                                                                     *)
(******************************************************************************)

(** exec_plug — the deterministic execution plug over that profile.
    @intent: alias of s5_exec_plug. *)
Definition exec_plug := s5_exec_plug.

(** rand_exec_plug — the randomized execution plug over that profile.
    @intent: alias of s5_rand_exec_plug. *)
Definition rand_exec_plug := s5_rand_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Four carriers, kept distinct: a message list for the raw traces, the       *)
(* dealt position 'I_5 for one seat's endpoint and for one seat's read trace  *)
(* content, a finfun of positions for a coalition's endpoints and a sequence  *)
(* of positions for the verifier's endpoint list. The raw                     *)
(* trace extractors carry a message list and are navigation only: they are    *)
(* not finite random variables. Only the randomized path carries a finite     *)
(* content-trace reader, that being the path the secrecy results are stated   *)
(* on.                                                                        *)
(******************************************************************************)

(** seat_endpoint — one seat's deterministic executed endpoint, a dealt
    position.
    @intent: exec_seat_endpoint specialized at s5_exec_plug. *)
Definition seat_endpoint := @exec_seat_endpoint s5_profile s5_exec_plug.

(** coalition_endpoints — a coalition's deterministic executed endpoints, a
    finfun of dealt positions indexed by seats.
    @intent: exec_coalition_endpoints specialized at s5_exec_plug. *)
Definition coalition_endpoints :=
  @exec_coalition_endpoints s5_profile s5_exec_plug.

(** verifier_trace — the verifier's raw executed trace on the deterministic
    plug, a message list.
    @intent: exec_verifier_trace specialized at s5_exec_plug. *)
Definition verifier_trace := @exec_verifier_trace s5_profile s5_exec_plug.

(** verifier_endpoints — the deterministic executed endpoint list of the run,
    the dealt positions the verifier reads.
    @intent: exec_endpoints specialized at s5_exec_plug. *)
Definition verifier_endpoints := @exec_endpoints s5_profile s5_exec_plug.

(** player_raw_trace — one seat's raw executed trace on the deterministic
    plug, a message list.
    @intent: exec_participant_trace specialized at s5_exec_plug. *)
Definition player_raw_trace := @exec_participant_trace s5_profile s5_exec_plug.

(** observed — the deterministic observed execution: the run, its static
    observation and the value it recovers.
    @intent: alias of s5_observed. *)
Definition observed := s5_observed.

(** rand_seat_endpoint — one seat's randomized executed endpoint, an additive
    share read as a position.
    @intent: exec_seat_endpoint specialized at s5_rand_exec_plug. *)
Definition rand_seat_endpoint :=
  @exec_seat_endpoint s5_profile s5_rand_exec_plug.

(** rand_coalition_endpoints — a coalition's randomized executed endpoints, a
    finfun of additive shares indexed by seats.
    @intent: exec_coalition_endpoints specialized at s5_rand_exec_plug. *)
Definition rand_coalition_endpoints :=
  @exec_coalition_endpoints s5_profile s5_rand_exec_plug.

(** rand_content_trace — seat i's randomized executed trace content, a random
    variable on the tape distribution with carrier 'I_5.
    @intent: alias of s5_sample_content_trace, the executed finite reader. *)
Definition rand_content_trace := @s5_sample_content_trace.

(** rand_verifier_trace — the verifier's raw executed trace on the randomized
    plug, a message list.
    @intent: exec_verifier_trace specialized at s5_rand_exec_plug. *)
Definition rand_verifier_trace :=
  @exec_verifier_trace s5_profile s5_rand_exec_plug.

(** rand_verifier_endpoints — the randomized executed endpoint list of the
    run, the additive shares the verifier reads.
    @intent: exec_endpoints specialized at s5_rand_exec_plug. *)
Definition rand_verifier_endpoints :=
  @exec_endpoints s5_profile s5_rand_exec_plug.

(** rand_player_raw_trace — one seat's raw executed trace on the randomized
    plug, a message list.
    @intent: exec_participant_trace specialized at s5_rand_exec_plug. *)
Definition rand_player_raw_trace :=
  @exec_participant_trace s5_profile s5_rand_exec_plug.

(** rand_observed — the randomized observed execution.
    @intent: alias of s5_rand_observed. *)
Definition rand_observed := s5_rand_observed.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* Each model is followed by the equation identifying its cut distribution,   *)
(* so that a statement about a named distribution can be attached to a named  *)
(* executed observer. The two sample spaces differ by definition and no       *)
(* theorem relates their base distributions.                                  *)
(******************************************************************************)

(** rand_sample — the randomized exact-secrecy model at the uniform iid tape
    distribution and the identity cut.
    @intent: alias of s5_rand_sample. *)
Definition rand_sample := @s5_rand_sample.

(** word_sample — the finite-word endpoint model at an arbitrary secret prior
    and word length.
    @intent: alias of s5_word_sample. *)
Definition word_sample := @s5_word_sample.

(** rand_family — the randomized tape model as a unit-indexed typed family.
    @intent: alias of s5_rand_family. *)
Definition rand_family := s5_rand_family.

(** word_family — the finite-word model family, indexed by a secret prior
    and a word length.
    @intent: alias of s5_word_family. *)
Definition word_family := s5_word_family.

(** rand_cut_distE — the randomized model's cut distribution is the point
    distribution at the identity.
    @intent: alias of s5_rand_cut_distE. *)
Definition rand_cut_distE := @s5_rand_cut_distE.

(** word_cut_distE — the finite-word model's cut distribution is the
    word-induced shuffle distribution.
    @intent: alias of s5_word_cut_distE. *)
Definition word_cut_distE := @s5_word_cut_distE.

(** word_cut_imageE — the finite-word model's shuffle-image distribution is
    that same word-induced distribution.
    @intent: alias of s5_word_cut_imageE. *)
Definition word_cut_imageE := @s5_word_cut_imageE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* Four statements over two plugs. exec_correct, exec_recovers and            *)
(* observed_recovers belong to the deterministic plug and recover the dealt   *)
(* position; rand_correct, rand_recovers and rand_observed_recovers belong to *)
(* the randomized plug and recover the encoded tape secret.                   *)
(******************************************************************************)

(** exec_correct — deterministic termination, endpoint count and recovery
    together.
    @intent: alias of s5_exec_correct. *)
Definition exec_correct := @s5_exec_correct.

(** exec_recovers — the deterministic executed run decodes to the dealt
    position.
    @intent: alias of s5_exec_recovers. *)
Definition exec_recovers := @s5_exec_recovers.

(** observed_recovers — the deterministic observed run decodes to the dealt
    position.
    @intent: alias of s5_observed_recovers. *)
Definition observed_recovers := @s5_observed_recovers.

(** rand_correct — randomized termination, endpoint count and recovery
    together.
    @intent: alias of s5_rand_correct. *)
Definition rand_correct := @s5_rand_correct.

(** rand_recovers — the randomized executed run decodes to the encoded tape
    secret.
    @intent: alias of s5_rand_exec_recovers. *)
Definition rand_recovers := @s5_rand_exec_recovers.

(** rand_observed_recovers — the randomized observed run decodes to the
    encoded tape secret.
    @intent: alias of s5_rand_observed_recovers. *)
Definition rand_observed_recovers := @s5_rand_observed_recovers.

(******************************************************************************)
(* ===== 6. Security ===== *)
(*                                                                            *)
(* Both aliases state exact privacy of the randomized path at the executed    *)
(* observers of rand_sample: the first is trace secrecy in conditional        *)
(* entropy form for one seat's trace content, the second is exact privacy in  *)
(* mutual information and conditional entropy form for a coalition of fewer   *)
(* than five seats. Neither is an approximate-privacy statement, and the      *)
(* deterministic path carries no secrecy result.                              *)
(******************************************************************************)

(** exec_trace_secrecy — trace secrecy in conditional entropy form: one seat's
    executed trace content leaves the tape secret's conditional entropy equal
    to its entropy.
    @intent: alias of s5_exec_trace_secrecy. *)
Definition exec_trace_secrecy := @s5_exec_trace_secrecy.

(** exec_coalition_secrecy — exact privacy in mutual information and
    conditional entropy form: a coalition of fewer than five seats has zero
    mutual information with the tape secret and leaves its conditional
    entropy equal to its entropy.
    @intent: alias of s5_exec_coalition_secrecy. *)
Definition exec_coalition_secrecy := @s5_exec_coalition_secrecy.

(******************************************************************************)
(* ===== bound (endpoint marginal, not security) ===== *)
(*                                                                            *)
(* The alias below is an endpoint marginal mixing bound: it bounds the        *)
(* distance from uniform of ONE seat's endpoint distribution after a word of  *)
(* L cuts, in the repository's full-L1 convention. It quantifies over one     *)
(* position, mentions no coalition view and no second secret, and is          *)
(* conditional on the trusted analytical certificate s5_rayleigh_Q2_R. It is  *)
(* neither exact nor approximate privacy, and is recorded as an endpoint      *)
(* marginal bound in the analysis manifest.                                   *)
(******************************************************************************)

(** word_endpoint_bound — endpoint marginal mixing of the finite-word model at
    word length L, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5_word_endpoint_bound. *)
Definition word_endpoint_bound := @s5_word_endpoint_bound.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(*                                                                            *)
(* One status per analysis path. The deterministic path compares no model     *)
(* with an idealized one. The randomized path carries its executed observers  *)
(* back to the landed static results by the two reader equalities below, and  *)
(* compares no idealized model. The finite-word path compares no model        *)
(* either: the landed spectral theorem bounds a pushforward on the carrier    *)
(* 'I_5, while the generic transfer theorem needs a bound on the carrier      *)
(* {perm 'I_5}, which is the premise word_missing_premise names and which the *)
(* repository does not supply.                                                *)
(******************************************************************************)

(** det_transfer_status — the deterministic path's transfer status.
    @intent: NoModelComparison, the path carrying recovery only. *)
Definition det_transfer_status : TransferStatus := NoModelComparison.

(** rand_transfer_status — the randomized path's transfer status.
    @intent: StaticExecutedOnly, the path carrying its landed static secrecy
    results to its executed observers and no ideal-to-finite theorem. *)
Definition rand_transfer_status : TransferStatus := StaticExecutedOnly.

(** rand_content_traceE — the executed content reader is the landed
    player-trace random variable, one of the two equalities witnessing
    rand_transfer_status.
    @intent: alias of s5_sample_content_traceE. *)
Definition rand_content_traceE := @s5_sample_content_traceE.

(** rand_coalition_viewE — the executed coalition endpoint reader is the
    randomized sharing's coalition view, the other equality witnessing
    rand_transfer_status.
    @intent: alias of s5_sample_coalition_viewE. *)
Definition rand_coalition_viewE := @s5_sample_coalition_viewE.

(** word_transfer_status — the finite-word path's transfer status.
    @intent: NoModelComparison, the base-distribution premise of the generic
    transfer theorem being absent at the cut carrier. *)
Definition word_transfer_status : TransferStatus := NoModelComparison.

(** word_missing_premise — the absent premise named as a proposition.
    @intent: alias of s5_word_base_premise, a variation-distance bound
    between the finite-word cut distribution on {perm 'I_5} and a reference
    distribution on that carrier. *)
Definition word_missing_premise := @s5_word_base_premise.

(** word_transfer_conditional — the generic transfer inequality at the
    finite-word cut distribution, under that premise.
    @intent: alias of s5_word_transfer_conditional. *)
Definition word_transfer_conditional := @s5_word_transfer_conditional.

End S5Analysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, the two *)
(* plugs and the three transfer statuses, whose bodies do not reach the piSMC *)
(* interpreter, so each of those lines pins the constant or the constructor   *)
(* the alias carries. On every other alias the value-level form               *)
(* Check (erefl : alias = landed) DIVERGES: the                               *)
(* unifier unfolds past the alias into exec_participant_trace and evaluates   *)
(* run_interp. Those aliases are retained by spelled type ascriptions, one    *)
(* representative per section, so the assumptions, observers and numeric      *)
(* constants are legible in the source and not only up to conversion. Every   *)
(* line is Timeout-guarded, so a future re-aim of an alias into interpreter   *)
(* territory fails loudly at a named line instead of hanging the build.       *)
(******************************************************************************)

Timeout 60 Check (erefl : S5Analysis.profile = s5_profile).
Timeout 60 Check (erefl : S5Analysis.profile_k = profile_k_s5).
Timeout 60 Check (erefl : S5Analysis.exec_plug = s5_exec_plug).
Timeout 60 Check (erefl : S5Analysis.rand_exec_plug = s5_rand_exec_plug).

(* 1 Program *)
Timeout 60 Check (S5Analysis.profile : MonodromyProfile).

(* 2 Execution: the two plugs stand over the one profile. *)
Timeout 60 Check (S5Analysis.exec_plug : ExecutionPlug S5Analysis.profile).
Timeout 60 Check (S5Analysis.rand_exec_plug : ExecutionPlug S5Analysis.profile).

(* 3 Observers: the randomized content reader keeps its 'I_5 carrier and its
   seat index domain, and is a random variable on the tape distribution. *)
Timeout 60 Check (S5Analysis.rand_content_trace :
  forall (R : realType) (i : 'I_5),
    {RV (s5_rand_sampleP R) -> 'I_5}).

(* 4 Models: the finite-word adapter keeps its dependent index on the
   deterministic plug, its arbitrary secret prior and its word length. *)
Timeout 60 Check (S5Analysis.word_sample :
  forall (R : realType), R.-fdist 'I_5 -> forall L : nat,
    SampleAdapter R S5Analysis.exec_plug).

(* 5 Correctness: randomized recovery keeps its group-membership hypothesis
   and returns the encoded tape secret, not the dealt position. *)
Timeout 60 Check (S5Analysis.rand_observed_recovers :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (@Gen_PGGTypes 3 3 (path_gen_tuple 3))),
    w0 \in pgg_G (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) ->
    exec_decode S5Analysis.rand_exec_plug
      (OE.oe_endpoints_size S5Analysis.rand_observed u w0)
    = s5_codec (s5_tape_secret u)).

(* 6 Security: executed coalition secrecy keeps its cardinality hypothesis and
   both of its forms, at the executed coalition reader of the randomized
   model. *)
Timeout 60 Check (S5Analysis.exec_coalition_secrecy :
  forall (R : realType) (C : {set 'I_5}), (#|C| < 5)%N ->
    `I( rsh_secret (@unif_randomized_sharing R 3 4) ;
        @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
          (S5Analysis.rand_sample R) 0 C ) = 0 /\
    `H( rsh_secret (@unif_randomized_sharing R 3 4)
        | @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
            (S5Analysis.rand_sample R) 0 C )
      = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))).

(* bound: the endpoint marginal bound keeps its one-position quantifier, its
   sqrt-5 factor and its L-th power. *)
Timeout 60 Check (S5Analysis.word_endpoint_bound :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdist_uniform (card_ord 5))
    <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).

(* 7 Transfer: the three statuses are typed values of the manifest vocabulary,
   and the absent premise is a proposition on the cut carrier {perm 'I_5}. *)
Timeout 60 Check (erefl : S5Analysis.det_transfer_status = NoModelComparison).
Timeout 60 Check (erefl :
  S5Analysis.rand_transfer_status = StaticExecutedOnly).
Timeout 60 Check (erefl : S5Analysis.word_transfer_status = NoModelComparison).
Timeout 60 Check (S5Analysis.word_missing_premise :
  forall (R : realType), R.-fdist 'I_5 -> forall L : nat,
    R.-fdist {perm 'I_5} -> R -> Prop).
