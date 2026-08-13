(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abelian_analysis: the typed facade of the four-seat abelian instance       *)
(*                                                                            *)
(* The facade presents the abelian analysis cone through one alias per public *)
(* value, inside Module AbelianAnalysis, in seven fixed source sections:      *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* The instance carries two analysis paths over one profile. The first deals  *)
(* a secret in 'I_4 and proves arbitrary-secret recovery; the second deals    *)
(* identity card content over a trivial run argument, so its endpoints record *)
(* the cut permutation itself, and it is the path the two shuffle models and  *)
(* the mixing limitation are attached to. Aliases naming a plug, an observer  *)
(* or a result of that second path are prefixed shuffle_ rather than rand_:   *)
(* its run argument carries no randomness at all, the probability living in   *)
(* the cut models of section 4. The prefix exec_ marks the first path. Inside *)
(* the second path the prefix word_ marks the finite generator-word model and *)
(* every result stated at it, the word length being the parameter the mixing  *)
(* limitation is quantified over.                                             *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the abel_       *)
(*     prefix of their targets;                                               *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the abelian instance cone is Require Import'ed only.    *)
(*                                                                            *)
(* Section 6 states one result, and it is a negative one: the two shuffle     *)
(* models stay at full-L1 distance one at every finite word length. That is a *)
(* fixed-length mixing limitation, not a privacy failure and not an           *)
(* unqualified protocol failure. Section 5 keeps the two correctness results  *)
(* on their own paths, including the constant recovery of the                 *)
(* identity-content path, which is a correctness statement and not part of    *)
(* the limitation.                                                            *)
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
From pgg_smc Require Export pgg_collusion_bound.
From pgg_smc Require Export pgg_analysis_status.

(* Imported instance cone: loaded, never re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile abelian_exec abelian_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.

(* abel_M — the abelian two-generator monodromy template at N = 4, spelled out
   for the retention checks at the end of the file. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

Module AbelianAnalysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(** profile — the probability-independent four-seat program profile.
    @intent: alias of abel_profile. *)
Definition profile := abel_profile.

(** profile_k — the profile's threshold character is four: the sum-mod scheme
    deals one share per sheet, so all four shares are needed.
    @intent: alias of profile_k_abel. *)
Definition profile_k := profile_k_abel.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(*                                                                            *)
(* Two plugs over the one profile. Their run arguments differ: the dealt      *)
(* secret 'I_4 for the secret-recovery plug and the unit for the             *)
(* shuffle-analysis plug. Their process lists are not claimed equal.          *)
(******************************************************************************)

(** exec_plug — the secret-recovery execution plug over that profile.
    @intent: alias of abel_exec_plug. *)
Definition exec_plug := abel_exec_plug.

(** shuffle_plug — the identity-content execution plug over that profile, the
    one the shuffle models of section 4 are attached to.
    @intent: alias of abel_shuffle_plug. *)
Definition shuffle_plug := abel_shuffle_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Carriers, kept distinct: a message list for the raw traces, a sheet        *)
(* position 'I_4 for one seat's endpoint, a sequence of positions for the     *)
(* verifier's endpoint list, and the tuple 4.-tuple 'I_4 for the complete     *)
(* four-endpoint vector. The raw trace extractors carry a message list and    *)
(* are navigation only: they are not finite random variables. The complete    *)
(* endpoint vector is the observer the mixing limitation of section 6 ends    *)
(* at, and it is injective on all of {perm 'I_4}.                             *)
(******************************************************************************)

(** seat_endpoint — one seat's executed endpoint on the secret-recovery plug,
    a sheet position.
    @intent: exec_seat_endpoint specialized at abel_exec_plug. *)
Definition seat_endpoint := @exec_seat_endpoint abel_profile abel_exec_plug.

(** endpoint_vector — the complete four-endpoint observation of a cut, with
    carrier 4.-tuple 'I_4.
    @intent: alias of abel_reader. *)
Definition endpoint_vector := abel_reader.

(** verifier_trace — the verifier's raw executed trace on the secret-recovery
    plug, a message list.
    @intent: exec_verifier_trace specialized at abel_exec_plug. *)
Definition verifier_trace := @exec_verifier_trace abel_profile abel_exec_plug.

(** verifier_endpoints — the executed endpoint list of the secret-recovery
    run, the sheet positions the verifier reads.
    @intent: exec_endpoints specialized at abel_exec_plug. *)
Definition verifier_endpoints := @exec_endpoints abel_profile abel_exec_plug.

(** player_raw_trace — one seat's raw executed trace on the secret-recovery
    plug, a message list.
    @intent: exec_participant_trace specialized at abel_exec_plug. *)
Definition player_raw_trace :=
  @exec_participant_trace abel_profile abel_exec_plug.

(** observed — the secret-recovery observed execution: the run, its static
    observation and the value it recovers.
    @intent: alias of abel_det_observed. *)
Definition observed := abel_det_observed.

(** shuffle_observed — the identity-content observed execution.
    @intent: alias of abel_shuffle_observed. *)
Definition shuffle_observed := abel_shuffle_observed.

(** endpoint_vector_inj — the complete four-endpoint observation determines the
    cut.
    @intent: alias of abel_reader_inj. *)
Definition endpoint_vector_inj := abel_reader_inj.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* Two models on the identity-content plug, followed by the equation          *)
(* identifying the second one's cut distribution, so that the statements of   *)
(* sections 6 and 7 can be attached to a named distribution. The first model  *)
(* is the ideal target: the uniform distribution on exactly the permutations  *)
(* the protocol's own generators reach.                                       *)
(******************************************************************************)

(** ideal_sample — the ideal shuffle model, uniform on the four-element
    generated group.
    @intent: alias of abel_ideal_adapter. *)
Definition ideal_sample := abel_ideal_adapter.

(** word_sample — the actual shuffle model at generator-word length L + 1.
    @intent: alias of abel_actual_adapter. *)
Definition word_sample := abel_actual_adapter.

(** word_family — the fixed-length word model family, indexed by the word
    length.
    @intent: alias of abel_word_family. *)
Definition word_family := abel_word_family.

(** actual_cut_distE — the actual model's cut distribution is the
    word-induced shuffle distribution.
    @intent: alias of abel_actual_cut_dist. *)
Definition actual_cut_distE := @abel_actual_cut_dist.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* Four statements over two plugs. exec_correct, exec_recovers and            *)
(* observed_recovers belong to the secret-recovery plug and recover the dealt *)
(* secret for every secret in 'I_4. shuffle_recovers belongs to the           *)
(* identity-content plug, which deals no secret: it recovers the constant     *)
(* abel_identity_recon_value at every cut in the group. That constant         *)
(* recovery is a correctness result about the identity-content path, and it   *)
(* is not the mixing limitation of section 6, which is about the cut          *)
(* distribution rather than the recovered value.                              *)
(******************************************************************************)

(** exec_correct — termination, endpoint count and recovery of the
    secret-recovery run together.
    @intent: alias of abel_exec_correct. *)
Definition exec_correct := @abel_exec_correct.

(** exec_recovers — the secret-recovery executed run decodes to the dealt
    secret.
    @intent: alias of abel_exec_recovers. *)
Definition exec_recovers := @abel_exec_recovers.

(** observed_recovers — the secret-recovery observed run decodes to the dealt
    secret.
    @intent: alias of abel_observed_recovers. *)
Definition observed_recovers := @abel_observed_recovers.

(** shuffle_recovers — the identity-content executed run decodes to the
    constant abel_identity_recon_value at every cut in the group.
    @intent: alias of abel_shuffle_recovers. *)
Definition shuffle_recovers := @abel_shuffle_recovers.

(******************************************************************************)
(* ===== 6. Security ===== *)
(*                                                                            *)
(* One alias, and it is a negative mixing result read at the executed         *)
(* complete four-endpoint observer of the two models of section 4. It is      *)
(* neither exact nor approximate privacy, it is not a trace secrecy or        *)
(* conditional entropy statement, and it says nothing about any coalition.    *)
(* The instance carries no privacy result at all.                             *)
(******************************************************************************)

(** word_mixing_limitation — fixed-length mixing limitation: the executed
    four-endpoint observations of the actual and ideal shuffle models stay at
    full-L1 distance exactly one at every finite word length.
    @intent: alias of abel_executed_observation_distance. *)
Definition word_mixing_limitation := @abel_executed_observation_distance.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(*                                                                            *)
(* One status per analysis path. The two correctness paths compare no model   *)
(* with an idealized one. The limitation path does compare two models, and    *)
(* the comparison is negative, so its status is NegativeTransfer and no       *)
(* ideal-to-finite security theorem is claimed. The four aliases after it     *)
(* expose the limitation in its three forms, each in the repository's         *)
(* full-L1 convention: on the cut distributions of the generated group, on    *)
(* the static endpoint vector, and on the two models' own sample spaces,      *)
(* together with the equality connecting the last two.                        *)
(******************************************************************************)

(** det_transfer_status — the secret-recovery path's transfer status.
    @intent: NoModelComparison, the path carrying recovery only. *)
Definition det_transfer_status : TransferStatus := NoModelComparison.

(** shuffle_transfer_status — the identity-content correctness path's transfer
    status.
    @intent: NoModelComparison, the path carrying constant recovery only. *)
Definition shuffle_transfer_status : TransferStatus := NoModelComparison.

(** limitation_transfer_status — the mixing-limitation path's transfer status.
    @intent: NegativeTransfer, the path carrying an exact distance between the
    actual and ideal shuffle models rather than a transfer theorem. *)
Definition limitation_transfer_status : TransferStatus := NegativeTransfer.

(** word_group_dist — the group form of the limitation: the actual and ideal
    shuffle distributions on the generated group are at full-L1 distance one.
    @intent: alias of abel_word_group_dist. *)
Definition word_group_dist := @abel_word_group_dist.

(** executed_distance — the static endpoint-vector form of the limitation: the
    same distance after the complete four-endpoint reader.
    @intent: alias of abel_executed_distance. *)
Definition executed_distance := @abel_executed_distance.

(** sample_reader_distE — the equality connecting the static form to the
    executed one: the executed observation's distribution is the reader
    pushforward of the cut distribution.
    @intent: alias of abel_sample_reader_dist. *)
Definition sample_reader_distE := @abel_sample_reader_dist.

(** executed_observation_distance — the executed form of the limitation, at
    the two models' own sample spaces.
    @intent: alias of abel_executed_observation_distance. *)
Definition executed_observation_distance := @abel_executed_observation_distance.

End AbelianAnalysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, the two *)
(* plugs and the three transfer statuses, whose bodies do not reach the piSMC *)
(* interpreter, so each of those lines pins the constant or the constructor   *)
(* the alias carries. On the remaining aliases the value-level form           *)
(* Check (erefl : alias = landed) DIVERGES: the unifier unfolds past the      *)
(* alias into exec_participant_trace and evaluates run_interp. Those aliases  *)
(* are retained by spelled type ascriptions, one representative per section,  *)
(* so the observers, carriers and numeric constants are legible in the source *)
(* and not only up to conversion. Every line is Timeout-guarded, so a future  *)
(* re-aim of an alias into interpreter territory fails loudly at a named line *)
(* instead of hanging the build.                                              *)
(******************************************************************************)

Timeout 60 Check (erefl : AbelianAnalysis.profile = abel_profile).
Timeout 60 Check (erefl : AbelianAnalysis.profile_k = profile_k_abel).
Timeout 60 Check (erefl : AbelianAnalysis.exec_plug = abel_exec_plug).
Timeout 60 Check (erefl : AbelianAnalysis.shuffle_plug = abel_shuffle_plug).

(* 1 Program *)
Timeout 60 Check (AbelianAnalysis.profile : MonodromyProfile).
Timeout 60 Check
  (AbelianAnalysis.profile_k : profile_k AbelianAnalysis.profile = 4).

(* 2 Execution: the two plugs stand over the one profile. *)
Timeout 60 Check
  (AbelianAnalysis.exec_plug : ExecutionPlug AbelianAnalysis.profile).
Timeout 60 Check
  (AbelianAnalysis.shuffle_plug : ExecutionPlug AbelianAnalysis.profile).

(* 3 Observers: the complete four-endpoint observer keeps its tuple carrier
   and is injective on all of {perm 'I_4}, not only on the generated group. *)
Timeout 60 Check
  (AbelianAnalysis.endpoint_vector : {perm 'I_4} -> 4.-tuple 'I_4).
Timeout 60 Check
  (AbelianAnalysis.endpoint_vector_inj :
     injective AbelianAnalysis.endpoint_vector).

(* 4 Models: both adapters stand on the identity-content plug, and the actual
   one keeps its word-length parameter. *)
Timeout 60 Check (AbelianAnalysis.ideal_sample :
  forall R : realType, SampleAdapter R AbelianAnalysis.shuffle_plug).
Timeout 60 Check (AbelianAnalysis.word_sample :
  forall (R : realType) (L : nat),
    SampleAdapter R AbelianAnalysis.shuffle_plug).

(* 5 Correctness: secret-recovery keeps its arbitrary secret and its
   group-membership hypothesis; identity-content recovery keeps the unit run
   argument and returns the named constant. *)
Timeout 60 Check (AbelianAnalysis.observed_recovers :
  forall (s : 'I_4) (w0 : pgg_gT abel_M), w0 \in pgg_G abel_M ->
    exec_decode AbelianAnalysis.exec_plug
      (OE.oe_endpoints_size AbelianAnalysis.observed s w0) = s).
Timeout 60 Check (AbelianAnalysis.shuffle_recovers :
  forall (x : unit) (w0 : pgg_gT abel_M), w0 \in pgg_G abel_M ->
    exec_decode AbelianAnalysis.shuffle_plug
      (exec_endpoints_size (abel_shuffle_endpoints x w0))
    = abel_identity_recon_value).

(* 6 Security: the limitation is an exact distance one, at every word length,
   between the two models' own executed four-endpoint observations. *)
Timeout 60 Check (AbelianAnalysis.word_mixing_limitation :
  forall (R : realType) (L : nat),
    var_dist
      (fdistmap (@abel_sample_reader R (AbelianAnalysis.word_sample R L))
                (sa_sampleP (AbelianAnalysis.word_sample R L)))
      (fdistmap (@abel_sample_reader R (AbelianAnalysis.ideal_sample R))
                (sa_sampleP (AbelianAnalysis.ideal_sample R))) = 1).

(* 7 Transfer: the three statuses are typed values of the manifest vocabulary,
   and the group form of the limitation keeps its word-length quantifier. *)
Timeout 60 Check
  (erefl : AbelianAnalysis.det_transfer_status = NoModelComparison).
Timeout 60 Check
  (erefl : AbelianAnalysis.shuffle_transfer_status = NoModelComparison).
Timeout 60 Check
  (erefl : AbelianAnalysis.limitation_transfer_status = NegativeTransfer).
Timeout 60 Check (AbelianAnalysis.word_group_dist :
  forall (R : realType) (L : nat),
    var_dist (abel_word_dist R L) (abel_group_uniform R) = 1).
Timeout 60 Check (AbelianAnalysis.executed_distance :
  forall (R : realType) (L : nat),
    var_dist (fdistmap AbelianAnalysis.endpoint_vector (abel_word_dist R L))
             (fdistmap AbelianAnalysis.endpoint_vector (abel_group_uniform R))
    = 1).
Timeout 60 Check (AbelianAnalysis.sample_reader_distE :
  forall (R : realType) (sa : SampleAdapter R AbelianAnalysis.shuffle_plug),
    fdistmap (@abel_sample_reader R sa) (sa_sampleP sa)
    = fdistmap AbelianAnalysis.endpoint_vector (sa_cut_dist sa)).
