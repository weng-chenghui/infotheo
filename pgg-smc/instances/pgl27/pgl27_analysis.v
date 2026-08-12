(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_analysis: the typed facade of the eight-card orbit instance          *)
(*                                                                            *)
(* The facade presents the PGL(2,7) analysis cone through one alias per       *)
(* public value, inside Module PGL27Analysis, in seven fixed source sections: *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the pgl27_      *)
(*     prefix of their targets;                                               *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the PGL(2,7) instance cone is Require Import'ed only,   *)
(*     so a client reaching this file through the analysis manifest names     *)
(*     the framework records by short name and the instance constants by      *)
(*     qualified name alone.                                                  *)
(*                                                                            *)
(* Check table against the phase-H1 minimum list of the eight-card facade:    *)
(*                                                                            *)
(*   probability-independent program profile  -> profile                      *)
(*   execution plug                           -> exec_plug                    *)
(*   ObservedExecution value                  -> observed                     *)
(*   participant endpoint observer            -> seat_endpoint                *)
(*   coalition endpoint observer              -> coalition_endpoints          *)
(*   finite content-trace observer            -> content_trace                *)
(*   exact-uniform sample model               -> exact_sample,                *)
(*                                               fixed_exact_sample           *)
(*   finite-word sample model                 -> word_sample,                 *)
(*                                               fixed_word_sample            *)
(*   execution correctness and recovery       -> exec_correct, exec_recovers, *)
(*                                               observed_recovers            *)
(*   exact-security bridges                   -> exact_coalition_distE,       *)
(*                                               exact_view_indep,            *)
(*                                               coalition_trace_secrecy      *)
(*   finite-word security bridges             -> exec_view_indist,            *)
(*                                               exec_trace_indist,           *)
(*                                               word_view_indist,            *)
(*                                               word_trace_indist,           *)
(*                                               view_mixing, word_mixing     *)
(*   PGL specialization of the transfer bound                                 *)
(*                                            -> word_view_indist_via_transfer*)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: every constant an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg.
From mathcomp Require Export boolp reals.
From infotheo Require Export realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Export pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Export pgg_collusion_bound.
From pgg_smc Require Export pgg_analysis_status.
From pgg_reconstruct Require Export algebraic_rigidity.

(* Imported instance cone: loaded, never re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace pgl27_mixing.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec pgl27_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Module PGL27Analysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(** profile — the probability-independent eight-card program profile.
    @intent: alias of pgl27_profile. *)
Definition profile := pgl27_profile.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(******************************************************************************)

(** exec_plug — the execution plug over that profile, carrying the shared
    piSMC run.
    @intent: alias of pgl27_exec_plug. *)
Definition exec_plug := pgl27_exec_plug.

(** verifier_trace — the verifier's raw executed trace, a message list read
    at the verifier process of the run.
    @intent: exec_verifier_trace specialized at pgl27_exec_plug. *)
Definition verifier_trace := @exec_verifier_trace pgl27_profile pgl27_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Five carriers, kept distinct: a message list for the raw traces, the card  *)
(* position 'I_8 for one seat's endpoint, a finfun of card positions for a    *)
(* coalition's endpoints and for the content reading of a coalition's rows,   *)
(* and bool for the orbit secret.                                             *)
(******************************************************************************)

(** player_raw_trace — one seat's raw executed trace, a message list.
    @intent: alias of pgl27_exec_player_raw_trace. *)
Definition player_raw_trace := @pgl27_exec_player_raw_trace.

(** coalition_raw_trace — a coalition's raw executed traces, a finfun of
    message lists indexed by seats.
    @intent: alias of pgl27_exec_coalition_raw_trace. *)
Definition coalition_raw_trace := @pgl27_exec_coalition_raw_trace.

(** seat_endpoint — one seat's executed endpoint, a dealt card position.
    @intent: exec_seat_endpoint specialized at pgl27_exec_plug. *)
Definition seat_endpoint := @exec_seat_endpoint pgl27_profile pgl27_exec_plug.

(** coalition_endpoints — a coalition's executed endpoints, a finfun of dealt
    card positions indexed by seats.
    @intent: exec_coalition_endpoints specialized at pgl27_exec_plug. *)
Definition coalition_endpoints :=
  @exec_coalition_endpoints pgl27_profile pgl27_exec_plug.

(** content_trace — the coalition's executed interpreter rows read through
    content_of, a finfun of card positions.
    @intent: alias of pgl27_exec_content_trace, the executed finite reader. *)
Definition content_trace := @pgl27_exec_content_trace.

(** static_view — the static coalition view the word-shuffle bounds are
    stated over, a random variable with carrier {ffun 'I_8 -> 'I_8}.
    @intent: alias of pgl27_view. *)
Definition static_view := @pgl27_view.

(** coalition_trace — the static coalition content trace, a random variable
    with carrier {ffun 'I_8 -> 'I_8}.
    @intent: alias of pgl27_coalition_trace. *)
Definition coalition_trace := @pgl27_coalition_trace.

(** secret — the dealt orbit secret read as a random variable.
    @intent: alias of pgl27_secret. *)
Definition secret := @pgl27_secret.

(** prior — the uniform joint distribution on secrets and group elements the
    static observers are random variables on.
    @intent: alias of pgl27P. *)
Definition prior := @pgl27P.

(** observed — the observed execution of the profile and plug: the run, its
    static observation and the value it recovers.
    @intent: alias of pgl27_observed. *)
Definition observed := pgl27_observed.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* Each model is followed by the equations that identify its cut, coalition   *)
(* and joint distributions, so that a security statement about a named        *)
(* distribution can be attached to a named executed observer.                 *)
(******************************************************************************)

(** exact_sample — the exact-uniform model at the uniform secret prior.
    @intent: alias of pgl27_sample. *)
Definition exact_sample := @pgl27_sample.

(** word_sample — the two-hundred-letter word model at an arbitrary secret
    prior.
    @intent: alias of pgl27_word_sample. *)
Definition word_sample := @pgl27_word_sample.

(** fixed_exact_sample — the exact-uniform model at a fixed secret.
    @intent: alias of pgl27_fixed_sample. *)
Definition fixed_exact_sample := @pgl27_fixed_sample.

(** fixed_word_sample — the word model at a fixed secret.
    @intent: alias of pgl27_fixed_word_sample. *)
Definition fixed_word_sample := @pgl27_fixed_word_sample.

(** sample_cut_distE — the exact model's cut distribution is the marginal
    bound's shuffle.
    @intent: alias of pgl27_sample_cut_distE. *)
Definition sample_cut_distE := @pgl27_sample_cut_distE.

(** word_cut_distE — the word model's cut distribution is the word shuffle.
    @intent: alias of pgl27_word_cut_distE. *)
Definition word_cut_distE := @pgl27_word_cut_distE.

(** fixed_cut_distE — the fixed-secret exact model's cut distribution is the
    uniform distribution on the group.
    @intent: alias of pgl27_fixed_cut_distE. *)
Definition fixed_cut_distE := @pgl27_fixed_cut_distE.

(** fixed_word_cut_distE — the fixed-secret word model's cut distribution is
    the word shuffle.
    @intent: alias of pgl27_fixed_word_cut_distE. *)
Definition fixed_word_cut_distE := @pgl27_fixed_word_cut_distE.

(** exact_coalition_distE — the exact model's executed coalition distribution
    is the pushforward of the uniform prior along the static view.
    @intent: alias of pgl27_exact_coalition_distE. *)
Definition exact_coalition_distE := @pgl27_exact_coalition_distE.

(** fixed_word_coalition_distE — the fixed-secret word model's executed
    coalition distribution is the pushforward of the word shuffle along the
    static view.
    @intent: alias of pgl27_fixed_word_coalition_distE. *)
Definition fixed_word_coalition_distE := @pgl27_fixed_word_coalition_distE.

(** fixed_word_content_trace_distE — the fixed-secret word model's executed
    content trace has the distribution of the coalition trace under the word
    shuffle.
    @intent: alias of pgl27_fixed_word_content_trace_distE. *)
Definition fixed_word_content_trace_distE :=
  @pgl27_fixed_word_content_trace_distE.

(** word_joint_viewE — the joint executed view-and-secret distribution of the
    arbitrary-prior word model is the static joint distribution.
    @intent: alias of pgl27_word_joint_viewE. *)
Definition word_joint_viewE := @pgl27_word_joint_viewE.

(** word_sample_joint_distE — the word model's joint sample distribution is
    the static word-generated joint distribution.
    @intent: alias of pgl27_word_sample_joint_distE. *)
Definition word_sample_joint_distE := @pgl27_word_sample_joint_distE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* The observed-execution package derives recovery but no separate combined   *)
(* correctness corollary at this instance; the combined statement is          *)
(* exec_correct below, and OE.oe_run_correct applies to observed generically. *)
(******************************************************************************)

(** exec_correct — termination, endpoint count and recovery together.
    @intent: alias of pgl27_exec_correct. *)
Definition exec_correct := @pgl27_exec_correct.

(** exec_recovers — the executed run decodes to the dealt secret.
    @intent: alias of pgl27_exec_recovers. *)
Definition exec_recovers := @pgl27_exec_recovers.

(** observed_recovers — the observed run decodes to the dealt secret.
    @intent: alias of pgl27_observed_recovers. *)
Definition observed_recovers := @pgl27_observed_recovers.

(******************************************************************************)
(* ===== 6. Security ===== *)
(******************************************************************************)

(** content_traceE — the executed content reader is the static coalition
    trace random variable, the equation that carries a static result to the
    executed observer.
    @intent: alias of pgl27_content_traceE. *)
Definition content_traceE := @pgl27_content_traceE.

(** word_view_indist — two secrets give static coalition views within 2^-39
    in variation distance under the word shuffle, at three cards.
    @intent: alias of pgl27_word_view_indist. *)
Definition word_view_indist := @pgl27_word_view_indist.

(** word_trace_indist — the same bound for the static coalition content
    trace.
    @intent: alias of pgl27_word_trace_indist. *)
Definition word_trace_indist := @pgl27_word_trace_indist.

(** exec_view_indist — two fixed secrets give executed coalition
    distributions within 2^-39 in variation distance, at three cards.
    @intent: alias of pgl27_exec_view_indist. *)
Definition exec_view_indist := @pgl27_exec_view_indist.

(** exec_trace_indist — the same bound for the executed content trace.
    @intent: alias of pgl27_exec_trace_indist. *)
Definition exec_trace_indist := @pgl27_exec_trace_indist.

(** view_mixing — the joint view-and-secret distribution under the word
    shuffle is within 2^-40 of the product of its marginals.
    @intent: alias of pgl27_view_mixing. *)
Definition view_mixing := @pgl27_view_mixing.

(** word_mixing — the word shuffle is within 2^-40 of the uniform
    distribution on the group.
    @intent: alias of pgl27_word_mixing. *)
Definition word_mixing := @pgl27_word_mixing.

(** coalition_trace_secrecy — the conditional entropy of the secret given a
    coalition trace equals its entropy, at three cards and the uniform prior.
    @intent: alias of pgl27_coalition_trace_secrecy. *)
Definition coalition_trace_secrecy := @pgl27_coalition_trace_secrecy.

(** exact_view_indep — at three cards the exact model's executed coalition
    observation and the orbit secret have a product joint distribution.
    @intent: alias of pgl27_exec_exact_view_indep. *)
Definition exact_view_indep := @pgl27_exec_exact_view_indep.

(** marginal_bound — the shuffle marginal bound of the exact model.
    @intent: alias of pgl27_marginal_bound. *)
Definition marginal_bound := @pgl27_marginal_bound.

(** certificate_bundle — the shuffle certificate bundle of the exact model,
    carrying that marginal bound and its exactness attachment.
    @intent: alias of pgl27_certificate_bundle. *)
Definition certificate_bundle := @pgl27_certificate_bundle.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(******************************************************************************)

(** var_dist_transfer — the generic exact-to-finite transfer inequality.
    @intent: alias of var_dist_fdistmap_transfer. *)
Definition var_dist_transfer := @var_dist_fdistmap_transfer.

(** word_view_indist_via_transfer — the 2^-39 coalition-view bound obtained
    as an instance of the generic transfer inequality.
    @intent: alias of pgl27_word_view_indist_via_transfer.
    Naming: intentional; the alias keeps the landed name so that the facade
    and the theorem it exposes are searchable by one string, and the
    _via_transfer suffix records the derivation that distinguishes this
    corollary from word_view_indist, whose statement it reproduces. *)
Definition word_view_indist_via_transfer :=
  @pgl27_word_view_indist_via_transfer.

(** word_transfer_status — the word path's transfer status.
    @intent: IdealFinite, the path carrying a public model-transfer theorem
    whose base-distribution premise is discharged by word_mixing. *)
Definition word_transfer_status : TransferStatus := IdealFinite.

End PGL27Analysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, whose   *)
(* bodies do not reach the piSMC interpreter.  On every other alias the       *)
(* value-level form Check (erefl : alias = landed) DIVERGES: the unifier      *)
(* unfolds past the alias into exec_participant_trace and evaluates           *)
(* run_interp.  Those aliases are retained by spelled type ascriptions, one   *)
(* representative per section, so the assumptions, observers and numeric      *)
(* constants are legible in the source and not only up to conversion.  Every  *)
(* line is Timeout-guarded, so a future re-aim of an alias into interpreter   *)
(* territory fails loudly at a named line instead of hanging the build.       *)
(******************************************************************************)

Timeout 60 Check (erefl : PGL27Analysis.profile = pgl27_profile).
Timeout 60 Check (erefl : PGL27Analysis.exec_plug = pgl27_exec_plug).

(* 1 Program *)
Timeout 60 Check (PGL27Analysis.profile : MonodromyProfile).

(* 2 Execution *)
Timeout 60 Check (PGL27Analysis.exec_plug :
  ExecutionPlug PGL27Analysis.profile).

(* 3 Observers: the executed content reader keeps its {ffun 'I_8 -> 'I_8}
   carrier and its coalition index domain. *)
Timeout 60 Check (PGL27Analysis.content_trace :
  {set 'I_8} -> bool -> pgg_gT pgl27_M -> {ffun 'I_8 -> 'I_8}).

(* 4 Models: the sample adapter keeps its dependent index on the plug. *)
Timeout 60 Check (PGL27Analysis.fixed_word_sample :
  forall R : realType, bool -> SampleAdapter R PGL27Analysis.exec_plug).

(* 5 Correctness: recovery keeps its group-membership hypothesis. *)
Timeout 60 Check (PGL27Analysis.observed_recovers :
  forall (s : bool) (w0 : pgg_gT pgl27_M),
    w0 \in pgg_G pgl27_M ->
    exec_decode PGL27Analysis.exec_plug
      (OE.oe_endpoints_size PGL27Analysis.observed s w0) = s).

(* 6 Security: the executed coalition bound keeps its cardinality hypothesis,
   its two sample-layer distributions and its 2^-39 constant. *)
Timeout 60 Check (PGL27Analysis.exec_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s) 0 C)
             (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s') 0 C)
    <= 2%:R^-39).

(* 7 Transfer: the specialization has the statement of word_view_indist
   verbatim, hypothesis for hypothesis and constant for constant, and the
   typed status is pinned at its constructor. *)
Timeout 60 Check (erefl : PGL27Analysis.word_transfer_status = IdealFinite).
Timeout 60 Check (PGL27Analysis.word_view_indist_via_transfer :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.static_view R C (s, g)) (rho_word R))
      (fdistmap (fun g => PGL27Analysis.static_view R C (s', g)) (rho_word R))
    <= 2%:R^-39).
