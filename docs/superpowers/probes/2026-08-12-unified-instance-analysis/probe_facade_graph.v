(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_facade_graph: the section 6.8 facade/manifest graph probe            *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 6.8 and  *)
(* 10.2. It compiles the typed status vocabulary planned for                  *)
(* pgg-smc/manifest/pgg_analysis_status.v, the typed manifest row record      *)
(* planned for pgg_analysis_manifest.v, one Observed-level row and one        *)
(* Sampled-level row instantiated at the compiled S5 probe packages, and a    *)
(* facade-skeleton module exposing typed transfer-status aliases, checked     *)
(* through module-qualified access the way the clean client will reach them.  *)
(*                                                                            *)
(* Planned production import graph (no cycle):                                *)
(*   pgg_analysis_status  (no pgg imports)                                    *)
(*     -> s5_analysis / s5x5_analysis / abelian_analysis (Require Export it)  *)
(*     -> pgg_analysis_manifest (Require Export all five facades)             *)
(*     -> pgg_analysis_client (single Require Import of the manifest)         *)
(*                                                                            *)
(* Planned _CoqProject additions, in listing order:                           *)
(*   pgg-smc/manifest/pgg_analysis_status.v      (after                       *)
(*     pgg-smc/protocol/pgg_observed_execution.v, line 141)                   *)
(*   pgg-smc/instances/s5/s5_exec.v, s5_models.v, s5_analysis.v (after        *)
(*     pgg-smc/instances/s5/s5_trace.v, line 233)                             *)
(*   pgg-smc/instances/s5x5/s5x5_exec.v, s5x5_models.v, s5x5_analysis.v       *)
(*     (after pgg-smc/instances/s5x5/s5x5_trace.v, line 240)                  *)
(*   pgg-smc/instances/abelian/abelian_exec.v, abelian_models.v,              *)
(*     abelian_analysis.v (after pgg-smc/instances/abelian/abel_profile.v,    *)
(*     line 245)                                                              *)
(*   pgg-smc/scripts/profile_facade_check.sh (not a Rocq target)              *)
(*                                                                            *)
(* Qualified-name discipline for existing collisions (naming audit):          *)
(*   s5_run.s5_players vs s5_trace.s5_players; the four content_of copies in  *)
(*   s5_trace, s5x5_trace, pgl27_trace, denboer_trace. No production file     *)
(*   Imports two *_trace modules; collided names are written qualified.       *)
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
From pgg_smc Require Import pgg_raag_s5 pgg_raag_path s5_profile s5_run.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy s5_trace s5_secrecy s5_mixing.
From uia_probe Require Import probe_s5_det_plug probe_s5_rand_plug.
From uia_probe Require Import probe_s5_adapters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* 1. The typed status vocabulary (planned pgg_analysis_status.v, verbatim)   *)
(******************************************************************************)

(* Cumulative completion ladder of an analysis path; replaces the prose-only
   ladder of the manifest banner. AnalysisBridged replaces the older label
   Security-bridged so that negative mixing paths classify accurately. *)
Inductive CompletionLevel : Set :=
  | Algebraic | Executable | Observed | Sampled | AnalysisBridged.

(* Model-transfer status of an analysis path. IdealFinite requires a public
   model-transfer theorem; NegativeTransfer requires a theorem transporting an
   obstruction to the path's observer; the other two carry no theorem and the
   manifest row names the absent premise. *)
Inductive TransferStatus : Set :=
  | NoModelComparison | StaticExecutedOnly | IdealFinite | NegativeTransfer.

(* The closed set of accepted named assumptions in the repository. *)
Inductive PggAxiom : Set :=
  | AxRayleighQ2R      (* s5_rayleigh_Q2_R: trusted analytical certificate *)
  | AxS5GroupOrder     (* s5_group_order_eq *)
  | AxS5x5GroupOrder.  (* s5x5_group_order_eq *)

(* Assumption status of a public value: kernel-closed, or the exact list of
   accepted named assumptions reported by Print Assumptions. *)
Inductive AssumptionStatus : Set :=
  | KernelClosed | AcceptsAxioms of seq PggAxiom.

(******************************************************************************)
(* 2. The typed manifest row record (planned pgg_analysis_manifest.v shape)   *)
(******************************************************************************)

(* One analysis path: the observed-execution package carries the profile and
   plug as projections, the sample slot is optional per realType, and the
   three status fields are the typed levels of section 10.2. Theorems are
   NOT stored here; they stay facade aliases pinned by the type checker. *)
Record AnalysisPathRow := MkAnalysisPathRow {
  apr_observed    : OE.ObservedExecution ;
  apr_sample      : forall R : realType,
                      option (@SampleAdapter R _
                                (OE.oe_execution apr_observed)) ;
  apr_completion  : CompletionLevel ;
  apr_transfer    : TransferStatus ;
  apr_assumptions : AssumptionStatus ;
}.

(******************************************************************************)
(* 3. Rows instantiated at the compiled S5 probe packages                     *)
(******************************************************************************)

(* S5 deterministic correctness path: Observed level, no model, no transfer
   theorem; assumption status from the probe's Print Assumptions. *)
Definition probe_s5_det_row : AnalysisPathRow :=
  @MkAnalysisPathRow s5_det_observed (fun _ => None)
    Observed NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder]).

(* S5 randomized exact-secrecy path: the randomized adapter attaches at every
   realType; the executed secrecy bridges put it at AnalysisBridged with
   StaticExecutedOnly transfer. *)
Definition probe_s5_rand_row : AnalysisPathRow :=
  @MkAnalysisPathRow s5_rand_observed (fun R => Some (s5_rand_sample R))
    AnalysisBridged StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder]).

(******************************************************************************)
(* 4. Facade skeleton: typed transfer-status aliases reachable qualified      *)
(******************************************************************************)

Module S5FacadeSkeleton.
Definition profile := s5_profile.
Definition exec_plug := s5_det_plug.
Definition rand_exec_plug := s5_rand_plug.
Definition observed := s5_det_observed.
Definition rand_observed := s5_rand_observed.
Definition det_transfer_status : TransferStatus := NoModelComparison.
Definition rand_transfer_status : TransferStatus := StaticExecutedOnly.
Definition word_transfer_status : TransferStatus := NoModelComparison.
End S5FacadeSkeleton.

(* The clean-client access pattern: bare qualified Checks. *)
Check S5FacadeSkeleton.profile.
Check S5FacadeSkeleton.exec_plug.
Check S5FacadeSkeleton.observed.
Check S5FacadeSkeleton.rand_transfer_status.
Check (S5FacadeSkeleton.rand_transfer_status : TransferStatus).
Check probe_s5_det_row.
Check (apr_transfer probe_s5_det_row : TransferStatus).
Check (apr_completion probe_s5_rand_row : CompletionLevel).

(* Mutation guards: a status alias checked at the wrong vocabulary type is a
   compile error, and an absent alias is a compile error — the two failure
   modes the manifest checker relies on. *)
Fail Check (S5FacadeSkeleton.rand_transfer_status : CompletionLevel).
Fail Check S5FacadeSkeleton.no_such_alias.

(* The two vocabulary namespaces are disjoint from every existing identifier:
   these names resolve to this file's inductives, not to anything imported. *)
Check (Observed : CompletionLevel).
Check (NegativeTransfer : TransferStatus).
Check (AcceptsAxioms [:: AxRayleighQ2R] : AssumptionStatus).
Check (KernelClosed : AssumptionStatus).
