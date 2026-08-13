(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_status: the typed status vocabulary of the analysis manifest  *)
(*                                                                            *)
(* Three enumerations classify one analysis path of the repository: how far   *)
(* the path is developed (CompletionLevel), what it proves about the relation *)
(* between its executed model and an idealized one (TransferStatus), and      *)
(* which named assumptions its results accept (AssumptionStatus over the      *)
(* closed set PggAxiom). A manifest row carries one value of each, and an     *)
(* instance facade exposes the values of its own paths as typed aliases.      *)
(*                                                                            *)
(* AnalysisBridged is the typed form of the prose label Security-bridged of   *)
(* the earlier manifest banner: a bridged path relates a security, leakage,   *)
(* mixing or limitation theorem to the same distribution and the same         *)
(* observer as its sample, which a negative mixing result also does.          *)
(*                                                                            *)
(* The three constructors of PggAxiom name the only accepted assumptions of   *)
(* the repository, so an assumption status is checkable against the output of *)
(* Print Assumptions without carrying strings.                                *)
(*                                                                            *)
(* The file imports protocol-layer packages only (the observed-execution and  *)
(* sample-adapter records its model vocabulary is typed against). It imports  *)
(* no instance, facade or manifest development, so no import cycle can close: *)
(* the manifest and every facade depend on it, never the converse.            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   CompletionLevel     == development level of an analysis path             *)
(*   TransferStatus      == model-transfer status of an analysis path         *)
(*   PggAxiom            == the accepted named assumptions of the repository  *)
(*   AssumptionStatus    == the assumptions a public value accepts            *)
(*   AnalysisModelFamily == a family of sample adapters over one observed     *)
(*                          execution, indexed per real field                 *)
(*   AnalysisModelSlot   == the completion-indexed model slot of a manifest   *)
(*                          row: mandatory family at Sampled and              *)
(*                          AnalysisBridged, optional family below           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Cumulative development level of an analysis path. Algebraic is a profile
   alone, Executable adds an execution plug over that profile, Observed adds
   an observed execution over that plug, Sampled adds a sample adapter over
   that execution together with its distribution-to-observer bridge, and
   AnalysisBridged adds a theorem about that distribution and that observer. *)
Inductive CompletionLevel : Set :=
  | Algebraic | Executable | Observed | Sampled | AnalysisBridged.

(* Relation an analysis path establishes between its executed model and an
   idealized one. IdealFinite is a public model-transfer theorem and
   NegativeTransfer is a theorem transporting an obstruction to the path's
   observer. StaticExecutedOnly and NoModelComparison carry no such theorem,
   and the manifest row of such a path names the absent premise instead. *)
Inductive TransferStatus : Set :=
  | NoModelComparison | StaticExecutedOnly | IdealFinite | NegativeTransfer.

(* The closed set of named assumptions accepted anywhere in the repository. *)
Inductive PggAxiom : Set :=
  | AxRayleighQ2R      (* s5_rayleigh_Q2_R: trusted analytical certificate *)
  | AxS5GroupOrder     (* s5_group_order_eq *)
  | AxS5x5GroupOrder.  (* s5x5_group_order_eq *)

(* Assumptions a public value accepts. BaselineClassicalOnly means no
   accepted assumption beyond the repository's documented boolp classical
   trio; AcceptsAxioms xs means the boolp trio plus exactly the named
   repository assumptions in xs. The trio is the ambient baseline of the
   whole repository and is deliberately not a PggAxiom constructor. *)
Inductive AssumptionStatus : Set :=
  | BaselineClassicalOnly | AcceptsAxioms of seq PggAxiom.

(******************************************************************************)
(*     The typed model-family witness of an analysis path                     *)
(******************************************************************************)

(** AnalysisModelFamily — a family of sample adapters over one observed
    execution.
    Kind: interface.
    A constructor supplies the index type amf_index R of the family at each
    real field and the sample map amf_sample sending an index to a sample
    adapter over the execution projected from the observed execution. A
    fixed model is a family with unit index; a parameterized model uses its
    real index type. *)
Record AnalysisModelFamily (observed : OE.ObservedExecution) :=
  MkAnalysisModelFamily {
    amf_index  : realType -> Type ;
    amf_sample : forall R : realType,
                   amf_index R
                   -> @SampleAdapter R _ (OE.oe_execution observed) ;
  }.

(* Under Set Implicit Arguments every argument of the amf_sample projection
   becomes implicit, including the family itself; the directive restores the
   call form amf_sample f R x, with only the observed execution inferred. *)
Arguments amf_sample {observed} f R x : rename.

(** AnalysisModelSlot — the completion-indexed model slot of a manifest row.
    @intent: at Sampled and AnalysisBridged the slot is a mandatory
    AnalysisModelFamily over the row's observed execution, so a row at those
    levels cannot be constructed without a typed model witness; at the three
    lower levels the slot is an optional family. *)
Definition AnalysisModelSlot (observed : OE.ObservedExecution)
    (c : CompletionLevel) : Type :=
  match c with
  | Sampled | AnalysisBridged => AnalysisModelFamily observed
  | Algebraic | Executable | Observed => option (AnalysisModelFamily observed)
  end.
