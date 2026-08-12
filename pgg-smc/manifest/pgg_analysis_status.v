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
(* The file has no pgg import. The manifest and every facade depend on it,    *)
(* so an import of any pgg development here would close a cycle.              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   CompletionLevel  == development level of an analysis path                *)
(*   TransferStatus   == model-transfer status of an analysis path            *)
(*   PggAxiom         == the accepted named assumptions of the repository     *)
(*   AssumptionStatus == the assumptions a public value accepts               *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

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

(* Assumptions a public value accepts: none beyond the ambient classical
   axioms, or the exact list of named assumptions Print Assumptions reports. *)
Inductive AssumptionStatus : Set :=
  | KernelClosed | AcceptsAxioms of seq PggAxiom.
