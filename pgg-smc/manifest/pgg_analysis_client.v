(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_client: the clean client of the analysis manifest             *)
(*                                                                            *)
(* One import reaches both featured facades. The file has EXACTLY ONE Require *)
(* of any kind, and every Check below is a bare Check on an alias, so no      *)
(* scope needs to be open and no notation needs to be in scope: what is       *)
(* established here is reachability of the aliases, not their spelling.       *)
(******************************************************************************)

From pgg_smc Require Import pgg_analysis_manifest.

(******************************************************************************)
(*     One alias from each of the seven sections of each facade               *)
(******************************************************************************)

(* Eight-card orbit instance, sections 1 to 7. *)
Check PGL27Analysis.profile.                    (* 1 Program *)
Check PGL27Analysis.exec_plug.                  (* 2 Execution *)
Check PGL27Analysis.content_trace.              (* 3 Observers *)
Check PGL27Analysis.word_sample.                (* 4 Models *)
Check PGL27Analysis.observed_recovers.          (* 5 Correctness *)
Check PGL27Analysis.exec_view_indist.           (* 6 Security *)
Check PGL27Analysis.word_view_indist_via_transfer. (* 7 Transfer *)

(* Five-card development, sections 1 to 6 and the bound sub-block. Section 7
   is empty by construction, so there is nothing to reach; the line standing
   in its place is a bound alias, which is deliberately NOT a security
   alias. *)
Check FiveCardAnalysis.profile.                 (* 1 Program *)
Check FiveCardAnalysis.exec_plug.               (* 2 Execution *)
Check FiveCardAnalysis.colour_view.             (* 3 Observers *)
Check FiveCardAnalysis.centi_sample.            (* 4 Models *)
Check FiveCardAnalysis.observed_recovers.       (* 5 Correctness *)
Check FiveCardAnalysis.exec_trace_secrecy.      (* 6 Security *)
Check FiveCardAnalysis.deal_centi_lt.           (* bound, not security *)

(******************************************************************************)
(*     The observed-execution values and the remaining distinct observers     *)
(******************************************************************************)

Check PGL27Analysis.observed.
Check FiveCardAnalysis.observed.
Check FiveCardAnalysis.den_boer_observed.

Check PGL27Analysis.verifier_trace.
Check PGL27Analysis.player_raw_trace.
Check PGL27Analysis.coalition_raw_trace.
Check PGL27Analysis.seat_endpoint.
Check PGL27Analysis.coalition_endpoints.
Check PGL27Analysis.static_view.
Check PGL27Analysis.coalition_trace.
Check PGL27Analysis.secret.

Check FiveCardAnalysis.verifier_trace.
Check FiveCardAnalysis.verifier_endpoints.
Check FiveCardAnalysis.player_raw_trace.
Check FiveCardAnalysis.coalition_raw_trace.
Check FiveCardAnalysis.input_raw_trace.
Check FiveCardAnalysis.input_trace.
Check FiveCardAnalysis.dealer_raw_trace.
Check FiveCardAnalysis.dealer_trace.
Check FiveCardAnalysis.content_trace.
Check FiveCardAnalysis.secret.

(******************************************************************************)
(*     What one import actually reaches                                       *)
(*                                                                            *)
(* Require is transitive in LOADING but not in IMPORTING. The two facades     *)
(* Require Export their type vocabulary and Require Import the instance       *)
(* files, so through the single import above this client gets:                *)
(*                                                                            *)
(*   - every facade alias, under its module name (the lines above); the two   *)
(*     modules keep the short names apart, so PGL27Analysis.profile and       *)
(*     FiveCardAnalysis.profile coexist and neither shadows the other;        *)
(*   - the exported type vocabulary, by short name (the lines below);         *)
(*   - every instance-file constant by QUALIFIED name only, because those     *)
(*     modules are loaded but never re-imported;                              *)
(*   - no instance-file constant by short name.                               *)
(******************************************************************************)

(* Exported vocabulary: short names, visible. *)
Check MonodromyProfile.
Check ExecutionPlug.
Check SampleAdapter.
Check OE.ObservedExecution.
Check ShuffleMarginalBound.
Check ShuffleCertificateBundle.
Check var_dist.
Check cond_mutual_info.
Check sw_rho_dist.
Check scb_bound.

(* Facade aliases are not visible unqualified either: the module name is the
   namespace, which is what keeps the two facades' short names distinct. *)
Fail Check profile.
Fail Check exec_plug.
Fail Check content_trace.

(* Instance-file constants: not visible by short name. *)
Locate pgl27_exec_endpoints.
Fail Check pgl27_exec_endpoints.
Locate five_card_exec_endpoints.
Fail Check five_card_exec_endpoints.
Locate five_card_exec_colour_view.
Fail Check five_card_exec_colour_view.

(* The same constants ARE reachable by qualified name, because Require loaded
   their modules transitively. Encapsulation here is a naming discipline, not
   a kernel-level barrier; a facade cannot prevent a determined client from
   naming what it depends on. *)
Check pgl27_exec.pgl27_exec_endpoints.
Check five_card_exec.five_card_exec_endpoints.
Check five_card_models.five_card_exec_colour_view.
