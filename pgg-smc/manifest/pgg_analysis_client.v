(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_client: the clean client of the analysis manifest             *)
(*                                                                            *)
(* One import reaches all five facades, the typed status vocabulary and the   *)
(* seventeen typed rows. The file has EXACTLY ONE Require of any kind, and    *)
(* every Check below is a bare Check on an alias, so no scope needs to be     *)
(* open and no notation needs to be in scope: what is established here is     *)
(* reachability of the aliases, not their spelling.                           *)
(*                                                                            *)
(* Section 7 of a facade may carry no theorem. It is then represented here by *)
(* its typed transfer-status alias, which every facade has.                   *)
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
Check PGL27Analysis.word_transfer_status.       (* 7 Transfer, typed status *)

(* Five-card development, sections 1 to 6, the bound sub-block and section 7.
   That section carries no theorem, so its representative is the typed
   transfer status; the bound alias below is deliberately NOT a security
   alias. *)
Check FiveCardAnalysis.profile.                 (* 1 Program *)
Check FiveCardAnalysis.exec_plug.               (* 2 Execution *)
Check FiveCardAnalysis.colour_view.             (* 3 Observers *)
Check FiveCardAnalysis.centi_sample.            (* 4 Models *)
Check FiveCardAnalysis.observed_recovers.       (* 5 Correctness *)
Check FiveCardAnalysis.exec_trace_secrecy.      (* 6 Security *)
Check FiveCardAnalysis.deal_centi_lt.           (* bound, not security *)
Check FiveCardAnalysis.exec_transfer_status.    (* 7 Transfer, typed status *)
Check FiveCardAnalysis.repeated_transfer_status.

(* Five-seat S_5 instance, sections 1 to 6, the bound sub-block and section
   7. *)
Check S5Analysis.profile.                       (* 1 Program *)
Check S5Analysis.rand_exec_plug.                (* 2 Execution *)
Check S5Analysis.rand_content_trace.            (* 3 Observers *)
Check S5Analysis.rand_sample.                   (* 4 Models *)
Check S5Analysis.rand_observed_recovers.        (* 5 Correctness *)
Check S5Analysis.exec_coalition_secrecy.        (* 6 Security *)
Check S5Analysis.word_endpoint_bound.           (* bound, not security *)
Check S5Analysis.rand_transfer_status.          (* 7 Transfer, typed status *)

(* Ten-seat S_5 x S_5 instance, sections 1 to 6, the bound sub-block and
   section 7. *)
Check S5x5Analysis.profile.                     (* 1 Program *)
Check S5x5Analysis.rand_exec_plug.              (* 2 Execution *)
Check S5x5Analysis.joint_view.                  (* 3 Observers *)
Check S5x5Analysis.rand_sample.                 (* 4 Models *)
Check S5x5Analysis.rand_observed_recovers.      (* 5 Correctness *)
Check S5x5Analysis.exec_joint_secrecy.          (* 6 Security *)
Check S5x5Analysis.word_pile1_bound.            (* bound, not security *)
Check S5x5Analysis.rand_transfer_status.        (* 7 Transfer, typed status *)

(* Four-seat abelian instance, sections 1 to 7. Its section 6 result is a
   negative one, and the transfer status records that. *)
Check AbelianAnalysis.profile.                  (* 1 Program *)
Check AbelianAnalysis.shuffle_plug.             (* 2 Execution *)
Check AbelianAnalysis.endpoint_vector.          (* 3 Observers *)
Check AbelianAnalysis.word_sample.              (* 4 Models *)
Check AbelianAnalysis.shuffle_recovers.         (* 5 Correctness *)
Check AbelianAnalysis.word_mixing_limitation.   (* 6 mixing limitation *)
Check AbelianAnalysis.limitation_transfer_status. (* 7 Transfer *)

(******************************************************************************)
(*     The observed-execution values and the remaining distinct observers     *)
(******************************************************************************)

Check PGL27Analysis.observed.
Check FiveCardAnalysis.observed.
Check FiveCardAnalysis.den_boer_observed.
Check S5Analysis.observed.
Check S5Analysis.rand_observed.
Check S5x5Analysis.observed.
Check S5x5Analysis.rand_observed.
Check AbelianAnalysis.observed.
Check AbelianAnalysis.shuffle_observed.

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

Check S5Analysis.seat_endpoint.
Check S5Analysis.coalition_endpoints.
Check S5Analysis.verifier_trace.
Check S5Analysis.verifier_endpoints.
Check S5Analysis.player_raw_trace.
Check S5Analysis.rand_seat_endpoint.
Check S5Analysis.rand_coalition_endpoints.
Check S5Analysis.rand_verifier_trace.
Check S5Analysis.rand_verifier_endpoints.
Check S5Analysis.rand_player_raw_trace.

(* The two piles of the ten-seat instance keep distinct readers at every
   level: seat, coalition and the joint pair. *)
Check S5x5Analysis.seat_endpoint.
Check S5x5Analysis.coalition_endpoints.
Check S5x5Analysis.verifier_trace.
Check S5x5Analysis.verifier_endpoints.
Check S5x5Analysis.player_raw_trace.
Check S5x5Analysis.rand_seat_endpoint.
Check S5x5Analysis.rand_coalition_endpoints.
Check S5x5Analysis.rand_content_trace.
Check S5x5Analysis.rand_verifier_trace.
Check S5x5Analysis.rand_verifier_endpoints.
Check S5x5Analysis.rand_player_raw_trace.
Check S5x5Analysis.pile1_seats.
Check S5x5Analysis.pile2_seats.
Check S5x5Analysis.pile1_seat_view.
Check S5x5Analysis.pile2_seat_view.
Check S5x5Analysis.pile1_coalition_view.
Check S5x5Analysis.pile2_coalition_view.

(* The abelian complete four-endpoint observer and its injectivity. *)
Check AbelianAnalysis.seat_endpoint.
Check AbelianAnalysis.verifier_trace.
Check AbelianAnalysis.verifier_endpoints.
Check AbelianAnalysis.player_raw_trace.
Check AbelianAnalysis.endpoint_vector_inj.
Check AbelianAnalysis.ideal_sample.

(******************************************************************************)
(*     The typed status vocabulary and the seventeen rows                     *)
(******************************************************************************)

Check CompletionLevel.
Check TransferStatus.
Check PggAxiom.
Check AssumptionStatus.
Check AnalysisPathRow.
Check apr_observed.
Check apr_sample.
Check apr_completion.
Check apr_transfer.
Check apr_assumptions.

Check pgl27_row_exact.
Check pgl27_row_word.
Check five_card_row_uniform.
Check five_card_row_biased.
Check five_card_row_repeated.
Check s5_row_det.
Check s5_row_rand.
Check s5_row_word.
Check s5x5_row_det.
Check s5x5_row_rand.
Check s5x5_row_pile1_word.
Check s5x5_row_pile2_word.
Check s5x5_row_pile1_limitation.
Check s5x5_row_pile2_limitation.
Check abel_row_recovery.
Check abel_row_identity.
Check abel_row_limitation.

(******************************************************************************)
(*     What one import actually reaches                                       *)
(*                                                                            *)
(* Require is transitive in LOADING but not in IMPORTING. The five facades    *)
(* Require Export their type vocabulary and Require Import the instance       *)
(* files, so through the single import above this client gets:                *)
(*                                                                            *)
(*   - every facade alias, under its module name (the lines above); the five  *)
(*     modules keep the short names apart, so PGL27Analysis.profile,          *)
(*     FiveCardAnalysis.profile, S5Analysis.profile, S5x5Analysis.profile and *)
(*     AbelianAnalysis.profile coexist and none shadows another;              *)
(*   - the exported type vocabulary, by short name (the lines below);         *)
(*   - the manifest's own rows and record, by short name;                     *)
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
   namespace, which is what keeps the five facades' short names distinct. *)
Fail Check profile.
Fail Check exec_plug.
Fail Check content_trace.
Fail Check rand_sample.
Fail Check joint_view.
Fail Check endpoint_vector.

(* Instance-file constants: not visible by short name. *)
Locate pgl27_exec_endpoints.
Fail Check pgl27_exec_endpoints.
Locate five_card_exec_endpoints.
Fail Check five_card_exec_endpoints.
Locate five_card_exec_colour_view.
Fail Check five_card_exec_colour_view.
Locate s5_rfree_share.
Fail Check s5_rfree_share.
Locate s5x5_rfree_recon.
Fail Check s5x5_rfree_recon.
Locate abel_reader.
Fail Check abel_reader.

(* The same constants ARE reachable by qualified name, because Require loaded
   their modules transitively. Encapsulation here is a naming discipline, not
   a kernel-level barrier; a facade cannot prevent a determined client from
   naming what it depends on. *)
Check pgl27_exec.pgl27_exec_endpoints.
Check five_card_exec.five_card_exec_endpoints.
Check five_card_models.five_card_exec_colour_view.
Check s5_exec.s5_rfree_share.
Check s5x5_exec.s5x5_rfree_recon.
Check abelian_exec.abel_reader.
