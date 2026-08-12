(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_f_client: the clean client of the analysis manifest.                 *)
(*                                                                            *)
(* Probe unit F of the 2026-08-12 layered-protocol-packing gate: the section  *)
(* 13.5 acceptance condition that a clean client can import the manifest and  *)
(* reach both featured facades.  The file has EXACTLY ONE import line and no  *)
(* other Require of any kind.                                                 *)
(*                                                                            *)
(* Every Check below is a bare Check on an alias, so the file needs no scope  *)
(* to be open and no notation to be in scope: reachability of the aliases is  *)
(* what is being established, not their spelling.                             *)
(******************************************************************************)

From lpp_probe Require Import probe_f_manifest.

(******************************************************************************)
(*     (a) One alias from each of the seven sections of each facade           *)
(******************************************************************************)

(* PGL(2,7) facade, sections 1 to 7. *)
Check fa_pgl27_profile.              (* 1 Program *)
Check fa_pgl27_exec_plug.            (* 2 Execution *)
Check fa_pgl27_coalition_trace.      (* 3 Observers *)
Check fa_pgl27_word_sample.          (* 4 Models *)
Check fa_pgl27_exec_correct.         (* 5 Correctness *)
Check fa_pgl27_word_view_indist.     (* 6 Security *)
Check fa_pgl27_transfer.             (* 7 Transfer *)

(* Five-card facade, sections 1 to 6 and the bound sub-block.  Section 7 is
   empty by construction, so there is nothing to reach; the line that would
   stand in its place is the bound alias, which is deliberately NOT a
   security alias. *)
Check fa_five_card_profile.              (* 1 Program *)
Check fa_five_card_exec_plug.            (* 2 Execution *)
Check fa_five_card_colour_view.          (* 3 Observers *)
Check fa_kim_centi_repeated_sample.      (* 4 Models *)
Check fa_five_card_exec_correct.         (* 5 Correctness *)
Check fa_five_card_exec_trace_secrecy.   (* 6 Security *)
Check fa_kim_deal_centi_lt.              (* bound, not security *)

(* The remaining observers of the five-card facade, each with its own
   carrier, all reachable through the one import. *)
Check fa_five_card_player_raw_trace.
Check fa_five_card_coalition_raw_trace.
Check fa_five_card_input_raw_trace.
Check fa_five_card_input_trace.
Check fa_five_card_dealer_raw_trace.
Check fa_five_card_dealer_trace.
Check fa_five_card_verifier_endpoints.
Check fa_five_card_content_trace.

(******************************************************************************)
(*     (b) The transfer layer                                                 *)
(******************************************************************************)

Check fa_var_dist_transfer.
Check fa_pgl27_transfer.

(******************************************************************************)
(*     (c) What one import actually reaches                                   *)
(*                                                                            *)
(* Rocq's Require is transitive in LOADING but not in IMPORTING.  The two     *)
(* facades Require Export their type vocabulary and Require Import the        *)
(* instance files, so through the single import above this client gets:       *)
(*                                                                            *)
(*   - every facade alias, by short name (the lines above);                   *)
(*   - the exported type vocabulary, by short name (the lines below);         *)
(*   - every instance-file constant by QUALIFIED name only, because those     *)
(*     modules are loaded but never re-imported;                              *)
(*   - no instance-file constant by short name.                               *)
(*                                                                            *)
(* The section 13 requirement is one-import REACHABILITY of the facade        *)
(* aliases, which the Check lines above establish.  The Locate and Fail Check *)
(* lines below record the encapsulation that comes with it: the facade is a   *)
(* narrow door, and the instance cone behind it stays behind a qualifier.     *)
(******************************************************************************)

(* Exported vocabulary: short names, visible. *)
Check MonodromyProfile.
Check ExecutionPlug.
Check SampleAdapter.
Check var_dist.
Check cond_mutual_info.
Check sw_rho_dist.

(* Instance-file constants: not visible by short name. *)
Locate pgl27_exec_endpoints.
Fail Check pgl27_exec_endpoints.
Locate five_card_exec_endpoints.
Fail Check five_card_exec_endpoints.

(* The probe-E generic bound is likewise hidden: the PGL facade imports
   probe_e_transfer without re-exporting it, so only the alias reaches here. *)
Locate var_dist_fdistmap_transfer.
Fail Check var_dist_fdistmap_transfer.

(* The same constants ARE reachable by qualified name, because Require loaded
   their modules transitively.  Encapsulation here is a naming discipline,
   not a kernel-level barrier; a facade cannot prevent a determined client
   from naming what it depends on. *)
Check pgl27_exec.pgl27_exec_endpoints.
Check five_card_exec.five_card_exec_endpoints.
Check probe_e_transfer.var_dist_fdistmap_transfer.
