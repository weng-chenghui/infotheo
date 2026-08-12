(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_f_pgl27_facade: the provisional PGL(2,7) typed facade.               *)
(*                                                                            *)
(* Probe unit F of the 2026-08-12 layered-protocol-packing gate: section      *)
(* 15.8, phase H1 of section 13.  The file presents the PGL(2,7) analysis     *)
(* cone through one alias per public value, in the seven fixed source         *)
(* sections of section 13.1, in this order:                                   *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* Every alias is a Definition whose body is the landed constant itself, so   *)
(* the alias type is the landed type verbatim; no proof body is copied.  The  *)
(* production facade (pgl27_analysis.v) will alias the post-migration         *)
(* parameterless names; here the targets are the landed R-parameterized API.  *)
(*                                                                            *)
(* Import discipline (probed in probe_f_client.v): the type vocabulary the    *)
(* alias types are written in is Require Export'ed, so that a client reaching *)
(* the facade through probe_f_manifest.v can name MonodromyProfile,           *)
(* ExecutionPlug, SampleAdapter, var_dist and the entropy notations.  The     *)
(* PGL(2,7) instance files are Require Import'ed only, so their short names   *)
(* are NOT re-exported and stay reachable from a client by qualified name     *)
(* alone.                                                                     *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: everything an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg.
From mathcomp Require Export boolp reals.
From infotheo Require Export realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_sample_adapter.
From pgg_reconstruct Require Export algebraic_rigidity.

(* Imported instance cone: not re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace pgl27_mixing.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec.
From lpp_probe Require Import probe_e_transfer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Smoke check: the lpp_probe logical root resolves                       *)
(******************************************************************************)

(* The rebuild script now maps this directory to the logical root lpp_probe,
   so probe files can Require one another.  The generic transfer bound of
   probe unit E is reachable here by that route. *)
Check @var_dist_fdistmap_transfer.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(* fa_pgl27_profile: the probability-independent PGL(2,7) program profile.
   @intent: alias of pgl27_profile; production aliases the parameterless
   post-migration value, this probe aliases the landed R-parameterized one. *)
Definition fa_pgl27_profile := @pgl27_profile.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(******************************************************************************)

(* fa_pgl27_exec_plug: the PGL(2,7) execution plug over that profile.
   @intent: alias of pgl27_exec_plug, the shared piSMC run of the profile. *)
Definition fa_pgl27_exec_plug := @pgl27_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(******************************************************************************)

(* fa_pgl27_player_raw_trace: one seat's raw executed trace, a message list.
   @intent: alias of pgl27_exec_player_raw_trace. *)
Definition fa_pgl27_player_raw_trace := @pgl27_exec_player_raw_trace.

(* fa_pgl27_coalition_raw_trace: a coalition's raw executed traces, a finfun
   of message lists indexed by seats.
   @intent: alias of pgl27_exec_coalition_raw_trace. *)
Definition fa_pgl27_coalition_raw_trace := @pgl27_exec_coalition_raw_trace.

(* fa_pgl27_seat_endpoint: the generic seat endpoint observer at the PGL plug,
   carrier the dealt card position 'I_8.
   @intent: exec_seat_endpoint specialized at pgl27_exec_plug. *)
Definition fa_pgl27_seat_endpoint (R : realType) :=
  @exec_seat_endpoint R (pgl27_profile R) (pgl27_exec_plug R).

(* fa_pgl27_coalition_endpoints: the generic coalition endpoint observer at the
   PGL plug, carrier a finfun of card positions.
   @intent: exec_coalition_endpoints specialized at pgl27_exec_plug. *)
Definition fa_pgl27_coalition_endpoints (R : realType) :=
  @exec_coalition_endpoints R (pgl27_profile R) (pgl27_exec_plug R).

(* fa_pgl27_coalition_trace: the finite content-trace observer of section 10.1,
   a random variable on the uniform prior with carrier {ffun 'I_8 -> 'I_8}.
   @intent: alias of pgl27_coalition_trace, the landed finite reader;
   production also exposes the executed reader of probe unit D2. *)
Definition fa_pgl27_coalition_trace := @pgl27_coalition_trace.

(* fa_pgl27_static_view: the static coalition view the word bounds are stated
   over, carrier {ffun 'I_8 -> 'I_8}.
   @intent: alias of pgl27_view. *)
Definition fa_pgl27_static_view := @pgl27_view.

(* fa_pgl27_secret: the dealt Boolean secret read as a random variable.
   @intent: alias of pgl27_secret. *)
Definition fa_pgl27_secret := @pgl27_secret.

(* fa_pgl27_prior: the uniform joint prior on secrets and group elements.
   @intent: alias of pgl27P, the distribution the static observers read. *)
Definition fa_pgl27_prior := @pgl27P.

(******************************************************************************)
(* ===== 4. Models ===== *)
(******************************************************************************)

(* fa_pgl27_sample: the exact-uniform sample model on the group.
   @intent: alias of pgl27_sample. *)
Definition fa_pgl27_sample := @pgl27_sample.

(* fa_pgl27_word_sample: the finite two-hundred-letter word sample model at an
   arbitrary Boolean prior.
   @intent: alias of pgl27_word_sample. *)
Definition fa_pgl27_word_sample := @pgl27_word_sample.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(******************************************************************************)

(* fa_pgl27_exec_correct: termination, endpoint count and recovery together.
   @intent: alias of pgl27_exec_correct. *)
Definition fa_pgl27_exec_correct := @pgl27_exec_correct.

(* fa_pgl27_exec_recovers: the derived run decodes to the dealt secret.
   @intent: alias of pgl27_exec_recovers. *)
Definition fa_pgl27_exec_recovers := @pgl27_exec_recovers.

(******************************************************************************)
(* ===== 6. Security ===== *)
(******************************************************************************)

(* fa_pgl27_word_view_indist: coalition-view variation distance at most 2^-39
   under the word shuffle, for coalitions of at most three seats.
   @intent: alias of pgl27_word_view_indist. *)
Definition fa_pgl27_word_view_indist := @pgl27_word_view_indist.

(* fa_pgl27_word_trace_indist: the same bound for the coalition content trace.
   @intent: alias of pgl27_word_trace_indist. *)
Definition fa_pgl27_word_trace_indist := @pgl27_word_trace_indist.

(* fa_pgl27_view_mixing: the joint view-and-secret distribution under the word
   shuffle is within 2^-40 of the product of its marginals.
   @intent: alias of pgl27_view_mixing. *)
Definition fa_pgl27_view_mixing := @pgl27_view_mixing.

(* fa_pgl27_word_mixing: the word shuffle is within 2^-40 of uniform.
   @intent: alias of pgl27_word_mixing. *)
Definition fa_pgl27_word_mixing := @pgl27_word_mixing.

(* fa_pgl27_coalition_trace_secrecy: the exact-uniform conditional entropy of
   the secret given a coalition trace equals its entropy.
   @intent: alias of pgl27_coalition_trace_secrecy. *)
Definition fa_pgl27_coalition_trace_secrecy := @pgl27_coalition_trace_secrecy.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(******************************************************************************)

(* fa_var_dist_transfer: the generic exact-to-finite transfer inequality.
   @intent: alias of var_dist_fdistmap_transfer of probe unit E. *)
Definition fa_var_dist_transfer := @var_dist_fdistmap_transfer.

(* fa_pgl27_transfer: the PGL(2,7) specialization of that inequality, whose
   statement is pgl27_word_view_indist verbatim.
   @intent: alias of pgl27_word_view_indist_via_transfer of probe unit E. *)
Definition fa_pgl27_transfer := @pgl27_word_view_indist_via_transfer.

(******************************************************************************)
(*     Type retention, part 1: every alias against its landed target          *)
(*                                                                            *)
(* alias_same_type x y elaborates only when x and y have one common type, and *)
(* it never compares their values.  The value-level check                     *)
(* Check (erefl : fa = landed) is stronger and is kept for the two aliases    *)
(* below where it is cheap, but on every alias whose body reaches the piSMC   *)
(* interpreter it DIVERGES: the unifier unfolds past the alias into           *)
(* exec_participant_trace and evaluates run_interp.  An unguarded compile of  *)
(* Check (erefl : fa_pgl27_player_raw_trace = pgl27_exec_player_raw_trace)    *)
(* was killed at ten minutes.  Every line here is Timeout-guarded so that a   *)
(* future re-aim of an alias into interpreter territory fails loudly at a     *)
(* named line instead of hanging the build.                                   *)
(******************************************************************************)

(* alias_same_type — the two arguments share one type.
   @intent: the type-level half of the facade retention check; the returned
   type is that common type, so a retyped alias makes the Check red. *)
Definition alias_same_type (T : Type) (x y : T) : Type := T.

Timeout 60 Check (erefl : fa_pgl27_profile = @pgl27_profile).
Timeout 60 Check (erefl : fa_pgl27_exec_plug = @pgl27_exec_plug).

Timeout 60 Check (alias_same_type fa_pgl27_profile (@pgl27_profile)).
Timeout 60 Check (alias_same_type fa_pgl27_exec_plug (@pgl27_exec_plug)).
Timeout 60 Check (alias_same_type fa_pgl27_player_raw_trace
  (@pgl27_exec_player_raw_trace)).
Timeout 60 Check (alias_same_type fa_pgl27_coalition_raw_trace
  (@pgl27_exec_coalition_raw_trace)).
Timeout 60 Check (alias_same_type fa_pgl27_seat_endpoint
  (fun R : realType =>
     @exec_seat_endpoint R (pgl27_profile R) (pgl27_exec_plug R))).
Timeout 60 Check (alias_same_type fa_pgl27_coalition_endpoints
  (fun R : realType =>
     @exec_coalition_endpoints R (pgl27_profile R) (pgl27_exec_plug R))).
Timeout 60 Check (alias_same_type fa_pgl27_coalition_trace
  (@pgl27_coalition_trace)).
Timeout 60 Check (alias_same_type fa_pgl27_static_view (@pgl27_view)).
Timeout 60 Check (alias_same_type fa_pgl27_secret (@pgl27_secret)).
Timeout 60 Check (alias_same_type fa_pgl27_prior (@pgl27P)).
Timeout 60 Check (alias_same_type fa_pgl27_sample (@pgl27_sample)).
Timeout 60 Check (alias_same_type fa_pgl27_word_sample (@pgl27_word_sample)).
Timeout 60 Check (alias_same_type fa_pgl27_exec_correct (@pgl27_exec_correct)).
Timeout 60 Check (alias_same_type fa_pgl27_exec_recovers
  (@pgl27_exec_recovers)).
Timeout 60 Check (alias_same_type fa_pgl27_word_view_indist
  (@pgl27_word_view_indist)).
Timeout 60 Check (alias_same_type fa_pgl27_word_trace_indist
  (@pgl27_word_trace_indist)).
Timeout 60 Check (alias_same_type fa_pgl27_view_mixing (@pgl27_view_mixing)).
Timeout 60 Check (alias_same_type fa_pgl27_word_mixing (@pgl27_word_mixing)).
Timeout 60 Check (alias_same_type fa_pgl27_coalition_trace_secrecy
  (@pgl27_coalition_trace_secrecy)).
Timeout 60 Check (alias_same_type fa_var_dist_transfer
  (@var_dist_fdistmap_transfer)).
Timeout 60 Check (alias_same_type fa_pgl27_transfer
  (@pgl27_word_view_indist_via_transfer)).

(******************************************************************************)
(*     Type retention, part 2: one written type per section                   *)
(*                                                                            *)
(* One representative of each of the seven sections is ascribed against its   *)
(* type written out in full, so that the retained assumptions and conclusions *)
(* are legible in the source and not only up to conversion.                   *)
(******************************************************************************)

(* 1 Program *)
Check (fa_pgl27_profile : forall R : realType, MonodromyProfile R).

(* 2 Execution *)
Check (fa_pgl27_exec_plug :
  forall R : realType, ExecutionPlug (fa_pgl27_profile R)).

(* 3 Observers: the finite content-trace reader keeps its {ffun 'I_8 -> 'I_8}
   carrier and its uniform-prior index. *)
Check (fa_pgl27_coalition_trace :
  forall R : realType,
    {set 'I_8} -> {RV (fa_pgl27_prior R) -> {ffun 'I_8 -> 'I_8}}).

(* 4 Models: the sample adapter keeps its dependent index on the plug. *)
Check (fa_pgl27_sample :
  forall R : realType, SampleAdapter (fa_pgl27_exec_plug R)).
Check (fa_pgl27_word_sample :
  forall R : realType, R.-fdist bool -> SampleAdapter (fa_pgl27_exec_plug R)).

(* 5 Correctness *)
Check (fa_pgl27_exec_recovers :
  forall (R : realType) (s : bool) (w0 : pgg_gT pgl27_M),
    w0 \in pgg_G pgl27_M ->
    exec_decode (fa_pgl27_exec_plug R)
      (exec_endpoints_size (pgl27_exec_endpoints R s w0)) = s).

(* 6 Security: the coalition bound keeps its cardinality hypothesis, its two
   pushforwards along the word shuffle and its 2^-39 constant. *)
Check (fa_pgl27_word_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist (fdistmap (fun g => fa_pgl27_static_view R C (s, g)) (rho_word R))
             (fdistmap (fun g => fa_pgl27_static_view R C (s', g)) (rho_word R))
    <= 2%:R^-39).

(* 7 Transfer: the PGL specialization has the statement of the section-6
   theorem verbatim, hypothesis for hypothesis and constant for constant. *)
Check (fa_pgl27_transfer :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist (fdistmap (fun g => fa_pgl27_static_view R C (s, g)) (rho_word R))
             (fdistmap (fun g => fa_pgl27_static_view R C (s', g)) (rho_word R))
    <= 2%:R^-39).

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions fa_pgl27_profile.
Print Assumptions fa_pgl27_exec_recovers.
Print Assumptions fa_pgl27_word_view_indist.
Print Assumptions fa_pgl27_coalition_trace_secrecy.
Print Assumptions fa_pgl27_transfer.
