(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_s5x5_mutation: each load-bearing S_5 x S_5 probe claim is falsifiable*)
(*                                                                            *)
(* Phase 0 mutation battery for the unified-instance-analysis request. Each   *)
(* command below perturbs one load-bearing claim of probe_s5x5_det_plug,      *)
(* probe_s5x5_rand_plug or probe_s5x5_adapters and is guarded by Fail, so     *)
(* compiling this file certifies that the perturbation is rejected. The       *)
(* rejection messages are recorded in the source comment above each guard     *)
(* because rocq compile does not echo the text of a Fail-guarded error.       *)
(*                                                                            *)
(* Build order: probe_s5x5_det_plug.v, probe_s5x5_rand_plug.v and             *)
(* probe_s5x5_adapters.v first.                                              *)
(*                                                                            *)
(* Provenance of the quoted messages. rocq compile does not echo the text of  *)
(* a Fail-guarded error, and the rocq-mcp session could not load the S_5 x    *)
(* S_5 import closure inside its query timeout, so the texts below were not   *)
(* harvested from a transcript. They record the expected rejection shape.     *)
(* What this file certifies is the rejection itself: the file compiles, so    *)
(* every guarded command failed.                                              *)
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
From pgg_reconstruct Require Import product_threshold.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_leakage_product pgg_trace_secrecy.
From pgg_smc Require Import pgg_s5x5 s5x5_pile rigidity_s5x5_instance.
From pgg_smc Require Import s5x5_profile s5x5_run s5x5_trace s5x5_secrecy.
From pgg_smc Require Import s5_mixing s5x5_mixing.
From uia_probe Require Import probe_s5_rand_plug probe_s5x5_det_plug.
From uia_probe Require Import probe_s5x5_rand_plug probe_s5x5_adapters.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section s5x5_mutations.

Let mpX : MonodromyProfile := s5x5_profile.

Variable R : realType.

(******************************************************************************)
(*     Mutation 1: a wrong seat/share bridge                                  *)
(******************************************************************************)

(* The plug's bridge pi_T' (mp_PI mpX) = ts_T' (rp_scheme (mp_plug mpX)) holds
   at the profile's own product scheme, whose share count is 10. Retargeting it
   at a product whose first factor has four parties is rejected:
     The term "erefl" has type "pi_T' (mp_PI mpX) = pi_T' (mp_PI mpX)"
     while it is expected to have type
     "pi_T' (mp_PI mpX) = ts_T' (product_scheme sum_mod_scheme sum_mod_scheme)"
     (cannot unify "pi_T' (mp_PI mpX)" and
      "ts_T' (product_scheme sum_mod_scheme sum_mod_scheme)"). *)
Fail Check (erefl : pi_T' (mp_PI mpX)
  = ts_T' (@product_scheme 3 3 (@sum_mod_scheme 3 3) (@sum_mod_scheme 3 4))).

(******************************************************************************)
(*     Mutation 2: a participant list that is not the seat enumeration        *)
(******************************************************************************)

(* ep_playersE forces the stored list to be the canonical enumeration, so a
   nine-element list is rejected:
     The term "erefl" has type
     "[:: Ordinal isT; ...] = [:: Ordinal isT; ...]"
     while it is expected to have type
     "[:: Ordinal isT; ...] = enum 'I_(pi_T' (mp_PI mpX)).+1". *)
Fail Definition s5x5_bad_players_plug : ExecutionPlug mpX :=
  @dealer_secret_plug mpX 'I_10 erefl
    [:: @Ordinal 10 0 isT; @Ordinal 10 1 isT; @Ordinal 10 2 isT;
        @Ordinal 10 3 isT; @Ordinal 10 4 isT; @Ordinal 10 5 isT;
        @Ordinal 10 6 isT; @Ordinal 10 7 isT; @Ordinal 10 8 isT] erefl
    (fun s _ => tnth (ts_encode s5x5_scheme s)) 300.

(******************************************************************************)
(*     Mutation 3: a fuel value that does not finish the run                  *)
(******************************************************************************)

(* Fuel 300 is what makes every process reach Finish. At fuel 3 the vm_compute
   proof of s5x5_abs_terminates leaves a goal the closing tactic cannot
   discharge:
     No applicable tactic. *)
Lemma s5x5_fuel_mutation : True.
Proof.
Fail have Hbad : forall (g : 'I_10 -> 'I_10) (w0 : pgg_gT s5x5_M),
  (run_interp 3 (s5x5_aprocs_cut g w0)).1 = nseq 12 Finish
  by move=> g w0; vm_compute.
by [].
Qed.

(******************************************************************************)
(*     Mutation 4: a static observation that forgets the cut                  *)
(******************************************************************************)

(* The executed endpoints are the two-pile layout read at the cut image of each
   start. Dropping pgg_rho from the observation leaves a claim the landed
   endpoint equation does not prove:
     Cannot apply lemma s5x5_rand_endpoints. *)
Lemma s5x5_obs_mutation : True.
Proof.
Fail have Hbad : forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M),
  @exec_endpoints mpX s5x5_rand_plug uv w0 0
  = @exec_static_endpoints mpX s5x5_rand_plug
      (fun uv p => tnth (s5x5_rfree_layout uv) p.2) uv w0
  by move=> uv w0; exact: s5x5_rand_endpoints.
by [].
Qed.

(******************************************************************************)
(*     Mutation 5: a dropped group-membership premise                        *)
(******************************************************************************)

(* The randomized reconstruction is claimed for cuts drawn from pgg_G and for
   no others, so its membership argument cannot be skipped:
     Cannot apply lemma (s5x5_rfree_recon uv w0). *)
Lemma s5x5_group_mutation : True.
Proof.
Fail have Hbad : forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M),
  ts_recon s5x5_scheme
    [tuple tnth (s5x5_rfree_layout uv) (@pgg_rho s5x5_M w0 i) | i < 10]
  = @combine_secret 3 3 (uv.1 ord0 ord0) (uv.2 ord0 ord0)
  by move=> uv w0; exact: (@s5x5_rfree_recon uv w0).
by [].
Qed.

(* Pile preservation is likewise a group fact: a bare group element is not a
   membership proof:
     The term "w0" has type "pgg_gT s5x5_M" while it is expected to have type
     "w0 \in pgg_G s5x5_M". *)
Lemma s5x5_stab_mutation : True.
Proof.
Fail have Hbad := (fun (w0 : pgg_gT s5x5_M) (i : 'I_5) => s5x5_p1_stab w0 i).
by [].
Qed.

(******************************************************************************)
(*     Mutation 6: a dropped cut generalization                              *)
(******************************************************************************)

(* s5x5_rprocs_cut1 identifies the identity-cut specialization only. Claiming it
   at every cut is rejected:
     Cannot apply lemma (s5x5_rprocs_cut1 R uv). *)
Lemma s5x5_cut_mutation : True.
Proof.
Fail have Hbad : forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M),
  s5x5_rprocs_cut uv w0 = s5x5_rprocs R uv
  by move=> uv w0; exact: (s5x5_rprocs_cut1 R uv).
by [].
Qed.

(******************************************************************************)
(*     Mutation 7: a wrong recovered value in the observed execution         *)
(******************************************************************************)

(* The recovered value is the codec image of the two pile secrets. Replacing it
   by the first pile's secret alone is rejected at the record's recovery field:
     The term "s5x5_rand_recon" has type
     "... exec_decode s5x5_rand_plug Hsz = s5x5_codec (s5x5_joint_tape_secret uv)"
     while it is expected to have type
     "... exec_decode s5x5_rand_plug Hsz = combine_secret (uv.1 ord0 ord0) ord0". *)
Fail Definition s5x5_bad_codec_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpX s5x5_rand_plug 0
    s5x5_rcontent_obs
    (fun uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type =>
       @combine_secret 3 3 (uv.1 ord0 ord0) ord0)
    s5x5_rand_terminates s5x5_rand_endpoints (@s5x5_rand_recon).

(******************************************************************************)
(*     Mutation 8: flattening the two piles into one coalition               *)
(******************************************************************************)

(* The executed pile secrecy theorems are indexed by a five-element pile
   coalition, not by a ten-seat coalition; the two set types do not unify:
     The term "C" has type "{set 'I_10}" while it is expected to have type
     "{set 'I_5}". *)
Fail Check (fun (C : {set 'I_10}) (HC : (#|C| < 5)%N) =>
  @s5x5_p1_secrecy R C HC).

(* The executed ten-seat coalition reader has the carrier
   {ffun 'I_10 -> 'I_10}; it is not the pile view carrier
   {ffun 'I_5 -> 'Z_5} of rsh_view, so no cast identifies them:
     The term "sa_coalition_view ..." has type
     "{RV s5x5_rand_sampleP R -> {ffun 'I_10 -> 'I_10}}"
     while it is expected to have type
     "{RV s5x5_rand_sampleP R -> {ffun 'I_5 -> 'Z_5}}". *)
Fail Check (fun (C1 : {set 'I_5}) =>
  (@sa_coalition_view R mpX s5x5_rand_plug (s5x5_rand_sample R) 0
     (s5x5_p1_seats C1)
   : {RV (s5x5_rand_sampleP R) -> {ffun 'I_5 -> 'Z_5}})).

(* The joint secrecy theorem takes two pile coalitions; supplying one ten-seat
   coalition twice is rejected for the same reason. *)
Fail Check (fun (C : {set 'I_10}) (HC : (#|C| < 5)%N) =>
  @s5x5_joint_secrecy R C C HC HC).

(******************************************************************************)
(*     Mutation 9: the partial secret codec claimed as a cancellation        *)
(******************************************************************************)

(* split_combineK requires s1 + 5 * s2 < 10, so it does not apply at the pile-2
   secret 2:
     The term "isT" has type "true" while it is expected to have type
     "\val (Ordinal isT) + 5 * \val (Ordinal isT) < 10". *)
Fail Check (@split_combineK 3 3 (@Ordinal 5 0 isT) (@Ordinal 5 2 isT) isT).

(* Consequently the codec cancellation cannot be claimed at every pile pair:
     Cannot apply lemma s5x5_codecK_partial. *)
Lemma s5x5_codec_mutation : True.
Proof.
Fail have Hbad : forall z : ('Z_5 * 'Z_5)%type, s5x5_decodec (s5x5_codec z) = z
  by move=> z; exact: s5x5_codecK_partial.
by [].
Qed.

(** s5x5_combine_not_injective — the profile secret combination collapses two
    distinct pile pairs.
    @main correctness: combine_secret 0 2 = combine_secret 0 0 in 'I_10, so
    recovering the combined secret does not recover the joint pile pair and
    the randomized secrecy statement must be about JointSecret, not about the
    ObservedExecution recovery field. *)
Lemma s5x5_combine_not_injective :
  @combine_secret 3 3 (@Ordinal 5 0 isT) (@Ordinal 5 2 isT)
  = @combine_secret 3 3 (@Ordinal 5 0 isT) (@Ordinal 5 0 isT).
Proof. by apply: ord_inj. Qed.

(******************************************************************************)
(*     Mutation 10: a pile bound cast as a base-distribution bound           *)
(******************************************************************************)

Variable secretP : R.-fdist 'I_10.
Variable L : nat.

(** s5x5_word_uniform_premise — the base-distribution premise of the generic
    transfer theorem, at the word-induced shuffle distribution and a reference
    distribution on the cut carrier.
    @intent: a variation-distance bound between rho_from_words L s5x5_gen_tuple
    and a reference distribution on {perm 'I_10}. Nothing in the repository
    supplies it; the pile spectral theorems bound pushforwards along position
    readers, on the carrier 'I_10. *)
Definition s5x5_word_uniform_premise (Q : R.-fdist {perm 'I_10}) (delta : R)
    : Prop :=
  (var_dist (@rho_from_words R 8 7 L s5x5_gen_tuple) Q <= delta)%R.

(* The pile-1 spectral bound lives at the carrier 'I_10 and the premise at the
   carrier {perm 'I_10}, so no cast turns one into the other:
     The term "s5x5_pile1_TV_bound R L s" has type
     "var_dist (fdistmap (fun sigma => sigma (widen5to10 s)) (rho_from_words ...))
               (fdist_uniform_pile1 R) <= ..."
     while it is expected to have type
     "s5x5_word_uniform_premise (fdist_uniform_pile1 R) ...". *)
Fail Check (fun s : 'I_5 =>
  (@s5x5_pile1_TV_bound R L s
     : s5x5_word_uniform_premise (fdist_uniform_pile1 R)
         (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ L)%R)).

(* The one-seat bound of s5x5_spectral_TV_bound is not a joint bound: it is
   claimed at a single seat, and the two-seat pushforward carrier does not
   unify with the one-seat carrier:
     The term "s5x5_spectral_TV_bound R L s" has type
     "var_dist (fdistmap (fun sigma => sigma s) ...) ... <= ..."
     while it is expected to have type
     "var_dist (fdistmap (fun sigma => (sigma s, sigma s')) ...) ... <= ...". *)
Fail Check (fun s s' : 'I_10 =>
  (@s5x5_spectral_TV_bound R L s
     : (var_dist (fdistmap
           (fun sigma : {perm 'I_10} => (sigma s, sigma s'))
           (@rho_from_words R 8 7 L s5x5_gen_tuple))
         (fdist_uniform (card_ord 10) `x fdist_uniform (card_ord 10))
       <= 1 + Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ L)%R)).

End s5x5_mutations.

Print Assumptions s5x5_fuel_mutation.
Print Assumptions s5x5_obs_mutation.
Print Assumptions s5x5_group_mutation.
Print Assumptions s5x5_stab_mutation.
Print Assumptions s5x5_cut_mutation.
Print Assumptions s5x5_codec_mutation.
Print Assumptions s5x5_combine_not_injective.
