(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_s5_mutation: each load-bearing S_5 probe claim is falsifiable        *)
(*                                                                            *)
(* Phase 0 mutation battery for the unified-instance-analysis request. Each   *)
(* command below perturbs one load-bearing claim of probe_s5_det_plug,        *)
(* probe_s5_rand_plug or probe_s5_adapters and is guarded by Fail, so         *)
(* compiling this file certifies that the perturbation is rejected. The       *)
(* rejection messages are recorded in the source comment above each guard     *)
(* because rocq compile does not echo the text of a Fail-guarded error.       *)
(*                                                                            *)
(* Build order: probe_s5_det_plug.v and probe_s5_rand_plug.v first.           *)
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
From pgg_smc Require Import pgg_trace_secrecy s5_trace s5_mixing.
From uia_probe Require Import probe_s5_det_plug probe_s5_rand_plug.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section s5_mutations.

(** s5_M — the S_5 adjacent-transposition monodromy template at N = 5.
    @intent: the Gen_PGGTypes form s5_PI and s5_plug carry, spelled out here
    because the instance files keep it section-local. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

Let mpS : MonodromyProfile := s5_profile.

Variable R : realType.

(******************************************************************************)
(*     Mutation 1: a wrong seat/share bridge                                  *)
(******************************************************************************)

(* The plug's bridge pi_T' (mp_PI mpS) = ts_T' (rp_scheme (mp_plug mpS)) holds
   at the profile's own scheme, whose share count is 5. Retargeting it at a
   four-share scheme is rejected:
     The term "erefl" has type "pi_T' (mp_PI mpS) = pi_T' (mp_PI mpS)"
     while it is expected to have type
     "pi_T' (mp_PI mpS) = ts_T' sum_mod_scheme"
     (cannot unify "pi_T' (mp_PI mpS)" and "ts_T' sum_mod_scheme"). *)
Fail Check (erefl : pi_T' (mp_PI mpS) = ts_T' (@sum_mod_scheme 3 3)).

(******************************************************************************)
(*     Mutation 2: a participant list that is not the seat enumeration        *)
(******************************************************************************)

(* ep_playersE forces the stored list to be the canonical enumeration, so a
   four-element list is rejected:
     The term "erefl" has type
     "[:: Ordinal isT; Ordinal isT; Ordinal isT; Ordinal isT] =
      [:: Ordinal isT; Ordinal isT; Ordinal isT; Ordinal isT]"
     while it is expected to have type
     "[:: Ordinal isT; Ordinal isT; Ordinal isT; Ordinal isT] =
      enum 'I_(pi_T' (mp_PI mpS)).+1". *)
Fail Definition s5_bad_players_plug : ExecutionPlug mpS :=
  @dealer_secret_plug mpS 'I_5 erefl
    [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT;
        @Ordinal 5 3 isT] erefl
    (fun s _ => tnth (ts_encode s5_scheme s)) 150.

(******************************************************************************)
(*     Mutation 3: a fuel value that does not finish the run                  *)
(******************************************************************************)

(* Fuel 150 is what makes every process reach Finish. At fuel 3 the vm_compute
   proof of s5_abs_terminates leaves a goal the closing tactic cannot discharge:
     No applicable tactic. *)
Lemma s5_fuel_mutation : True.
Proof.
Fail have Hbad : forall (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M),
  (run_interp 3 (s5_aprocs_cut g w0)).1 = nseq 7 Finish
  by move=> g w0; vm_compute.
by [].
Qed.

(******************************************************************************)
(*     Mutation 4: a static observation that forgets the cut                  *)
(******************************************************************************)

(* The executed endpoints are the layout read at the cut image of each start.
   Dropping pgg_rho from the observation leaves a claim the landed endpoint
   equation does not prove:
     Cannot apply lemma s5_rand_endpoints. *)
Lemma s5_obs_mutation : True.
Proof.
Fail have Hbad : forall (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M),
  @exec_endpoints mpS s5_rand_plug u w0 0
  = @exec_static_endpoints mpS s5_rand_plug
      (fun u p => tnth (s5_rfree_layout u) p.2) u w0
  by move=> u w0; exact: s5_rand_endpoints.
by [].
Qed.

(******************************************************************************)
(*     Mutation 5: a dropped group-membership premise                        *)
(******************************************************************************)

(* Reconstruction invariance is claimed for cuts drawn from pgg_G and for no
   others, so its membership argument cannot be skipped:
     Cannot apply lemma
     (fun u : 'rV_5 => s5_recon_perm_invariant (s5_rfree_valid u)). *)
Lemma s5_group_mutation : True.
Proof.
Fail have Hbad := (fun (u : 'rV['Z_5]_5) =>
  s5_recon_perm_invariant (s5_rfree_valid u)).
by [].
Qed.

(******************************************************************************)
(*     Mutation 6: a dropped cut generalization                              *)
(******************************************************************************)

(* s5_rprocs_cut1 identifies the identity-cut specialization only. Claiming it
   at every cut is rejected:
     Cannot apply lemma (s5_rprocs_cut1 R u). *)
Lemma s5_cut_mutation : True.
Proof.
Fail have Hbad : forall (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M),
  s5_rprocs_cut u w0 = s5_rprocs R u
  by move=> u w0; exact: (s5_rprocs_cut1 R u).
by [].
Qed.

(******************************************************************************)
(*     Mutation 7: a wrong codec in the packaged observed execution          *)
(******************************************************************************)

(* The recovered value is the codec image of the tape secret. Replacing the
   codec by a constant is rejected at the record's recovery field:
     The term "s5_rand_recon" has type
     "... exec_decode s5_rand_plug Hsz = s5_codec (s5_tape_secret u)"
     while it is expected to have type
     "... exec_decode s5_rand_plug Hsz = ord0"
     (cannot unify "exec_decode s5_rand_plug Hsz = s5_codec (s5_tape_secret u)"
     and "exec_decode s5_rand_plug Hsz = ord0"). *)
Fail Definition s5_bad_codec_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpS s5_rand_plug 0
    s5_rcontent_obs (fun _ => ord0 : 'I_5)
    s5_rand_terminates s5_rand_endpoints (@s5_rand_recon).

(******************************************************************************)
(*     Mutation 8: the spectral bound is not a base-distribution bound        *)
(******************************************************************************)

Variable L : nat.

(** s5_word_uniform_premise — the base-distribution premise of the generic
    transfer theorem, at the word-induced shuffle distribution and the uniform
    distribution on the cut carrier.
    @intent: a variation-distance bound between rho_from_words L
    (path_gen_tuple 3) and a reference distribution on {perm 'I_5}. Nothing in
    the repository supplies it; the spectral theorem bounds the pushforward
    along a position reader, on the carrier 'I_5. *)
Definition s5_word_uniform_premise (Q : R.-fdist {perm 'I_5}) (delta : R) : Prop :=
  (var_dist (rho_from_words L (path_gen_tuple 3)) Q <= delta)%R.

(* The spectral bound lives at the carrier 'I_5 and the premise at the carrier
   {perm 'I_5}, so no cast turns one into the other:
     The term "s5_spectral_convergence_proved R L s" has type
     "var_dist (fdistmap (fun sigma => sigma s) (rho_from_words ...))
               (fdist_uniform (card_ord 5)) <= ..."
     while it is expected to have type
     "s5_word_uniform_premise (fdist_uniform (card_ord 5)) ...". *)
Fail Check (fun s : 'I_5 =>
  (s5_spectral_convergence_proved R L s
     : s5_word_uniform_premise (fdist_uniform (card_ord 5))
         (Num.sqrt 5%:R * s5_alpha_R R ^+ L)%R)).

End s5_mutations.

Print Assumptions s5_fuel_mutation.
Print Assumptions s5_obs_mutation.
Print Assumptions s5_group_mutation.
Print Assumptions s5_cut_mutation.
