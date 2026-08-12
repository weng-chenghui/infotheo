(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_abel_mutation: each load-bearing abelian probe claim is falsifiable  *)
(*                                                                            *)
(* Phase 0 mutation battery for the unified-instance-analysis request. Each   *)
(* guarded command below perturbs one load-bearing claim of                   *)
(* probe_abel_profile, probe_abel_plugs or probe_abel_negative. Every         *)
(* perturbation is preceded by a Check of the unperturbed claim, so a Fail    *)
(* that fired for a spelling reason rather than for the intended reason would *)
(* show up as a red Check.                                                    *)
(*                                                                            *)
(* Build order: probe_abel_profile.v, probe_abel_plugs.v,                     *)
(* probe_abel_negative.v.                                                     *)
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
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile.
From uia_probe Require Import probe_abel_profile probe_abel_plugs.
From uia_probe Require Import probe_abel_negative.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Mutation 1: the landed two-seat interface in the plug position         *)
(******************************************************************************)

(* Control: the four-seat profile carries an execution plug. *)
Check abel_det_plug.

(* The landed abel_profile has pi_T' = 1 and ts_T' = 3, so the seat/share
   bridge would have to prove 1 = 3:
     The term "erefl" has type
      "pi_T' (mp_PI abel_profile) = pi_T' (mp_PI abel_profile)"
     while it is expected to have type
      "pi_T' (mp_PI abel_profile) = ts_T' (rp_scheme (mp_plug abel_profile))". *)
Fail Definition abel_old_seat_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile 'I_4 erefl
    (enum 'I_(pi_T' (mp_PI abel_profile)).+1) erefl
    (fun s _ => tnth (ts_encode abel_ts s)) 150.

(******************************************************************************)
(*     Mutation 2: the wrong constant for the identity-content run            *)
(******************************************************************************)

(* Control: the reconstructed constant is the ordinal 2. *)
Check (erefl : abel_identity_recon_value = @Ordinal 4 2 isT).

(* The residue of 0 + 1 + 2 + 3 modulo 4 is 2, not 1:
     The term "erefl" has type
      "abel_identity_recon_value = abel_identity_recon_value"
     while it is expected to have type
      "abel_identity_recon_value = Ordinal (n:=4) (m:=1) isT". *)
Fail Check (erefl : abel_identity_recon_value = @Ordinal 4 1 isT).

(* Control: the packaged observed execution expects that constant. *)
Check abel_shuffle_observed.

(* Retargeting the expected value at the ordinal 1 makes the record's recovery
   field ill-typed. *)
Fail Definition abel_bad_shuffle_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profileP abel_shuffle_plug 0
    abel_id_obs (fun _ : unit => @Ordinal 4 1 isT)
    abel_shuffle_terminates abel_shuffle_endpoints (@abel_shuffle_recon).

(******************************************************************************)
(*     Mutation 3: a wrong exact distance                                     *)
(******************************************************************************)

(* Control: the distance at every positive word length is 1. *)
Check abel_word_group_dist.

(* Halving it is not provable from the landed theorem:
     Cannot apply lemma abel_word_group_dist. *)
Lemma abel_distance_value_mutation : True.
Proof.
Fail have Hbad : forall (R : realType) (L : nat),
  var_dist (abel_word_dist R L) (abel_group_uniform R) = (2%:R : R)^-1
  by move=> R L; exact: abel_word_group_dist.
by [].
Qed.

(******************************************************************************)
(*     Mutation 4: the positive-length hypothesis                             *)
(******************************************************************************)

(* Control: at word length zero the distance is 1 + 1/2. *)
Check abel_word_group_dist0.

(* Claiming the distance 1 at word length zero is not provable:
     Cannot apply lemma abel_word_group_dist0. *)
Lemma abel_length_zero_mutation : True.
Proof.
Fail have Hbad : forall R : realType,
  var_dist (@rho_from_words R 2 1 0 abel_sigmas) (abel_group_uniform R) = 1
  by move=> R; exact: abel_word_group_dist0.
by [].
Qed.

(******************************************************************************)
(*     Mutation 5: an incomplete endpoint reader                              *)
(******************************************************************************)

(** abel_pair_reader — the reader that records only the first two endpoints.
    @intent: the images of the starting positions 0 and 1 under a cut, the
    incomplete observation the negative result must not use. *)
Definition abel_pair_reader (sigma : {perm 'I_4}) : 2.-tuple 'I_4 :=
  [tuple sigma (@Ordinal 4 0 isT); sigma (@Ordinal 4 1 isT)].

(** abel_pair_reader_not_injective — the two-endpoint reader does not determine
    the cut.
    @main architecture: ~ injective abel_pair_reader, witnessed by the identity
    and the second generator, which both fix the sheets 0 and 1. *)
Lemma abel_pair_reader_not_injective : ~ injective abel_pair_reader.
Proof.
move=> Hinj.
have Heq : abel_pair_reader 1%g = abel_pair_reader abel_s2.
  by apply: val_inj; rewrite /= !perm1 /abel_s2 !permE.
by move: abel_1_neq_s2; rewrite (Hinj _ _ Heq) eqxx.
Qed.

(* Control: the complete four-endpoint reader determines the cut. *)
Check abel_reader_inj.

(* The transport of the exact distance is carried by the injectivity of the
   complete reader, so it does not go through for the two-endpoint reader:
     The LHS of var_dist_fdistmap_inj does not match any subterm of the goal. *)
Lemma abel_partial_reader_mutation : True.
Proof.
Fail have Hbad : forall (R : realType) (L : nat),
  var_dist (fdistmap abel_pair_reader (abel_word_dist R L))
           (fdistmap abel_pair_reader (abel_group_uniform R)) = 1
  by move=> R L; rewrite (var_dist_fdistmap_inj _ _ abel_reader_inj)
                         abel_word_group_dist.
by [].
Qed.

(******************************************************************************)
(*     Mutation 6: the wrong parity class                                     *)
(******************************************************************************)

(* Control: an odd-length word evaluates to one of the two generators. *)
Check abel_word_eval_odd.

(** abel_odd_identity_mass — at odd word length the identity carries no mass.
    @main bound: abel_word_dist R L 1 = 0 for odd L.+1, so the parity class
    reached at odd length is {s1, s2} and not {1, s1 s2}. *)
Lemma abel_odd_identity_mass (R : realType) (L : nat) : odd L.+1 ->
  abel_word_dist R L 1%g = 0.
Proof.
move=> HL.
case: (abel_word_dist_class R (fun w => abel_word_eval_odd w HL)
         (negbT abel_s1_neq_s2E)) => _ _ H0.
exact: (H0 1%g (negbT abel_1_neq_s1) (negbT abel_1_neq_s2)).
Qed.

(* Claiming the even-length class at odd length is not provable:
     Cannot apply lemma abel_word_eval_even. *)
Lemma abel_parity_class_mutation : True.
Proof.
Fail have Hbad : forall (n : nat) (w : pgg_word abel_M n), odd n ->
  @word_eval abel_M n w
  = if odd (@freq_vec abel_M n w ord0) then (abel_s1 * abel_s2)%g else 1%g
  by move=> n w Hn; exact: abel_word_eval_even.
by [].
Qed.

(******************************************************************************)
(*     Mutation 7: a fuel value that does not finish the run                  *)
(******************************************************************************)

(* Control: fuel 150 finishes every process of the six-process run. *)
Check abel_shuffle_terminates.

(* At fuel 3 the vm_compute proof leaves a goal the closing tactic cannot
   discharge:
     No applicable tactic. *)
Lemma abel_fuel_mutation : True.
Proof.
Fail have Hbad : forall (x : unit) (w0 : pgg_gT abel_M),
  (run_interp 3 (@exec_procs abel_profileP abel_shuffle_plug x w0 0)).1
  = nseq 6 Finish
  by move=> x w0; vm_compute.
by [].
Qed.

Print Assumptions abel_pair_reader_not_injective.
Print Assumptions abel_odd_identity_mass.
