(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_abel_sig: the discharged signatures of the abelian probe results     *)
(*                                                                            *)
(* Phase 0 signature inventory for the unified-instance-analysis request. The *)
(* negative results of probe_abel_negative.v are proved inside a section with *)
(* Variable R : realType, so their discharged arity and the implicitness of R *)
(* decide how probe_abel_mutation.v must spell them. This file only prints    *)
(* those signatures; it proves nothing.                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile.
From uia_probe Require Import probe_abel_profile probe_abel_plugs.
From uia_probe Require Import probe_abel_negative.

About abel_group_uniform.
About abel_word_dist.
About abel_word_group_dist.
About abel_word_group_dist0.
About abel_executed_distance.
About abel_word_dist_class.
About abel_ideal_adapter.
About abel_actual_adapter.
About abel_adapter_distance.
About var_dist_fdistmap_inj.
About abel_reader.
About abel_reader_inj.
About abel_shuffle_recon.
About abel_identity_recon_value.
