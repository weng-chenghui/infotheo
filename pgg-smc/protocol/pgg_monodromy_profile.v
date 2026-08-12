(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* MonodromyProfile: one piSMC program, plug a group, read its characters     *)
(*                                                                            *)
(* A MonodromyProfile bundles, for a plugged monodromy group M, the data      *)
(* that gives the shared exchange_* piSMC program its observable characters:   *)
(*   mp_M        the group representation and its permutation action          *)
(*   mp_secretT  the reconstructed secret carrier                             *)
(*   mp_PI       the starting layout (drives what the SSend carries)           *)
(*   mp_plug     the reconstruction plug: scheme + content + monodromy +       *)
(*               full-group reconstruction invariance (see covering_scheme).   *)
(*                                                                            *)
(* The record is program data alone: it carries no probability model and no   *)
(* security theorem, and mentions no realType. Shuffle bounds are separate    *)
(* values of ShuffleMarginalBound and ShuffleCertificateBundle                *)
(* (algebraic_rigidity.v).                                                    *)
(*                                                                            *)
(* The generic section protocol_of_profile builds the program from the profile*)
(* (run_party/run_verifier are exchange_* at mp_PI, run_recover is the plug's *)
(* ts_recon), exposes the threshold character profile_k, and proves the two   *)
(* guarantees that CONSUME the fields:                                        *)
(*   profile_private      fewer than profile_k shares are indistinguishable   *)
(*   profile_recon_encode the dealt secret is recovered                       *)
(*                                                                            *)
(* The in-scope profiles filling this record are pgl27_profile,               *)
(* five_card_profile, s5_profile and s5x5_profile.                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** MonodromyProfile — one plug bundling a group's program data.
    Kind: interface.
    A constructor supplies the group action, the starting layout and the
    reconstruction plug; the generic protocol_of_profile section turns such a
    value into the shared piSMC program and its threshold character. *)
Record MonodromyProfile := MkMonodromyProfile {
  (* mp_M selects the finite group representation and its permutation action
     on the sheets. *)
  mp_M        : MonodromyReprWithGeneratorType ;
  (* mp_secretT is the dependent secret carrier used by the reconstruction
     plug. Being a field rather than a parameter, it permits profiles whose
     secrets have different types. *)
  mp_secretT  : Type ;
  (* mp_PI supplies the participant count and the starting positions of the
     shared exchange program. *)
  mp_PI       : PGGInterface mp_M ;
  (* mp_plug supplies the reconstruction scheme together with its
     group-invariance data. *)
  mp_plug     : ReconPlug mp_M mp_secretT ;
}.

(******************************************************************************)
(*     The shared program, plugged with a profile                             *)
(******************************************************************************)

Section protocol_of_profile.

Variable mp : MonodromyProfile.

Let M    := mp_M mp.
Let PI   := mp_PI mp.
Let N    := (pgg_N' M).+1.
Let plug := mp_plug mp.
Let players := enum 'I_(pi_T' PI).+1.

(** run_party — a participant of the shared program. Kind: instance. *)
Definition run_party (i : 'I_(pi_T' PI).+1) := exchange_player PI i.

(** run_verifier — the verifier of the shared program. Kind: instance. *)
Definition run_verifier := exchange_verifier PI players.

(** run_recover — reconstruction via the plug's scheme. Kind: instance.
    Why: the program's recover phase calls ts_recon of the plug's scheme; the
    recovered value lives in the plug's secret type mp_secretT. *)
Definition run_recover (collected : (ts_T' (rp_scheme plug)).+1.-tuple 'I_N)
    : mp_secretT mp :=
  ts_recon (rp_scheme plug) collected.

(** profile_k — the privacy-threshold character of the profile.
    @intent: the threshold k read off the plug's scheme. *)
Definition profile_k : nat := ts_k (rp_scheme plug).

(** profile_private — fewer than profile_k shares cannot distinguish two
    secrets.
    @intent: the privacy guarantee, consuming the plug's scheme's ts_private
    field. *)
Definition profile_private := ts_private (rp_scheme plug).

(** profile_recon_encode — reconstructing the canonical encoding returns the
    dealt secret.
    @main correctness: the correctness guarantee, consuming the plug's
    scheme's ts_correct field on the canonical encoding. *)
Lemma profile_recon_encode (s : mp_secretT mp) :
  run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.

End protocol_of_profile.
