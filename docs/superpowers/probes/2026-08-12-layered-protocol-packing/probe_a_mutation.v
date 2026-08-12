(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe A, mutation check: the revised records still separate the two        *)
(* instances                                                                  *)
(*                                                                            *)
(* Removing mp_security from MonodromyProfile and ep_cards_bridge from        *)
(* ExecutionPlug removes two typed fields. This file checks that what remains *)
(* still rejects a cross-instance assembly: the eight-card orbit              *)
(* reconstruction plug against the five-card monodromy, the five-card         *)
(* execution data against the eight-card orbit profile, and the eight-card    *)
(* orbit execution data against the five-card profile.                        *)
(*                                                                            *)
(* Each rejected assembly is wrapped in Fail, so the file compiles green      *)
(* exactly when all three are rejected. The honest assemblies are declared    *)
(* first as positive controls, so a Fail cannot pass by a mistake shared with *)
(* the honest case.                                                           *)
(*                                                                            *)
(* The message quoted above each Fail is the verbatim compiler diagnostic     *)
(* obtained by removing that one Fail and recompiling: rocq compile in batch  *)
(* mode does not echo the message of a Fail that succeeds, so the three       *)
(* messages were harvested one per compile.                                   *)
(*                                                                            *)
(* Module PS below repeats the two revised records and the two smart          *)
(* constructors of probe_a_profile_split.v. It is a copy rather than an       *)
(* import because the probe directory carries a dash-bearing name and so is   *)
(* not a legal Rocq logical path under the -R flags of rebuild.sh.            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_sample_adapter.
From pgg_smc Require Import pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The revised records                                                    *)
(******************************************************************************)

Module PS.

(** MonodromyProfile — a plugged monodromy group with its starting layout and
    its reconstruction plug.
    Kind: interface.
    The record of pgg_monodromy_profile.v:49-55 without the parameter R and
    without the field mp_security. *)
Record MonodromyProfile := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_secretT  : Type ;
  mp_PI       : PGGInterface mp_M ;
  mp_plug     : ReconPlug mp_M mp_secretT ;
}.

(** ExecutionPlug — the execution layer over a MonodromyProfile.
    Kind: interface.
    The record of pgg_execution_plug.v:57-72 without the parameter R and
    without the field ep_cards_bridge. *)
Record ExecutionPlug (mp : MonodromyProfile) :=
  MkExecutionPlug {
    ep_inputT         : Type ;
    ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
    ep_players        : seq 'I_(pi_T' (mp_PI mp)).+1 ;
    ep_playersE       : ep_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
    ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                          -> ('I_(pgg_N' (mp_M mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1) ;
    ep_input_procs    : ep_inputT
                          -> seq (aproc pgg_dtype
                                    (pgg_data (pgg_N' (mp_M mp)).+1)) ;
    ep_fuel           : nat ;
  }.

(** dealer_secret_plug — the execution plug of a dealer-dealt secret.
    @intent: the plug whose input process list is empty at every run
    argument. *)
Definition dealer_secret_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content (fun _ => [::]) fuel.

(** committed_input_plug — the execution plug of a committed input.
    @intent: the plug whose runs carry one commit process per committing
    party. *)
Definition committed_input_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (input_procs : inputT
                     -> seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content input_procs fuel.

End PS.

(******************************************************************************)
(*     The honest assemblies, as positive controls                            *)
(******************************************************************************)

(** pgl27_profileM — the eight-card orbit profile over the revised record.
    @intent: pgl27_M with secret type bool, starting layout pgl27_PI and
    reconstruction plug pgl27_plug.
    Naming: intentional; the trailing M marks the mutation-probe twin of the
    production pgl27_profile, which this file must not shadow. *)
Definition pgl27_profileM : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_plug.

(** five_card_profileM — the five-card profile over the revised record.
    @intent: FiveCardKim_M with secret type bool, starting layout
    FiveCardKim_PI and reconstruction plug five_card_plug.
    Naming: intentional; the trailing M marks the mutation-probe twin of the
    production five_card_profile, which this file must not shadow. *)
Definition five_card_profileM : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile FiveCardKim_M bool FiveCardKim_PI five_card_plug.

(** pgl27_players_enumEM — the eight-element participant list is the seat
    enumeration.
    @composes: pgl27_exec_plugM *)
Lemma pgl27_players_enumEM :
  pgl27_players = enum 'I_(pi_T' (PS.mp_PI pgl27_profileM)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** five_card_players_enumEM — the five-element participant list is the seat
    enumeration.
    @composes: five_card_exec_plugM *)
Lemma five_card_players_enumEM :
  den_boer_players = enum 'I_(pi_T' (PS.mp_PI five_card_profileM)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl27_exec_plugM — the eight-card orbit execution plug.
    @intent: run argument bool, participant list pgl27_players, content the
    shares of the dealt orbit secret and fuel pgl27_fuel. *)
Definition pgl27_exec_plugM : PS.ExecutionPlug pgl27_profileM :=
  @PS.dealer_secret_plug pgl27_profileM bool erefl pgl27_players
    pgl27_players_enumEM (fun s _ => tnth (ts_encode orbit_scheme s))
    pgl27_fuel.

(** five_card_exec_plugM — the five-card execution plug.
    @intent: run argument the committed pair of bits, participant list
    den_boer_players, content the den Boer layout of the decoded committed
    cards, the two commit processes of parties 7 and 8 and fuel 100. *)
Definition five_card_exec_plugM : PS.ExecutionPlug five_card_profileM :=
  @PS.committed_input_plug five_card_profileM (bool * bool)%type erefl
    den_boer_players five_card_players_enumEM
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(******************************************************************************)
(*     Mutation 1: the orbit reconstruction plug at the five-card monodromy   *)
(******************************************************************************)

(* Observed message:
   The command has indeed failed with message:
   The term "pgl27_plug" has type "ReconPlug pgl27_M bool"
   while it is expected to have type "ReconPlug FiveCardKim_M bool". *)
Fail Definition mutant_profile_orbit_plug : PS.MonodromyProfile :=
  @PS.MkMonodromyProfile FiveCardKim_M bool FiveCardKim_PI pgl27_plug.

(******************************************************************************)
(*     Mutation 2: the five-card execution data at the orbit profile          *)
(******************************************************************************)

(* Observed message:
   The command has indeed failed with message:
   The term "den_boer_players" has type "seq 'I_(pi_T' FiveCardKim_PI).+1"
   while it is expected to have type
    "seq 'I_(pi_T' (PS.mp_PI pgl27_profileM)).+1". *)
Fail Definition mutant_five_card_plug_at_orbit
    : PS.ExecutionPlug pgl27_profileM :=
  @PS.committed_input_plug pgl27_profileM (bool * bool)%type erefl
    den_boer_players five_card_players_enumEM
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(******************************************************************************)
(*     Mutation 3: the orbit execution data at the five-card profile          *)
(******************************************************************************)

(* Observed message:
   The command has indeed failed with message:
   The term "pgl27_players" has type "seq 'I_(pi_T' pgl27_PI).+1"
   while it is expected to have type
    "seq 'I_(pi_T' (PS.mp_PI five_card_profileM)).+1". *)
Fail Definition mutant_orbit_plug_at_five_card
    : PS.ExecutionPlug five_card_profileM :=
  @PS.dealer_secret_plug five_card_profileM bool erefl pgl27_players
    pgl27_players_enumEM (fun s _ => tnth (ts_encode orbit_scheme s))
    pgl27_fuel.
