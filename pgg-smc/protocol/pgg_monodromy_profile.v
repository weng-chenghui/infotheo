(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* MonodromyProfile: one piSMC program, plug a group, read its characters     *)
(*                                                                            *)
(* A MonodromyProfile R bundles, for a plugged monodromy group M, the data    *)
(* that gives the shared exchange_* piSMC program its observable characters:   *)
(*   mp_PI       the starting layout (drives what the SSend carries)           *)
(*   mp_security the anonymity character: eps = sw_bound_eps                    *)
(*   mp_plug     the reconstruction plug: scheme + content + monodromy +       *)
(*               full-group reconstruction invariance (see covering_scheme).   *)
(*                                                                            *)
(* The generic section run_profile builds the program from the profile        *)
(* (run_dealer/run_party/run_verifier are exchange_* at mp_PI, with the dealer *)
(* baking the plug's content readout rp_content into the wire), exposes the    *)
(* characters (run_eps, run_k), and proves the three guarantees that CONSUME   *)
(* the fields:                                                                 *)
(*   run_anonymous  var_dist(sent distribution, uniform) <= run_eps           *)
(*   run_private    fewer than run_k shares are indistinguishable              *)
(*   run_recovers   the dealt secret is recovered                             *)
(*                                                                            *)
(* This record was relocated here from the wreath7 instance so that the core   *)
(* protocol owns it; each instance supplies its own plug (s5_profile,          *)
(* abel_profile, s5x5_profile, den_boer_profile).                             *)
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

(** MonodromyProfile — one plug bundling a group's protocol characters.
    Kind: interface.
    Why: a value of this type is "a plugged group"; the generic run_profile
    section turns it into the shared piSMC program plus its security/privacy
    characters. The reconstruction half is the ReconPlug, so correctness and
    the dealer's content readout come from one field. *)
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_secretT  : Type ;
  mp_PI       : PGGInterface mp_M ;
  mp_security : SecurityWitness R mp_M ;
  mp_plug     : ReconPlug mp_M mp_secretT ;
}.

(******************************************************************************)
(*     The shared program, plugged with a profile                             *)
(******************************************************************************)

Section run_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.

Let M    := mp_M mp.
Let PI   := mp_PI mp.
Let N    := (pgg_N' M).+1.
Let plug := mp_plug mp.
Let players := enum 'I_(pi_T' PI).+1.

(** run_dealer — the dealer of the shared program, plugged at mp_PI.
    Kind: instance.
    Why: exchange_dealer at the profile's interface; it bakes the plug's
    content readout rp_content into each dealt column so the revealed values
    are the plug's readout of the plugged group's shuffle. *)
Definition run_dealer (W : seq (pgg_gT M)) (P_idx : nat) :=
  exchange_dealer PI (rp_content plug) players W P_idx.

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

(** run_eps — the anonymity character of the plug. Kind: definition.
    Why: the security epsilon read off mp_security; group-sensitive. *)
Definition run_eps : R := sw_bound_eps (mp_security mp).

(** run_k — the privacy-threshold character of the plug. Kind: definition.
    Why: the threshold k read off the plug's scheme. *)
Definition run_k : nat := ts_k (rp_scheme plug).

(** run_anonymous — the sent distribution is run_eps-close to uniform.
    Kind: main.
    Why: the security guarantee, consuming mp_security (its sw_bound field). *)
Definition run_anonymous := sw_bound (mp_security mp).

(** run_private — fewer than run_k shares cannot distinguish two secrets.
    Kind: main.
    Why: the privacy guarantee, consuming the plug's scheme (ts_private). *)
Definition run_private := ts_private (rp_scheme plug).

(** run_recovers — the dealt secret is recovered.
    Kind: main.
    Why: the correctness guarantee, consuming the plug's scheme (ts_correct on
    the canonical encoding). *)
Lemma run_recovers (s : mp_secretT mp) :
  run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.

End run_profile.
