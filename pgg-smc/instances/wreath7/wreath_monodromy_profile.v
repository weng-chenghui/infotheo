(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* MonodromyProfile: one piSMC program, plug a group, read its characters     *)
(*                                                                            *)
(* A MonodromyProfile R bundles, for a plugged monodromy group M, the data    *)
(* that gives the shared exchange_* piSMC program its observable characters:   *)
(*   mp_PI       the starting layout (drives what the SSend carries)           *)
(*   mp_security the anonymity character: eps = sw_bound_eps                    *)
(*   mp_scheme   the threshold scheme: privacy threshold k = ts_k              *)
(*                                                                            *)
(* The generic section run_profile builds the program from the profile        *)
(* (run_dealer/run_party/run_verifier are exchange_* at mp_PI, so the          *)
(* SSend/SRecv carry the plugged group's shuffle), exposes the characters      *)
(* (run_eps, run_k), and proves the three guarantees that CONSUME the fields:  *)
(*   run_anonymous  var_dist(sent distribution, uniform) <= run_eps           *)
(*   run_private    fewer than run_k shares are indistinguishable              *)
(*   run_recovers   the dealt secret is recovered                              *)
(*                                                                            *)
(* Plugging groups into the SAME run_* shows different characters:             *)
(*   wreath_profile   non-abelian Z_7 wr S_2 (security vanishes: spectral       *)
(*                    SecurityAsymptotic, gap 3/20), k = 7                      *)
(*   abelian_profile  Z_2 x Z_2 commuting generators (security floors), k = 2  *)
(*   s5_profile       S_5 adjacent transpositions (security vanishes), k = 5   *)
(* The discriminator is the plugged group's commutativity (wreath_nonabelian   *)
(* vs abel_gens_commute), which is what the security character turns on.       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_wreath wreath_recovery wreath_security
                            rigidity_wreath_instance rigidity_abelian_instance
                            wreath_mixing.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5
                            s5_mixing rigidity_s5_instance.
From pgg_reconstruct Require Import pgg_sharing_framework algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** MonodromyProfile — one plug bundling a group's protocol characters.
    Kind: interface.
    Why: a value of this type is "a plugged group"; the generic run_profile
    section turns it into the shared piSMC program plus its security/privacy
    characters. *)
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_PI       : PGGInterface mp_M ;
  mp_security : SecurityWitness R mp_M ;
  mp_scheme   : ThresholdScheme 'I_(pgg_N' mp_M).+1 'I_(pgg_N' mp_M).+1 ;
}.

(******************************************************************************)
(*     The shared program, plugged with a profile                             *)
(******************************************************************************)

Section run_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.

Let M   := mp_M mp.
Let PI  := mp_PI mp.
Let N   := (pgg_N' M).+1.
Let sch := mp_scheme mp.
Let players := enum 'I_(pi_T' PI).+1.

(** run_dealer — the dealer of the shared program, plugged at mp_PI.
    Kind: instance.
    Why: exchange_dealer at the profile's interface; its SSend payload
    dealt_hand PI W j = [rho w (start j) | w <- W] carries the plugged group's
    shuffle. *)
Definition run_dealer (W : seq (pgg_gT M)) (P_idx : nat) :=
  exchange_dealer PI players W P_idx.

(** run_party — a participant of the shared program. Kind: instance. *)
Definition run_party (i : 'I_(pi_T' PI).+1) := exchange_player PI i.

(** run_verifier — the verifier of the shared program. Kind: instance. *)
Definition run_verifier := exchange_verifier PI players.

(** run_recover — reconstruction via the plugged scheme. Kind: instance.
    Why: the program's recover phase calls ts_recon of the profile's scheme. *)
Definition run_recover (collected : (ts_T' sch).+1.-tuple 'I_N) : 'I_N :=
  ts_recon sch collected.

(** run_eps — the anonymity character of the plug. Kind: definition.
    Why: the security epsilon read off mp_security; group-sensitive. *)
Definition run_eps : R := sw_bound_eps (mp_security mp).

(** run_k — the privacy-threshold character of the plug. Kind: definition.
    Why: the threshold k read off mp_scheme. *)
Definition run_k : nat := ts_k sch.

(** run_anonymous — the sent distribution is run_eps-close to uniform.
    Kind: main.
    Why: the security guarantee, consuming mp_security (its sw_bound field). *)
Definition run_anonymous := sw_bound (mp_security mp).

(** run_private — fewer than run_k shares cannot distinguish two secrets.
    Kind: main.
    Why: the privacy guarantee, consuming mp_scheme (its ts_private field). *)
Definition run_private := ts_private sch.

(** run_recovers — the dealt secret is recovered.
    Kind: main.
    Why: the correctness guarantee, consuming mp_scheme (ts_correct on the
    canonical encoding). *)
Lemma run_recovers (s : 'I_N) : run_recover (ts_encode sch s) = s.
Proof. exact: ts_correct (ts_encode_valid sch s). Qed.

End run_profile.

(******************************************************************************)
(*     Two plugs into the SAME run_* program                                  *)
(******************************************************************************)

Section instances.

Variable R : realType.

(** wreath_sym_PI — the 14-card starting interface for the symmetric wreath.
    Kind: instance.
    Why: the M_wreath_sym analogue of wreath_PI (identity start tuple), so the
    shared exchange_* program plugs at the symmetric-generator monodromy that
    carries the spectral asymptotic. *)
Definition wreath_sym_PI : PGGInterface M_wreath_sym :=
  @MkPGGI M_wreath_sym 13 (ord_tuple 14) wreath_starts_uniq.

(** wreath_profile — plug the non-abelian wreath Z_7 wr S_2 (N = 14).
    Kind: instance.
    Why: the secure plug; |G| = 98 non-abelian, k = 7. It plugs the symmetric
    (inverse-closed) presentation M_wreath_sym, the same group as M_wreath
    (wreath_sym_same_group), so its security character is the proven spectral
    SecurityAsymptotic (sa_eps_inf = 0, gap 3/20): security genuinely vanishes,
    matching the S_5 plug. The word length 285 mirrors the S_5 40-bit choice. *)
Definition wreath_profile : MonodromyProfile R :=
  @MkMonodromyProfile R M_wreath_sym wreath_sym_PI
    (wreath_security_witness_asymptotic R 285) wreath2_scheme.

(** abel_profile — plug the abelian Z_2 x Z_2 (N = 4), paired with sum_mod.
    Kind: instance.
    Why: the insecure plug; commuting generators, k = 2. The scheme is a plain
    sum_mod on the 4 sheets (the differentiator is the group, not the scheme). *)
Definition abel_profile : MonodromyProfile R :=
  @MkMonodromyProfile R (Gen_PGGTypes abel_sigmas) (Gen_PGG_2 abel_sigmas)
    (abel_security_witness_direct_1 R) (@sum_mod_scheme 2 1).

(** s5_starts_uniq — the five starting card positions are distinct.
    Kind: helper. Why: the uniqueness witness for s5_PI, mirroring
    wreath_starts_uniq. *)
Lemma s5_starts_uniq : uniq (ord_tuple 5).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** s5_PI — the concrete five-sheet starting interface for the S_5 plug.
    Kind: instance.
    Why: the identity start tuple (ord_tuple 5), the S_5 analogue of wreath_PI,
    so the shared exchange_* program can be plugged at the S_5 monodromy. *)
Definition s5_PI : PGGInterface (Gen_PGGTypes (path_gen_tuple 3)) :=
  @MkPGGI (Gen_PGGTypes (path_gen_tuple 3)) 4 (ord_tuple 5) s5_starts_uniq.

(** s5_profile — plug the S_5 adjacent-transposition monodromy (N = 5).
    Kind: instance.
    Why: the third plug; |S_5| = 120, and unlike the wreath its mixing is
    formalised: the Schreier-walk SecurityWitness carries a SecurityAsymptotic
    with sa_eps_inf = 0, so its anonymity bound decays geometrically (base
    181/200) to 0. The threshold scheme is sum-mod on the 5 sheets, k = 5. *)
Definition s5_profile : MonodromyProfile R :=
  @MkMonodromyProfile R (Gen_PGGTypes (path_gen_tuple 3)) s5_PI
    (s5_security_witness_schreier R 285) (@sum_mod_scheme 3 4).

(******************************************************************************)
(*     The contrast: same program, different characters                       *)
(******************************************************************************)

(** run_k_wreath, run_k_abel — the privacy thresholds differ by plug.
    Kind: example. Why: 7 vs 2, read off the same run_k. *)
Lemma run_k_wreath : run_k wreath_profile = 7.
Proof. by []. Qed.

Lemma run_k_abel : run_k abel_profile = 2.
Proof. by []. Qed.

Lemma run_k_s5 : run_k s5_profile = 5.
Proof. by []. Qed.

(** wreath_plug_nonabelian — the wreath plug's group is non-abelian.
    Kind: main.
    Why: the structural root of its security character (mixing can drive eps to
    0). Consumes wreath_nonabelian. *)
Lemma wreath_plug_nonabelian : ~~ abelian (pgg_G (mp_M wreath_profile)).
Proof.
have -> : mp_M wreath_profile = M_wreath_sym by [].
rewrite wreath_sym_same_group; exact: wreath_nonabelian.
Qed.

(** wreath_plug_asymptotic — the wreath plug now carries a SecurityAsymptotic,
    the S_5 standard.
    Kind: main.
    Why: the headline of the rewire. The wreath plug's security character is the
    spectral asymptotic Some wreath_asymptotic, whose additive floor is 0 by
    wreath_asymptotic_eps_inf_zero (proved in wreath_mixing.v): the walk
    genuinely mixes, parity with the S_5 plug, unlike the abelian floor. The
    floor-0 equation is stated there, since this file's pismc notations shadow
    ring_scope's 0. *)
Lemma wreath_plug_asymptotic :
  sw_asymptotic (mp_security wreath_profile) = Some (wreath_asymptotic R).
Proof. by []. Qed.

(** abel_gens_commute — the abelian plug's generators commute.
    Kind: main.
    Why: the structural root of its INSECURE character (commuting shuffles do
    not mix, eps floors). The opposite of wreath_plug_nonabelian, same run_*. *)
Lemma abel_gens_commute : commute abel_s1 abel_s2.
Proof.
apply/permP => x; rewrite !permM /abel_s1 /abel_s2.
by case: x => -[|[|[|[|x]]]] Hx; rewrite ?permE.
Qed.

(* The quantitative security characters of these plugs (the abelian var_dist
   floor and the S_5 asymptotic vanishing) are real-number facts about the
   plugged security witnesses; they live in wreath_profile_security.v, which
   does not import the pismc/session-type notations that this file needs for
   the program and that shadow ring_scope's numeral notations. *)

End instances.

Arguments wreath_profile R.
Arguments abel_profile R.
