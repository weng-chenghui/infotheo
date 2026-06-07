(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abel_profile: the abelian (insecure) plug of the shared program            *)
(*                                                                            *)
(* Relocated from the wreath7 contrast file. The plug uses a sum-mod scheme on *)
(* the 4 abelian sheets with the identity content readout, the abelian         *)
(* monodromy pgg_rho, and a reconstruction invariance proved by the same       *)
(* group-agnostic argument as s5_sum_mod_perm_compatible. The differentiator   *)
(* from the secure plugs is the GROUP (commuting generators), not the scheme.  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_abelian.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** abel_ts — sum-mod threshold scheme on the 4 abelian sheets, one share per
    sheet (k = 4). Kind: instance. What: @sum_mod_scheme 2 3 : ThresholdScheme
    'I_4 'I_4 (ts_T' = 3, so the share-index space 'I_4 matches the sheet space
    that the abelian monodromy pgg_rho permutes). Why: the plain scheme for the
    abelian plug; the differentiator from the secure plugs is the group, not the
    scheme. Used-by: abel_plug. *)
Definition abel_ts : ThresholdScheme 'I_4 'I_4 := @sum_mod_scheme 2 3.

(** abel_sum_mod_perm_compatible — sum-mod reconstruction is invariant under the
    abelian monodromy. Kind: helper. What: ts_recon_perm_invariant over
    pgg_G (Gen_PGGTypes abel_sigmas) for abel_ts and pgg_rho. Why: the
    rp_recon_invariant field of abel_plug; the proof is the group-agnostic
    single-reindex argument shared with s5_sum_mod_perm_compatible. Used-by:
    abel_plug. *)
Lemma abel_sum_mod_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G (@Gen_PGGTypes 1 2 abel_sigmas)) _ _ abel_ts
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)).
Proof.
move=> g s shares Hg Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry.
rewrite (reindex_inj (@perm_inj _ (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas) g))).
by apply: eq_bigr.
Qed.

(** abel_plug — the abelian reconstruction plug. Kind: instance. What: abel_ts +
    id content + abelian monodromy + abel_sum_mod_perm_compatible. Why: routes
    the abelian (insecure) example through the general MonodromyProfile program.
    Used-by: abel_profile. *)
Definition abel_plug : ReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) :=
  @MkReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) abel_ts id
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)) abel_sum_mod_perm_compatible.

(** abel_profile — plug the abelian Z_2 x Z_2 (N = 4), paired with sum-mod.
    Kind: instance. What: the MonodromyProfile bundling Gen_PGG_2 abel_sigmas,
    the direct security witness, and abel_plug. Why: the insecure plug;
    commuting generators, k = 2, the eps-floor contrast to the secure plugs.
    Used-by: contrast demos. *)
Definition abel_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R (@Gen_PGGTypes 1 2 abel_sigmas) (Gen_PGG_2 abel_sigmas)
    (abel_security_witness_direct_1 R) abel_plug.

(** run_k_abel — the abelian plug's privacy threshold is 4 (one share per
    sheet). Kind: example. What: run_k (abel_profile R) = 4. Why: contrast
    character (vs the S_5 k = 5), read off the shared run_k. *)
Lemma run_k_abel (R : realType) : run_k (abel_profile R) = 4.
Proof. by []. Qed.

(** abel_gens_commute — the abelian plug's generators commute.
    Kind: main. What: commute abel_s1 abel_s2. Why: the structural root of the
    insecure character (commuting shuffles do not mix, eps floors), the opposite
    of the non-abelian secure plugs. Used-by: abelian security narrative. *)
Lemma abel_gens_commute : commute abel_s1 abel_s2.
Proof.
apply/permP => x; rewrite !permM /abel_s1 /abel_s2.
by case: x => -[|[|[|[|x]]]] Hx; rewrite ?permE.
Qed.
