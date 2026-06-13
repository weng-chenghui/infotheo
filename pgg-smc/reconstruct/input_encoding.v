(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Input encoding: inputs determine the starting layout                       *)
(*                                                                            *)
(* InputEncoding is the deterministic half of a randomized encoding of a       *)
(* function f over an existing ReconPlug: assemble maps inputs to a valid      *)
(* share layout (ie_assemble_valid), and equal-output inputs lie in one cut    *)
(* orbit (ie_orbit). The cut supplies the randomness.                          *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** InputEncoding — inputs determine a valid share layout for the plug, with
    equal-output inputs in one cut orbit.
    @intent: the deterministic half of a randomized encoding of ie_output; the
    existing cut supplies the randomness. *)
Record InputEncoding (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type) := MkInputEncoding {
  ie_assemble : inputT -> (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1 ;
  ie_output      : inputT -> secretT ;
  ie_assemble_valid : forall x,
      ts_valid (rp_scheme plug) (ie_output x) (ie_assemble x) ;
  ie_orbit : forall x x', ie_output x = ie_output x' ->
      exists g : pgg_gT M, g \in pgg_G M /\
        ie_assemble x' =
          [tuple tnth (ie_assemble x) (rp_monodromy plug g i)
                | i < (ts_T' (rp_scheme plug)).+1] ;
}.

Arguments InputEncoding M secretT plug inputT.
Arguments MkInputEncoding {M secretT plug inputT}.

(** ie_output_correct — the cut-permuted assembled layout reconstructs ie_output x,
    for every cut element of the full group.
    @composes: den_boer_run_output. *)
Lemma ie_output_correct (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type)
    (ie : InputEncoding plug inputT) (x : inputT) (g0 : pgg_gT M) :
  g0 \in pgg_G M ->
  ts_recon (rp_scheme plug)
    [tuple tnth (ie_assemble ie x) (rp_monodromy plug g0 i)
          | i < (ts_T' (rp_scheme plug)).+1] = ie_output ie x.
Proof.
move=> Hg0. apply: (rp_recon_invariant Hg0). exact: ie_assemble_valid.
Qed.

(** recon_from_layout — the secret recovered from a layout viewed through the
    cut P, in the reindex (position-permutation) form matching the scheme's
    reconstruction invariance.
    @intent: the operational recovery for input-dependent layouts, reading the
    cut-permuted layout under the plug scheme. *)
Definition recon_from_layout (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT)
    (layout : (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1)
    (P : pgg_gT M) : secretT :=
  ts_recon (rp_scheme plug)
    [tuple tnth layout (rp_monodromy plug P i)
          | i < (ts_T' (rp_scheme plug)).+1].

(** recon_from_layout_output — recovering an encoded input's layout returns
    ie_output x, for every cut; generic over the plug and the encoded function.
    @composes: ie_output_correct. *)
Lemma recon_from_layout_output (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type)
    (ie : InputEncoding plug inputT) (x : inputT) (P : pgg_gT M) :
  P \in pgg_G M ->
  recon_from_layout (ie_assemble ie x) P = ie_output ie x.
Proof. exact: ie_output_correct. Qed.
