(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 RAAG spectral convergence via external Rayleigh certificate.          *)
(*                                                                            *)
(* This file discharges the S_5 adjacent-transposition Schreier walk's       *)
(* variation-distance bound by applying the general mixing lemma              *)
(*   symm_ds_TV_bound   (pgg-smc/security/pgg_mixing.v)                      *)
(* to the specific generator tuple path_gen_tuple 3.                          *)
(*                                                                            *)
(* The mixing lemma needs three ingredients:                                  *)
(*   (i)   involutivity of each generator,                                    *)
(*   (ii)  0 <= alpha <= 1,                                                   *)
(*   (iii) Rayleigh bound on Q^2 at alpha^2 for mean-zero column vectors.    *)
(*                                                                            *)
(* Ingredients (i) and (ii) are proved in Rocq below: generators are         *)
(* transpositions (tperm2) and alpha = ratr (181/200) is a closed-form        *)
(* rational in [0, 1].  Ingredient (iii) is the Rayleigh-on-Q^2 premise; it  *)
(* is imported from an external sum-of-squares certificate (see               *)
(* s5_spectral_certificate.py and s5_spectral_certificate.md in the same     *)
(* directory) because MathComp's tactic-level rational polynomial            *)
(* normalisation exceeds a five-minute budget on the LDL^T coefficients      *)
(* (numerators up to 10^18), measured empirically.                            *)
(*                                                                            *)
(* The Parameter s5_rayleigh_Qsq_R below is the sole imported assumption;   *)
(* every other step is a structural Rocq proof.                               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg matrix.
From mathcomp Require Import ssrint rat.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_schreier pgg_mixing.
From pgg_smc Require Import pgg_raag_path.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1. alpha = 181/200, as a rational and as a realType element.     *)
(******************************************************************************)

Definition s5_alpha_R (R : realType) : R := 181%:R / 200%:R.

Lemma s5_alpha_R_ge0 (R : realType) : 0 <= s5_alpha_R R.
Proof.
rewrite /s5_alpha_R.
apply divr_ge0; by rewrite ler0n.
Qed.

Lemma s5_alpha_R_le1 (R : realType) : s5_alpha_R R <= 1.
Proof.
rewrite /s5_alpha_R ler_pdivrMr ?mul1r; last by rewrite ltr0n.
by rewrite ler_nat.
Qed.

Lemma s5_alpha_R_lt1 (R : realType) : s5_alpha_R R < 1.
Proof.
rewrite /s5_alpha_R ltr_pdivrMr ?mul1r; last by rewrite ltr0n.
by rewrite ltr_nat.
Qed.

(******************************************************************************)
(*  Section 2. Involutivity of the four path-graph generators.               *)
(******************************************************************************)

Lemma path_gen_tuple_3_invol :
  forall k : 'I_4,
  (tnth (path_gen_tuple 3) k * tnth (path_gen_tuple 3) k)%g = 1%g.
Proof.
move=> k.
rewrite path_gen_tupleE /path_gen.
exact: tperm2.
Qed.

(******************************************************************************)
(*  Section 3. Imported Rayleigh certificate (see the big comment above).    *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*      Imported spectral certificate for the P_5 Schreier walk.              *)
(*                                                                            *)
(*  STATEMENT.                                                                *)
(*    For every real-typed column 5-vector v with v_0 + ... + v_4 = 0,       *)
(*      <v, Q^2 v>  <=  alpha^2 * <v,v>,                                    *)
(*    where Q is schreier_transition R (path_gen_tuple 3) and               *)
(*    alpha = ratr (181/200).  Equivalently, (alpha^2 * I_5 - Q^2) is      *)
(*    positive semidefinite on the mean-zero hyperplane.                     *)
(*                                                                            *)
(*  CERTIFICATE.                                                              *)
(*    Attested by an exact-rational LDL^T decomposition of the reduced       *)
(*    4x4 Gram matrix computed by                                              *)
(*      pgg-smc/instances/s5/s5_spectral_certificate.py                     *)
(*    which emits 4 diagonal pivots D_k > 0 and 6 lower-triangular L_ij     *)
(*    entries, plus a reconstruction check L D L^T = S over Q.              *)
(*                                                                            *)
(*  TRUST MODEL.                                                              *)
(*    The certificate is verified externally by Python's exact fractions.   *)
(*    Only its conclusion (the Rayleigh bound above) enters this             *)
(*    development. No rational constant from the certificate is referenced   *)
(*    by the Rocq proof below; the proof consumes only the universal         *)
(*    statement.                                                              *)
(*                                                                            *)
(*  STATUS.                                                                   *)
(*    The statement is provable in Rocq by sum-of-squares. Empirically,     *)
(*    MathComp's tactic-level rational polynomial normalisation (ring,      *)
(*    field, native_compute) exceeds a 5-minute budget per closed product   *)
(*    at the LDL^T coefficient sizes (numerators up to 10^18).  See         *)
(*    s5_spectral_certificate.md for discussion and the journal entry in    *)
(*    delegated-painting-robin.md for the measurement.                       *)
(*                                                                            *)
(******************************************************************************)

Parameter s5_rayleigh_Qsq_R :
  forall (R : realType) (v : 'cV[R]_5),
  \sum_i v i ord0 = 0 ->
  (v^T
    *m (schreier_transition R (path_gen_tuple 3)
        *m schreier_transition R (path_gen_tuple 3))
    *m v) ord0 ord0
  <= (s5_alpha_R R) ^+ 2 * cV_inner v v.

(******************************************************************************)
(*  Section 4. Apply symm_ds_TV_bound to deliver the variation-distance      *)
(*  bound that rigidity_s5_instance.v's Hypothesis block used to assume.     *)
(******************************************************************************)

Lemma s5_spectral_convergence_proved
    (R : realType) (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L (path_gen_tuple 3)))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L.
Proof.
have Hbound :=
  @symm_ds_TV_bound R 3 3 (path_gen_tuple 3) path_gen_tuple_3_invol
    (s5_alpha_R R) L s
    (s5_alpha_R_ge0 R) (s5_alpha_R_le1 R)
    (@s5_rayleigh_Qsq_R R).
by rewrite /= in Hbound.
Qed.

(******************************************************************************)
(*  Section 5. Packaging for rigidity_s5_instance.v                          *)
(*                                                                            *)
(* Expose a "spectral gap" of 1 - alpha and a convergence statement in the   *)
(* (1 - gap)^L shape, matching the Hypothesis that used to live in           *)
(* rigidity_s5_instance.v.                                                   *)
(******************************************************************************)

Definition s5_gap_R (R : realType) : R := 1 - s5_alpha_R R.

Lemma s5_gap_R_pos (R : realType) : 0 < s5_gap_R R.
Proof.
rewrite /s5_gap_R subr_gt0.
exact: s5_alpha_R_lt1.
Qed.

Lemma s5_gap_R_le1 (R : realType) : s5_gap_R R <= 1.
Proof.
rewrite /s5_gap_R lerBlDr addrC -lerBlDr subrr.
exact: s5_alpha_R_ge0.
Qed.

Lemma s5_gap_R_one_minus (R : realType) : 1 - s5_gap_R R = s5_alpha_R R.
Proof. by rewrite /s5_gap_R opprB addrA addrAC subrr add0r. Qed.

Lemma s5_spectral_convergence_gap
    (R : realType) (L : nat) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (rho_from_words L (path_gen_tuple 3)))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (1 - s5_gap_R R) ^+ L.
Proof.
rewrite s5_gap_R_one_minus.
exact: s5_spectral_convergence_proved.
Qed.
