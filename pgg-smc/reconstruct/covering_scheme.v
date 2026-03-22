(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* AG Codes on Covering Curves — Central Records                              *)
(*                                                                            *)
(* This file defines the central data structures connecting the monodromy     *)
(* group G to the covering curve's genus (via Riemann-Hurwitz) and to the    *)
(* threshold of the secret sharing scheme (via AG codes).                     *)
(*                                                                            *)
(* Galois theory connection:                                                  *)
(*   A covering C → X of curves corresponds to a function field extension    *)
(*   K(C)/K(X). The monodromy group G is the Galois group of the Galois     *)
(*   closure of this extension. The fiber over a point x ∈ X is the set of  *)
(*   roots of the minimal polynomial of a primitive element of K(C) over    *)
(*   K(X) specialized at x. The Riemann-Hurwitz formula links |G| to the   *)
(*   genus of K(C), constraining the AG code parameters.                     *)
(*                                                                            *)
(*   Sources:                                                                 *)
(*     Szamuely, "Galois Groups and Fundamental Groups" (2009), Ch. 4       *)
(*     Grothendieck, SGA1 Exposé V (étale covers ↔ π₁-sets)                *)
(*                                                                            *)
(* Design rationale — why axiomatize the AG code:                             *)
(*   CoveringScheme axiomatizes cs_perm_compatible and cs_gap because the    *)
(*   security-threshold tradeoff theorem only needs: (1) Riemann-Hurwitz     *)
(*   (proved here from cd_hurwitz) to link |G| to genus, and (2) the gap     *)
(*   bound ts_T <= ts_k + 2*genus to link genus to threshold. Both facts     *)
(*   hold for any AG code on any curve (Goppa bound), so concretizing the    *)
(*   curve (Hermitian, elliptic, Garcia-Stichtenoth tower) would only show   *)
(*   that a CoveringScheme instance exists — not change any downstream proof. *)
(*                                                                            *)
(*   CoveringData M == covering geometry parameterized by MonodromyReprType  *)
(*     cd_base_genus == genus of base curve B                                *)
(*     cd_n_branch   == number of branch points                              *)
(*     cd_ramif      == total ramification index                             *)
(*     cd_genus      == genus of covering curve C                            *)
(*     cd_hurwitz    == Riemann-Hurwitz constraint (nat formulation):         *)
(*       2 * cd_genus + 2 * #|G| = #|G| * (2 * cd_base_genus) + cd_ramif + 2 *)
(*                                                                            *)
(*   CoveringScheme M == a ThresholdScheme built from a covering of M        *)
(*     cs_data       == covering geometry (connects G to genus)              *)
(*     cs_scheme     == the ThresholdScheme instance                         *)
(*     cs_perm       == monodromy-induced permutation on share indices       *)
(*     cs_perm_compatible == coord permutation preserves reconstruction     *)
(*     cs_gap        == genus determines threshold gap:                      *)
(*                      ts_T scheme <= ts_k scheme + 2 * genus               *)
(*                                                                            *)
(* Key results:                                                               *)
(*   genus0_exact  == genus 0 implies exact threshold (ts_T <= ts_k)         *)
(*   higher_genus_wider_gap == higher genus allows wider gap                 *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Covering Data — Riemann-Hurwitz                             *)
(******************************************************************************)

Section covering_data.
Variable M : MonodromyReprType.
Let G := pgg_G M.

(* Covering geometry: connects |G| to genus via Riemann-Hurwitz.
   The nat formulation avoids subtraction:
     Original: 2g(C) - 2 = |G| * (2g(B) - 2) + R
     Nat form: 2g(C) + 2|G| = |G| * 2g(B) + R + 2
   This holds for all genera g(B) >= 0. *)
Record CoveringData := MkCoveringData {
  cd_base_genus : nat ;          (* genus of base curve B *)
  cd_n_branch   : nat ;          (* number of branch points *)
  cd_ramif      : nat ;          (* total ramification index *)
  cd_genus      : nat ;          (* genus of covering curve C *)
  cd_hurwitz    :                (* Riemann-Hurwitz constraint *)
    2 * cd_genus + 2 * #|G| = #|G| * (2 * cd_base_genus) + cd_ramif + 2 ;
}.

(* Genus is determined by |G|, base genus, and ramification *)
Lemma genus_from_hurwitz (cd : CoveringData) :
  2 * cd_genus cd = #|G| * (2 * cd_base_genus cd) + cd_ramif cd + 2 - 2 * #|G|.
Proof.
have := cd_hurwitz cd.
move/(f_equal (fun x => x - 2 * #|G|)).
by rewrite addnK.
Qed.

End covering_data.

Arguments CoveringData M : clear implicits.
Arguments MkCoveringData {M}.

(******************************************************************************)
(*     Section 2: Covering Scheme — G Determines Threshold                    *)
(******************************************************************************)

Section covering_scheme.
Variable M : MonodromyReprType.
Let N := (pgg_N' M).+1.
Let rho := @pgg_rho M.

(* A CoveringScheme bundles:
   1. Covering geometry (CoveringData) — connects G to genus via Riemann-Hurwitz
   2. A ThresholdScheme — the actual secret sharing scheme
   3. Coordinate permutation — monodromy-induced share reordering
   4. Compatibility — permuting shares preserves reconstruction
   5. Gap bound — genus determines the threshold gap *)
Record CoveringScheme := MkCoveringScheme {
  cs_data   : CoveringData M ;
  cs_T'     : nat ;
  cs_scheme : ThresholdScheme 'I_N 'I_N ;
  cs_scheme_T : ts_T' cs_scheme = cs_T' ;
  cs_perm   : pgg_gT M -> {perm 'I_(ts_T' cs_scheme).+1} ;
  cs_perm_compatible :
    @ts_perm_compatible _ (pgg_G M) _ _ cs_scheme cs_perm ;
  cs_gap :
    ts_T cs_scheme <= ts_k cs_scheme + 2 * cd_genus (cs_data) ;
}.

End covering_scheme.

Arguments CoveringScheme M : clear implicits.
Arguments MkCoveringScheme {M}.

(******************************************************************************)
(*     Section 3: Consequences of the Covering Structure                      *)
(******************************************************************************)

Section covering_consequences.
Variable M : MonodromyReprType.

(* Genus 0 implies exact threshold (gap = 0) *)
Lemma genus0_exact (cs : CoveringScheme M) :
  cd_genus (cs_data cs) = 0 ->
  ts_T (cs_scheme cs) <= ts_k (cs_scheme cs).
Proof.
move=> Hg0.
have := cs_gap cs.
by rewrite Hg0 muln0 addn0.
Qed.

(* Higher genus allows a wider threshold gap *)
Lemma higher_genus_wider_gap (cs1 cs2 : CoveringScheme M) :
  cd_genus (cs_data cs1) <= cd_genus (cs_data cs2) ->
  ts_k (cs_scheme cs1) + 2 * cd_genus (cs_data cs1) <=
  ts_k (cs_scheme cs1) + 2 * cd_genus (cs_data cs2).
Proof. by move=> Hle; rewrite leq_add2l leq_mul2l Hle orbT. Qed.

(* The threshold gap is bounded by twice the genus *)
Lemma gap_bound (cs : CoveringScheme M) :
  ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).
Proof. by have := cs_gap cs; rewrite -leq_subLR. Qed.

End covering_consequences.

(******************************************************************************)
(*     Section 4: Ramification Consequences for Base Genus 0                  *)
(******************************************************************************)

Section ramif_base0.
Variable M : MonodromyReprType.
Let G := pgg_G M.

(* When base = P^1 (genus 0), Riemann-Hurwitz simplifies:
   2g(C) + 2|G| = R + 2
   i.e., 2g(C) = R + 2 - 2|G| *)

Lemma hurwitz_base0 (cd : CoveringData M) :
  cd_base_genus cd = 0 ->
  2 * cd_genus cd + 2 * #|G| = cd_ramif cd + 2.
Proof.
move=> Hb0.
by move: (cd_hurwitz cd); rewrite Hb0 !muln0 add0n.
Qed.

(* Genus 0 with base = P^1 forces ramification = 2|G| - 2 *)
Lemma genus0_ramif (cd : CoveringData M) :
  cd_base_genus cd = 0 ->
  cd_genus cd = 0 ->
  cd_ramif cd = 2 * #|G| - 2.
Proof.
move=> Hb0 Hg0; have := hurwitz_base0 Hb0.
rewrite Hg0 muln0 add0n => Heq.
by rewrite -(addnK 2 (cd_ramif cd)) Heq addnK.
Qed.

(* Ramification exceeding 2|G|-2 forces positive genus *)
Lemma ramif_forces_genus (cd : CoveringData M) :
  cd_base_genus cd = 0 ->
  2 * #|G| - 2 < cd_ramif cd ->
  0 < cd_genus cd.
Proof.
move=> Hb0 Hramif.
(* From hurwitz_base0: 2*g + 2|G| = R + 2.
   If g = 0: 2|G| = R + 2, so R = 2|G| - 2.
   But R > 2|G| - 2, contradiction. So g > 0. *)
rewrite lt0n; apply/negP => /eqP Hg0.
have := genus0_ramif Hb0 Hg0.
by move=> HR; rewrite HR ltnn in Hramif.
Qed.

End ramif_base0.
