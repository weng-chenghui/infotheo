(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Genus-2 Covering: Hyperelliptic AG Code via CoveringScheme                *)
(*                                                                            *)
(* Demonstrates the wider threshold gap from a genus-2 hyperelliptic curve   *)
(* y^2 = f(x) with deg(f) = 5. The covering C -> P^1 produces a            *)
(* (k, k+4)-threshold scheme, compared to (k, k+2) for genus-1.            *)
(*                                                                            *)
(* Axiomatized (curve-level facts, same boundary as genus-1):                *)
(*   1. ev_g2_encode — evaluation structure (A(x)+y*B(x) representation)   *)
(*   2. g2_dual_ev_encode — dual evaluation encoding                        *)
(*   3. ts2_compatible — monodromy-compatible threshold (Issue #39)         *)
(*                                                                            *)
(* Proved (via hyperelliptic_code.v):                                        *)
(*   - Goppa weight bound (resultant parity argument)                        *)
(*   - Privacy (from dual minimum distance)                                  *)
(*   - ThresholdScheme construction (via Massey)                             *)
(*   - Gap bound ts_T <= ts_k + 4                                           *)
(*                                                                            *)
(*   genus2_data       == CoveringData with genus 2, base P^1               *)
(*   genus2_covering   == CoveringScheme with (k, k+4)-threshold            *)
(*   genus2_gap        == ts_T <= ts_k + 4 for genus-2 covering             *)
(*   genus2_vs_genus1  == cd_genus = 2 (wider gap than genus-1)             *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From mathcomp Require Import ssralg finalg matrix mxalgebra vector.
From mathcomp Require Import poly separable.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import covering_scheme.
From pgg_reconstruct Require Import ag_code ag_massey_bridge.
From pgg_reconstruct Require Import hyperelliptic_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Genus-2 Covering Data                                                  *)
(******************************************************************************)

Section genus2.

Variable M : MonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.
Let rho := @pgg_rho M.

(* For a genus-2 hyperelliptic covering C -> P^1:
   - Base genus = 0
   - Ramification must satisfy: 2*2 + 2|G| = R + 2, so R = 2|G| + 2
   - 5 branch points (Weierstrass points of genus-2 curve) *)

Hypothesis HG : 1 < #|G|.

Let ramif2 := (2 * #|G| + 2)%N.

Lemma genus2_hurwitz :
  (2 * 2 + 2 * #|G| = #|G| * (2 * 0) + ramif2 + 2)%N.
Proof.
by rewrite muln0 muln0 add0n /ramif2 -addnA addnC.
Qed.

Definition genus2_data : CoveringData M := {|
  cd_base_genus := 0 ;
  cd_n_branch   := 5 ;   (* genus-2 hyperelliptic: 5 Weierstrass points *)
  cd_ramif      := ramif2 ;
  cd_genus      := 2 ;
  cd_hurwitz    := genus2_hurwitz ;
|}.

(******************************************************************************)
(*     AG Code on Genus-2 Hyperelliptic Curve                                *)
(******************************************************************************)

(* The Goppa weight bound is PROVED via the hyperelliptic resultant argument
   (hyperelliptic_code.v). The privacy surjection is derived from the dual
   minimum distance axiom. This reduces the axiomatization boundary:

   Axiomatized (curve-level facts):
   1. ev_g2_rank: generator matrix has full row rank (Riemann-Roch)
   2. ev_g2_encode: evaluation structure (A(x)+y*B(x) representation)
   3. g2_dual_ev_encode: dual evaluation encoding (proves dual_min_dist)
   4. ts2_compatible: monodromy-compatible threshold (Issue #39)

   Proved (via hyperelliptic_code.v):
   - goppa_g2_wt: Goppa weight bound (from resultant parity argument)
   - ag_g2_priv_surj: privacy (from dual minimum distance)
   - ThresholdScheme construction (via Massey)
   - Gap bound ts_T <= ts_k + 4 (from code parameters with g = 2)            *)

(* Field over which the genus-2 curve is defined *)
Variable F_g2 : finFieldType.
Hypothesis HN_g2 : N = #|F_g2|.

(* n'' such that n = n''.+2 = N = code length *)
Variable n''_g2 : nat.
Hypothesis Hn_g2 : n''_g2.+2 = N.

Let n_g2 := n''_g2.+2.

(* Code parameters: dimension k, genus g = 2 *)
Variable k_g2 : nat.
Let g_g2 : nat := 2.

(* Generator matrix (evaluation of Riemann-Roch basis at rational points) *)
Variable ev_g2 : 'M[F_g2]_(k_g2, n_g2).

(* Hyperelliptic curve y^2 = f(x) with deg(f) = 5 (genus 2) *)
Variable curve_poly_g2 : {poly F_g2}.
Hypothesis curve_deg_g2 : size curve_poly_g2 = (2 * g_g2 + 1).+1.
Hypothesis curve_sep_g2 : separable_poly curve_poly_g2.

(* Evaluation points on the curve *)
Variable pts_x_g2 : n_g2.-tuple F_g2.
Variable pts_y_g2 : n_g2.-tuple F_g2.
Hypothesis pts_on_curve_g2 :
  forall i : 'I_n_g2, (tnth pts_y_g2 i) ^+ 2 = curve_poly_g2.[tnth pts_x_g2 i].
Hypothesis pts_distinct_g2 :
  forall i j : 'I_n_g2, i != j ->
  (tnth pts_x_g2 i != tnth pts_x_g2 j) || (tnth pts_y_g2 i != tnth pts_y_g2 j).
Hypothesis pts_x_uniq_g2 : uniq pts_x_g2.

(* Code-level axioms (structural, not opaque) *)
Hypothesis ev_g2_rank : \rank ev_g2 = k_g2.
Hypothesis Hk_g2 : 0 < k_g2.
Hypothesis Hkn_g2 : k_g2 <= n_g2.
Hypothesis Hkg_g2 : g_g2 < k_g2.        (* 2 < k, i.e., k >= 3 *)
Hypothesis Hkgn_g2 : k_g2 + g_g2 < n_g2. (* k + 2 < n *)

(* Design distance m = k + g - 1 = k + 1 *)
Let m_deg_g2 := (k_g2 + g_g2 - 1)%N.
Let deg_f_g2 := (2 * g_g2 + 1)%N.

Hypothesis Hdeg_f_le_g2 : deg_f_g2 <= m_deg_g2.  (* 5 <= k+1, i.e., k >= 4 *)

(* Evaluation encoding: ev represents functions A(x) + y*B(x) *)
Hypothesis ev_g2_encode :
  forall v : 'rV[F_g2]_k_g2, v != 0 ->
  exists A B : {poly F_g2},
    ((A != 0) || (B != 0)) /\
    size A <= (m_deg_g2./2).+1 /\
    size B <= ((m_deg_g2 - deg_f_g2)./2).+1 /\
    forall i : 'I_n_g2,
      (v *m ev_g2) ord0 i = A.[tnth pts_x_g2 i] + tnth pts_y_g2 i * B.[tnth pts_x_g2 i].

(* Dual evaluation encoding (replaces dual_min_dist axiom) *)
Let m_deg_dual_g2 := (n_g2 + g_g2 - k_g2 - 1)%N.

Hypothesis g2_dual_ev_encode :
  forall w : 'rV[F_g2]_n_g2, w != 0 ->
  (forall c : 'rV[F_g2]_n_g2, c \in ag_code ev_g2 -> w *m c^T = 0) ->
  exists A B : {poly F_g2},
    ((A != 0) || (B != 0)) /\
    size (hyp_resultant curve_poly_g2 A B) <= m_deg_dual_g2.+1 /\
    forall i : 'I_n_g2,
      w ord0 i = A.[tnth pts_x_g2 i] + tnth pts_y_g2 i * B.[tnth pts_x_g2 i].

Hypothesis Hparam_g2 : n_g2 <= k_g2 + g_g2 + 1. (* n <= k + 3 *)

(* Goppa weight bound: PROVED from hyperelliptic resultant argument *)
Let goppa_g2_wt : forall m : 'rV[F_g2]_k_g2, m != 0 ->
  n_g2 - (k_g2 + g_g2 - 1) <= wH (m *m ev_g2).
Proof.
move=> v Hv.
exact: (@hyp_goppa_wt_mdeg F_g2 g_g2 curve_poly_g2 curve_deg_g2
  m_deg_g2 n''_g2 pts_x_g2 pts_y_g2 pts_on_curve_g2
  pts_x_uniq_g2 Hdeg_f_le_g2 k_g2 ev_g2 ev_g2_encode v Hv).
Qed.

(* Privacy: derived from dual minimum distance *)
Let ag_g2_priv_surj :
  forall (S : {set 'I_n_g2}) (target : 'rV[F_g2]_n_g2),
    #|S| < (k_g2 - g_g2).-1.+2 ->
    exists c : 'rV[F_g2]_n_g2,
      c \in ag_code ev_g2 /\ vproj c S = vproj target S.
Proof.
move=> S target HS.
exact: (hyp_priv_surj curve_deg_g2 pts_on_curve_g2 pts_x_uniq_g2 Hkgn_g2 Hkg_g2 erefl g2_dual_ev_encode target HS).
Qed.

(* Concrete ThresholdScheme from AG code via Massey *)
Let ts2 : ThresholdScheme 'I_N 'I_N :=
  @ag_genus_scheme F_g2 n''_g2 k_g2 g_g2 ev_g2
    ev_g2_rank Hk_g2 Hkn_g2 Hkgn_g2 goppa_g2_wt ag_g2_priv_surj
    N HN_g2.

(* Gap: PROVED from code parameters (not axiomatized) *)
Let ts2_gap : ts_T ts2 <= ts_k ts2 + 2 * g_g2 :=
  @ag_genus_gap F_g2 n''_g2 k_g2 g_g2 ev_g2
    ev_g2_rank Hk_g2 Hkn_g2 Hkg_g2 Hkgn_g2 goppa_g2_wt ag_g2_priv_surj
    Hparam_g2 N HN_g2.

(* 2 * g_g2 = 2 * 2 = 4, so ts2_gap gives ts_T ts2 <= ts_k ts2 + 4 *)
Let ts2_gap4 : ts_T ts2 <= ts_k ts2 + 4.
Proof. exact: ts2_gap. Qed.

(* Monodromy-compatible threshold scheme — axiomatized directly (Issue #39).
   The previous share_compatible bridge was unsatisfiable for non-trivial G
   (see notes/20260316_share_compatible_analysis.md). *)
Hypothesis ts2_compatible :
  @ts_compatible _ G _ _ ts2 (fun g x => rho g x).

Definition genus2_covering : CoveringScheme M := {|
  cs_data       := genus2_data ;
  cs_T'         := ts_T' ts2 ;
  cs_scheme     := ts2 ;
  cs_scheme_T   := erefl ;
  cs_compatible := ts2_compatible ;
  cs_gap        := ts2_gap4 ;
|}.

(* Quasi-(k, k+4) threshold *)
Lemma genus2_gap :
  ts_T (cs_scheme genus2_covering) <= ts_k (cs_scheme genus2_covering) + 4.
Proof. exact: ts2_gap4. Qed.

(* The gap is strictly wider than genus-1 *)
Lemma genus2_vs_genus1 :
  cd_genus (cs_data genus2_covering) = 2.
Proof. by []. Qed.

End genus2.
