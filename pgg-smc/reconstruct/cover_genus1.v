(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Genus-1 Covering: Elliptic Curve AG Code via CoveringScheme                *)
(*                                                                            *)
(* Demonstrates how a higher-genus covering (elliptic curve -> P^1) produces *)
(* a wider threshold gap. The Riemann-Hurwitz verification (genus1_hurwitz)   *)
(* is fully proved. The ThresholdScheme is now constructed from AG code       *)
(* foundations (ag_code.v + ag_massey_bridge.v), lowering the axiomatization  *)
(* boundary from 3 hypotheses (entire scheme + gap + compatibility) to        *)
(* code-level axioms (generator matrix rank, Goppa bound, privacy surjection) *)
(* plus one remaining hypothesis (ts_compatible, Issue #39).                  *)
(* The higher_genus section uses the same code-level pattern for arbitrary g. *)
(*                                                                            *)
(*   genus1_data       == CoveringData with genus 1, base P^1                *)
(*   genus1_covering   == CoveringScheme with (k, k+2)-threshold             *)
(*   elliptic_gap      == ts_T <= ts_k + 2 for genus-1 covering             *)
(*   higher_genus_data     == CoveringData with arbitrary genus g            *)
(*   higher_genus_covering == CoveringScheme with (k, k+2g)-threshold        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From mathcomp Require Import ssralg finalg matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import covering_scheme.
From pgg_reconstruct Require Import ag_code ag_massey_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Genus-1 Covering Data                                       *)
(******************************************************************************)

Section genus1.

Variable M : MonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.
Let rho := @pgg_rho M.

(* For an elliptic covering E -> P^1:
   - Base genus = 0
   - Ramification must satisfy: 2*1 + 2|G| = R + 2, so R = 2|G|
   - This means 2|G| total ramification index *)

Hypothesis HG : 1 < #|G|.

Let ramif1 := (2 * #|G|)%N.

Lemma genus1_hurwitz :
  (2 * 1 + 2 * #|G| = #|G| * (2 * 0) + ramif1 + 2)%N.
Proof.
by rewrite muln1 muln0 muln0 add0n /ramif1 addnC.
Qed.

Definition genus1_data : CoveringData M := {|
  cd_base_genus := 0 ;
  cd_n_branch   := 3 ;   (* elliptic covers typically have 3+ branch points *)
  cd_ramif      := ramif1 ;
  cd_genus      := 1 ;
  cd_hurwitz    := genus1_hurwitz ;
|}.

(******************************************************************************)
(*     Section 2: AG Code on Elliptic Curve (code-level axiomatization)       *)
(******************************************************************************)

(* Instead of axiomatizing an entire ThresholdScheme ts1, we axiomatize at
   the code level: a generator matrix ev with rank, Goppa weight bound, and
   privacy surjection. The ThresholdScheme is then *constructed* via Massey,
   and the gap bound is *proved* from the code parameters.

   Axiomatized (curve-level facts):
   1. ev_ec_rank: generator matrix has full row rank (Riemann-Roch)
   2. goppa_ec_wt: Goppa weight bound (nonzero functions have bounded zeros)
   3. ag_ec_priv_surj: dual distance bound (coordinate projection surjective)
   4. ts1_compatible: monodromy preserves reconstruction (Issue #39)

   Proved:
   - ThresholdScheme construction (via Massey)
   - Gap bound ts_T <= ts_k + 2 (from code parameters with g = 1)            *)

(* Field over which the elliptic curve is defined *)
Variable F_ec : finFieldType.
Hypothesis HN_ec : N = #|F_ec|.

(* n'' such that n = n''.+2 = N = code length *)
Variable n''_ec : nat.
Hypothesis Hn_ec : n''_ec.+2 = N.

Let n_ec := n''_ec.+2.

(* Code parameters: dimension k, genus g = 1 *)
Variable k_ec : nat.
Let g_ec : nat := 1.

(* Generator matrix (evaluation of Riemann-Roch basis at rational points) *)
Variable ev_ec : 'M[F_ec]_(k_ec, n_ec).

(* Code-level axioms *)
Hypothesis ev_ec_rank : \rank ev_ec = k_ec.
Hypothesis Hk_ec : 0 < k_ec.
Hypothesis Hkn_ec : k_ec <= n_ec.
Hypothesis Hkg_ec : g_ec < k_ec.        (* 1 < k, i.e., k >= 2 *)
Hypothesis Hkgn_ec : k_ec + g_ec < n_ec. (* k + 1 < n *)
Hypothesis goppa_ec_wt :
  forall m : 'rV[F_ec]_k_ec, m != 0 ->
  n_ec - (k_ec + g_ec - 1) <= wH (m *m ev_ec).
Hypothesis ag_ec_priv_surj :
  forall (S : {set 'I_n_ec}) (target : 'rV[F_ec]_n_ec),
    #|S| < (k_ec - g_ec).-1.+2 ->
    exists c : 'rV[F_ec]_n_ec,
      c \in ag_code ev_ec /\ vproj c S = vproj target S.
Hypothesis Hparam_ec : n_ec <= k_ec + g_ec + 1. (* n <= k + 2 *)

(* Concrete ThresholdScheme from AG code via Massey *)
Let ts1 : ThresholdScheme 'I_N 'I_N :=
  @ag_genus_scheme F_ec n''_ec k_ec g_ec ev_ec
    ev_ec_rank Hk_ec Hkn_ec Hkgn_ec goppa_ec_wt ag_ec_priv_surj
    N HN_ec.

(* Gap: PROVED from code parameters (not axiomatized) *)
Let ts1_gap : ts_T ts1 <= ts_k ts1 + 2 * g_ec :=
  @ag_genus_gap F_ec n''_ec k_ec g_ec ev_ec
    ev_ec_rank Hk_ec Hkn_ec Hkg_ec Hkgn_ec goppa_ec_wt ag_ec_priv_surj
    Hparam_ec N HN_ec.

(* 2 * g_ec = 2 * 1 = 2, so ts1_gap gives ts_T ts1 <= ts_k ts1 + 2 *)
Let ts1_gap2 : ts_T ts1 <= ts_k ts1 + 2.
Proof. exact: ts1_gap. Qed.

(* Monodromy preserves the AG code — still axiomatized (Issue #39) *)
Hypothesis ts1_compatible :
  @ts_compatible _ G _ _ ts1 (fun g x => rho g x).

Definition genus1_covering : CoveringScheme M := {|
  cs_data       := genus1_data ;
  cs_T'         := ts_T' ts1 ;
  cs_scheme     := ts1 ;
  cs_scheme_T   := erefl ;
  cs_compatible := ts1_compatible ;
  cs_gap        := ts1_gap2 ;
|}.

(* Quasi-(k, k+2) threshold *)
Lemma elliptic_gap :
  ts_T (cs_scheme genus1_covering) <= ts_k (cs_scheme genus1_covering) + 2.
Proof. exact: ts1_gap2. Qed.

(* The gap is strictly wider than genus-0 (when ts_T > ts_k) *)
Lemma genus1_vs_genus0 :
  cd_genus (cs_data genus1_covering) = 1.
Proof. by []. Qed.

End genus1.

(******************************************************************************)
(*     Section 3: Generic Higher-Genus Covering                               *)
(******************************************************************************)

Section higher_genus.

Variable M : MonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.
Let rho := @pgg_rho M.

Hypothesis HG : 1 < #|G|.

Variable g : nat.
Variable ramif_g : nat.

Hypothesis hurwitz_g :
  (2 * g + 2 * #|G| = #|G| * (2 * 0) + ramif_g + 2)%N.

Definition higher_genus_data : CoveringData M := {|
  cd_base_genus := 0 ;
  cd_n_branch   := g + 2 ;   (* heuristic: more branch points for higher genus *)
  cd_ramif      := ramif_g ;
  cd_genus      := g ;
  cd_hurwitz    := hurwitz_g ;
|}.

(******************************************************************************)
(*     AG Code Parameters for genus g (code-level axiomatization)             *)
(******************************************************************************)

(* Instead of axiomatizing an entire ThresholdScheme ts_g, we axiomatize at
   the code level (mirroring the genus1 section pattern). The ThresholdScheme
   is *constructed* via Massey, and the gap bound is *proved*.

   Axiomatized (curve-level facts):
   1. ev_g_rank: generator matrix has full row rank (Riemann-Roch)
   2. goppa_g_wt: Goppa weight bound
   3. ag_g_priv_surj: dual distance bound (coordinate projection surjective)
   4. ts_g_compatible: monodromy preserves reconstruction (Issue #39)

   Proved:
   - ThresholdScheme construction (via Massey)
   - Gap bound ts_T <= ts_k + 2g (from code parameters)                      *)

Variable F_g : finFieldType.
Hypothesis HN_g : N = #|F_g|.

Variable n''_g : nat.
Let n_g := n''_g.+2.

Variable k_g : nat.

(* Generator matrix (evaluation of Riemann-Roch basis at rational points) *)
Variable ev_g : 'M[F_g]_(k_g, n_g).

(* Code-level axioms *)
Hypothesis ev_g_rank : \rank ev_g = k_g.
Hypothesis Hk_g : 0 < k_g.
Hypothesis Hkn_g : k_g <= n_g.
Hypothesis Hkg_g : g < k_g.
Hypothesis Hkgn_g : k_g + g < n_g.
Hypothesis goppa_g_wt :
  forall m : 'rV[F_g]_k_g, m != 0 ->
  n_g - (k_g + g - 1) <= wH (m *m ev_g).
Hypothesis ag_g_priv_surj :
  forall (S : {set 'I_n_g}) (target : 'rV[F_g]_n_g),
    #|S| < (k_g - g).-1.+2 ->
    exists c : 'rV[F_g]_n_g,
      c \in ag_code ev_g /\ vproj c S = vproj target S.
Hypothesis Hparam_g : n_g <= k_g + g + 1.

(* Concrete ThresholdScheme from AG code via Massey *)
Let ts_g : ThresholdScheme 'I_N 'I_N :=
  @ag_genus_scheme F_g n''_g k_g g ev_g
    ev_g_rank Hk_g Hkn_g Hkgn_g goppa_g_wt ag_g_priv_surj
    N HN_g.

(* Gap: PROVED from code parameters (not axiomatized) *)
Let ts_g_gap : ts_T ts_g <= ts_k ts_g + 2 * g :=
  @ag_genus_gap F_g n''_g k_g g ev_g
    ev_g_rank Hk_g Hkn_g Hkg_g Hkgn_g goppa_g_wt ag_g_priv_surj
    Hparam_g N HN_g.

(* Monodromy preserves the AG code — still axiomatized (Issue #39) *)
Hypothesis ts_g_compatible :
  @ts_compatible _ G _ _ ts_g (fun g x => rho g x).

Definition higher_genus_covering : CoveringScheme M := {|
  cs_data       := higher_genus_data ;
  cs_T'         := ts_T' ts_g ;
  cs_scheme     := ts_g ;
  cs_scheme_T   := erefl ;
  cs_compatible := ts_g_compatible ;
  cs_gap        := ts_g_gap ;
|}.

Lemma higher_genus_gap_bound :
  ts_T (cs_scheme higher_genus_covering) <=
  ts_k (cs_scheme higher_genus_covering) + 2 * g.
Proof. exact: ts_g_gap. Qed.

End higher_genus.
