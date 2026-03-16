(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Genus-0 Covering: Shamir/Reed-Solomon via CoveringScheme                   *)
(*                                                                            *)
(* Instantiates CoveringScheme for a genus-0 covering (P^1 -> P^1),          *)
(* corresponding to Shamir's secret sharing / Reed-Solomon codes.             *)
(* The key result: genus 0 implies exact threshold (gap = 0).                 *)
(*                                                                            *)
(* The ThresholdScheme is now concrete (from RS codes via Massey's            *)
(* construction in rs_massey_bridge.v). Exactness (ts_T = ts_k) is proved.   *)
(* ts_compatible is axiomatized directly (Issue #39).                        *)
(*                                                                            *)
(*   genus0_data       == CoveringData with genus 0, base P^1                *)
(*   genus0_covering   == CoveringScheme with exact (k,k)-threshold          *)
(*   shamir_exact      == ts_T = ts_k for genus-0 covering                   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop prime div ssralg finalg.
From mathcomp Require Import matrix mxalgebra vector zmodp poly cyclic.
Require Import ssralg_ext hamming linearcode reed_solomon.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import covering_scheme.
From pgg_reconstruct Require Import rs_massey_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Genus-0 Covering Data                                       *)
(******************************************************************************)

Section genus0.

Variable M : MonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.
Let rho := @pgg_rho M.

(* For genus-0 covering P^1 -> P^1:
   - Base genus = 0 (projective line)
   - 2 branch points (minimum for nontrivial covering)
   - Ramification = 2|G| - 2 (total from 2 fully ramified points)
   - Genus = 0 (Riemann-Hurwitz: 0 + 2|G| = (2|G|-2) + 2) *)

Hypothesis HG : 1 < #|G|.  (* nontrivial group *)

(* Ramification for 2 fully-ramified branch points *)
Let ramif0 := (2 * #|G| - 2)%N.

Lemma genus0_hurwitz :
  2 * 0 + 2 * #|G| = #|G| * (2 * 0) + ramif0 + 2.
Proof.
rewrite mulr0 mulr0 add0r add0r /ramif0.
suff : (2 * #|G| = (2 * #|G| - 2) + 2)%N by [].
rewrite subnK //.
by rewrite -[X in X <= _]muln1 leq_mul2l (ltnW HG).
Qed.

Definition genus0_data : CoveringData M := {|
  cd_base_genus := 0 ;
  cd_n_branch   := 2 ;
  cd_ramif      := ramif0 ;
  cd_genus      := 0 ;
  cd_hurwitz    := genus0_hurwitz ;
|}.

(******************************************************************************)
(*     Section 2: Concrete RS-based Threshold Scheme                          *)
(******************************************************************************)

(* Field parameters for the RS code underlying Shamir's scheme *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Let F := GF m' primeq.

Variable n'' : nat.
Variable a : F.

Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : N = #|F|.

(* Concrete threshold scheme from RS codes via Massey (rs_massey_bridge.v) *)
Let ts0 : ThresholdScheme 'I_N 'I_N := rs_genus0_scheme primeq a qn an HN.

(* Exactness: proved from RS min_dist + Massey construction *)
Let ts0_exact : ts_T ts0 = ts_k ts0 := rs_genus0_exact primeq a qn an HN.

(* Monodromy-compatible threshold scheme — axiomatized directly (Issue #39).
   The previous share_compatible bridge was unsatisfiable for non-trivial G
   (see notes/20260316_share_compatible_analysis.md). *)
Hypothesis ts0_compatible :
  @ts_compatible _ G _ _ ts0 (fun g x => rho g x).

(* The CoveringScheme instance *)
Definition genus0_covering : CoveringScheme M := {|
  cs_data       := genus0_data ;
  cs_T'         := ts_T' ts0 ;
  cs_scheme     := ts0 ;
  cs_scheme_T   := erefl ;
  cs_compatible := ts0_compatible ;
  cs_gap        := leq_trans (leqnn _)
                     (leq_trans (eq_leq ts0_exact) (leq_addr _ _)) ;
|}.

(* Exact threshold for genus-0 covering *)
Lemma shamir_exact :
  ts_T (cs_scheme genus0_covering) = ts_k (cs_scheme genus0_covering).
Proof. exact: ts0_exact. Qed.

(* Protocol integration: reconstruction recovers the secret *)
Lemma genus0_secret_invariant (PI : PGGInterface M)
    (HT : ts_T' ts0 = pi_T' PI) (s : 'I_N) (P : pgg_gT M) :
  P \in G ->
  ts_valid ts0 s (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> PG Hvalid.
exact: pgg_secret_invariant PG Hvalid ts0_compatible.
Qed.

End genus0.
