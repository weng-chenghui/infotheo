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
(* ts_perm_compatible is derived from code automorphism hypotheses.          *)
(*                                                                            *)
(* Shamir-via-Galois connection:                                              *)
(*   Genus 0 means the covering is P^1 → P^1, i.e., the function field     *)
(*   extension K(C)/K(X) is the splitting field of a degree-N rational      *)
(*   function. The RS code evaluates polynomials at fiber points (= roots   *)
(*   of this rational function = Shamir's evaluation points). Thus          *)
(*   Reed-Solomon reconstruction IS Lagrange interpolation over the fiber,  *)
(*   recovering Shamir's scheme for ANY monodromy group.                     *)
(*                                                                            *)
(*   Source: Chen-Cramer, "Algebraic Geometric Secret Sharing Schemes and   *)
(*     Secure Multi-Party Computations over Small Fields", CRYPTO 2006      *)
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
From pgg_reconstruct Require Import coord_perm_compatible.

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

(* Coordinate-permutation compatibility: derived from code automorphisms.
   sigma_code maps monodromy elements to column permutations of the RS code
   that fix position 0 (the secret). massey_perm_compatible +
   transport_perm_compatible derive ts_perm_compatible from these. *)
Variable sigma_code : pgg_gT M -> {perm 'I_n''.+3}.

Hypothesis sigma_fix0 :
  forall g, g \in G -> sigma_code g ord0 = ord0.

Hypothesis code_auto :
  forall g, g \in G ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

Let ts0_perm : pgg_gT M -> {perm 'I_(ts_T' ts0).+1} :=
  massey_share_perm (G:=G) sigma_fix0.

Lemma ts0_perm_compatible :
  @ts_perm_compatible _ G _ _ ts0 ts0_perm.
Proof.
rewrite /ts0 /= /rs_genus0_scheme /rs_massey.
apply: transport_perm_compatible.
exact: massey_perm_compatible.
Qed.

(* The CoveringScheme instance *)
Definition genus0_covering : CoveringScheme M := {|
  cs_data       := genus0_data ;
  cs_T'         := ts_T' ts0 ;
  cs_scheme     := ts0 ;
  cs_scheme_T   := erefl ;
  cs_perm       := ts0_perm ;
  cs_perm_compatible := ts0_perm_compatible ;
  cs_gap        := leq_trans (leqnn _)
                     (leq_trans (eq_leq ts0_exact) (leq_addr _ _)) ;
|}.

(* Exact threshold for genus-0 covering *)
Lemma shamir_exact :
  ts_T (cs_scheme genus0_covering) = ts_k (cs_scheme genus0_covering).
Proof. exact: ts0_exact. Qed.

(* Protocol integration: reconstruction recovers the secret
   (requires G-stable starts hypothesis) *)
Lemma genus0_secret_invariant (PI : PGGInterface M)
    (HT : ts_T' ts0 = pi_T' PI) (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in G ->
       forall i : 'I_(ts_T' ts0).+1,
         rho g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
         tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) (ts0_perm g i)) :
  P \in G ->
  ts_valid ts0 s (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> PG Hvalid.
exact: pgg_secret_invariant_perm G_stable PG Hvalid ts0_perm_compatible.
Qed.

End genus0.
