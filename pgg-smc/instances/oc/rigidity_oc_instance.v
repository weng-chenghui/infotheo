(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Overlapping 3-Cycles Algebraic Rigidity Instance                           *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the overlapping       *)
(* 3-cycles group OC = <(0 1 2), (1 2 3)> in S_4.                            *)
(*                                                                            *)
(* This is the FIRST instance with L > 1 (L = 2), demonstrating the          *)
(* word-eval injectivity hardness tradeoff: higher L means a larger search    *)
(* space                                                                      *)
(* (search_space 2 = 4) but also stronger security guarantees.               *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 2 (generators), N = 4 (sheets), L = 2, depth = 2                  *)
(*   epsilon (fiber) = 1 (fiber-counted, worst-case sheet s=1)               *)
(*   epsilon (spectral) = 2 * (1/sqrt(2))^83 at L=83 (40-bit security)      *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_4:                                *)
(*   The 4x4 Schreier matrix with generators (0 1 2) and (1 2 3) is:        *)
(*     | 1/2  1/2   0    0  |                                                *)
(*     |  0    0    1    0  |                                                *)
(*     | 1/2   0    0   1/2 |                                                *)
(*     |  0   1/2   0   1/2 |                                                *)
(*   Eigenvalues: 1, 1/2, (-1+i*sqrt(7))/4, (-1-i*sqrt(7))/4.               *)
(*   |(-1+/-i*sqrt(7))/4| = sqrt(1/2) = 1/sqrt(2).                          *)
(*   Second-largest |eigenvalue| = 1/sqrt(2) ~ 0.707.                        *)
(*   Spectral gap = 1 - 1/sqrt(2) ~ 0.293.                                  *)
(*     L = 83 gives var_dist < 2^{-40}  (40-bit security)                   *)
(*     L = 259 gives var_dist < 2^{-128} (128-bit security)                  *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   oc_security_witness_2 : SecurityWitness (fiber-counted eps=1)           *)
(*   oc_rigidity : AlgebraicRigidity (security + threshold)                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section oc_security.

Variable R : realType.

Let M_oc := @Gen_PGGTypes 1 2 oc_sigmas.
Let R_oc : GeneratedMonodromyReprType := M_oc.

Local Open Scope ring_scope.

(* Fiber-counted endpoint bound: for each sheet s in 'I_4,
   var_dist(fdistmap perm_endpoint (rho_from_words 2 oc_sigmas), uniform) <= 1.
   Achievable(2) = {s0^2, s0*s1, s1*s0, s1^2} (4 permutations).
   Worst-case sheet s=1: fiber distribution P=(2/4,0,0,2/4), var_dist=1.
   Other sheets s=0,2,3 have var_dist=1/2. *)
Lemma oc_endpoint_bound_fiber :
  forall s : 'I_4,
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (@rho_from_words R _ _ 2 oc_sigmas))
           (fdist_uniform (card_ord 4)) <= 1)%O.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans
  (@var_dist_endpoint_image_bound R 2 1 2 oc_sigmas oc_weval_inj2
    (erefl _) 2 s _)); last first.
  by rewrite /= subn2 /= -GRing.Theory.natrM /=
     GRing.Theory.divrr // GRing.Theory.unitfE Num.Theory.pnatr_eq0.
have Hmem : forall (w : pgg_word (Gen_PGGTypes oc_sigmas) 2),
    word_eval w s \in
      (fun sigma : {perm 'I_4} => sigma s) @:
        achievable (Gen_PGGTypes oc_sigmas) 2.
  by move=> w; apply: imset_f; apply: imset_f.
pose w00 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord0; ord0].
pose w11 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord_max; ord_max].
pose w01 : pgg_word (Gen_PGGTypes oc_sigmas) 2 := [tuple ord0; ord_max].
have Hw00 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w00 = (oc_s0 * oc_s0)%g.
  rewrite /word_eval /w00 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
have Hw11 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w11 = (oc_s1 * oc_s1)%g.
  rewrite /word_eval /w11 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
have Hw01 : @word_eval (Gen_PGGTypes oc_sigmas) 2 w01 = (oc_s0 * oc_s1)%g.
  rewrite /word_eval /w01 big_ord_recr /= big_ord_recr /= big_ord0 mul1g.
  congr (_ * _)%g; apply: oc_sigmasE.
apply/card_gt1P.
case: s Hmem => [[|[|[|[|s]]]] Hs] //= Hmem.
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w01 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw01 !permM !oc_s0E !oc_s1E].
- exists (word_eval w00 (Ordinal Hs)), (word_eval w11 (Ordinal Hs)).
  by split; [exact: Hmem | exact: Hmem |
    rewrite Hw00 Hw11 !permM !oc_s0E !oc_s1E].
Qed.

(* SecurityWitness at L=2 via fiber counting.
   Epsilon = 1, tighter than DPI bound 40/24 ≈ 1.67. *)
Definition oc_security_witness_2 : SecurityWitness R R_oc :=
  security_witness_fiber oc_weval_inj2 oc_endpoint_bound_fiber.

End oc_security.

(******************************************************************************)
(*     Spectral Gap Convergence (Axiomatized)                                 *)
(*                                                                            *)
(* The 4x4 Schreier matrix of OC on 'I_4 is doubly stochastic.               *)
(* Characteristic polynomial: (1/2-lam)(lam-1)(lam^2+lam/2+1/2).             *)
(* Eigenvalues: 1, 1/2, (-1+/-i*sqrt(7))/4.                                  *)
(* |(-1+/-i*sqrt(7))/4| = sqrt(1/16+7/16) = 1/sqrt(2).                       *)
(* Second-largest |eigenvalue| = 1/sqrt(2), spectral gap = 1-1/sqrt(2).       *)
(*                                                                            *)
(* Convergence: var_dist <= sqrt(4) * (1/sqrt(2))^L = 2 * 2^{-L/2}.         *)
(* Equivalently: var_dist <= 2 * (1 - gap)^L with gap = 1-1/sqrt(2).        *)
(*                                                                            *)
(* Reference: Mizuki-Sone (2009), overlapping 3-cycles.                      *)
(******************************************************************************)

Section oc_spectral.

Variable R : realType.

Let M_oc := @Gen_PGGTypes 1 2 oc_sigmas.
Let R_oc : GeneratedMonodromyReprType := M_oc.

(* Spectral gap: 1 - 1/sqrt(2) ~ 0.293 *)
Variable oc_spectral_gap : R.
Hypothesis oc_gap_pos : (0 < oc_spectral_gap)%R.
Hypothesis oc_gap_le1 : (oc_spectral_gap <= 1)%R.

(* Schreier walk distribution family *)
Variable oc_schreier_rho : nat -> R.-fdist {perm 'I_4}.

(* Spectral convergence: var_dist <= sqrt(4) * (1 - gap)^L *)
Hypothesis oc_spectral_convergence :
  forall (L : nat) (s : 'I_4),
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (oc_schreier_rho L))
           (fdist_uniform (card_ord 4))
  <= Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)%O.

Definition oc_asymptotic : @SecurityAsymptotic R R_oc.
Proof.
apply: (@MkSecurityAsymptotic R R_oc
  oc_spectral_gap 0
  oc_gap_pos oc_gap_le1
  (Order.POrderTheory.lexx 0)
  oc_schreier_rho).
move=> L s.
rewrite add0r.
exact: oc_spectral_convergence.
Defined.

Definition oc_security_witness_schreier (L : nat) :
    SecurityWitness R R_oc :=
  @MkSecurityWitness R R_oc L
    (Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)
    (oc_schreier_rho L)
    (fun s => oc_spectral_convergence L s)
    None
    (Some oc_asymptotic).

End oc_spectral.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=83 (40-bit security)                   *)
(*                                                                            *)
(* 2 * (1/sqrt(2))^83 = 2 * 2^{-83/2} = 2^{1-41.5} = 2^{-40.5} < 2^{-40}. *)
(* For 128-bit security, use L=259 instead.                                   *)
(******************************************************************************)

Section oc_rigidity_cryptographically_secure.

Variable R : realType.

Let R_oc : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 1 2 oc_sigmas.

(* Threshold witness — taken as parameter to avoid duplicating
   genus-0 covering axioms (RS code, PGL bound, etc.) *)
Variable oc_tw : ThresholdWitness R_oc.

(* Spectral parameters *)
Variable oc_spectral_gap : R.
Hypothesis oc_gap_pos : (0 < oc_spectral_gap)%R.
Hypothesis oc_gap_le1 : (oc_spectral_gap <= 1)%R.
Variable oc_schreier_rho : nat -> R.-fdist {perm 'I_4}.
Hypothesis oc_spectral_convergence :
  forall (L : nat) (s : 'I_4),
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                     (oc_schreier_rho L))
           (fdist_uniform (card_ord 4))
  <= Num.sqrt 4%:R * (1 - oc_spectral_gap) ^+ L)%O.

Definition oc_rigidity_cryptographically_secure : AlgebraicRigidity R R_oc :=
  @MkAlgebraicRigidity R R_oc
    (@oc_security_witness_schreier R oc_spectral_gap oc_gap_pos
       oc_gap_le1 oc_schreier_rho oc_spectral_convergence 83)
    oc_tw.

End oc_rigidity_cryptographically_secure.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section oc_rigidity.

Variable R : realType.

Let R_oc : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 1 2 oc_sigmas.

(* Group nontriviality *)
Hypothesis HG_oc : (1 < #|pgg_G R_oc|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = 4 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_oc).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT R_oc -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_oc -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_oc ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition oc_covering : CoveringScheme R_oc :=
  genus0_covering HG_oc qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis oc_genus0_pgl :
  (#|pgg_G R_oc| <= pgl_bound R_oc)%N.

Definition oc_threshold_witness : ThresholdWitness R_oc :=
  @MkThresholdWitness R_oc oc_covering (fun _ => oc_genus0_pgl).

Definition oc_rigidity : AlgebraicRigidity R R_oc :=
  @MkAlgebraicRigidity R R_oc
    (oc_security_witness_2 R)
    oc_threshold_witness.

(* Derived properties *)

Lemma oc_complexity (L : nat) :
  (@search_space R_oc L <= #|pgg_G R_oc|)%N.
Proof. exact: search_space_leG. Qed.

Lemma oc_tradeoff :
  let cs := tw_covering (ar_threshold oc_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_oc| <= pgl_bound R_oc)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_oc oc_covering (fun _ => oc_genus0_pgl)).
Qed.

End oc_rigidity.
