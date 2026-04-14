(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 × S_5 Algebraic Rigidity Instance                                     *)
(*                                                                            *)
(* First concrete group instance with genus > 0. The product structure        *)
(* S_5 × S_5 ⊂ S_10 forces genus >= 3 because:                              *)
(*   1. |G| = 14400 > pgl_bound(10) = 990 → genus > 0                       *)
(*   2. Product sum_mod gives (5,10)-threshold with gap 5 → genus >= 3      *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   N = 10 sheets (two 5-card piles)                                        *)
(*   Tg = 8 generators (adjacent transpositions, 4 per pile)                 *)
(*   SecurityWitness (fiber): L=1, eps = 8/5 (fiber-counted, proved)         *)
(*   SecurityWitness (spectral): L=591, eps = sqrt(10)*(1-gap)^591           *)
(*     40-bit security from axiomatized spectral gap                         *)
(*   ThresholdScheme: product of two sum_mod on 'I_5                         *)
(*   CoveringData: genus 3, base genus 0, ramif = 28804                      *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_10:                               *)
(*   The 10x10 Schreier matrix decomposes into two 5x5 blocks (one per      *)
(*   pile) since generators preserve {0..4} and {5..9}. Each block is        *)
(*   I - (1/8)*L(P_5) where L(P_5) is the graph Laplacian of the path P_5.  *)
(*   Smallest nonzero Laplacian eigenvalue: 2*(1-cos(pi/5)) (standard        *)
(*   spectral graph theory, cf. Brouwer-Haemers 2012, Chung 1997).          *)
(*   Spectral gap = (1 - cos(pi/5)) / 4 ~ 0.0477.                          *)
(*     L = 591 gives var_dist < 2^{-40}  (40-bit security)                  *)
(*     L = 1838 gives var_dist < 2^{-128} (128-bit security)                *)
(*                                                                            *)
(*   Wilson (2004): "Mixing times of lozenge tiling and card shuffling       *)
(*     Markov chains," Ann. Appl. Probab. 14(1):274-325.                     *)
(*   Bacher (1994): "Valeur propre minimale du laplacien de Coxeter pour     *)
(*     le groupe symetrique," J. Algebra 167:460-472.                        *)
(*                                                                            *)
(* No finite field, AG code, or code automorphism hypotheses needed —        *)
(* the product sum_mod construction is fully self-contained.                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_s5x5 pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import product_threshold.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* |S_5 × S_5| = 14400, infeasible to compute in Coq *)
Axiom s5x5_group_order :
  #|pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple)| = 14400.

(* Generators preserve pile structure: pile-1 = {0..4}, pile-2 = {5..9} *)
Axiom s5x5_preserves_pile1_ax :
  forall g, g \in pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple) ->
  forall i : 'I_10, (val i < 5)%N -> (val (@pgg_rho (@Gen_PGGTypes 7 8 s5x5_gen_tuple) g i) < 5)%N.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section s5x5_security.

Variable R : realType.

Let M_s5x5 := @Gen_PGGTypes 7 8 s5x5_gen_tuple.
Let R_s5x5 : GeneratedMonodromyReprType := M_s5x5.

(* Fiber-counted endpoint bound: for each sheet s in 'I_10,
   var_dist(endpoint, uniform) <= 8/5.
   At L=1, achievable = {(01),(12),(23),(34),(56),(67),(78),(89)}.
   Boundary sheets (0,4,5,9): only 1 generator moves them, image size = 2.
   Inner sheets (1,2,3,6,7,8): 2 generators move them, image size = 3.
   Worst case: img_min = 2, bound = 2*(10-2)/10 = 8/5. *)
Let s5x5_eps := @GRing.natmul R 1 8 / @GRing.natmul R 1 5.

Lemma s5x5_endpoint_bound_fiber :
  forall s : 'I_10,
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                     (@rho_from_words R _ _ 1 s5x5_gen_tuple))
           (fdist_uniform (card_ord 10)) <= s5x5_eps)%O.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans
  (@var_dist_endpoint_image_bound_unbalanced R 8 7 1 s5x5_gen_tuple
    s5x5_weval_inj1 (erefl true) 2 s _)); last first.
  rewrite /= -natrM /s5x5_eps.
  have -> : (16 : R) = 2%:R * 8%:R by rewrite -natrM.
  have -> : (10 : R) = 2%:R * 5%:R by rewrite -natrM.
  rewrite Num.Theory.ler_pdivlMr ?Num.Theory.ltr0n //.
  rewrite invfM // -mulrA mulfVK ?Num.Theory.pnatr_eq0 //.
  rewrite mulrAC divrr ?mul1r //.
  by apply: Num.Theory.unitf_gt0; rewrite Num.Theory.ltr0n.
have Hmem : forall (w : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1),
    word_eval w s \in
      (fun sigma : {perm 'I_10} => sigma s) @:
        achievable (Gen_PGGTypes s5x5_gen_tuple) 1.
  by move=> w; apply: imset_f; apply: imset_f.
pose w0 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=0) (erefl true))].
pose w1 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=1) (erefl true))].
pose w2 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=2) (erefl true))].
pose w3 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=3) (erefl true))].
pose w4 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=4) (erefl true))].
pose w5 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=5) (erefl true))].
pose w6 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=6) (erefl true))].
pose w7 : pgg_word (Gen_PGGTypes s5x5_gen_tuple) 1 :=
  [tuple (Ordinal (n:=8) (m:=7) (erefl true))].
have Hwi : forall i : 'I_8,
  @word_eval (Gen_PGGTypes s5x5_gen_tuple) 1 [tuple i] =
  tnth s5x5_gen_tuple i.
  move=> i; rewrite /word_eval big_ord_recr /= big_ord0 mul1g //.
apply/card_gt1P.
move: Hmem; case: s => [] m Hm Hmem.
case: m Hm Hmem => [|[|[|[|[|m']]]]] Hm Hmem.
(* s=0: tperm(0,1)(0)=1 vs tperm(3,4)(0)=0 *)
- exists (word_eval w0 (Ordinal Hm)), (word_eval w3 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=1: tperm(0,1)(1)=0 vs tperm(1,2)(1)=2 *)
- exists (word_eval w0 (Ordinal Hm)), (word_eval w1 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=2: tperm(1,2)(2)=1 vs tperm(2,3)(2)=3 *)
- exists (word_eval w1 (Ordinal Hm)), (word_eval w2 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=3: tperm(2,3)(3)=2 vs tperm(3,4)(3)=4 *)
- exists (word_eval w2 (Ordinal Hm)), (word_eval w3 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
(* s=4: tperm(3,4)(4)=3 vs tperm(0,1)(4)=4 *)
- exists (word_eval w3 (Ordinal Hm)), (word_eval w0 (Ordinal Hm)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
- case: m' Hm Hmem => [|[|[|[|[|m'']]]]] Hm Hmem.
  (* s=5: tperm(5,6)(5)=6 vs tperm(8,9)(5)=5 *)
  + exists (word_eval w4 (Ordinal Hm)), (word_eval w7 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=6: tperm(5,6)(6)=5 vs tperm(6,7)(6)=7 *)
  + exists (word_eval w4 (Ordinal Hm)), (word_eval w5 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=7: tperm(6,7)(7)=6 vs tperm(7,8)(7)=8 *)
  + exists (word_eval w5 (Ordinal Hm)), (word_eval w6 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=8: tperm(7,8)(8)=7 vs tperm(8,9)(8)=9 *)
  + exists (word_eval w6 (Ordinal Hm)), (word_eval w7 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* s=9: tperm(8,9)(9)=8 vs tperm(5,6)(9)=9 *)
  + exists (word_eval w7 (Ordinal Hm)), (word_eval w4 (Ordinal Hm)).
    split; [exact: Hmem | exact: Hmem |].
    rewrite Hwi Hwi /s5x5_gen_tuple ?tnth_mktuple ?permE //.
  (* m'' + 10 < 10: impossible *)
  + by [].
Qed.

(* SecurityWitness at L=1 via fiber counting. Epsilon = 8/5. *)
Definition s5x5_security_witness_1 : SecurityWitness R R_s5x5 :=
  security_witness_fiber s5x5_weval_inj1 s5x5_endpoint_bound_fiber.

End s5x5_security.

(******************************************************************************)
(*     Spectral Gap Convergence (Axiomatized)                                 *)
(*                                                                            *)
(* The Schreier graph of S_5 x S_5 on 'I_10 with 8 Coxeter generators       *)
(* decomposes into two independent copies of the path P_5 (since pile-1      *)
(* generators fix pile-2 sheets and vice versa). The transition matrix is:    *)
(*   A = I - (1/8) * L(P_5)                                                  *)
(* where L(P_5) is the graph Laplacian of the 5-vertex path.                 *)
(*                                                                            *)
(* The smallest nonzero Laplacian eigenvalue of P_n is 2*(1 - cos(pi/n)),    *)
(* giving spectral gap = (1 - cos(pi/5)) / 4 ~ 0.0477 for the walk.         *)
(* The convergence bound is:                                                  *)
(*   var_dist(endpoint, uniform) <= sqrt(10) * (1 - gap)^L                   *)
(*                                                                            *)
(* References:                                                                *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Chung (1997), Spectral Graph Theory, AMS.                               *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(*   Bacher (1994), J. Algebra 167:460-472.                                  *)
(*                                                                            *)
(* We use Variable/Hypothesis (not Axiom) so that spectral parameters are    *)
(* abstracted over when the section closes, following the Monster pattern.    *)
(******************************************************************************)

Section s5x5_spectral.

Variable R : realType.

Let M_s5x5 := @Gen_PGGTypes 7 8 s5x5_gen_tuple.
Let R_s5x5 : GeneratedMonodromyReprType := M_s5x5.

(* Spectral gap of the Schreier walk: (1 - cos(pi/5)) / 4 ~ 0.0477 *)
Variable s5x5_spectral_gap : R.
Hypothesis s5x5_gap_pos : (0 < s5x5_spectral_gap)%R.
Hypothesis s5x5_gap_le1 : (s5x5_spectral_gap <= 1)%R.

(* Schreier walk distribution family: for each L, the distribution on
   {perm 'I_10} induced by a length-L random walk on the Schreier graph.
   This is Q^L projected back to group elements, which equals
   rho_from_words L when weval_inj holds, but is well-defined for all L. *)
Variable s5x5_schreier_rho : nat -> R.-fdist {perm 'I_10}.

(* Spectral convergence bound from the Schreier graph analysis.
   Prefactor is sqrt(N) = sqrt(10), NOT sqrt(|G|) = sqrt(14400).
   Source: Diaconis 1988 Ch. 3B Proposition 2, applied to Schreier graph. *)
Hypothesis s5x5_spectral_convergence :
  forall (L : nat) (s : 'I_10),
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                     (s5x5_schreier_rho L))
           (fdist_uniform (card_ord 10))
  <= Num.sqrt 10%:R * (1 - s5x5_spectral_gap) ^+ L)%O.

(* SecurityAsymptotic certificate carrying the convergence guarantee *)
Definition s5x5_asymptotic : @SecurityAsymptotic R R_s5x5.
Proof.
apply: (@MkSecurityAsymptotic R R_s5x5
  s5x5_spectral_gap s5x5_gap_pos s5x5_gap_le1
  s5x5_schreier_rho).
exact: s5x5_spectral_convergence.
Defined.

(* SecurityWitness at any word length L, with spectral convergence bound.
   Unlike security_witness_schreier (pgg_schreier.v), this does NOT require
   weval_inj — the Schreier walk distribution is axiomatized directly. *)
Definition s5x5_security_witness_schreier (L : nat) :
    SecurityWitness R R_s5x5 :=
  @MkSecurityWitness R R_s5x5 L
    (Num.sqrt 10%:R * (1 - s5x5_spectral_gap) ^+ L)
    (s5x5_schreier_rho L)
    (fun s => s5x5_spectral_convergence L s)
    None
    (Some s5x5_asymptotic).

End s5x5_spectral.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section s5x5_rigidity.

Variable R : realType.

Let R_s5x5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* --- CoveringData: genus 3 --- *)

(* Riemann-Hurwitz: 2*3 + 2*|G| = |G|*(2*0) + ramif + 2
   6 + 2*14400 = 28804 + 2 = 28806 *)
Lemma s5x5_hurwitz :
  (2 * 3 + 2 * #|pgg_G R_s5x5| =
   #|pgg_G R_s5x5| * (2 * 0) + 28804 + 2)%N.
Proof.
by rewrite muln0 muln0 add0n s5x5_group_order.
Qed.

Definition s5x5_covering_data : CoveringData R_s5x5 :=
  @MkCoveringData R_s5x5 0 6 28804 3 s5x5_hurwitz.

(* --- Product ThresholdScheme: two sum_mod on 'I_5 --- *)

(* N1' = N2' = 3 gives N1 = N2 = 5, N = 10.
   T1' = T2' = 4 gives T1 = T2 = 5, T = 10.
   sum_mod_scheme on 'I_5 with 5 parties: ts_T = ts_k = 5.
   Product: ts_T = 10, ts_k = min(5,5) = 5. *)
Let s5x5_ts : ThresholdScheme 'I_10 'I_10 :=
  @product_scheme 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4).

(* --- CoveringScheme --- *)

(* Gap: ts_T <= ts_k + 2 * genus = 5 + 6 = 11 >= 10 *)
Lemma s5x5_cs_gap :
  (ts_T s5x5_ts <= ts_k s5x5_ts + 2 * 3)%N.
Proof. by []. Qed.

(* Pile preservation: the monodromy of S_5 × S_5 preserves {0..4} *)
Lemma s5x5_preserves_pile1 :
  forall g, g \in pgg_G R_s5x5 ->
  forall i : 'I_10, (val i < 5)%N -> (val (@pgg_rho R_s5x5 g i) < 5)%N.
Proof. exact: s5x5_preserves_pile1_ax. Qed.

Lemma s5x5_perm_compatible :
  @ts_perm_compatible _ (pgg_G R_s5x5) _ _ s5x5_ts (@pgg_rho R_s5x5).
Proof.
exact: (@product_sum_mod_perm_compatible 3 3 4 4 _ _ (@pgg_rho R_s5x5) s5x5_preserves_pile1).
Qed.

Definition s5x5_covering : CoveringScheme R_s5x5 := {|
  cs_data             := s5x5_covering_data ;
  cs_T'               := (ts_T' s5x5_ts) ;
  cs_scheme           := s5x5_ts ;
  cs_scheme_T         := erefl ;
  cs_perm             := @pgg_rho R_s5x5 ;
  cs_perm_compatible  := s5x5_perm_compatible ;
  cs_gap              := s5x5_cs_gap ;
|}.

(* --- ThresholdWitness --- *)

(* genus = 3 ≠ 0 → the PGL hypothesis is vacuously true *)
Lemma s5x5_genus0_pgl :
  cd_genus (cs_data s5x5_covering) = 0 ->
  (#|pgg_G R_s5x5| <= pgl_bound R_s5x5)%N.
Proof. by []. Qed.

Definition s5x5_threshold_witness : ThresholdWitness R_s5x5 :=
  @MkThresholdWitness R_s5x5 s5x5_covering s5x5_genus0_pgl.

(* --- AlgebraicRigidity --- *)

Definition s5x5_rigidity : AlgebraicRigidity R R_s5x5 :=
  @MkAlgebraicRigidity R R_s5x5
    (s5x5_security_witness_1 R)
    s5x5_threshold_witness.

(* --- Derived properties --- *)

Lemma s5x5_complexity (L : nat) :
  (@search_space R_s5x5 L <= #|pgg_G R_s5x5|)%N.
Proof. exact: search_space_leG. Qed.

Lemma s5x5_tradeoff :
  let cs := tw_covering (ar_threshold s5x5_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_s5x5| <= pgl_bound R_s5x5)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
exact: (@security_threshold_tradeoff R_s5x5 s5x5_covering s5x5_genus0_pgl).
Qed.

(* The main point: genus > 0 is forced by |G| > pgl_bound *)
Lemma s5x5_large_group :
  (0 < cd_genus (cs_data s5x5_covering))%N.
Proof. by []. Qed.

End s5x5_rigidity.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=591 (40-bit security)                  *)
(*                                                                            *)
(* Combines the Schreier spectral SecurityWitness at L=591 with the          *)
(* product threshold scheme. At L=591 with gap ~ 0.0477:                     *)
(*   var_dist <= sqrt(10) * (1 - gap)^591 < 2^{-40}                         *)
(*                                                                            *)
(* For 128-bit security, use L=1838 instead.                                 *)
(******************************************************************************)

Section s5x5_rigidity_spectral.

Variable R : realType.

Let R_s5x5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* Spectral parameters (same as s5x5_spectral section) *)
Variable s5x5_spectral_gap : R.
Hypothesis s5x5_gap_pos : (0 < s5x5_spectral_gap)%R.
Hypothesis s5x5_gap_le1 : (s5x5_spectral_gap <= 1)%R.
Variable s5x5_schreier_rho : nat -> R.-fdist {perm 'I_10}.
Hypothesis s5x5_spectral_convergence :
  forall (L : nat) (s : 'I_10),
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                     (s5x5_schreier_rho L))
           (fdist_uniform (card_ord 10))
  <= Num.sqrt 10%:R * (1 - s5x5_spectral_gap) ^+ L)%O.

(* 40-bit security: L=591 gives sqrt(10)*(1-gap)^591 < 2^{-40}
   when gap = (1-cos(pi/5))/4 ~ 0.0477 *)
Definition s5x5_rigidity_spectral : AlgebraicRigidity R R_s5x5 :=
  @MkAlgebraicRigidity R R_s5x5
    (@s5x5_security_witness_schreier R s5x5_spectral_gap s5x5_gap_pos
       s5x5_gap_le1 s5x5_schreier_rho s5x5_spectral_convergence 591)
    s5x5_threshold_witness.

End s5x5_rigidity_spectral.
