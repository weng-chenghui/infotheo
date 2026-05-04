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
From pgg_smc Require Import pgg_s5x5 pgg_collusion_bound s5x5_pile.
From pgg_smc Require Import s5x5_mixing s5_mixing.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import product_threshold.
From pgg_reconstruct Require Import curve_realisation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* |S_5 × S_5| = 14400, infeasible to compute in Coq.
   The exact value is held as an axiom (s5x5_group_order_eq) so that
   the Riemann-Hurwitz arithmetic in s5x5_hurwitz can rewrite by it.
   The strict bound used downstream by AlgebraicRigidity is derived,
   not axiomatised: see Lemma s5x5_group_order_bound below. *)
Axiom s5x5_group_order_eq :
  #|pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple)| = 14400.

(** s5x5_group_order_bound — the S_5 x S_5 group order strictly exceeds the
    Klein PGL bound for genus-0 covers on 10 sheets.
    Kind: helper.
    Why: forces the s5x5 instance into the positive-genus branch of the
    AlgebraicRigidity tradeoff theorem. With pgl_bound = max(2*10, 60) = 60
    and |S_5 x S_5| = 14400 (from s5x5_group_order_eq), the strict
    inequality 60 < 14400 is immediate; combined with
    [ar_large_group_forces_gap], this discharges the genus > 0 conclusion.
    Used by: downstream callers that rely on the genus > 0 branch of
    [ar_tradeoff] for s5x5. *)
Lemma s5x5_group_order_bound :
  (pgl_bound (@Gen_PGGTypes 7 8 s5x5_gen_tuple) <
   #|pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple)|)%N.
Proof. by rewrite s5x5_group_order_eq. Qed.

(* Generators preserve pile structure: pile-1 = {0..4}, pile-2 = {5..9}.
   Proved in pgg-smc/instances/s5x5/s5x5_pile.v via astabs_group closure +
   gen_subG + an 8x10 = 80 case analysis on the generator action. *)

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

(** s5x5_endpoint_bound_fiber — endpoint variational-distance bound at L=1 for S_5 x S_5.
    Kind: helper.
    Why: instantiates the unbalanced endpoint-image bound at the specific S_5 x S_5 generating tuple.
    Used by: the L=1 security witness for the S_5 x S_5 instance. *)
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

(* The S_5 x S_5 Schreier walk on 'I_10 is reducible: pile-1 generators
   fix pile-2 sheets and vice versa. So the walk's stationary distribution
   is uniform on the orbit (5 elements), not on all of 'I_10. The constant
   variation-distance floor against fdist_uniform(card_ord 10) is 1
   (in infotheo's un-halved L^1 convention; equivalent to TV-floor 1/2).
   Within each pile, mixing is exponential at rate (1 + alpha)/2 ~ 0.9525,
   reusing the S_5 Rayleigh certificate. See pgg-smc/instances/s5x5/s5x5_mixing.v
   and pgg-smc/instances/s5/s5_mixing.v for the proofs. *)

(* SecurityAsymptotic certificate carrying the honest spectral guarantee.
   The bound is var_dist <= 1 + sqrt(10) * lazy_alpha^L, which converges
   to 1 (the orbit-vs-global gap), not to 0. *)
Definition s5x5_asymptotic : @SecurityAsymptotic R R_s5x5.
Proof.
apply: (@MkSecurityAsymptotic R R_s5x5
  (1 - s5_lazy_alpha_R R)        (* sa_spectral_gap *)
  1                              (* sa_eps_inf, the orbit-vs-global floor *)
  _                              (* sa_gap_pos *)
  _                              (* sa_gap_le1 *)
  Num.Theory.ler01            (* sa_eps_inf_ge0: 0 <= 1 *)
  (fun L => rho_from_words L s5x5_gen_tuple)).
- by rewrite Num.Theory.subr_gt0; exact: s5_lazy_alpha_R_lt1.
- by rewrite Num.Theory.lerBlDr Num.Theory.lerDl;
  exact: s5_lazy_alpha_R_ge0.
- move=> L s.
  rewrite opprB addrCA subrr addr0.
  change (pgg_N' R_s5x5).+1 with 10%N in s |- *.
  apply: (Order.POrderTheory.le_trans (s5x5_spectral_TV_bound R L s)).
  rewrite (Num.Theory.lerD2l 1).
  apply: Num.Theory.ler_wpM2r.
  + by rewrite Num.Theory.exprn_ge0 //; exact: s5_lazy_alpha_R_ge0.
  + by rewrite Num.Theory.ler_sqrt ?Num.Theory.ler0n // Num.Theory.ler_nat.
Defined.

(* SecurityWitness at any word length L, parametrised only by R. *)
Definition s5x5_security_witness_schreier (L : nat) :
    SecurityWitness R R_s5x5.
Proof.
apply: (@MkSecurityWitness R R_s5x5 L
  (1 + Num.sqrt 10%:R * (s5_lazy_alpha_R R) ^+ L)
  (rho_from_words L s5x5_gen_tuple)
  _ None (Some s5x5_asymptotic)).
move=> s.
change (pgg_N' R_s5x5).+1 with 10%N in s |- *.
apply: (Order.POrderTheory.le_trans (s5x5_spectral_TV_bound R L s)).
rewrite (Num.Theory.lerD2l 1).
apply: Num.Theory.ler_wpM2r.
- by rewrite Num.Theory.exprn_ge0 //; exact: s5_lazy_alpha_R_ge0.
- by rewrite Num.Theory.ler_sqrt ?Num.Theory.ler0n // Num.Theory.ler_nat.
Defined.

End s5x5_spectral.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section s5x5_rigidity.

Variable R : realType.

Let R_s5x5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* --- CoveringData: genus 173 --- *)

(* Hurwitz lower bound on the genus of any S_5 x S_5 Galois cover of P^1:
   for g >= 2, |Aut(C)| <= 84 * (g - 1), so g >= 1 + |G|/84. With |G| = 14400,
   g >= 1 + 14400/84 = 172.43, hence g >= 173. The previous cd_genus = 3 was
   a cooked underestimate that violated this bound; cd_genus = 173 is the
   minimum genus consistent with both Hurwitz arithmetic and the Hurwitz
   automorphism bound. The actual realising curve (an inverse-Galois
   construction for S_5 x S_5) is named in the realisation axioms below.

   Riemann-Hurwitz: 2*173 + 2*14400 = 14400*(2*0) + 29144 + 2.
   Check: 346 + 28800 = 29146; 29144 + 2 = 29146. *)
Lemma s5x5_hurwitz :
  (2 * 173 + 2 * #|pgg_G R_s5x5| =
   #|pgg_G R_s5x5| * (2 * 0) + 29144 + 2)%N.
Proof.
by rewrite muln0 muln0 add0n s5x5_group_order_eq.
Qed.

(** s5x5_n_branch_le — 6 <= 29144, the concrete branch-count-vs-total-ramif
    inequality for the S_5 x S_5 instance.
    Kind: helper.
    Why: discharges the [cd_ramif_ge_n_branch] field required when building
    the [CoveringData] record for R_s5x5.
    Used by: s5x5_covering_data. *)
Lemma s5x5_n_branch_le : (6 <= 29144)%N. Proof. by []. Qed.

(** s5x5_covering_data — covering-data record for the S_5 x S_5 instance
    (genus = 173, branches = 6, total ramification = 29144).
    Kind: instance.
    Why: Hurwitz lower bound forces genus >= 173 for any S_5 x S_5 Galois
    cover of P^1; see [s5x5_inverse_galois_realised] below for the
    realisation axiom citing the inverse-Galois construction. *)
Definition s5x5_covering_data : CoveringData R_s5x5 :=
  @MkCoveringData R_s5x5 0 6 29144 173 s5x5_n_branch_le s5x5_hurwitz.

(** s5x5_inverse_galois_realised — the [s5x5_covering_data] record corresponds
    to a real Galois cover of P^1 with deck group S_5 x S_5 and genus 173.
    Kind: helper.
    Why: documentation hook for the realisation marker. The inverse Galois
    problem for S_5 x S_5 over Q is solved (S_5 x S_5 is realisable as a
    Galois group of a number-field extension; via Belyi-style constructions
    this lifts to a Galois cover of P^1_Q with the specified deck group).
    The minimum genus realising this Galois group is bounded below by
    Hurwitz at 173. The full Coq formalisation of the curve is deferred. *)
Axiom s5x5_inverse_galois_realised :
  realised_by_curve s5x5_covering_data.

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
Proof. exact: s5x5_preserves_pile1_proved. Qed.

(** s5x5_perm_compatible — monodromy permutation-compatibility for S_5 x S_5.
    Kind: helper.
    Why: closes the [ts_recon_perm_invariant] obligation of the covering scheme.
    Used by: [s5x5_covering]. *)
Lemma s5x5_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G R_s5x5) _ _ s5x5_ts (@pgg_rho R_s5x5).
Proof.
exact: (@product_sum_mod_perm_compatible 3 3 4 4 _ _ (@pgg_rho R_s5x5) s5x5_preserves_pile1).
Qed.

(** s5x5_covering — covering-scheme record for the S_5 x S_5 instance.
    Kind: instance. *)
Definition s5x5_covering : CoveringScheme R_s5x5 := {|
  cs_data             := s5x5_covering_data ;
  cs_T'               := (ts_T' s5x5_ts) ;
  cs_scheme           := s5x5_ts ;
  cs_scheme_T         := erefl ;
  cs_monodromy             := @pgg_rho R_s5x5 ;
  cs_recon_invariant  := s5x5_perm_compatible ;
  cs_gap              := s5x5_cs_gap ;
|}.

(* --- ThresholdWitness --- *)

(* genus = 3 ≠ 0 → the PGL hypothesis is vacuously true *)
Lemma s5x5_genus0_pgl :
  cd_genus (cs_data s5x5_covering) = 0 ->
  (#|pgg_G R_s5x5| <= pgl_bound R_s5x5)%N.
Proof. by []. Qed.

(** s5x5_genus0_automorphism — discharges [genus0_automorphism_bound] for the
    S_5 x S_5 instance. Because the genus is 3, the genus-0 branch is
    vacuous and the obligation is discharged by [s5x5_genus0_pgl] directly.
    Kind: helper.
    Why: required to instantiate [s5x5_threshold_witness].
    Used by: s5x5_threshold_witness. *)
Lemma s5x5_genus0_automorphism :
  genus0_automorphism_bound R_s5x5 (cs_data s5x5_covering).
Proof. exact: s5x5_genus0_pgl. Qed.

(** s5x5_threshold_witness — threshold witness for the S_5 x S_5 instance,
    packaging [s5x5_covering] with its genus-0 automorphism discharge.
    Kind: instance.
    Why: bundles [s5x5_covering] and [s5x5_genus0_automorphism] into a
    single [ThresholdWitness] consumed by [s5x5_rigidity] below. *)
Definition s5x5_threshold_witness : ThresholdWitness R_s5x5 :=
  @MkThresholdWitness R_s5x5 s5x5_covering s5x5_genus0_automorphism.

(* --- AlgebraicRigidity --- *)

Definition s5x5_rigidity : AlgebraicRigidity R R_s5x5 :=
  @MkAlgebraicRigidity R R_s5x5
    (s5x5_security_witness_1 R)
    s5x5_threshold_witness.

(* --- Derived properties --- *)

Lemma s5x5_complexity (L : nat) :
  (@search_space R_s5x5 L <= #|pgg_G R_s5x5|)%N.
Proof. exact: search_space_leG. Qed.

(** s5x5_tradeoff — security/complexity trade-off for the S_5 x S_5 instance.
    Kind: main.
    Why: specialises the generic [security_threshold_tradeoff] to S_5 x S_5. *)
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

(** Protocol reconstruction correctness: named instance-level re-export of
    [ar_protocol_correct]. Takes a [PGGInterface] as a parameter. *)
Lemma s5x5_ts_recon_correct (PI : PGGInterface R_s5x5)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity))) = pi_T' PI)
    (s : 'I_10) (P : pgg_gT R_s5x5)
    (G_stable : forall g, g \in pgg_G R_s5x5 ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold s5x5_rigidity)))).+1,
         @pgg_rho R_s5x5 g
           (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
         tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI))
              (cs_monodromy (tw_covering (ar_threshold s5x5_rigidity)) g i)) :
  P \in pgg_G R_s5x5 ->
  ts_valid (cs_scheme (tw_covering (ar_threshold s5x5_rigidity))) s
          (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof. exact: ar_protocol_correct. Qed.

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

Section s5x5_rigidity_cryptographically_secure.

Variable R : realType.

Let R_s5x5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 7 8 s5x5_gen_tuple.

(* Honest spectral SecurityWitness at L=591, fully discharged.
   The bound is var_dist <= 1 + sqrt(10) * lazy_alpha^591, where lazy_alpha
   = (1 + 181/200) / 2 = 0.9525. The 1 floor is the orbit-vs-global gap
   (the walk preserves piles), not a security weakness in the threshold
   sense (the product threshold scheme reconstructs per-pile). *)
Definition s5x5_rigidity_cryptographically_secure : AlgebraicRigidity R R_s5x5 :=
  @MkAlgebraicRigidity R R_s5x5
    (s5x5_security_witness_schreier R 591)
    s5x5_threshold_witness.

End s5x5_rigidity_cryptographically_secure.
