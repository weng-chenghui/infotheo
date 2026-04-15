(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 Algebraic Rigidity Instance                                            *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the S_5 adjacent      *)
(* transposition RAAG (Coxeter type A_4, path graph with 4 generators).       *)
(*                                                                            *)
(* This demonstrates all algebraic rigidity parameters computed from          *)
(* a single (G, I) choice with concrete vm_compute-checkable results:         *)
(*   1. Complexity: search_space L <= |G|                                     *)
(*   2. Security (fiber): var_dist <= 6/5 at L=1 (fiber-counted, proved)     *)
(*   3. Security (spectral): L=285, eps = sqrt(5)*(1-gap)^285               *)
(*      40-bit security from axiomatized spectral gap                        *)
(*   4. Threshold: genus-0 covering from RS codes (+ PGL hypothesis)          *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_5:                                *)
(*   The 5x5 Schreier matrix with 4 adjacent transpositions is               *)
(*     A = I - (1/4)*L(P_5)                                                   *)
(*   where L(P_5) is the graph Laplacian of the 5-vertex path.               *)
(*   Smallest nonzero Laplacian eigenvalue: 2*(1-cos(pi/5)).                  *)
(*   Spectral gap = (1 - cos(pi/5)) / 2 ~ 0.0955.                           *)
(*     L = 285 gives var_dist < 2^{-40}  (40-bit security)                   *)
(*     L = 893 gives var_dist < 2^{-128} (128-bit security)                  *)
(*                                                                            *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Chung (1997), Spectral Graph Theory, AMS.                               *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(*   Bacher (1994), J. Algebra 167:460-472.                                  *)
(*                                                                            *)
(* vm_compute demonstrations:                                                 *)
(*   s5_nt_L1 : n_traces_natB 4 1 path_comm_nat = 4                          *)
(*   s5_nt_L2 : n_traces_natB 4 2 path_comm_nat = 13                         *)
(*   s5_nt_L3 : n_traces_natB 4 3 path_comm_nat = 40                         *)
(*                                                                            *)
(* Proved (not axiomatized):                                                  *)
(*   s5_security_witness_1 : SecurityWitness (fiber-counted eps=6/5)         *)
(*   s5_rigidity : AlgebraicRigidity (security + threshold)                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5 pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section s5_security.

Variable R : realType.

Let M_s5 := @Gen_PGGTypes 3 3 (path_gen_tuple 3).
Let R_s5 : GeneratedMonodromyReprType := M_s5.

Local Open Scope ring_scope.

(* Fiber-counted endpoint bound: for each sheet s in 'I_5,
   var_dist(fdistmap perm_endpoint (rho_from_words 1 path_gen_tuple_3), uniform) <= 6/5.
   Achievable(1) = {(01),(12),(23),(34)} (4 adjacent transpositions).
   Worst-case sheets s=0,4: P=(3/4,1/4,0,0,0), var_dist=6/5. *)
Lemma s5_endpoint_bound_fiber :
  forall s : 'I_5,
  (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (@rho_from_words R _ _ 1 (path_gen_tuple 3)))
           (fdist_uniform (card_ord 5)) <= 6%:R / 5%:R)%O.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans
  (@var_dist_endpoint_image_bound_unbalanced R 3 3 1 (path_gen_tuple 3)
    s5_weval_inj1 (erefl true) 2 s _)); last first.
  by rewrite /= -GRing.Theory.natrM.
have Hmem : forall (w : pgg_word (Gen_PGGTypes (path_gen_tuple 3)) 1),
    word_eval w s \in
      (fun sigma : {perm 'I_5} => sigma s) @:
        achievable (Gen_PGGTypes (path_gen_tuple 3)) 1.
  by move=> w; apply: imset_f; apply: imset_f.
pose w0 : pgg_word (Gen_PGGTypes (path_gen_tuple 3)) 1 := [tuple ord0].
pose w3 : pgg_word (Gen_PGGTypes (path_gen_tuple 3)) 1 := [tuple ord_max].
pose w1 : pgg_word (Gen_PGGTypes (path_gen_tuple 3)) 1 :=
  [tuple (Ordinal (n:=4) (m:=1) (erefl true))].
have Hw0 : @word_eval (Gen_PGGTypes (path_gen_tuple 3)) 1 w0 =
           @path_gen 3 ord0.
  rewrite /word_eval /w0 big_ord_recr /= big_ord0 mul1g.
  by rewrite (@path_gen_tupleE 3).
have Hw3 : @word_eval (Gen_PGGTypes (path_gen_tuple 3)) 1 w3 =
           @path_gen 3 ord_max.
  rewrite /word_eval /w3 big_ord_recr /= big_ord0 mul1g.
  by rewrite (@path_gen_tupleE 3).
have Hw1 : @word_eval (Gen_PGGTypes (path_gen_tuple 3)) 1 w1 =
           @path_gen 3 (Ordinal (n:=4) (m:=1) (erefl true)).
  rewrite /word_eval /w1 big_ord_recr /= big_ord0 mul1g.
  by rewrite (@path_gen_tupleE 3).
apply/card_gt1P.
case: s Hmem => [[|[|[|[|[|s]]]]] Hs] //= Hmem.
(* s=0: tperm(0,1)(0)=1 vs tperm(3,4)(0)=0 *)
- exists (word_eval w0 (Ordinal Hs)), (word_eval w3 (Ordinal Hs)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hw0 Hw3 /path_gen.
  have -> : Ordinal Hs = @path_lo 3 ord0 by apply: val_inj.
  rewrite tpermL tpermD; rewrite -?val_eqE //.
(* s=1: tperm(0,1)(1)=0 vs tperm(3,4)(1)=1 *)
- exists (word_eval w0 (Ordinal Hs)), (word_eval w3 (Ordinal Hs)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hw0 Hw3 /path_gen.
  have -> : Ordinal Hs = @path_hi 3 ord0 by apply: val_inj.
  rewrite tpermR tpermD; rewrite -?val_eqE //.
(* s=2: tperm(0,1)(2)=2 vs tperm(1,2)(2)=1 *)
- exists (word_eval w0 (Ordinal Hs)), (word_eval w1 (Ordinal Hs)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hw0 Hw1 /path_gen.
  have -> : Ordinal Hs = @path_hi 3 (Ordinal (n:=4) (m:=1) (erefl true))
    by apply: val_inj.
  rewrite tpermD; [| rewrite -?val_eqE //..].
  rewrite tpermR; rewrite -?val_eqE //.
(* s=3: tperm(0,1)(3)=3 vs tperm(3,4)(3)=4 *)
- exists (word_eval w0 (Ordinal Hs)), (word_eval w3 (Ordinal Hs)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hw0 Hw3 /path_gen.
  have -> : Ordinal Hs = @path_lo 3 ord_max by apply: val_inj.
  rewrite tpermD; [| rewrite -?val_eqE //..].
  rewrite tpermL; rewrite -?val_eqE //.
(* s=4: tperm(0,1)(4)=4 vs tperm(3,4)(4)=3 *)
- exists (word_eval w0 (Ordinal Hs)), (word_eval w3 (Ordinal Hs)).
  split; [exact: Hmem | exact: Hmem |].
  rewrite Hw0 Hw3 /path_gen.
  have -> : Ordinal Hs = @path_hi 3 ord_max by apply: val_inj.
  rewrite tpermD; [| rewrite -?val_eqE //..].
  rewrite tpermR; rewrite -?val_eqE //.
Qed.

(* SecurityWitness at L=1 via fiber counting.
   Epsilon = 6/5, much tighter than DPI bound 2*(5!-4)/5! ≈ 1.93. *)
Definition s5_security_witness_1 : SecurityWitness R R_s5 :=
  security_witness_fiber s5_weval_inj1 s5_endpoint_bound_fiber.

End s5_security.

(******************************************************************************)
(*     Spectral Gap Convergence (Axiomatized)                                 *)
(*                                                                            *)
(* The Schreier graph of S_5 on 'I_5 with 4 adjacent transpositions is       *)
(* the path graph P_5. The transition matrix is:                              *)
(*   A = I - (1/4) * L(P_5)                                                   *)
(* where L(P_5) is the graph Laplacian of the 5-vertex path.                  *)
(*                                                                            *)
(* Eigenvalues of A: 1 - (1/4)*2*(1-cos(k*pi/5)) for k=0,...,4.              *)
(* Second largest: 1 - (1-cos(pi/5))/2 ~ 0.9045.                             *)
(* Spectral gap = (1 - cos(pi/5)) / 2 ~ 0.0955.                             *)
(*                                                                            *)
(* References:                                                                *)
(*   Brouwer-Haemers (2012), Spectra of Graphs, Springer.                    *)
(*   Wilson (2004), Ann. Appl. Probab. 14(1):274-325.                        *)
(******************************************************************************)

Section s5_spectral.

Variable R : realType.

Let M_s5 := @Gen_PGGTypes 3 3 (path_gen_tuple 3).
Let R_s5 : GeneratedMonodromyReprType := M_s5.

(* Spectral gap of the Schreier walk: (1 - cos(pi/5)) / 2 ~ 0.0955 *)
Variable s5_spectral_gap : R.
Hypothesis s5_gap_pos : (0 < s5_spectral_gap)%R.
Hypothesis s5_gap_le1 : (s5_spectral_gap <= 1)%R.

(* Schreier walk distribution family *)
Variable s5_schreier_rho : nat -> R.-fdist {perm 'I_5}.

(* Spectral convergence: var_dist <= sqrt(5) * (1 - gap)^L *)
Hypothesis s5_spectral_convergence :
  forall (L : nat) (s : 'I_5),
  (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (s5_schreier_rho L))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (1 - s5_spectral_gap) ^+ L)%O.

Definition s5_asymptotic : @SecurityAsymptotic R R_s5.
Proof.
apply: (@MkSecurityAsymptotic R R_s5
  s5_spectral_gap s5_gap_pos s5_gap_le1
  s5_schreier_rho).
exact: s5_spectral_convergence.
Defined.

Definition s5_security_witness_schreier (L : nat) :
    SecurityWitness R R_s5 :=
  @MkSecurityWitness R R_s5 L
    (Num.sqrt 5%:R * (1 - s5_spectral_gap) ^+ L)
    (s5_schreier_rho L)
    (fun s => s5_spectral_convergence L s)
    None
    (Some s5_asymptotic).

End s5_spectral.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=285 (40-bit security)                  *)
(*                                                                            *)
(* sqrt(5) * (1 - gap)^285 < 2^{-40} when gap ~ 0.0955.                     *)
(* For 128-bit security, use L=893 instead.                                   *)
(******************************************************************************)

Section s5_rigidity_cryptographically_secure.

Variable R : realType.

Let R_s5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(* Threshold witness — taken as parameter to avoid duplicating
   genus-0 covering axioms (RS code, PGL bound, etc.) *)
Variable s5_tw : ThresholdWitness R_s5.

(* Spectral parameters *)
Variable s5_spectral_gap : R.
Hypothesis s5_gap_pos : (0 < s5_spectral_gap)%R.
Hypothesis s5_gap_le1 : (s5_spectral_gap <= 1)%R.
Variable s5_schreier_rho : nat -> R.-fdist {perm 'I_5}.
Hypothesis s5_spectral_convergence :
  forall (L : nat) (s : 'I_5),
  (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                     (s5_schreier_rho L))
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (1 - s5_spectral_gap) ^+ L)%O.

Definition s5_rigidity_cryptographically_secure : AlgebraicRigidity R R_s5 :=
  @MkAlgebraicRigidity R R_s5
    (@s5_security_witness_schreier R s5_spectral_gap s5_gap_pos
       s5_gap_le1 s5_schreier_rho s5_spectral_convergence 285)
    s5_tw.

End s5_rigidity_cryptographically_secure.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section s5_rigidity.

Variable R : realType.

Let R_s5 : GeneratedMonodromyReprType :=
  @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(* Group nontriviality *)
Hypothesis HG_s5 : (1 < #|pgg_G R_s5|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = 5 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_s5).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT R_s5 -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_s5 -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_s5 ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition s5_covering : CoveringScheme R_s5 :=
  genus0_covering HG_s5 qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis s5_genus0_pgl :
  (#|pgg_G R_s5| <= pgl_bound R_s5)%N.

Definition s5_threshold_witness : ThresholdWitness R_s5 :=
  @MkThresholdWitness R_s5 s5_covering (fun _ => s5_genus0_pgl).

Definition s5_rigidity : AlgebraicRigidity R R_s5 :=
  @MkAlgebraicRigidity R R_s5
    (s5_security_witness_1 R)
    s5_threshold_witness.

(* Derived properties *)

Lemma s5_complexity (L : nat) :
  (@search_space R_s5 L <= #|pgg_G R_s5|)%N.
Proof. exact: search_space_leG. Qed.

Let R_s5_raag : RAAGType := @Gen_PGGTypes 3 3 (path_gen_tuple 3).

Lemma s5_search_chain (L : nat) :
  ((@search_space R_s5_raag L <= @n_traces R_s5_raag L) &&
   (@n_traces R_s5_raag L <= 4 ^ L))%N.
Proof. exact: search_space_chain. Qed.

Lemma s5_tradeoff :
  let cs := tw_covering (ar_threshold s5_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_s5| <= pgl_bound R_s5)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_s5 s5_covering (fun _ => s5_genus0_pgl)).
Qed.

End s5_rigidity.
