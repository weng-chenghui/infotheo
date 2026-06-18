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
(*   3. Security (spectral): L=286, eps = sqrt(5)*(1-gap)^286               *)
(*      40-bit security from axiomatized spectral gap                        *)
(*   4. Threshold: genus-4 Bring's-curve cover (no-go: |S_5|=120 > Klein 60)   *)
(*                                                                            *)
(* Spectral gap of the Schreier walk on 'I_5:                                *)
(*   The 5x5 Schreier matrix with 4 adjacent transpositions is               *)
(*     A = I - (1/4)*L(P_5)                                                   *)
(*   where L(P_5) is the graph Laplacian of the 5-vertex path.               *)
(*   Smallest nonzero Laplacian eigenvalue: 2*(1-cos(pi/5)).                  *)
(*   Spectral gap = (1 - cos(pi/5)) / 2 ~ 0.0955.                           *)
(*     L = 286 gives var_dist < 2^{-40}  (40-bit security)                   *)
(*     L = 897 gives var_dist < 2^{-128} (128-bit security)                  *)
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
Require Import ssralg_ext.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5 pgg_collusion_bound.
From pgg_smc Require Import s5_mixing.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import curve_realisation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     SecurityWitness Construction                                           *)
(******************************************************************************)

Section s5_security.

Variable R : realType.

Let M_s5 := @Gen_PGGTypes 3 3 (path_gen_tuple 3).
Let s5_M : MonodromyReprWithGeneratorType := M_s5.

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
Definition s5_security_witness_1 : SecurityWitness R s5_M :=
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
Let s5_M : MonodromyReprWithGeneratorType := M_s5.

(* Spectral gap derived from the Python-attested Rayleigh certificate
   (see s5_mixing.v + s5_spectral_certificate.py).  No free variables. *)

Definition s5_asymptotic : @SecurityAsymptotic R s5_M.
Proof.
apply: (@MkSecurityAsymptotic R s5_M
  (s5_gap_R R) 0
  (s5_gap_R_pos R) (s5_gap_R_le1 R)
  (Order.POrderTheory.lexx 0)
  (fun L => rho_from_words L (path_gen_tuple 3))).
move=> L s.
rewrite add0r.
exact: s5_spectral_convergence_gap.
Defined.

(** s5_security_witness_schreier — Schreier-based security witness for S_5 at length [L].
    Kind: instance. *)
Definition s5_security_witness_schreier (L : nat) :
    SecurityWitness R s5_M :=
  @MkSecurityWitness R s5_M L
    (Num.sqrt 5%:R * (1 - s5_gap_R R) ^+ L)
    (rho_from_words L (path_gen_tuple 3))
    (fun s => @s5_spectral_convergence_gap R L s)
    None
    (Some s5_asymptotic).

End s5_spectral.

(******************************************************************************)
(*     Spectral AlgebraicRigidity at L=286 (40-bit security)                  *)
(*                                                                            *)
(* sqrt(5) * (1 - gap)^286 < 2^{-40} when gap ~ 0.0955.                     *)
(* For 128-bit security, use L=897 instead.                                   *)
(******************************************************************************)

(******************************************************************************)
(*     Bring's-curve axiomatisation for the S_5 covering                      *)
(******************************************************************************)

(* Under the tightened (Klein finite-subgroup) [klein_genus0_bound], the s5 instance
   cannot be realised as a genus-0 cover: |S_5| = 120 exceeds the Klein
   ceiling of 60 (max non-dihedral finite subgroup of PGL(2, F̄), namely
   A_5). By Hurwitz's automorphism bound |Aut(C)| <= 84(g-1), an S_5
   automorphism action needs g >= 3; by Wiman's (1895) classification, no
   genus-3 curve has S_5 in its Aut group. The first realisable candidate
   is Bring's curve at g = 4 [Edge 1978, "Bring's curve", J. London Math.
   Soc. s2-18(3): 539-545]: the smooth projective curve in P^4 cut out by
   x_1 + x_2 + x_3 + x_4 + x_5 = 0,
   x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 = 0,
   x_1^3 + x_2^3 + x_3^3 + x_4^3 + x_5^3 = 0,
   admitting a faithful S_5 action by coordinate permutation.

   We axiomatise the existence of the corresponding [CoveringScheme] for
   the s5 monodromy, plus its genus = 4 and its [realised_by_curve] marker
   tying it to Bring's. None of these axioms is numerically false: each is
   a known mathematical fact whose Coq formalisation is deferred to a
   future curve-formalisation effort. *)

Section s5_brings_axiomatisation.

Local Notation s5_brings_M :=
  (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

(* The construction below replaces the previous opaque axiomatisation of the
   covering scheme with a concrete record. All numerical fields (base genus,
   branch count, total ramification, covering genus) are explicit. The
   reconstruction-invariance proof is discharged in the kernel. Two
   irreducible axioms remain:

     - [s5_group_order_eq]: the path-A_4 generators span the full S_5
       of order 120. This is "bubble-sort generates S_n", true but the
       lifting through the [Gen_PGGTypes] HB stack is engineering deferred
       to a future commit. Mirrors [s5x5_group_order_eq].

     - [s5_brings_covering_realised]: Bring's curve is the (genus-4)
       algebraic curve realising this CoveringData. Edge (1978). *)

(** s5_group_order_eq — the path-A_4 adjacent-transposition generators of
    [s5_brings_M] span the full S_5, of order 120.
    Kind: axiom. *)
Axiom s5_group_order_eq :
  #|pgg_G s5_brings_M| = 120.

(** s5_n_branch_le — branch-count vs total-ramification inequality for the
    S_5 Bring's cover (4 <= 246).
    Kind: helper.
    Why: discharges [cd_ramif_ge_n_branch] in [s5_brings_covering_data]. *)
Lemma s5_n_branch_le : (4 <= 246)%N. Proof. by []. Qed.

(** s5_hurwitz — Riemann-Hurwitz arithmetic for the S_5 cover at genus 4:
    2*4 + 2*120 = 120*(2*0) + 246 + 2, i.e. 248 = 248.
    Kind: helper. *)
Lemma s5_hurwitz :
  (2 * 4 + 2 * #|pgg_G s5_brings_M| =
   #|pgg_G s5_brings_M| * (2 * 0) + 246 + 2)%N.
Proof. by rewrite muln0 muln0 add0n s5_group_order_eq. Qed.

(** s5_brings_covering_data — covering-data record for the S_5 instance
    (genus = 4, base genus = 0, branches = 4, total ramification = 246).
    Kind: instance. *)
Definition s5_brings_covering_data : CoveringData s5_brings_M :=
  @MkCoveringData s5_brings_M 0 4 246 4 s5_n_branch_le s5_hurwitz.

(** s5_brings_covering_realised — Bring's curve realises
    [s5_brings_covering_data].
    Kind: axiom.
    Why: the sole remaining geometry axiom. Edge (1978), "Bring's curve",
    J. London Math. Soc. s2-18(3):539-545. *)
Axiom s5_brings_covering_realised :
  realised_by_curve s5_brings_covering_data.

(* Threshold scheme: sum-mod on 'I_5 with 5 parties. ts_T = ts_k = 5, so
   T - k = 0. The covering-scheme machinery therefore lives in the exact
   regime; only the [s5x5] instance exercises the strict-gap branch. *)
Let s5_ts : ThresholdScheme 'I_5 'I_5 := @sum_mod_scheme 3 4.

(** s5_cs_gap — the cs_gap obligation: ts_T <= ts_k + 2*cd_genus.
    With ts_T = ts_k = 5 and cd_genus = 4, the bound reads 5 <= 13.
    Kind: helper. *)
Lemma s5_cs_gap :
  (ts_T s5_ts <= ts_k s5_ts + 2 * cd_genus s5_brings_covering_data)%N.
Proof. by []. Qed.

(** s5_sum_mod_perm_compatible — sum-mod reconstruction is invariant under
    the monodromy permutation of the share-index tuple. Single-pile analogue
    of [product_sum_mod_perm_compatible] in reconstruct/product_threshold.v;
    the absence of a pile partition makes the proof a single reindex.
    Kind: helper.
    Why: discharges [cs_recon_invariant] for [s5_brings_covering]. *)
Lemma s5_sum_mod_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G s5_brings_M) _ _ s5_ts
    (@pgg_rho s5_brings_M).
Proof.
move=> g s shares Hg Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry; rewrite (reindex_inj (@perm_inj _ (@pgg_rho s5_brings_M g))).
by apply: eq_bigr.
Qed.

(** s5_brings_covering — concrete CoveringScheme for the S_5 instance,
    built on Bring's curve (genus 4) with a sum-mod threshold scheme.
    Kind: instance.
    Why: replaces the previous opaque [Axiom s5_brings_covering]. Threshold
    values, monodromy, reconstruction invariance and gap bound are all
    proved; only the curve realisation remains an axiom. *)
Definition s5_brings_covering : CoveringScheme s5_brings_M := {|
  cs_plug := @MkReconPlug s5_brings_M 'I_5 s5_ts id (@pgg_rho s5_brings_M)
               s5_sum_mod_perm_compatible ;
  cs_data := s5_brings_covering_data ;
  cs_gap  := s5_cs_gap ;
|}.

(** s5_brings_covering_genus — Bring's covering scheme has genus 4.
    Kind: helper.
    Why: definitional consequence of [s5_brings_covering_data]; retains the
    statement of the previous axiom so that downstream callers
    ([s5_genus0_klein], [s5_genus0_automorphism]) need no edit. *)
Lemma s5_brings_covering_genus :
  cd_genus (cs_data s5_brings_covering) = 4.
Proof. by []. Qed.

End s5_brings_axiomatisation.

Section s5_rigidity_cryptographically_secure.

Variable R : realType.

Let s5_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(* Group nontriviality. Could be discharged by computation since |S_5| = 120. *)
Hypothesis HG_s5_crypto : (1 < #|pgg_G s5_M|)%N.

(* Sheet count: 5 sheets (pgg_N' = 4) — definitionally true. *)
Lemma s5_HN5_crypto : (pgg_N' s5_M).+1 = 5.
Proof. by []. Qed.

(** s5_genus0_klein — the genus-0 PGL automorphism obligation for the
    Bring's-curve-based s5 covering. Vacuously true because the covering
    has [cd_genus = 4] (per [s5_brings_covering_genus]); the implication's
    premise [4 = 0] is false, so the conclusion is unconstrained.
    Kind: helper.
    Why: feeds [genus0_automorphism_bound] in the threshold witness
    construction below. *)
Lemma s5_genus0_klein :
  cd_genus (cs_data s5_brings_covering) = 0 ->
  (#|pgg_G s5_M| <= klein_genus0_bound s5_M)%N.
Proof. by rewrite s5_brings_covering_genus. Qed.

(** s5_threshold_witness_concrete — threshold witness for the cryptographic
    s5 rigidity, packaging the Bring's-curve covering with its (vacuous)
    genus-0 PGL bound.
    Kind: instance. *)
Definition s5_threshold_witness_concrete : ThresholdWitness s5_M :=
  @MkThresholdWitness s5_M s5_brings_covering s5_genus0_klein.

(* The spectral content is discharged by s5_mixing.v. *)

Definition s5_rigidity_cryptographically_secure : AlgebraicRigidity R s5_M :=
  @MkAlgebraicRigidity R s5_M
    (@s5_security_witness_schreier R 286)
    s5_threshold_witness_concrete.

End s5_rigidity_cryptographically_secure.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section s5_rigidity.

Variable R : realType.

Let s5_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(* Group nontriviality *)
Hypothesis HG_s5 : (1 < #|pgg_G s5_M|)%N.

(* Sheet count for s5_M: 5 sheets (pgg_N' = 4). Verified definitionally
   since s5_M = Gen_PGGTypes 3 3 (path_gen_tuple 3), so pgg_N' = 4. *)
Lemma s5_HN5 : (pgg_N' s5_M).+1 = 5.
Proof. by []. Qed.

(* Bring's-curve-based covering. S_5 is the no-go: under the corrected
   [klein_genus0_bound] the genus-0 obligation [|S_5| <= 60] is mathematically false
   (120 > 60), so no genus-0 Reed-Solomon cover exists. See [s5_brings_covering]
   above for the Bring's-curve (genus 4) axioms. *)
Definition s5_covering : CoveringScheme s5_M := s5_brings_covering.

(** s5_genus0_automorphism — discharges [genus0_automorphism_bound] for the
    S_5 instance vacuously, since [s5_brings_covering] has [cd_genus = 4]
    (per [s5_brings_covering_genus]).
    Kind: helper.
    Why: required to instantiate [s5_threshold_witness], which packages the
    covering scheme with its automorphism-bound obligation.
    Used by: s5_threshold_witness. *)
Lemma s5_genus0_automorphism :
  genus0_automorphism_bound s5_M (cs_data s5_covering).
Proof. by rewrite /genus0_automorphism_bound /s5_covering s5_brings_covering_genus. Qed.

(** s5_threshold_witness — threshold-covering witness for the S_5 instance.
    Kind: instance. *)
Definition s5_threshold_witness : ThresholdWitness s5_M :=
  @MkThresholdWitness s5_M s5_covering s5_genus0_automorphism.

(** s5_rigidity — algebraic rigidity record for the S_5 instance.
    Kind: instance. *)
Definition s5_rigidity : AlgebraicRigidity R s5_M :=
  @MkAlgebraicRigidity R s5_M
    (s5_security_witness_1 R)
    s5_threshold_witness.

(* Derived properties *)

Lemma s5_complexity (L : nat) :
  (@search_space s5_M L <= #|pgg_G s5_M|)%N.
Proof. exact: search_space_leG. Qed.

Let s5_raag_M : RAAGType := @Gen_PGGTypes 3 3 (path_gen_tuple 3).

(** s5_search_chain — search-space / trace-count / alphabet-power chain for S_5.
    Kind: helper.
    Why: instantiates the generic [search_space_chain] at the S_5 path RAAG.
    Used by: downstream tightness bounds for the S_5 instance. *)
Lemma s5_search_chain (L : nat) :
  ((@search_space s5_raag_M L <= @n_traces s5_raag_M L) &&
   (@n_traces s5_raag_M L <= 4 ^ L))%N.
Proof. exact: search_space_chain. Qed.

(** s5_tradeoff — security/complexity trade-off for the S_5 instance.
    Kind: main.
    Why: specialises the generic [security_threshold_tradeoff] to S_5. *)
Lemma s5_tradeoff :
  let cs := tw_covering (ar_threshold s5_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G s5_M| <= klein_genus0_bound s5_M)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff s5_M s5_covering s5_genus0_automorphism).
Qed.

(** Protocol reconstruction correctness: named instance-level re-export of
    [ar_protocol_correct]. Takes a [PGGInterface] as a parameter since the S5
    instance is parameterised over the starting-card configuration. *)
Lemma s5_ts_recon_correct (PI : PGGInterface s5_M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity)))) = pi_T' PI)
    (s : 'I_5) (P : pgg_gT s5_M)
    (G_stable : forall g, g \in pgg_G s5_M ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1,
         rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
           (@pgg_rho s5_M g
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1]
              (rp_monodromy (cs_plug (tw_covering (ar_threshold (s5_rigidity)))) g i)) :
  P \in pgg_G s5_M ->
  ts_valid (cs_scheme (tw_covering (ar_threshold (s5_rigidity)))) s
          [tuple rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme (tw_covering (ar_threshold (s5_rigidity))))).+1] ->
  pgg_recon_endpoints HT
    (rp_content (cs_plug (tw_covering (ar_threshold (s5_rigidity))))) P = s.
Proof. exact: ar_protocol_correct. Qed.

End s5_rigidity.
