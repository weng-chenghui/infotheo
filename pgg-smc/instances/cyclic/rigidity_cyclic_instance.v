(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Cyclic Group (N-Cycle) Algebraic Rigidity Instance                         *)
(*                                                                            *)
(* Constructs a concrete AlgebraicRigidity instance for the cyclic group      *)
(* Z/NZ acting on N sheets via the canonical N-cycle permutation              *)
(* (0 1 2 ... N-1).                                                           *)
(*                                                                            *)
(* This is the simplest instance with a single generator (Tg = 1), L = 1.    *)
(* The marginal bound is proved via var_dist_endpoint_weval_inj (DPI bound).  *)
(*                                                                            *)
(* Parameters:                                                                *)
(*   Tg = 1 (one generator: the N-cycle), N = n+2 (sheets), L = 1            *)
(*   epsilon = 2 * (N - 1) / N  (via security_witness_endpoint_inj)           *)
(*                                                                            *)
(* The direct endpoint bound uses perm_endpoint injectivity on achievable(1),       *)
(* which is trivial for Tg=1 (singleton achievable set).                     *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   ncycle_sigmas_inj : generator tuple is injective (trivial, Tg=1)        *)
(*   ncycle_weval_inj1 : word-eval injectivity at L=1                        *)
(*   ncycle_security_witness_direct_1 : ShuffleMarginalBound (endpoint_inj)  *)
(*   ncycle_rigidity : AlgebraicRigidity (security + threshold)              *)
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
                            pgg_collusion_bound pgg_abelian.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     ShuffleMarginalBound Construction                                      *)
(******************************************************************************)

Section ncycle_security.

Variable R : realType.
Variable n : nat.

(* Build as Gen_PGGTypes for compatibility with security_witness_endpoint_inj *)
Let ncycle_sigs := cyclic_sigmas (ncycle n).
Let M_ncycle := @Gen_PGGTypes 0 n ncycle_sigs.
Let R_ncycle : MonodromyReprWithGeneratorType := M_ncycle.

(* Generator tuple injectivity: trivial for Tg = 1 (singleton domain) *)
Lemma ncycle_sigmas_inj :
  injective (fun i : 'I_1 => tnth ncycle_sigs i).
Proof. by move=> i j _; rewrite (ord1 i) (ord1 j). Qed.

(* Word-eval injectivity at L=1 *)
Lemma ncycle_weval_inj1 : @weval_inj M_ncycle 1.
Proof. exact: gen_inj_weval_inj1 ncycle_sigmas_inj. Qed.

(* Direct endpoint ShuffleMarginalBound at L=1.
   Epsilon = 2*(N-1)/N, tighter than DPI bound 2*(N!-1)/N!.
   Proof: Tg=1, L=1, achievable has 1 element → perm_endpoint trivially injective. *)
Lemma ncycle_perm_endpoint_inj1 :
  forall s : 'I_(n.+2),
  {in @achievable M_ncycle 1 &,
   injective (fun sigma : {perm 'I_(n.+2)} => sigma s)}.
Proof.
(* achievable(1) for Tg=1 has exactly 1 element → perm_endpoint trivially injective *)
move=> s x y Hx Hy _.
suff : (#|@achievable M_ncycle 1| <= 1)%N by move/card_le1_eqP; apply.
have -> : #|@achievable M_ncycle 1| = @search_space M_ncycle 1 by [].
rewrite (weval_inj_search_space ncycle_weval_inj1).
by rewrite exp1n.
Qed.

(** ncycle_security_witness_direct_1 — the direct endpoint marginal bound of
    the N-cycle at word length 1.
    @intent: security_witness_endpoint_inj at the single N-cycle generator,
    word length 1 and the endpoint-injectivity proof.
    Naming: intentional; the instance prefix, the migrated constructor family
    security_witness, the direct route and the word length 1 each contribute
    a component, and no canonical MathComp suffix denotes the combination. *)
Definition ncycle_security_witness_direct_1 : ShuffleMarginalBound R R_ncycle :=
  security_witness_endpoint_inj R ncycle_weval_inj1 ncycle_perm_endpoint_inj1.

End ncycle_security.

(******************************************************************************)
(*     AlgebraicRigidity Instance                                             *)
(******************************************************************************)

Section ncycle_rigidity.

Variable R : realType.
Variable n : nat.

Let ncycle_sigs := cyclic_sigmas (ncycle n).
Let R_ncycle : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 0 n ncycle_sigs.

(* Group nontriviality *)
Hypothesis HG_ncycle : (1 < #|pgg_G R_ncycle|)%N.

(* Field parameters for RS code: F = GF(q^m') with |F| = N = n+2 *)
Variables (q m' : nat).
Hypothesis primeq : prime q.
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.
Hypothesis HN : (pgg_N' R_ncycle).+1 = #|GF m' primeq|.

(* Code automorphism: monodromy action on RS code coordinates *)
Variable sigma_code : pgg_gT R_ncycle -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_ncycle -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_ncycle ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).

(* Genus-0 covering scheme constructed from RS codes *)
Definition ncycle_covering : CoveringScheme R_ncycle :=
  genus0_covering HG_ncycle qn an HN sigma_fix0 code_auto.

(* PGL bound hypothesis *)
Hypothesis ncycle_genus0_klein :
  (#|pgg_G R_ncycle| <= klein_genus0_bound R_ncycle)%N.

Definition ncycle_threshold_witness : ThresholdWitness R_ncycle :=
  @MkThresholdWitness R_ncycle ncycle_covering (fun _ => ncycle_genus0_klein).

(** ncycle_rigidity — the AlgebraicRigidity value of the N-cycle instance.
    @intent: MkAlgebraicRigidity at the certificate-free bundle of
    ncycle_security_witness_direct_1 and ncycle_threshold_witness. *)
Definition ncycle_rigidity : AlgebraicRigidity R R_ncycle :=
  @MkAlgebraicRigidity R R_ncycle
    (shuffle_bundle_of_bound (ncycle_security_witness_direct_1 R n))
    ncycle_threshold_witness.

(* Derived properties *)

Lemma ncycle_complexity (L : nat) :
  (@search_space R_ncycle L <= #|pgg_G R_ncycle|)%N.
Proof. exact: search_space_leG. Qed.

Lemma ncycle_tradeoff :
  let cs := tw_covering (ar_threshold ncycle_rigidity) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_ncycle| <= klein_genus0_bound R_ncycle)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof.
move=> /=.
exact: (@security_threshold_tradeoff R_ncycle ncycle_covering
                                     (fun _ => ncycle_genus0_klein)).
Qed.

End ncycle_rigidity.
