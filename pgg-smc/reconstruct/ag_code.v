(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* AG Code Foundations: Linear Code from a Generator Matrix                   *)
(*                                                                            *)
(* Defines a linear code as the image of a generator (evaluation) matrix and  *)
(* derives minimum distance bounds from an axiomatized Goppa weight bound.    *)
(* This lowers the axiomatization boundary for higher-genus coverings: instead *)
(* of axiomatizing an entire ThresholdScheme, we axiomatize at the code level *)
(* (generator matrix + Goppa bound) and derive the ThresholdScheme via        *)
(* Massey's construction (ag_massey_bridge.v).                                *)
(*                                                                            *)
(*   ag_code ev      == linear code {m *m ev | m : 'rV_k} as {vspace 'rV_n} *)
(*   ag_not_trivial  == ag_code is nontrivial when ev has full row rank       *)
(*   ag_min_dist_lb  == minimum distance >= n - (k + g - 1) from Goppa bound *)
(*   ag_min_dist_ge2 == minimum distance >= 2 when k + g < n                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Code Definition from Generator Matrix                       *)
(******************************************************************************)

Section ag_code_def.

Variables (F : finFieldType) (n k : nat).
Variable ev : 'M[F]_(k, n).

(** ag_code — linear code defined as the image of the generator matrix ev.
    Kind: main.
    Why: anchors the downstream AG-code reasoning at the code (vspace) level,
         so that minimum-distance and dimension facts can be derived from the
         generator matrix without axiomatizing a full ThresholdScheme.
*)
Definition ag_code : Lcode0.t F n :=
  (linfun (mulmxr ev) @: fullv)%VS.

(** ag_code_eval — every evaluation m *m ev lies in ag_code.
    Kind: helper.
    Why: witnesses membership in the image of the generator.
    Used by: ag_not_trivial, ag_min_dist_lb (to exhibit code words).
*)
Lemma ag_code_eval (m : 'rV[F]_k) : m *m ev \in ag_code.
Proof.
apply/memv_imgP; exists m; first by apply: memvf.
by rewrite lfunE.
Qed.

(** ag_code_memP — membership in ag_code reflects existence of a message preimage.
    Kind: canonical.
*)
Lemma ag_code_memP (c : 'rV[F]_n) :
  reflect (exists m : 'rV[F]_k, c = m *m ev) (c \in ag_code).
Proof.
apply: (iffP memv_imgP).
- move=> [u _ ->]; exists u; by rewrite lfunE.
- move=> [m ->]; exists m; first by apply: memvf. by rewrite lfunE.
Qed.

(** dim_ag_code — full-rank generators give a k-dimensional code.
    Kind: main.
    Why: identifies the message space dimension with the code dimension when
         the evaluation matrix has full row rank, an essential ingredient for
         the ThresholdScheme bridge in ag_massey_bridge.v.
*)
Lemma dim_ag_code : \rank ev = k -> \dim ag_code = k.
Proof.
move=> Hrank.
have Hfree : row_free ev by rewrite -row_leq_rank Hrank.
rewrite limg_dim_eq.
  rewrite dimvf dim_matrix.
  change (1 * k = k)%N.
  by rewrite mul1n.
apply/vspaceP => v; rewrite memv_cap memv0 memvf /=.
by rewrite memv_ker lfunE mulmx_free_eq0.
Qed.

End ag_code_def.

(******************************************************************************)
(*     Section 2: Code Properties from Goppa Weight Bound                     *)
(******************************************************************************)

Section ag_code_props.

Variables (F : finFieldType) (n k : nat).
Variable ev : 'M[F]_(k, n).
Hypothesis ev_rank : \rank ev = k.
Hypothesis Hk : 0 < k.
Hypothesis Hkn : k <= n.

Variable g : nat.
Hypothesis goppa_wt :
  forall m : 'rV[F]_k, m != 0 -> n - (k + g - 1) <= wH (m *m ev).

(** ag_mulmx_inj — full-rank generator matrices are injective on message vectors.
    Kind: helper.
    Why: cancels ev on the right under the full row rank hypothesis.
    Used by: ag_mulmx_neq0 (to push nonzero messages to nonzero codewords).
*)
Lemma ag_mulmx_inj : forall m1 m2 : 'rV[F]_k,
  m1 *m ev = m2 *m ev -> m1 = m2.
Proof.
move=> m1 m2 Heq.
have Hfree : row_free ev by rewrite -row_leq_rank ev_rank.
exact: (row_free_inj Hfree Heq).
Qed.

(** ag_mulmx_neq0 — nonzero messages yield nonzero codewords.
    Kind: helper.
    Why: immediate from injectivity of ev on the message space.
    Used by: ag_not_trivial (to exhibit a nonzero code word).
*)
Lemma ag_mulmx_neq0 (m : 'rV[F]_k) : m != 0 -> m *m ev != 0.
Proof.
move=> Hm; apply/negP => /eqP Habs.
have : m = 0 by apply: ag_mulmx_inj; rewrite Habs mul0mx.
by move/eqP; rewrite (negbTE Hm).
Qed.

(** ag_not_trivial — ag_code is nontrivial under the full-rank hypothesis.
    Kind: main.
    Why: needed to apply the generic min_dist machinery from linearcode.v,
         which requires a witness that the code is not the zero code.
*)
Lemma ag_not_trivial : not_trivial (ag_code ev).
Proof.
have _ := (Hkn, goppa_wt).
apply/not_trivialP; apply/negP => /eqP H0.
have Hmem : delta_mx 0 (Ordinal Hk) *m ev \in ag_code ev by apply: ag_code_eval.
rewrite H0 memv0 in Hmem.
have Hm : (delta_mx 0 (Ordinal Hk) : 'rV[F]_k) != 0.
  (* Fallback (A002): extracting one entry from a row-vector equality
     is not a congruence over a matched head symbol; goal-level `congr`
     cannot operate on the opaque `delta_mx` / zero-vector heads. *)
  apply/negP => /eqP/(congr1 (fun m : 'rV_k => m 0 (Ordinal Hk))).
  by rewrite mxE !eqxx /= mxE => /eqP; rewrite oner_eq0.
by move: (ag_mulmx_neq0 Hm); rewrite (eqP Hmem) eqxx.
Qed.

(** ag_min_dist_lb — Goppa minimum distance bound: d >= n - (k + g - 1).
    Kind: main.
    Why: the headline minimum-distance bound for AG codes, derived directly
         from the axiomatized Goppa weight inequality, used by
         ag_massey_bridge.v to populate the ThresholdScheme.
*)
Lemma ag_min_dist_lb : n - (k + g - 1) <= min_dist ag_not_trivial.
Proof.
have [c [Hc [Hc0 HcwH]]] := min_dist_achieved ag_not_trivial.
rewrite -HcwH.
have /ag_code_memP [m Hm] := Hc.
have Hm0 : m != 0.
  apply/negP => /eqP Hm0; apply: Hc0.
  by rewrite Hm Hm0 mul0mx.
by rewrite Hm; apply: goppa_wt.
Qed.

(** ag_min_dist_ge2 — codes with k + g < n have minimum distance at least two.
    Kind: main.
    Why: a cleaner usable form of ag_min_dist_lb that matches the hypothesis
         shape of consumers needing strict positivity of d - 1.
*)
Lemma ag_min_dist_ge2 : k + g < n -> 1 < min_dist ag_not_trivial.
Proof.
move=> Hlt.
apply: leq_trans ag_min_dist_lb.
rewrite ltn_subRL.
by rewrite subnK // (leq_trans Hk) // leq_addr.
Qed.

End ag_code_props.

Arguments ag_not_trivial {F n k} ev ev_rank Hk Hkn {g} goppa_wt.
Arguments ag_min_dist_lb {F n k} ev ev_rank Hk Hkn {g} goppa_wt.
Arguments ag_min_dist_ge2 {F n k} ev ev_rank Hk Hkn {g} goppa_wt.
