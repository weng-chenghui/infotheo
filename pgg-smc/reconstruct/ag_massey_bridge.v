(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* AG-Massey Bridge: ThresholdScheme from AG Codes via Massey's Construction *)
(*                                                                            *)
(* Connects AG codes (ag_code.v) to Massey's secret sharing (massey.v),      *)
(* yielding a concrete ThresholdScheme for higher-genus coverings.            *)
(* The gap bound ts_T <= ts_k + 2g is proved from the code parameters.       *)
(*                                                                            *)
(*   ag_massey         == ThresholdScheme F F from AG code via Massey         *)
(*   ag_genus_scheme   == ThresholdScheme 'I_N 'I_N via transport            *)
(*   ag_massey_gap     == ts_T ag_massey <= ts_k ag_massey + 2 * g           *)
(*   ag_genus_gap      == gap bound transported to 'I_N                      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework massey
  rs_massey_bridge ag_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: AG Code -> Massey ThresholdScheme + Gap + Transport         *)
(******************************************************************************)

Section ag_massey_sect.

Variable F : finFieldType.
Variable n'' : nat.
Let n := n''.+2.
Variables (k g : nat).
Variable ev : 'M[F]_(k, n).

Hypothesis ev_rank : \rank ev = k.
Hypothesis Hk : 0 < k.
Hypothesis Hkn : k <= n.
Hypothesis Hkg : g < k.
Hypothesis Hkgn : k + g < n.
Hypothesis goppa_wt :
  forall m : 'rV[F]_k, m != 0 -> n - (k + g - 1) <= wH (m *m ev).

(* d_perp' such that d_perp = d_perp'.+2 = (k - g).+1.
   Since g < k, we have k - g >= 1, so (k - g).-1.+2 = (k - g).+1. *)
Let d_perp' := (k - g).-1.

Hypothesis ag_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < d_perp'.+2 ->
    exists c : 'rV[F]_n, c \in ag_code ev /\ vproj c S = vproj target S.

Let C_nt := ag_not_trivial ev ev_rank Hk Hkn goppa_wt.
Let Hd2 := ag_min_dist_ge2 ev ev_rank Hk Hkn goppa_wt Hkgn.

(** ag_massey — ThresholdScheme obtained from an AG code via Massey's construction.
    Kind: main.
    Why: wires the code-level axiomatization (generator matrix plus Goppa bound)
         into the ThresholdScheme interface that downstream covering proofs
         consume, lowering the axiomatization boundary versus postulating a
         ThresholdScheme directly.
*)
Definition ag_massey : ThresholdScheme F F :=
  massey_scheme C_nt Hd2 ag_priv_surj.

(* d_perp'.+2 = (k - g).+1 when g < k *)
Lemma d_perp_eq : d_perp'.+2 = (k - g).+1.
Proof. by rewrite prednK // subn_gt0. Qed.

(* ts_T = n'' + 1 = n - 1, ts_k = d_perp' + 1 = k - g.
   Need: n - 1 <= k - g + 2g = k + g. From Hparam: n <= k + g + 1. *)
Hypothesis Hparam : n <= k + g + 1.

(** ag_massey_gap — ts_T is at most ts_k + 2 * g for the AG-Massey scheme.
    Kind: main.
    Why: the headline privacy/recovery gap for higher-genus codes, showing how
         the genus surcharge 2g rides on top of the privacy threshold.
*)
Lemma ag_massey_gap : ts_T ag_massey <= ts_k ag_massey + 2 * g.
Proof.
rewrite /ts_T /ts_k /= prednK ?subn_gt0 //.
rewrite mulSn mul1n addnA subnK; last exact: ltnW.
by have H := Hparam; rewrite addn1 in H.
Qed.

(* Transport to 'I_N *)
Variable N : nat.
Hypothesis HN : N = #|F|.

(* Bijection between 'I_N and F *)
Let ag_toF (x : 'I_N) : F := enum_val (cast_ord HN x).
Let ag_ofF (x : F) : 'I_N := cast_ord (esym HN) (enum_rank x).

Let ag_ofFK : cancel ag_ofF ag_toF.
Proof. by move=> x; rewrite /ag_ofF /ag_toF cast_ordKV enum_rankK. Qed.

Let ag_toFK : cancel ag_toF ag_ofF.
Proof. by move=> x; rewrite /ag_toF /ag_ofF enum_valK cast_ordK. Qed.

(** ag_genus_scheme — AG-Massey scheme transported along the F-to-'I_N bijection.
    Kind: main.
    Why: presents the genus-aware scheme on the neutral ordinal domain that
         other parts of pgg-smc use for sharing, avoiding per-consumer F casts.
*)
Definition ag_genus_scheme : ThresholdScheme 'I_N 'I_N :=
  transport_scheme ag_toFK ag_ofFK ag_massey.

(** ag_genus_gap — gap bound transported along the bijection.
    Kind: main.
    Why: exposes the same ts_T <= ts_k + 2 * g estimate on 'I_N, matching the
         interface shape expected by downstream covering proofs.
*)
Lemma ag_genus_gap :
  ts_T ag_genus_scheme <= ts_k ag_genus_scheme + 2 * g.
Proof. exact: ag_massey_gap. Qed.

End ag_massey_sect.
