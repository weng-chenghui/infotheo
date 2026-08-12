(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Kim Biased Five Card Trick Instance                                        *)
(*                                                                            *)
(* Kim & Cetinkaya's biased five card trick (arXiv:2511.05111) is the         *)
(* eps <> 0 member of the shared five-card family: the cyclic cut is biased   *)
(* with probability 1/5 - eps for no-cut and 1/5 + eps/4 for each rotation.   *)
(* The den Boer five card trick is the same family at eps = 0.                *)
(*                                                                            *)
(* The Reed-Solomon AlgebraicRigidity block that used to live here was        *)
(* retired. The five-card trick recovers a secret through the boolean fcI     *)
(* three-consecutive-hearts read, not through a Reed-Solomon code, so the     *)
(* genus-0 RS packaging was vacuous for the cyclic group of order |C_5| = 5.  *)
(*                                                                            *)
(* What remains is the search-space complexity bound:                         *)
(*   kim_complexity : search_space L <= |G|                                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound five_card_kim.
From pgg_smc Require Import five_card_family pgg_monodromy_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Biased Five-Card Family Member                                         *)
(******************************************************************************)

Section kim_family.

Variable R : realType.

(* Bias parameter and its constraints *)
Variable eps : R.
Hypothesis eps_lt : eps < 5%:R^-1.
Hypothesis eps_gt : - (4%:R * 5%:R^-1) < eps.
Hypothesis eps_spectral : (`|eps| < 4%:R / 5%:R)%R.
Let M_kim : MonodromyReprWithGeneratorType := FiveCardKim_M.

(** kim_complexity — search-space complexity bound for the Kim instance.
    Kind: main.
    @main bound: the brute-force search space over length-L words is bounded
    by the monodromy group order, specialising [search_space_leG] to the Kim
    five-card monodromy. *)
Lemma kim_complexity (L : nat) :
  (@search_space M_kim L <= #|pgg_G M_kim|)%N.
Proof. exact: search_space_leG. Qed.

End kim_family.
