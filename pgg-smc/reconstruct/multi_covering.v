(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Multi-component covers: per-component CoveringData for intransitive        *)
(* monodromy actions.                                                         *)
(*                                                                            *)
(* The original [Record CoveringData] in covering_scheme.v has a single       *)
(* (cd_genus, cd_total_ramif) tuple, plus a Hurwitz constraint that uses      *)
(* the GROUP ORDER [#|G|] rather than the cover degree. This implicitly       *)
(* models a CONNECTED GALOIS cover of degree [|G|], so for an action of       *)
(* group G on N sheets where the action is intransitive (the cover splits     *)
(* into orbits), the framework's Hurwitz formula forces the Galois-closure    *)
(* genus, not the operational per-component genus.                            *)
(*                                                                            *)
(* Concrete consequence for s5x5: the natural action of S_5 x S_5 on 10      *)
(* sheets has two orbits (the two piles, size 5 each). The honest realising  *)
(* curve is TWO disjoint Bring's curves, each of genus 4. But the framework's *)
(* Galois-closure formula with |G| = 14400 forces a SINGLE connected curve   *)
(* of genus >= 173 (Hurwitz bound: |Aut(C)| <= 84(g-1)). 173 is mathematic-  *)
(* ally true under the Galois interpretation but operationally misleading:    *)
(* it claims a curve of genus 173 underlies the protocol when in reality      *)
(* the protocol uses two separate Bring's curves at genus 4.                  *)
(*                                                                            *)
(* This file extends the framework with a multi-component representation,    *)
(* where each orbit of the monodromy action is its own [MultiComponent]:     *)
(*                                                                            *)
(*   Record MultiComponent M := {                                             *)
(*     mc_n_sheets   : nat ;        (* sheets in this component  *)          *)
(*     mc_base_genus : nat ;                                                  *)
(*     mc_n_branch   : nat ;                                                  *)
(*     mc_total_ramif: nat ;                                                  *)
(*     mc_genus      : nat ;        (* per-component, NOT Galois-closure *)   *)
(*     mc_ramif_le   : mc_n_branch <= mc_total_ramif ;                        *)
(*     mc_hurwitz    : 2*mc_genus + 2*mc_n_sheets =                           *)
(*                     mc_n_sheets * (2 * mc_base_genus) + mc_total_ramif + 2 *)
(*   }.                                                                       *)
(*                                                                            *)
(* The key change vs the original CoveringData: [mc_n_sheets] (the cover     *)
(* degree of this component) replaces [#|G|] (the group order) in the       *)
(* Hurwitz formula. This is the standard Riemann-Hurwitz for a non-Galois   *)
(* cover of degree N with arbitrary monodromy. The ratio g/N is bounded by   *)
(* the cover's branch structure, NOT by the group order.                     *)
(*                                                                            *)
(* For s5x5: each pile is a degree-5 cover with monodromy S_5, realised by   *)
(* Bring's curve at genus 4. The per-component Hurwitz: 2*4 + 2*5 = 0 + 16   *)
(* + 2 -> 18 = 18 with R = 16 (Bring's-as-degree-5-cover ramification).      *)
(* No genus 173.                                                              *)
(*                                                                            *)
(* This file does NOT replace [Record CoveringData] in covering_scheme.v.    *)
(* It is a parallel structure that demonstrates the framework's extensibility *)
(* for intransitive monodromies. A full refactor (replacing CoveringData     *)
(* with MultiCoveringData throughout) would cascade through every instance   *)
(* and is left as future work.                                               *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import covering_scheme curve_realisation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Per-component data with degree-based Hurwitz                *)
(******************************************************************************)

(** MultiComponent — Riemann-Hurwitz data for a single connected component
    of a possibly-intransitive cover. The component is a non-Galois cover
    of degree [mc_n_sheets]; the Hurwitz formula uses [mc_n_sheets] (the
    cover degree), NOT the group order [#|G|], so per-component genera
    can be small even when [#|G|] is huge.

    The record carries no monodromy-type parameter because all its fields
    are natural numbers; the connection to a specific monodromy is made
    via [MultiCoveringData] below.

    Kind: interface. *)
Record MultiComponent := MkMultiComponent {
  mc_n_sheets    : nat ;
  mc_base_genus  : nat ;
  mc_n_branch    : nat ;
  mc_total_ramif : nat ;
  mc_genus       : nat ;
  mc_ramif_le    : (mc_n_branch <= mc_total_ramif)%N ;
  mc_hurwitz     : (2 * mc_genus + 2 * mc_n_sheets =
                    mc_n_sheets * (2 * mc_base_genus) + mc_total_ramif + 2)%N ;
}.

(******************************************************************************)
(*     Section 2: Aggregate data for an N-sheet cover                         *)
(******************************************************************************)

Section multi_covering.

Variable M : MonodromyReprType.

(** MultiCoveringData — list of [MultiComponent] records, one per orbit
    of the monodromy action. The framework's [pgg_N' M].+1 sheets must
    partition across the components.
    Kind: interface. *)
Record MultiCoveringData := MkMultiCoveringData {
  mcd_components       : seq MultiComponent ;
  mcd_total_sheets_eq  : (\sum_(c <- mcd_components) mc_n_sheets c
                          = (pgg_N' M).+1)%N ;
}.

(** mcd_total_genus — sum of per-component genera. For a connected single-
    component cover this equals the single component's genus; for a multi-
    component cover this is the disjoint-union genus.
    Kind: helper.
    Why: gives a single nat invariant suitable for downstream gap-bound
    comparisons (cf. cs_gap : ts_T <= ts_k + 2 * mcd_total_genus). *)
Definition mcd_total_genus (mcd : MultiCoveringData) : nat :=
  (\sum_(c <- mcd_components mcd) mc_genus c)%N.

(** mcd_max_genus — maximum per-component genus. For a single-component
    cover this equals mcd_total_genus; for multi-component this is the
    largest individual component genus. Useful when the gap bound applies
    per-component rather than globally.
    Kind: helper. *)
Definition mcd_max_genus (mcd : MultiCoveringData) : nat :=
  \max_(c <- mcd_components mcd) mc_genus c.

End multi_covering.

Arguments MultiCoveringData M : clear implicits.
Arguments MkMultiCoveringData {M}.

(******************************************************************************)
(*     Section 3: Realisation marker for multi-component covers               *)
(******************************************************************************)

(** realised_by_multi_curve — opaque predicate asserting that a
    [MultiCoveringData] record corresponds to a real disjoint union of
    algebraic curves realising the per-component data.
    Kind: interface.
    Why: parallel to [realised_by_curve] (single-component), serves as a
    documentation hook in instance files using the multi-component
    extension. *)
Parameter realised_by_multi_curve :
  forall (M : MonodromyReprType), MultiCoveringData M -> Prop.

Arguments realised_by_multi_curve {M} mcd.
