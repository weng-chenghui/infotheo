(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Curve realisation: opaque interface for "this CoveringData comes from a    *)
(* real algebraic curve".                                                      *)
(*                                                                            *)
(* The framework's [Record CoveringData] (covering_scheme.v) constrains only  *)
(* the natural-number arithmetic of Riemann-Hurwitz: it does NOT verify that  *)
(* a real algebraic curve realises the chosen genus and ramification data.    *)
(* In principle, any (cd_base_genus, cd_n_branch, cd_total_ramif, cd_genus)   *)
(* tuple satisfying the Hurwitz identity yields a valid record, regardless    *)
(* of whether such a curve actually exists.                                   *)
(*                                                                            *)
(* This file provides an opaque [realised_by_curve] predicate that instances  *)
(* can use to explicitly claim "this CoveringData corresponds to a real       *)
(* curve". The predicate is a [Parameter]: it is never unfolded, never        *)
(* proved internally, and never used in tactics. Its sole role is to serve    *)
(* as a documentation hook in instance files.                                 *)
(*                                                                            *)
(* Usage pattern, in an instance file, after constructing s5_covering_data    *)
(* with cd_genus = 4 and cd_total_ramif = 246 satisfying Hurwitz:              *)
(*                                                                            *)
(*   Axiom s5_data_realises_brings :                                          *)
(*     realised_by_curve s5_covering_data.                                    *)
(*                                                                            *)
(* The Axiom names Bring's curve [Edge 1978, "Bring's curve", J. London       *)
(* Math. Soc.]: the smooth projective curve x_1 + x_2 + x_3 + x_4 + x_5 = 0,  *)
(* x_1^2 + ... + x_5^2 = 0, x_1^3 + ... + x_5^3 = 0 in P^4, of genus 4 with a *)
(* faithful action of S_5 by coordinate permutation.                          *)
(*                                                                            *)
(* The Axiom is mathematically true: Bring's curve is a well-known            *)
(* algebraic-geometry object, and the cited paper provides the construction. *)
(* The Coq-level proof is deferred (real algebraic geometry formalisation is *)
(* a research-scale project), but the assumption is grounded in published    *)
(* mathematics, not in a logical loophole.                                    *)
(*                                                                            *)
(* Compare with the OLD pattern (now rejected): writing                        *)
(*   Hypothesis s5_genus0_pgl : #|S_5| <= pgl_bound R_s5.                     *)
(* under the corrected pgl_bound, this evaluates to 120 <= 60, which is       *)
(* literally false. Hypothesizing it does not save it; the proposition has    *)
(* no model. The realised_by_curve approach replaces this falsity with the    *)
(* mathematically-true (but not formalised) claim that a specific real curve  *)
(* exists.                                                                    *)
(*                                                                            *)
(* Discharging realised_by_curve in the future:                                *)
(*   When a real curve formalisation lands (e.g. Bring's curve in Coq), the   *)
(*   instance's Axiom can be replaced by a Lemma proving                       *)
(*   realised_by_curve cd from the curve construction. Each instance is       *)
(*   independently discharged; no global retrofit is needed.                   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: The realisation predicate                                   *)
(******************************************************************************)

(** realised_by_curve — opaque predicate asserting that a [CoveringData] record
    corresponds to a real algebraic curve realising its (genus, ramification)
    data. Never unfolded or used in tactics; serves as a documentation hook.
    Kind: interface. *)
Parameter realised_by_curve :
  forall (M : MonodromyReprType), CoveringData M -> Prop.

Arguments realised_by_curve {M} cd.

(******************************************************************************)
(*     Section 2: Helper for bundling realisation with a CoveringData         *)
(******************************************************************************)

(** RealisedCoveringData — packages a [CoveringData] with its realisation
    witness. Optional convenience wrapper for instance files; existing
    constructions can pass [cd] and [realised_by_curve cd] separately.
    Kind: interface. *)
Record RealisedCoveringData (M : MonodromyReprType) := MkRealisedCoveringData {
  rcd_data     : CoveringData M ;
  rcd_realised : realised_by_curve rcd_data ;
}.

Arguments rcd_data {M} _.
Arguments rcd_realised {M} _.
