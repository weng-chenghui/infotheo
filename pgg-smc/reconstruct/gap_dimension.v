(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Gap-to-Dimension Window                                                    *)
(*                                                                            *)
(* The arithmetic necessary condition behind early rejection of infeasible    *)
(* covering-scheme parameters: a strict threshold gap forces the underlying   *)
(* AG-code dimension into the band 1 < D < n-1.                               *)
(*                                                                            *)
(* Framework reading (reconstruct/ag_massey_bridge.v): for the AG-Massey       *)
(* scheme on a length-n code of dimension D = k and genus g, ts_T = n-1 and    *)
(* ts_k = k-g. The section constraints g < k and k+g < n together with the     *)
(* gap bound n <= k+g+1 pin n = k+g+1, so a strict gap ts_k < ts_T equals 2g.  *)
(* This file isolates the resulting dimension window as reusable nat           *)
(* arithmetic; the invariant-submodule profiler and the cs_gap_feasible gate   *)
(* intersect this band with the available invariant dimensions to reject       *)
(* mathematically impossible instances before any code is constructed.        *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** gap_dim_window — a strict threshold gap forces the code-dimension band.
    Kind: main.
    What: under the AG-Massey relations ts_T = n-1, ts_k = k-g and code
          dimension D = k, with the section constraints g < k, k+g < n and the
          gap bound n <= k+g+1, a strict gap k-g < n-1 forces 0 < g, 1 < k and
          k < n-1, i.e. D lies strictly inside the open band (1, n-1).
    Why: the "required dimensions" half of early feasibility rejection; the
         invariant-submodule profiler (invariant_profiler.v) intersects this
         band with the available secret-encoding invariant dimensions, and an
         empty intersection rejects the instance parameters as impossible.
*)
Lemma gap_dim_window (n k g : nat) :
  g < k -> k + g < n -> n <= k + g + 1 ->
  k - g < n - 1 ->
  [/\ 0 < g, 1 < k & k < n - 1].
Proof.
move=> gk kgn nkg1 gap.
have nE : n = k + g + 1.
  by apply/eqP; rewrite eqn_leq nkg1 /= addn1.
have g_pos : 0 < g.
  rewrite lt0n; apply/eqP => g0.
  by move: gap; rewrite nE g0 addnK subn0 addn0 ltnn.
split.
- exact: g_pos.
- exact: leq_ltn_trans g_pos gk.
- by rewrite nE addnK -[X in X < _](addn0 k) ltn_add2l.
Qed.
