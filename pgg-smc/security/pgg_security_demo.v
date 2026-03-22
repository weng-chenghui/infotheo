(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Security Demo: Eps Progression, Transitivity, and Threshold Tradeoff   *)
(*                                                                            *)
(* Demonstrates that PGG CAN achieve low epsilon with meaningful (k,T)        *)
(* threshold, by contrasting transitive vs non-transitive RAAG groups.        *)
(*                                                                            *)
(* Mathematical context:                                                      *)
(*   - Non-transitive groups (star, disjoint): orbit structure forces a       *)
(*     positive eps floor regardless of L.                                    *)
(*   - Transitive groups (path, OC, cyclic): eps CAN converge to 0 as the    *)
(*     achievable set grows, but the path is NOT monotonic (identity spikes). *)
(*   - Higher genus gives (k, k+2g) threshold with 2g fault tolerance.       *)
(*                                                                            *)
(* Sections:                                                                  *)
(*   0. Utility functions (orbit, transitivity, scanning, threshold)          *)
(*   1. Transitivity diagnostic for each RAAG family                         *)
(*   2. Non-transitive groups — eps floor                                     *)
(*   3. Transitive groups — eps progression (non-monotonic!)                  *)
(*   4. Threshold options                                                     *)
(*   5. Combined tradeoff — best secure instances                            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div
  path.
From pgg_smc Require Import pgg_security_solver.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 0: Utility Functions                                          *)
(******************************************************************************)

(* Orbit computation: reachable sheets from s under generators.
   Iteratively applies all generators until fixed point. *)
Fixpoint orbit_step (gens : nat -> nat -> nat) (Tg : nat)
    (current : seq nat) (fuel : nat) : seq nat :=
  match fuel with
  | 0 => current
  | fuel'.+1 =>
    let new_pts := undup (current ++
      flatten [seq map (gens i) current | i <- iota 0 Tg]) in
    if size new_pts == size current then current
    else orbit_step gens Tg new_pts fuel'
  end.

Definition orbit_of (desc : RAAGDesc) (s : nat) : seq nat :=
  sort leq (orbit_step (rd_gens desc) (rd_Tg desc) [:: s] (rd_N desc)).

Definition is_transitive (desc : RAAGDesc) : bool :=
  size (orbit_of desc 0) == rd_N desc.

(* Fiber epsilon scan: compute eps at each L in a list *)
Definition fiber_eps_scan (desc : RAAGDesc) (Ls : seq nat)
    : seq (nat * (nat * nat)) :=
  map (fun L => (L, raag_fiber_eps_nat desc L)) Ls.

(* Achievable set size at given L *)
Definition achievable_size (desc : RAAGDesc) (L : nat) : nat :=
  size (achievable_fps desc L).

(* Achievable size scan *)
Definition achievable_scan (desc : RAAGDesc) (Ls : seq nat)
    : seq (nat * nat) :=
  map (fun L => (L, achievable_size desc L)) Ls.

(* PGL bound: N * (N^2 - 1), maximum |G| for genus=0 *)
Definition pgl_bound_nat (N : nat) : nat := N * (N ^ 2 - 1).

(* Threshold options: for N sheets and genus 0..max_g,
   returns (genus, k, T, gap) where T=N, gap=2*genus, k=N-gap *)
Definition threshold_options (N max_g : nat)
    : seq (nat * nat * nat * nat) :=
  map (fun g => let gap := 2 * g in (g, N - gap, N, gap))
      (iota 0 max_g.+1).

(******************************************************************************)
(*     Section 1: Transitivity Diagnostic                                    *)
(*                                                                           *)
(*     Key insight: transitive groups CAN have eps -> 0 as L grows.          *)
(*     Non-transitive groups are STUCK at a positive eps floor.              *)
(******************************************************************************)

(* Transitivity classification *)
Eval vm_compute in is_transitive (star_desc 2).      (* = false *)
Eval vm_compute in is_transitive (disjoint_desc 2).  (* = false *)
Eval vm_compute in is_transitive (path_desc 3).      (* = true *)
Eval vm_compute in is_transitive (oc_desc 2 3).      (* = true *)
Eval vm_compute in is_transitive (oc_desc 2 5).      (* = true *)
Eval vm_compute in is_transitive (cyclic_desc 5).    (* = true *)

(* Orbit structure for star(2): N=5, orbits {0,1} and {2,3,4} *)
Eval vm_compute in orbit_of (star_desc 2) 0.   (* = [0; 1] *)
Eval vm_compute in orbit_of (star_desc 2) 2.   (* = [2; 3; 4] *)

(* Orbit structure for disjoint(2): N=4, orbits {0,1} and {2,3} *)
Eval vm_compute in orbit_of (disjoint_desc 2) 0.  (* = [0; 1] *)
Eval vm_compute in orbit_of (disjoint_desc 2) 2.  (* = [2; 3] *)

(* Orbit structure for path(3): N=5, single orbit {0,1,2,3,4} *)
Eval vm_compute in orbit_of (path_desc 3) 0.   (* = [0; 1; 2; 3; 4] *)

(* Orbit structure for OC(2,3): N=4, single orbit *)
Eval vm_compute in orbit_of (oc_desc 2 3) 0.   (* = [0; 1; 2; 3] *)

(* Orbit structure for OC(2,5): N=6, single orbit *)
Eval vm_compute in orbit_of (oc_desc 2 5) 0.   (* = [0; 1; 2; 3; 4; 5] *)

(******************************************************************************)
(*     Section 2: Non-Transitive Groups — Eps Floor                          *)
(*                                                                           *)
(*     Star(m) and Disjoint(k) have orbit partitions that force a positive   *)
(*     eps floor.  Increasing L does NOT help: eps stays constant.           *)
(*                                                                           *)
(*     Star(2): orbits {0,1}, {2,3,4}. Sheet 0 always maps to {0,1},        *)
(*     so var_dist from uniform >= 6/5.                                      *)
(*     Disjoint(2): orbits {0,1}, {2,3}. Each sheet stays in its pair,      *)
(*     so var_dist >= 1.                                                     *)
(******************************************************************************)

(* Star(2): eps stuck at 6/5 for all L *)
Eval vm_compute in fiber_eps_scan (star_desc 2) [:: 1; 2; 3; 4; 5; 6; 7].

(* Disjoint(2): eps stuck at 1 for all L *)
Eval vm_compute in fiber_eps_scan (disjoint_desc 2) [:: 1; 2; 3; 4; 5; 6].

(* Achievable set saturates well below N! *)
Eval vm_compute in achievable_scan (star_desc 2) [:: 1; 2; 3; 4; 5; 6; 7].
Eval vm_compute in achievable_scan (disjoint_desc 2) [:: 1; 2; 3; 4; 5; 6].

(* Star(5): eps stuck at 12/8 = 3/2 *)
Eval vm_compute in fiber_eps_scan (star_desc 5) [:: 1; 2; 3].

(******************************************************************************)
(*     Section 3: Transitive Groups — Eps Progression (Non-Monotonic!)       *)
(*                                                                           *)
(*     Path(3)/S5: generating set = adjacent transpositions of S5.           *)
(*     As L grows, achievable set -> S5, eps -> 0.                           *)
(*     BUT: at L=2, identity enters achievable (sigma^2=id for transpos.)    *)
(*     creating a spike at the starting sheet.                               *)
(*                                                                           *)
(*     OC(2,p): overlapping p-cycles. Converges faster due to larger cycles. *)
(******************************************************************************)

(* Path(3) = S5 generators: eps progression L=1..6 *)
Eval vm_compute in fiber_eps_scan (path_desc 3) [:: 1; 2; 3; 4; 5; 6].

(* Path(3): achievable set size progression *)
Eval vm_compute in achievable_scan (path_desc 3) [:: 1; 2; 3; 4; 5; 6].
(* Compare: |S5| = 120 *)

(* OC(2,3): eps progression L=1..5 *)
Eval vm_compute in fiber_eps_scan (oc_desc 2 3) [:: 1; 2; 3; 4; 5].

(* OC(2,3): achievable set size *)
Eval vm_compute in achievable_scan (oc_desc 2 3) [:: 1; 2; 3; 4; 5].

(* OC(2,5): eps progression L=1..8 *)
Eval vm_compute in fiber_eps_scan (oc_desc 2 5) [:: 1; 2; 3; 4; 5; 6; 7; 8].

(* OC(2,5): achievable set size *)
Eval vm_compute in achievable_scan (oc_desc 2 5) [:: 1; 2; 3; 4; 5; 6; 7; 8].

(* Cyclic(5): eps progression L=1..6 *)
Eval vm_compute in fiber_eps_scan (cyclic_desc 5) [:: 1; 2; 3; 4; 5; 6].

(* Cyclic(5): achievable set size (|G| = 5, so saturates quickly) *)
Eval vm_compute in achievable_scan (cyclic_desc 5) [:: 1; 2; 3; 4; 5; 6].

(* Path(4) = S6 generators: larger example *)
Eval vm_compute in fiber_eps_scan (path_desc 4) [:: 1; 2; 3; 4; 5].
Eval vm_compute in achievable_scan (path_desc 4) [:: 1; 2; 3; 4; 5].

(******************************************************************************)
(*     Section 4: Threshold Options                                          *)
(*                                                                           *)
(*     genus=0: gap=0 -> (N,N)-threshold, requires |G| <= pgl_bound(N).     *)
(*     genus=g: gap=2g -> (N-2g, N)-threshold, tolerates 2g failures.       *)
(*     PGL bound = N*(N^2-1).                                                *)
(******************************************************************************)

(* PGL bounds for various N *)
Eval vm_compute in pgl_bound_nat 4.    (* = 60 *)
Eval vm_compute in pgl_bound_nat 5.    (* = 120 *)
Eval vm_compute in pgl_bound_nat 6.    (* = 210 *)
Eval vm_compute in pgl_bound_nat 7.    (* = 336 *)

(* Threshold options for N=4 (genus 0..3) *)
Eval vm_compute in threshold_options 4 3.
(* = [(0, 4, 4, 0); (1, 2, 4, 2); (2, 0, 4, 4); (3, 0, 4, 6)] *)
(* genus=0: (4,4) exact; genus=1: (2,4) tolerates 2 failures *)

(* Threshold options for N=5 (genus 0..3) *)
Eval vm_compute in threshold_options 5 3.
(* genus=0: (5,5); genus=1: (3,5) tolerates 2 failures *)

(* Threshold options for N=6 (genus 0..3) *)
Eval vm_compute in threshold_options 6 3.
(* genus=0: (6,6); genus=1: (4,6); genus=2: (2,6) *)

(* Threshold options for N=7 (genus 0..3) *)
Eval vm_compute in threshold_options 7 3.

(* Can Path(3) use genus=0?  |S5|=120, pgl_bound(5)=120. YES! *)
(* Can OC(2,5) use genus=0?  Need |G| <= pgl_bound(6)=210. *)

(******************************************************************************)
(*     Section 5: Combined Tradeoff — Best Secure Instances                  *)
(*                                                                           *)
(*     For each transitive family, show (L, eps, threshold options).         *)
(*     Highlight instances with eps < 1 AND fault-tolerant threshold.        *)
(******************************************************************************)

(* Path(3), N=5, |S5|=120, pgl_bound(5)=120 (genus=0 possible!) *)
(* Eps progression with threshold context:
   genus=0 -> (5,5)-threshold (exact, no fault tolerance)
   genus=1 -> (3,5)-threshold (tolerates 2 failures)            *)
Eval vm_compute in
  let desc := path_desc 3 in
  let Ls := [:: 1; 2; 3; 4; 5; 6] in
  (fiber_eps_scan desc Ls,
   achievable_scan desc Ls,
   threshold_options 5 2,
   pgl_bound_nat 5).

(* OC(2,5), N=6, pgl_bound(6)=210 *)
(* genus=0 -> (6,6)-threshold; genus=1 -> (4,6)-threshold *)
Eval vm_compute in
  let desc := oc_desc 2 5 in
  let Ls := [:: 1; 2; 3; 4; 5; 6; 7; 8] in
  (fiber_eps_scan desc Ls,
   achievable_scan desc Ls,
   threshold_options 6 2,
   pgl_bound_nat 6).

(* OC(2,3), N=4, pgl_bound(4)=60 *)
Eval vm_compute in
  let desc := oc_desc 2 3 in
  let Ls := [:: 1; 2; 3; 4; 5] in
  (fiber_eps_scan desc Ls,
   achievable_scan desc Ls,
   threshold_options 4 2,
   pgl_bound_nat 4).

(* Path(4), N=6, |S6|=720, pgl_bound(6)=210 *)
(* |S6|=720 > 210, so genus=0 NOT available for full S6 *)
Eval vm_compute in
  let desc := path_desc 4 in
  let Ls := [:: 1; 2; 3; 4; 5] in
  (fiber_eps_scan desc Ls,
   achievable_scan desc Ls,
   threshold_options 6 2,
   pgl_bound_nat 6).

(* Contrast: Star(2), N=5 — non-transitive, eps stuck *)
Eval vm_compute in
  let desc := star_desc 2 in
  let Ls := [:: 1; 2; 3; 4; 5] in
  (fiber_eps_scan desc Ls,
   achievable_scan desc Ls,
   threshold_options 5 2,
   pgl_bound_nat 5).

(******************************************************************************)
(*     Summary of key findings (expected results):                           *)
(*                                                                           *)
(*     1. Transitivity diagnostic correctly classifies all families.         *)
(*     2. Star/disjoint: eps constant across L (stuck at floor).            *)
(*     3. Path(3): eps decreases from 6/5 toward 0 (possibly non-monotone). *)
(*        At high L, achievable -> 120 = |S5|, eps -> 0.                   *)
(*     4. Path(3) at L>=5, genus=1: eps ~ 0, (3,5)-threshold.             *)
(*        This is a meaningful secure instance with fault tolerance!         *)
(*     5. OC(2,5): fast convergence due to 5-cycles, with (4,6)-threshold. *)
(******************************************************************************)
