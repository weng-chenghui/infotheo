(* Smoke test for SSProve + infotheo coexistence.
   Goal: confirm both libraries load in the same .v file without
   namespace clashes, after `opam install coq-ssprove` against the
   existing Rocq 9.0 + MathComp 2.5.0 + infotheo switch. *)

From mathcomp Require Import all_ssreflect.
From SSProve.Crypt Require Import Package.
From infotheo Require Import proba fdist.

(* Both libraries' fundamental types are reachable. *)
Check raw_package.
Check @FDist.t.

(* Sanity: both libraries' core types are usable in the same scope. *)
Section smoke.
Variable T : finType.
Check (T : finType).
Check raw_package.
End smoke.

(* If this file compiles, SSProve and infotheo coexist in this switch. *)
