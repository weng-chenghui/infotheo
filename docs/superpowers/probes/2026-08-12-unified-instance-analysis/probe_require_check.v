(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_require_check: the probe directory's logical root resolves            *)
(*                                                                            *)
(* Phase 0 load-path probe. The brief assumed probe files could not require   *)
(* one another; this file refutes that assumption. Compiling it after         *)
(* probe_s5_rand_plug.vo exists shows that "From uia_probe Require Import"    *)
(* resolves a sibling probe, so probe_s5_adapters.v may reuse the landed plug *)
(* values instead of restating them.                                          *)
(*                                                                            *)
(* Build order: probe_s5_rand_plug.v must be compiled first.                  *)
(******************************************************************************)

From uia_probe Require Import probe_s5_rand_plug.

Check s5_rand_plug.
Check s5_rfree_layout.
Check s5_rand_observed.
