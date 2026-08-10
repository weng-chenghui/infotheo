(* AUDIT FILE: expected-failure compile.                                      *)
(* Exact imports of five_card_leakage.v (NO div).  If "%%" is genuinely not   *)
(* in scope there, the Check below is a syntax error and this file fails to   *)
(* compile — that failure is the evidence for the probe's import-adjustment   *)
(* claim (probe_objects.v lines 9-13).                                        *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Check (fun n m : nat => (n %% m)%N).
