(* DSDP Alice secrecy under IND-CPA.

   Hybrid (computational + information-theoretic) closed-form bound

       Pr[A(AliceView) = V_2] <= 1 / m + 2 * epsilon_cpa

   for the 3-party DSDP protocol against static semi-honest corrupted Alice.
   Two real-or-zero IND-CPA ciphertext swaps plus an information-theoretic
   residual-uniformity step.

   Plan: ~/.claude/plans/sprightly-finding-robin.md
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap.
From SSProve.Crypt Require Import Package.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import homomorphic_encryption.
Require Import dsdp_program dsdp_entropy dsdp_pismc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* Pin SSProve's real type as the ambient realType for this file. *)
Notation R := SSProve.Crypt.Axioms.R.

(* Adversary type abbreviation. *)
Notation adversary := (package _ _ _).

Section dsdp_security_indcpa.

(* AHE scheme is parametric, matching the existing project convention
   from dsdp_pismc.v. *)
Variable AHE : AHEncType.

(* Design Commitment 1 (Rocq audit).  rand AHE is declared as Type in
   homomorphic_encryption/he_types.v:40.  SSProve cannot sample over a
   bare Type.  This scaffold introduces a refined finType carrier Renc
   for the encryption randomness; later instantiation against a
   concrete scheme (Benaloh/Paillier) identifies Renc with rand AHE. *)
Variable Renc : finType.

End dsdp_security_indcpa.
