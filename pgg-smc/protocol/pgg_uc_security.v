(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: UC-security composition                                               *)
(*                                                                            *)
(* STATUS: OPEN CONJECTURE.                                                   *)
(*                                                                            *)
(* Placeholder types [Adversary] and [Simulator] are stubbed here so the      *)
(* simulation statement typechecks. A full UC treatment requires a concrete  *)
(* [Simulator] construction driven by [collusion_bound]                       *)
(* (pgg_collusion_bound.v:239) and [ar_protocol_correct]                     *)
(* (algebraic_rigidity.v:350), plus an ideal/real execution infrastructure    *)
(* beyond the current [pgg_posterior_fdist]. This file names the obligation  *)
(* so [Print Assumptions] surfaces it.                                        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Adversary and Simulator placeholder types                             *)
(******************************************************************************)

(* An adversary is modelled by the collusion set it controls.
   This matches the model used in [pgg_collusion_bound.v]. *)
Definition Adversary (N : nat) : Type := {set 'I_N}.

(* A simulator maps target secrets to a real-valued distribution over
   secrets. We use a pair (output, bound) as the minimal signature; a
   concrete UC simulator would return a probabilistic term instead. *)
Definition Simulator (R : numDomainType) (N : nat) : Type :=
  'I_N -> 'I_N -> R.

(******************************************************************************)
(*     Ideal functionality                                                    *)
(******************************************************************************)

(* Ideal: uniform over secrets, indifferent to the secret input.
   We return the uniform weight 1/N as a scalar, which is the minimal
   observable quantity a UC simulator needs to match. *)
Definition F_shuffle (R : numFieldType) (N : nat) (Npos : (0 < N)%N) :
  'I_N -> 'I_N -> R :=
  fun _ _ => N%:R^-1.

(******************************************************************************)
(*     Real vs ideal execution sketches                                       *)
(******************************************************************************)

Section uc_statement.
Variable R : numFieldType.
Variable N : nat.
Hypothesis Npos : (0 < N)%N.

(* Real execution: abstract probability that the adversary outputs a
   given secret. Left as an opaque function since the UC infrastructure
   needed to define it concretely is outside this file's scope. *)
Variable real_exec : Adversary N -> 'I_N -> R.

(* Ideal execution: adversary sees only the ideal uniform output. *)
Definition ideal_exec (_ : Simulator R N) (_ : Adversary N) (s : 'I_N) : R :=
  @F_shuffle R N Npos s s.

(* Statistical distance between real and ideal executions at a given
   target secret and adversary. *)
Definition uc_distance (Sim : Simulator R N) (Adv : Adversary N) (s : 'I_N) : R :=
  `|real_exec Adv s - ideal_exec Sim Adv s|.

(******************************************************************************)
(*     UC simulation Conjecture                                               *)
(******************************************************************************)

(* The UC-security composition statement: for any algebraic-rigidity
   witness, there exists a simulator whose ideal execution is ε-close
   to the real execution, where ε is the security witness bound.

   This is stated here as a Conjecture. A future PR would discharge
   it from collusion_bound + ar_protocol_correct + G_stable hypotheses. *)
Conjecture uc_simulation :
  forall (epsilon : R),
  0 <= epsilon ->
  exists Sim : Simulator R N,
    forall (Adv : Adversary N) (s : 'I_N),
      uc_distance Sim Adv s <= epsilon.

End uc_statement.
