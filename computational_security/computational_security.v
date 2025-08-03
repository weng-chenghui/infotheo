(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import mathcomp_extra contra Rstruct ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy.

(**md**************************************************************************)
(* # Computation Security Propositions                                        *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section definitions.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (n m k: nat).

(* Commonly the "computational indistinguishability" is defined as:

  "Let X and Y be two distribution ensembles indexed by a security parameter n
    (which usually refers to the length of the input)... "

   Here we use random variables with a co-domain of an n-sized vector as the
   distribution ensembles, instead of using sets of n random variables as the
   distribution ensembles.

  (I guess that the original motivation to have a ensembles is as a collection
   of all sampling functions in the probalistic program. So if the Real and
   Simulated both have N sampling functions in each program, the differences
   among them one by one must be indistinguishable).
*)
Let TX := [the finComNzRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Variables (X : {RV P -> VX}) (Y : {RV P -> VX}).

(* "...we say they are computationally indistinguishable if for any non-uniform
   probabilistic polynomial time algorithm A..."

  In the paper "How to Simulate It in Isabelle: Towards Formal Proof for Secure
  Multi-Party Computation"\cite{Butler2017}, the authors also avoided to define
  as the definition above:
 
  "We do not formalise a notion of polynomial-time programs in Isabelle as we do
  not need it to capture the following proofs. In principle this could be done
  with a deep embedding of a programming language, its semantic denotation
  function and a complexity measure. Instead, we will assume a family of
  constants giving us the set of all polynomial-time distinguishers for every
  type ν, indexed by a size parameter." \cite[\S3]{Butler2017}

  Since we use `T` as event type, we can define our polydist as follows:
*)
Variable polydist : R ->  k.-bseq (R.-fdist T -> R.-fdist bool).

(*
  Compare to the Isabelle work \cite[\S3]{Butler2017}:

  "A polynomial-time distinguisher “characterises” an arbitrary spmf.

        consts polydist :: nat ⇒ (ν spmf ⇒ bool spmf ) set

  ", where spmf stands for "Subprobability mass functions.
  An spmf encodes a discrete (sub) probability distribution."
  \cite[\S2]{Butler2017}
*)


(* "...the following quantity is a negligible function in n:"

   "A negligible function is a function e :: N → R such that for all c ∈ N
   there exists N_c ∈ N such that for all x > N_c we have |e(x)| < 1/x^c"
   \cite[\S3]{Butler2017}
*)

Definition is_negfn (f : R -> R) (x : R):=
  forall (c : int), exists Nc : R,
    (x > Nc) -> 0 <= f x -> x ^ c * f x < 1.

Definition comp_indist :=
  forall (a b : R) (d : R.-fdist T -> R.-fdist bool),
    exists e : R -> R, is_negfn e b -> d \in polydist b.



  
End definitions.

