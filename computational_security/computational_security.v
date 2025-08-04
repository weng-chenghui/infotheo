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
Variables (T : finType) (P : R.-fdist T) (k : nat).

(* Commonly the "computational indistinguishability" is defined as:

  "Let X and Y be two distribution ensembles indexed by a security parameter n
    (which usually refers to the length of the input)... "

  In the paper "How to Simulate It in Isabelle: Towards Formal Proof for Secure
  Multi-Party Computation"\cite{Butler2017}, the authors generalized the
  definition above:

  "We model a probability ensemble as having some input of of this type,
   and a natural number security size parameter. The space of events considered
   depends on the view ; also of arbitrary first-order type, ν.

        type synonym (α, ν) ensemble = α ⇒ nat ⇒ ν spmf"
*)
Definition ensembleT := nat -> R.-fdist T.

(* "...we say they are computationally indistinguishable if for any non-uniform
   probabilistic polynomial time algorithm A..."

  In the paper\cite{Butler2017}, the authors also avoided to define the function
  as the definition above:
 
  "We do not formalise a notion of polynomial-time programs in Isabelle as we do
  not need it to capture the following proofs. In principle this could be done
  with a deep embedding of a programming language, its semantic denotation
  function and a complexity measure. Instead, we will assume a family of
  constants giving us the set of all polynomial-time distinguishers for every
  type ν, indexed by a size parameter." \cite[\S3]{Butler2017}

  Since we use `T` as event type, we can define our polydist as follows:
*)
Definition dingT := (size (enum T)).-bseq (R.-fdist T * R.-fdist bool)%type.
(* Because we already have "dist", ChatGPT suggested to use `ding`...*)
(* Using a pair instead of `R.-fdist T -> R.-fdist bool` because
   a \in k.-bseq (R.-fdist T -> R.-fdist bool) will cause an error about
   that "k.-bseq (R.-fdist T -> R.-fdist bool) is not a pred_sort".
*)

Variable polydist : nat ->  k.-bseq dingT.
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
Definition is_negfn (e : nat -> R) (x : nat) :=
  forall (c : nat), exists Nc : int,
    (x > Nc) -> 0 <= e x -> ((x ^ c)%:R * e x) < 1.

Variable (X Y : ensembleT).

(* TODO: define a dist give prob 1.0 to "false" and 0.0 to "true" *)
Variable (dist_false : R.-fdist bool).

(*
comp indist :: (α, ν) ensemble ⇒ (α, ν) ensemble ⇒ bool
where comp indist X Y ≡
  ∀(D :: ν spmf ⇒ bool spmf ). ∃ (ǫ :: nat ⇒ real ).
    negligible ǫ ∧ (∀ (a :: α) (n :: nat ). 
      (D ∈ polydist n) -> |spmf (D (X a n)) True − spmf (D (Y a n)) True| ≤ ǫ n))
*)
Definition comp_indist :=
  forall (n : nat) (d : dingT),
    exists e : nat -> R, is_negfn e n -> d \in polydist n ->
      let dingX := nth (X n, dist_false) d (find (fun p => p.1 == X n) d) in
      let dingY := nth (Y n, dist_false) d (find (fun p => p.1 == Y n) d) in
      let diff := dingX.2 true - dingY.2 true in
      if diff > 0 then diff <= e n else dingY.2 true - dingX.2 true <= e n.
      (* Because I cannot find absolute value for type R *)
  
End definitions.

Section example.
Context {R : realType}.
Variable (T TX TY : finType) (m n : nat).
  
About comp_indist.

Hypothesis cardTX : #|TX| = m.+1.
Hypothesis cardTY : #|TY| = n.+1.

Let distX := @fdist_uniform R TX m cardTX.
Let distY := @fdist_uniform R TY n cardTY.
Let X : @ensembleT R TX := fun (a : nat) => distX.
Let Y : @ensembleT R TY := fun (b : nat) => distY.

Let distB := @fdist_uniform R bool 1 card_bool.

End example.
