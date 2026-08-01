(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot ssralg reals.
Require Import fdist.

(**md**************************************************************************)
(* # Finite stochastic maps                                                   *)
(*                                                                            *)
(* The Kleisli category of the finite-distribution monad over a realType R:   *)
(* objects are finTypes, arrows are the stochastic maps A -> R.-fdist B, and  *)
(* the identity arrows are the Dirac maps.  The tensor of two laws is their   *)
(* product distribution.                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*               stoch A B == the type A -> R.-fdist B of stochastic maps     *)
(*                            from A to B                                     *)
(*                 dirac g == the stochastic map a |-> fdist1 (g a) of a      *)
(*                            function g : A -> B                             *)
(*          stoch_comp g f == the stochastic map a |-> f a >>= g              *)
(*             stoch_compA == stoch_comp is associative                       *)
(*          stoch_comp_idl == dirac id is a left identity for stoch_comp      *)
(*          stoch_comp_idr == dirac id is a right identity for stoch_comp     *)
(*              dirac_comp == dirac (g \o f) is stoch_comp (dirac g)          *)
(*                            (dirac f)                                       *)
(* stoch_comp_dirac_fdistmap == stoch_comp (dirac g) f a is fdistmap g (f a)  *)
(*             eq_fdistmap == fdistmap is congruent in a pointwise-equal      *)
(*                            transported map                                 *)
(*            fdistmap_cst == the transport of a law along a constant map     *)
(*                            with value b is fdist1 b                        *)
(*         fdistmap_cst_eq == the transport of a law along a map pointwise    *)
(*                            equal to a constant b is fdist1 b               *)
(*              tensor p q == the product distribution of p and q on A * B    *)
(*                 tensorE == tensor p q (a, b) is p a * q b                  *)
(*           tensor_fdist1 == tensor (fdist1 a) q is the transport of q       *)
(*                            along b |-> (a, b)                              *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section stoch.
Context {R : realType}.

(* def:smc:stochastic-map *)
(* A stochastic map from A to B assigns to each point of A a distribution
   over B. *)
Definition stoch (A B : finType) := A -> R.-fdist B.

(* def:smc:dirac *)
(* mathcomp-analysis measure theory also names a Dirac measure `dirac`; that
   file is outside this import closure, so the two never collide here. *)
(* The Dirac map of g sends a to the point mass at g a. *)
Definition dirac (A B : finType) (g : A -> B) : stoch A B :=
  fun a => fdist1 (g a).

(* def:smc:finstoch *)
(* The composite of g after f draws b from f a and then draws from g b. *)
Definition stoch_comp (A B C : finType)
    (g : stoch B C) (f : stoch A B) : stoch A C :=
  fun a => f a >>= g.

(* prop:smc:finstoch-laws *)
(* Composition of stochastic maps is associative. *)
Lemma stoch_compA (A B C D : finType)
    (h : stoch C D) (g : stoch B C) (f : stoch A B) :
  stoch_comp h (stoch_comp g f) =1 stoch_comp (stoch_comp h g) f.
Proof. by move=> a; rewrite /stoch_comp fdistbindA. Qed.

(* prop:smc:finstoch-laws *)
(* The Dirac map of the identity is a left unit for composition. *)
Lemma stoch_comp_idl (A B : finType) (f : stoch A B) :
  stoch_comp (dirac id) f =1 f.
Proof. by move=> a; rewrite /stoch_comp /dirac fdistbind1. Qed.

(* prop:smc:finstoch-laws *)
(* The Dirac map of the identity is a right unit for composition. *)
Lemma stoch_comp_idr (A B : finType) (f : stoch A B) :
  stoch_comp f (dirac id) =1 f.
Proof. by move=> a; rewrite /stoch_comp /dirac fdist1bind. Qed.

(* prop:smc:transport-commutes *)
(* The Dirac map of a composite function is the composite of the Dirac maps. *)
Lemma dirac_comp (A B C : finType) (g : B -> C) (f : A -> B) :
  dirac (g \o f) =1 stoch_comp (dirac g) (dirac f).
Proof. by move=> a; rewrite /stoch_comp /dirac fdist1bind. Qed.

(* Naming: mainSymbol chain, stoch_comp of a dirac; RHS symbol fdistmap. *)
(* Composition with a Dirac map on the left is transport along the underlying
   function. *)
Lemma stoch_comp_dirac_fdistmap (A B C : finType) (g : B -> C) (f : stoch A B) :
  stoch_comp (dirac g) f =1 fun a => fdistmap g (f a).
Proof. by move=> a; rewrite /stoch_comp /dirac /fdistmap. Qed.

(* Pointwise equal maps transport a law to the same law. *)
Lemma eq_fdistmap (A B : finType) (g h : A -> B) (p : R.-fdist A) :
  g =1 h -> fdistmap g p = fdistmap h p.
Proof.
move=> gh; apply/fdist_ext => b; rewrite !fdistmapE.
by apply: eq_bigl => a; rewrite !inE gh.
Qed.

(* The transport of a law along a constant map with value b is the point mass
   at b. *)
Lemma fdistmap_cst (A B : finType) (p : R.-fdist A) (b : B) :
  fdistmap (fun=> b) p = fdist1 b.
Proof.
apply/fdist_ext => b'; rewrite fdistmapE fdist1E.
rewrite (eq_bigl (fun a : A => (a \in A) && (b == b'))); last first.
  by move=> a; rewrite !inE.
case: (altP (b =P b')) => [<-|nb].
  by rewrite eqxx -(FDist.f1 p); apply: eq_bigl => a; rewrite andbT.
by rewrite eq_sym (negbTE nb) big_pred0// => a; rewrite andbF.
Qed.

(* The transport of a law along a map pointwise equal to the constant b is the
   point mass at b. *)
Lemma fdistmap_cst_eq (A B : finType) (g : A -> B) (p : R.-fdist A) (b : B) :
  g =1 (fun=> b) -> fdistmap g p = fdist1 b.
Proof. by move=> gb; rewrite -(fdistmap_cst p b); apply: eq_fdistmap. Qed.

(* def:smc:tensor *)
(* The tensor of two laws is their product distribution on the product type. *)
Definition tensor (A B : finType) (p : R.-fdist A) (q : R.-fdist B)
  : R.-fdist (A * B)%type := (p `x q)%fdist.

(* def:smc:tensor *)
(* The tensor of two laws evaluates to the product of their masses. *)
Lemma tensorE (A B : finType) (p : R.-fdist A) (q : R.-fdist B) a b :
  tensor p q (a, b) = p a * q b.
Proof. by rewrite /tensor fdist_prodE. Qed.

(* A tensor with a Dirac left factor is the transport of the right factor
   along the pairing with the Dirac point. *)
Lemma tensor_fdist1 (A B : finType) (a : A) (q : R.-fdist B) :
  tensor (fdist1 a) q = fdistmap (fun b => (a, b)) q.
Proof.
apply/fdist_ext => -[a' b']; rewrite tensorE fdistmapE.
rewrite (eq_bigl (fun x : B => (x \in B) && ((a == a') && (x == b'))));
  last by move=> x; rewrite !inE /= xpair_eqE.
rewrite fdist1E; case: (altP (a =P a')) => [<-|na].
  rewrite eqxx mul1r (eq_bigl (fun i : B => i == b')); last first.
    by move=> i; rewrite inE.
  by rewrite big_pred1_eq.
by rewrite eq_sym (negbTE na) mul0r big_pred0// => i; rewrite (negbTE na).
Qed.

End stoch.
