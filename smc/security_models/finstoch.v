(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot ssralg reals.
Require Import fdist fdist_extra.

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
(*              tensor p q == the product distribution of p and q on A * B    *)
(*                 tensorE == tensor p q (a, b) is p a * q b                  *)
(*           tensor_fdist1 == tensor (fdist1 a) q is the transport of q       *)
(*                            along b |-> (a, b)                              *)
(*          tensor_fdist1r == tensor p (fdist1 b) is the transport of p       *)
(*                            along a |-> (a, b)                              *)
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

(* Naming: intentional; the name leads with stoch_comp rather than with the
   RHS head symbol fdistmap so that it files with the stoch_comp family of
   this section, the chain then reading stoch_comp of a dirac is fdistmap. *)
(* Composition with a Dirac map on the left is transport along the underlying
   function. *)
Lemma stoch_comp_dirac_fdistmap (A B C : finType) (g : B -> C) (f : stoch A B) :
  stoch_comp (dirac g) f =1 fun a => fdistmap g (f a).
Proof. by move=> a; rewrite /stoch_comp /dirac /fdistmap. Qed.

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
apply/fdist_ext => -[a' b']; rewrite tensorE fdistmapE fdist1E.
under eq_bigl do rewrite !inE /= xpair_eqE.
by rewrite big_mkcondl big_pred1_eq eq_sym mulr_natl mulrb.
Qed.

(* A tensor with a Dirac right factor is the transport of the left factor
   along the pairing with the Dirac point. *)
Lemma tensor_fdist1r (A B : finType) (p : R.-fdist A) (b : B) :
  tensor p (fdist1 b) = fdistmap (fun a => (a, b)) p.
Proof.
by rewrite /tensor -fdistX_prod -/(tensor (fdist1 b) p) tensor_fdist1 /fdistX
   fdistmap_comp.
Qed.

End stoch.
