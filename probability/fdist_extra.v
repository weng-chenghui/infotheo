(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot ssralg reals.
Require Import fdist.

(**md**************************************************************************)
(* # Companion lemmas for fdist.v                                             *)
(*                                                                            *)
(* Facts about the finite-distribution monad that fdist.v does not state.     *)
(* Kept beside it, and depending on nothing beyond it, so that any file       *)
(* requiring fdist can require these too.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*               fdist_prod2 == the second marginal of a product is its       *)
(*                              second factor, the counterpart of             *)
(*                              fdist_prod1                                   *)
(*             fdistmap_bind == the fdistmap/fdistbind commutation of the     *)
(*                              fdist monad                                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section fdist_extra.

Context {R : realType}.

(* The second marginal of a genuine product is the second factor. *)
Lemma fdist_prod2 (T1 T2 : finType) (Q1 : R.-fdist T1)
    (Q2 : R.-fdist T2) : (Q1 `x Q2)`2 = Q2.
Proof. by rewrite -fdistX1 fdistX_prod fdist_prod1. Qed.

(* The fdistmap/fdistbind commutation of the fdist monad.  A convenience rather
   than a necessity, though the obvious inline spelling does not substitute for
   it: [rewrite /fdistmap fdistbindA] at a use site unfolds every [fdistmap] in
   the goal, destroying the nested ones a later [fdistmap_comp] must match. *)
Lemma fdistmap_bind (T1 T2 T3 : finType) (Q : R.-fdist T1)
    (g : T1 -> R.-fdist T2) (h : T2 -> T3) :
  fdistmap h (Q >>= g) = Q >>= (fun a => fdistmap h (g a)).
Proof. by rewrite /fdistmap fdistbindA. Qed.

End fdist_extra.
