From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Require Import negligible epshop.

(**md**************************************************************************)
(* # epsHop over the security parameter                                       *)
(*                                                                            *)
(* The family layer of epsHop, the second of the two monads the language is   *)
(* stacked from.  epsHop states a bound at one security parameter: a program  *)
(* is a chain of hops and its result publishes one real, and nothing in that  *)
(* file mentions the parameter.  A family program, of type forall k,          *)
(* chain_result (C k), is a value of the Reader monad over the security       *)
(* parameter, and the binder fun k => is that monad's bind.  Negligibility    *)
(* is the monad's terminal, a statement about the whole family that no        *)
(* single member of it can carry.                                             *)
(*                                                                            *)
(* A family program whose label list is the same at every k opens at a        *)
(* negligible quantity as soon as every label's cost family is negligible.    *)
(* The negligible families form a submonoid of the additive families, closed  *)
(* under addition and containing the zero family (negligible_fun_add,         *)
(* negligible_fun_cst0, negligible_fun_sum) and downward closed               *)
(* (negligible_fun_le); loss_eval is a monoid morphism out of the free        *)
(* monoid on labels, and result_total says the bound a program publishes is   *)
(* the total that morphism returns.  A total therefore lands in the           *)
(* submonoid exactly when each of its generators does, which is the one       *)
(* mathematical content of this file.                                         *)
(*                                                                            *)
(* The labels of a dictionary are made negligible once, by registering that   *)
(* dictionary as a negligibleClaims.  A theorem about a program written at    *)
(* that dictionary then names no label at all: canonical inference supplies   *)
(* the negligibility of every label the program can spend, and the            *)
(* asymptotic reading of a bound costs the client one hypothesis per          *)
(* quantity rather than one per hop.                                          *)
(*                                                                            *)
(* ## What the syntax costs                                                   *)
(*                                                                            *)
(* \negligible[ and ]{ are new symbol tokens, and fun, => and by are          *)
(* keywords already.  The second surface, the one taking a named family       *)
(* program, closes on the token ] alone and adds nothing further.  This file  *)
(* declares no custom entry, so no identifier stops being readable as a term  *)
(* below it.                                                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*      negligibleClaims L R == a family of dictionaries indexed by the       *)
(*                              security parameter, together with the         *)
(*                              negligibility of the cost family of every     *)
(*                              label                                         *)
(*                  claims C == the dictionary a negligibleClaims carries, a  *)
(*                              coercion to Funclass                          *)
(*       claims_negligible C == every label of C costs a negligible family    *)
(*    loss_eval_negligible s == the total of a fixed label list, read along   *)
(*                              the security parameter, is negligible         *)
(*          first_negligible == a family program with a k-independent loss    *)
(*                              opens at a negligible quantity                *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* A family of dictionaries indexed by the security parameter, together with
   the fact that every label of the label type costs a negligible family.
   The field is quantified over the label type rather than over the labels of
   one program, so whatever a chain over this dictionary spends is covered,
   and a client registers the structure once beside its dictionary.
   Registration is keyed on a named family dictionary: a dictionary written
   as a lambda registers but never resolves, an application of it having no
   head constant for unification to match on. *)
Structure negligibleClaims (L : Type) (R : realType) := NegligibleClaims {
  claims :> nat -> L -> claim R ;
  claims_negligible :
    forall l, negligible_fun (fun k => claim_cost (claims k l)) }.

(* Set Implicit Arguments makes the carrier field implicit in the
   constructor, it being inferable from the type of the proof field; the
   client writes the dictionary first, so it is restored. *)
Arguments NegligibleClaims {L R} _ _.

Section first_negligible_theory.
Variable L : Type.
Variable R : realType.
Variable C : negligibleClaims L R.

(* The total of any list of labels is a negligible family.  loss_eval read
   along the security parameter is a monoid morphism into the submonoid of
   negligible families, and the structure's field is the generator case for
   every label of the type at once, so no membership premise on the list is
   needed. *)
Lemma loss_eval_negligible (s : seq L) :
  negligible_fun (fun k => loss_eval (C k) s).
Proof.
rewrite /loss_eval; apply: negligible_fun_sum => l.
exact: claims_negligible.
Qed.

(* The terminal of the family monad: a family program spending the same
   labels at every security parameter opens at a negligible quantity.  Hs is
   that independence of the loss from the parameter, stated against the loss
   at 0 so that no label list is written anywhere and discharged by
   fun _ => erefl at a literal program; Hf identifies the quantity the
   client's theorem is about with the game the program opens at.  What the
   program contributes is result_sound and result_total: its first game is
   below its published bound, and that bound is the total of its labels, so
   the only thing left to read is the label list. *)
Lemma first_negligible (f : nat -> R) (P : forall k, chain_result (C k))
    (Hs : forall k, result_loss (P k) = result_loss (P 0))
    (Hf : forall k, f k = result_first (P k)) : negligible_fun f.
Proof.
apply: (negligible_fun_le (g := fun k => result_bound (P k))).
  by move=> k; rewrite Hf; exact: result_sound.
apply: (negligible_fun_le (g := fun k => loss_eval (C k) (result_loss (P 0)))).
  by move=> k; rewrite -(result_total (P k)) Hs -loss_evalE.
exact: loss_eval_negligible.
Qed.

End first_negligible_theory.

Arguments first_negligible {L R} C f P Hs Hf.

(* Read "f is negligible, by Hf identifying it with the first game of the
   program, for each k the program e".  The body is a value of the Reader
   monad over the security parameter, the inner program written once under
   the binder, and the dictionary it is written at is resolved to a
   registered negligibleClaims by canonical inference, so the block names no
   label.  The erefl is the check that the loss does not vary with k. *)
Notation "'\negligible[' f 'by' Hf ']{' 'fun' k '=>' e '}'" :=
  (first_negligible _ f (fun k => e) (fun _ => erefl) Hf)
  (f constr at level 10, Hf constr at level 10, k ident,
   e constr at level 200) : epshop_scope.

(* The same terminal over a family program that already has a name.  The
   dictionary is read off the program's type rather than written in the
   block, so a program declared at a named family dictionary carries its own
   labels into the terminal and the client names none of them. *)
Notation "'\negligible[' f 'by' Hf ']' P" :=
  (first_negligible _ f P (fun _ => erefl) Hf)
  (f constr at level 10, Hf constr at level 10, P constr at level 10)
  : epshop_scope.
