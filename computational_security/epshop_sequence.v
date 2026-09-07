From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Require Import negligible epshop.

(**md**************************************************************************)
(* # epsHop over the security parameter                                       *)
(*                                                                            *)
(* The sequence layer of epsHop, the second of the two monads the language    *)
(* is stacked from.  epsHop states a bound at one security parameter: a       *)
(* program is a chain of hops and its result publishes one real, and nothing  *)
(* in that file mentions the parameter.  A sequence program, of type          *)
(* forall k, chain_result (C k), is a value of the Reader monad over the      *)
(* security parameter, and the binder fun k => is that monad's bind.          *)
(* Negligibility is the monad's terminal, a statement about the whole         *)
(* sequence that no single member of it can carry.                            *)
(*                                                                            *)
(* A sequence program whose label list is the same at every k has a           *)
(* negligible advantage as soon as every label's loss sequence is negligible. *)
(* The negligible sequences form a submonoid of the additive sequences,       *)
(* closed under addition and containing the zero sequence                     *)
(* (negligible_fun_add, negligible_fun_cst0, negligible_fun_sum) and downward *)
(* closed (negligible_fun_le); loss_eval is a monoid morphism out of the free *)
(* monoid on labels, and result_total says the bound a program publishes is   *)
(* the total that morphism returns.  A total therefore lands in the           *)
(* submonoid exactly when each of its generators does, which is the one       *)
(* mathematical content of this file.                                         *)
(*                                                                            *)
(* The labels of a dictionary are made negligible once, by registering that   *)
(* dictionary sequence as a negligibleClaims.  The field is quantified over   *)
(* the label type, so whatever a chain over the dictionary spends is covered. *)
(* A theorem about a program written at that dictionary then names no label   *)
(* at all: canonical inference supplies the negligibility of every label the  *)
(* program can spend, and the asymptotic reading of a bound asks the client   *)
(* one hypothesis per quantity rather than one per hop.  The terminal's own   *)
(* check that the loss does not vary with k is discharged by fun _ => erefl   *)
(* at a literal program, and what the program contributes is result_sound     *)
(* and result_total, so only the label list is left to read.                  *)
(*                                                                            *)
(* ## What the syntax spends                                                  *)
(*                                                                            *)
(* \negligible[ and ]{ are new symbol tokens, and fun, => and by are          *)
(* keywords already.  The second surface, the one taking a named sequence     *)
(* program, closes on the token ] alone and adds nothing further.  This file  *)
(* declares no custom entry, so no identifier stops being readable as a term  *)
(* below it.                                                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*      negligibleClaims L R == a sequence of dictionaries indexed by the     *)
(*                              security parameter, together with the         *)
(*                              negligibility of the loss sequence of every   *)
(*                              label                                         *)
(*                  claims C == the dictionary a negligibleClaims carries, a  *)
(*                              coercion to Funclass                          *)
(*       claims_negligible C == every label of C has a negligible loss        *)
(*                              sequence                                      *)
(*    loss_eval_negligible s == the total of a fixed label list, read along   *)
(*                              the security parameter, is negligible         *)
(*      advantage_negligible == a sequence program with a k-independent loss  *)
(*                              has a negligible advantage                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)


Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* A sequence of dictionaries indexed by the security parameter, every label
   of which has a negligible loss sequence.  Registration is keyed on a named
   dictionary sequence, since a lambda has no head constant for unification. *)
Structure negligibleClaims (L : Type) (R : realType) := NegligibleClaims {
  claims :> nat -> L -> claim R ;
  claims_negligible :
    forall l, negligible_fun (fun k => claim_loss (claims k l)) }.

(* Set Implicit Arguments makes the carrier field implicit in the
   constructor, it being inferable from the type of the proof field; the
   client writes the dictionary first, so it is restored. *)
Arguments NegligibleClaims {L R} _ _.

Section advantage_negligible_theory.
Variable L : Type.
Variable R : realType.
Variable C : negligibleClaims L R.

(* The total of any list of labels is a negligible sequence.  Along the
   security parameter loss_eval is a monoid morphism into the negligible
   sequences, and the field covers every generator. *)
Lemma loss_eval_negligible (s : seq L) :
  negligible_fun (fun k => loss_eval (C k) s).
Proof.
rewrite /loss_eval; apply: negligible_fun_sum => l.
exact: claims_negligible.
Qed.

(* The terminal of the sequence monad: a sequence program spending the same
   labels at every k has a negligible advantage.  Hs states that independence
   against the loss at 0, and Hf identifies the client's quantity with the
   program's advantage. *)
Lemma advantage_negligible (f : nat -> R) (P : forall k, chain_result (C k))
    (Hs : forall k, result_loss (P k) = result_loss (P 0))
    (Hf : forall k, f k = result_advantage (P k)) : negligible_fun f.
Proof.
apply: (negligible_fun_le (g := fun k => result_bound (P k))).
  by move=> k; rewrite Hf; exact: result_sound.
apply: (negligible_fun_le (g := fun k => loss_eval (C k) (result_loss (P 0)))).
  by move=> k; rewrite -(result_total (P k)) Hs -loss_evalE.
exact: loss_eval_negligible.
Qed.

End advantage_negligible_theory.

Arguments advantage_negligible {L R} C f P Hs Hf.

(* Read: f is negligible, by Hf identifying it with the advantage of the
   program e under the binder.  The dictionary is resolved to a registered
   negligibleClaims by canonical inference, and the erefl checks the loss is
   k-independent. *)
Notation "'\negligible[' f 'by' Hf ']{' 'fun' k '=>' e '}'" :=
  (advantage_negligible _ f (fun k => e) (fun _ => erefl) Hf)
  (f constr at level 10, Hf constr at level 10, k ident,
   e constr at level 200) : epshop_scope.

(* The same terminal over a sequence program that already has a name.  The
   dictionary is read off the program's type, so the client names no label. *)
Notation "'\negligible[' f 'by' Hf ']' P" :=
  (advantage_negligible _ f P (fun _ => erefl) Hf)
  (f constr at level 10, Hf constr at level 10, P constr at level 10)
  : epshop_scope.
