From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.

(**md**************************************************************************)
(* # Chains of hops graded by a loss                                          *)
(*                                                                            *)
(* A chain is a morphism of a category graded by the loss monoid.  Its        *)
(* objects are acceptance probabilities, elements of an abstract real type,   *)
(* and a morphism from a to b carries a list of loss terms, a premise, and a  *)
(* proof that the premise implies `| a - b | <= loss_eval of that list.       *)
(* Composition concatenates the two lists, so the loss of a composite is the  *)
(* sum of the losses of its parts, and the identity logs the empty list.      *)
(* This is stronger than a Writer monad over the free monoid of loss terms:   *)
(* bind carries a side condition a Writer has no field to state, namely that  *)
(* the continuation starts at the point where the previous fragment stopped.  *)
(* That equation is what makes the concatenated loss bound the distance       *)
(* between the two outer endpoints, by one triangle inequality per bind.      *)
(*                                                                            *)
(* A loss term is a label paired with a real.  The label names, through its   *)
(* own type, the assumption and the reduction a step invokes, so the loss of  *)
(* a finished chain is the list of assumptions its bound rests on and not     *)
(* only a numeric total.  The label type L is a parameter of the whole file,  *)
(* so a client names its steps in whatever eqType it prefers.                 *)
(*                                                                            *)
(* ## What each statement logs                                                *)
(*                                                                            *)
(* | statement          | endpoints          | logs         | premise       | *)
(* |--------------------|--------------------|--------------|---------------| *)
(* | chain_start g      | g and g            | nothing      | True          | *)
(* | chain_hop l e x g' | x and g'           | LossTerm l e | distance at   | *)
(* |                    |                    |              | most e        | *)
(* | chain_eq x g'      | x and g'           | nothing      | x = g'        | *)
(* | chain_bind m f     | m's first and the  | both lists,  | both premises | *)
(* |                    | continuation's     | in order     |               | *)
(* |                    | current            |              |               | *)
(* | chain_eval m l c   | m's first only     | m's list and | m's premise   | *)
(* |                    |                    | LossTerm l c | and current   | *)
(* |                    |                    |              | at most c     | *)
(*                                                                            *)
(* The invariant every chain carries is chain_sound: the premise implies      *)
(* that the distance between the first and the current endpoint is at most    *)
(* the evaluated loss.  chain_eval changes the sort of the statement, from a  *)
(* distance between two endpoints to a bound on one, by consuming a bound c   *)
(* on the current endpoint; what it returns is a chain_bound, whose           *)
(* bound_sound reads bound_first <= loss_eval bound_loss.                     *)
(*                                                                            *)
(* The left unit holds definitionally on the loss and on the endpoints, and   *)
(* only as an equivalence on the premise, True /\ p being equivalent to p     *)
(* and not equal to it.  The right unit needs cats0 and associativity of the  *)
(* loss needs catA, so both are propositional.  Equality of two chains that   *)
(* agree on the four observable fields needs Prop_irrelevance for the fifth,  *)
(* which is chain_observable_eq.  The laws are therefore stated up to         *)
(* chain_equiv, which asks for equal endpoints, a permutation of the losses   *)
(* and equivalent premises, and under which loss_eval is invariant by         *)
(* perm_big.  A bound read off a chain is thus unaffected by the unit and     *)
(* associativity rearrangements the notation performs.                        *)
(*                                                                            *)
(* A client writes Require Import hop_chain. and then Local Open Scope        *)
(* chain_scope.  The notation x <-- m ;; f is declared outside every          *)
(* Section, so it is exported with the file.  Its tokens differ from the      *)
(* fdist bind notation x <- m ; f of computational_security/indcpa_game.v     *)
(* and it lives in a scope of its own, so the two may be open together.       *)
(*                                                                            *)
(* ```                                                                        *)
(*             loss_term L R == a label in L paired with a real cost          *)
(*          loss_term_cost a == the real cost of one loss term                *)
(*                  loss L R == a list of loss terms, the free monoid the     *)
(*                              category is graded by                         *)
(*               loss_eval s == the numeric total of a list of loss terms     *)
(*             loss_eval_nil == the empty loss costs zero                     *)
(*             loss_eval_cat == concatenation of losses adds their costs      *)
(*                loss_eval1 == a one term loss costs that term               *)
(*                 chain L R == a first endpoint, a current endpoint, a loss, *)
(*                              a premise, and the proof that the premise     *)
(*                              bounds the distance between the endpoints by  *)
(*                              the loss                                      *)
(*             chain_start g == the identity at g, logging nothing            *)
(*        chain_hop l e x g' == the step from x to g' whose premise is the    *)
(*                              numeric bound e and which logs LossTerm l e   *)
(*             chain_eq x g' == the step from x to g' whose premise is their  *)
(*                              equality and which logs nothing               *)
(*         chain_bind m f Hb == m followed by f, where Hb says f starts where *)
(*                              m stopped, logging the concatenated loss      *)
(*               chain_bound == a first endpoint, a loss, a premise, and the  *)
(*                              proof that the premise bounds the endpoint by *)
(*                              the loss                                      *)
(*          chain_eval m l c == the chain_bound obtained from m by charging   *)
(*                              LossTerm l c for its current endpoint         *)
(*            loss_term_code == a loss term read as a label and cost pair, the*)
(*                              coding its eqType is copied along             *)
(*            loss_eval_perm == permuting a loss leaves its total unchanged   *)
(*            left_unit_loss == binding after chain_start leaves the loss     *)
(*       left_unit_endpoints == binding after chain_start leaves the endpoints*)
(*         left_unit_premise == binding after chain_start leaves the premise  *)
(*                              up to equivalence                             *)
(*           right_unit_loss == binding chain_start after a chain leaves the  *)
(*                              loss                                          *)
(*                 loss_catA == concatenation of losses is associative        *)
(*       chain_observable_eq == two chains agreeing on the four observable    *)
(*                              fields are equal                              *)
(*               chain_equiv == equal endpoints, permuted losses, equivalent  *)
(*                              premises                                      *)
(*     chain_equiv_loss_eval == equivalent chains have the same numeric total *)
(*           left_unit_equiv == the left unit law, up to chain_equiv          *)
(*          right_unit_equiv == the right unit law, up to chain_equiv         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section chain_dsl.
Variable L : eqType.
Variable R : realType.

(* One summand of a security loss: the label naming the assumption and the
   reduction that a step invokes, and the real that step costs. *)
Inductive loss_term := LossTerm of L & R.

(* The real a loss term costs, its label discarded. *)
Definition loss_term_cost (a : loss_term) : R := let: LossTerm _ c := a in c.

(* An accumulated security loss, the free monoid on loss terms.  A list
   rather than a real so that a finished chain still names the assumptions
   its bound rests on. *)
Definition loss := seq loss_term.

(* The numeric total of a loss, the monoid map to the additive reals along
   which every bound of this file is finally read. *)
Definition loss_eval (s : loss) : R := \sum_(a <- s) loss_term_cost a.

(* The empty loss is the unit: a step that assumes nothing costs nothing. *)
Lemma loss_eval_nil : loss_eval [::] = 0.
Proof. by rewrite /loss_eval big_nil. Qed.

(* loss_eval is a monoid morphism, which is why composing two fragments adds
   their losses instead of relating them in some other way. *)
Lemma loss_eval_cat s1 s2 :
  loss_eval (s1 ++ s2) = loss_eval s1 + loss_eval s2.
Proof. by rewrite /loss_eval big_cat. Qed.

(* A single step costs exactly what its own term costs. *)
Lemma loss_eval1 l c : loss_eval [:: LossTerm l c] = c.
Proof. by rewrite /loss_eval big_cons big_nil addr0. Qed.

(* A chain fragment: where it starts, where it now is, what it logged, what
   it assumed, and the one theorem it carries.  chain_sound is the invariant
   every constructor below re-establishes, so that a client reads a bound off
   a finished chain without restating a triangle inequality. *)
Record chain := Chain {
  chain_first : R ;
  chain_current : R ;
  chain_loss : loss ;
  chain_premise : Prop ;
  chain_sound : chain_premise ->
    `| chain_first - chain_current | <= loss_eval chain_loss }.

(* The identity morphism at g: it assumes nothing and costs nothing. *)
Lemma start_sound (g : R) : True -> `| g - g | <= loss_eval [::].
Proof. by move=> _; rewrite subrr normr0 loss_eval_nil. Qed.

Definition chain_start (g : R) : chain :=
  {| chain_first := g ; chain_current := g ; chain_loss := [::] ;
     chain_premise := True ; chain_sound := @start_sound g |}.

(* One hop, from x to g', charged at e under the label l.  The premise is
   the numeric bound itself rather than a named hypothesis: a continuation of
   a bind is elaborated at a generic starting point, so a hypothesis stated
   at a specific starting value cannot be supplied there. *)
Lemma hop_sound (l : L) (e x g' : R) :
  `| x - g' | <= e -> `| x - g' | <= loss_eval [:: LossTerm l e].
Proof. by rewrite loss_eval1. Qed.

Definition chain_hop (l : L) (e x g' : R) : chain :=
  {| chain_first := x ; chain_current := g' ;
     chain_loss := [:: LossTerm l e] ;
     chain_premise := `| x - g' | <= e ;
     chain_sound := @hop_sound l e x g' |}.

(* An exact rewriting step, from x to g' at no cost.  It is the step an
   information-theoretic identity between two games takes, as against a
   hop, which spends an assumption. *)
Lemma eq_sound (x g' : R) : x = g' -> `| x - g' | <= loss_eval [::].
Proof. by move=> ->; rewrite subrr normr0 loss_eval_nil. Qed.

Definition chain_eq (x g' : R) : chain :=
  {| chain_first := x ; chain_current := g' ; chain_loss := [::] ;
     chain_premise := x = g' ; chain_sound := @eq_sound x g' |}.

(* Composition, sound only when the continuation starts where the previous
   fragment stopped, which is the side condition Hb.  It is the one triangle
   inequality of the development, discharged once here so that a chain of any
   length needs none. *)
Lemma bind_sound (m : chain) (f : R -> chain)
    (Hb : chain_first (f (chain_current m)) = chain_current m) :
  chain_premise m /\ chain_premise (f (chain_current m)) ->
  `| chain_first m - chain_current (f (chain_current m)) |
  <= loss_eval (chain_loss m ++ chain_loss (f (chain_current m))).
Proof.
case=> hm hf; rewrite loss_eval_cat.
apply: le_trans (ler_distD (chain_current m) _ _) _.
apply: lerD; first exact: chain_sound.
by rewrite -[X in `| X - _ |]Hb; exact: chain_sound.
Qed.

Definition chain_bind (m : chain) (f : R -> chain)
    (Hb : chain_first (f (chain_current m)) = chain_current m) : chain :=
  {| chain_first := chain_first m ;
     chain_current := chain_current (f (chain_current m)) ;
     chain_loss := chain_loss m ++ chain_loss (f (chain_current m)) ;
     chain_premise := chain_premise m /\ chain_premise (f (chain_current m)) ;
     chain_sound := @bind_sound m f Hb |}.

(* The terminal object of the grading, where the statement changes sort:
   from a distance between two acceptance probabilities to a bound on one.
   This is the shape a security theorem is stated in, the endpoint of the
   chain having been bounded rather than compared. *)
Record chain_bound := {
  bound_first : R ;
  bound_loss : loss ;
  bound_premise : Prop ;
  bound_sound : bound_premise -> bound_first <= loss_eval bound_loss }.

(* Charging the current endpoint at c under the label l turns a chain into
   such a bound: the distance the chain proved plus the bound on where it
   stopped is a bound on where it started. *)
Lemma eval_sound (m : chain) (l : L) (c : R) :
  chain_premise m /\ chain_current m <= c ->
  chain_first m <= loss_eval (chain_loss m ++ [:: LossTerm l c]).
Proof.
case=> hm hc; rewrite loss_eval_cat loss_eval1.
have h1 : chain_first m - chain_current m <= loss_eval (chain_loss m).
  exact: (le_trans (ler_norm (chain_first m - chain_current m))
                   (@chain_sound m hm)).
by rewrite -(subrK (chain_current m) (chain_first m)); exact: lerD h1 hc.
Qed.

Definition chain_eval (m : chain) (l : L) (c : R) : chain_bound :=
  {| bound_first := chain_first m ;
     bound_loss := chain_loss m ++ [:: LossTerm l c] ;
     bound_premise := chain_premise m /\ chain_current m <= c ;
     bound_sound := @eval_sound m l c |}.

End chain_dsl.

Arguments chain_start {L R} g.
Arguments chain_hop {L R} l e x g'.
Arguments chain_eq {L R} x g'.
Arguments chain_bind {L R} m f Hb.
Arguments chain_eval {L R} m l c.

(* A loss term is a label and a cost, so its equality is that of the pair,
   which is what perm_eq on losses is taken along below. *)
Definition loss_term_code (L : eqType) (R : realType) (a : loss_term L R)
  : L * R := let: LossTerm l c := a in (l, c).

Definition loss_term_decode (L : eqType) (R : realType) (x : L * R)
  : loss_term L R := LossTerm x.1 x.2.

Lemma loss_term_codeK (L : eqType) (R : realType) :
  cancel (@loss_term_code L R) (@loss_term_decode L R).
Proof. by case. Qed.

HB.instance Definition _ (L : eqType) (R : realType) :=
  Equality.copy (loss_term L R) (can_type (@loss_term_codeK L R)).

Declare Scope chain_scope.
Delimit Scope chain_scope with chain.

(* Sequential composition of chain fragments.  The erefl discharges the side
   condition of chain_bind by conversion, which is why a fragment must be
   written at the variable the previous line bound.  The tokens are distinct
   from the fdist bind notation x <- m ; f of indcpa_game.v, and the scope is
   separate, so both may be open at once. *)
Notation "x '<--' m ';;' f" := (chain_bind m (fun x => f) erefl)
  (at level 100, right associativity,
   format "'[v' x  '<--'  m ;;  '//' f ']'") : chain_scope.

Section monad_laws.
Variable L : eqType.
Variable R : realType.

(* The loss monoid is free commutative as far as loss_eval can tell, since a
   sum over a list is invariant under permutation.  This is what lets the
   laws below be stated up to a permutation of the logged terms. *)
Lemma loss_eval_perm (s1 s2 : loss L R) :
  perm_eq s1 s2 -> loss_eval s1 = loss_eval s2.
Proof. by move=> ps; rewrite /loss_eval (perm_big _ ps). Qed.

(* Left unit on the loss: [::] ++ s reduces, so this is definitional. *)
Lemma left_unit_loss (g : R) (f : R -> chain L R)
    (Hb : chain_first (f g) = g) :
  chain_loss (chain_bind (chain_start g) f Hb) = chain_loss (f g).
Proof. by []. Qed.

(* Left unit on the endpoints: definitional as well. *)
Lemma left_unit_endpoints (g : R) (f : R -> chain L R)
    (Hb : chain_first (f g) = g) :
  chain_current (chain_bind (chain_start g) f Hb) = chain_current (f g).
Proof. by []. Qed.

(* Left unit on the premise: True /\ p is equivalent to p and not equal to
   it, so this half of the law is an iff and not a conversion. *)
Lemma left_unit_premise (g : R) (f : R -> chain L R)
    (Hb : chain_first (f g) = g) :
  chain_premise (chain_bind (chain_start g) f Hb) <-> chain_premise (f g).
Proof. by split=> [[]|]. Qed.

(* Right unit on the loss needs cats0, so it is propositional. *)
Lemma right_unit_loss (m : chain L R) :
  chain_loss (chain_bind m (fun x => chain_start x) erefl) = chain_loss m.
Proof. by rewrite /= cats0. Qed.

(* Associativity of the loss is catA, again propositional. *)
Lemma loss_catA (s1 s2 s3 : loss L R) :
  s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
Proof. exact: catA. Qed.

(* Two chains agreeing on the four observable fields are equal: the fifth
   field is a proof of a Prop, and Prop_irrelevance identifies those.  A law
   stated as an equality of records rather than as chain_equiv therefore
   costs one classical axiom. *)
Lemma chain_observable_eq (c1 c2 : chain L R) :
  chain_first c1 = chain_first c2 -> chain_current c1 = chain_current c2 ->
  chain_loss c1 = chain_loss c2 -> chain_premise c1 = chain_premise c2 ->
  c1 = c2.
Proof.
case: c1 => a1 b1 l1 p1 s1; case: c2 => a2 b2 l2 p2 s2 /= Ha Hb Hl Hp.
move: s1 s2; rewrite Ha Hb Hl Hp => s1 s2.
by congr Chain; exact: Prop_irrelevance.
Qed.

(* The equivalence the laws hold up to: equal endpoints, a permutation of
   the losses, and equivalent premises.  It is coarse enough to absorb the
   unit and associativity rearrangements and fine enough to determine every
   bound a chain is read for. *)
Definition chain_equiv (c1 c2 : chain L R) : Prop :=
  [/\ chain_first c1 = chain_first c2,
      chain_current c1 = chain_current c2,
      perm_eq (chain_loss c1) (chain_loss c2)
    & chain_premise c1 <-> chain_premise c2].

(* The numeric total is an invariant of chain_equiv, which is what makes the
   coarser equivalence adequate for reading bounds. *)
Lemma chain_equiv_loss_eval (c1 c2 : chain L R) :
  chain_equiv c1 c2 ->
  loss_eval (chain_loss c1) = loss_eval (chain_loss c2).
Proof. by case=> _ _ ps _; exact: loss_eval_perm. Qed.

(* The left unit law, in the sense the premise field allows. *)
Lemma left_unit_equiv (g : R) (f : R -> chain L R)
    (Hb : chain_first (f g) = g) :
  chain_equiv (chain_bind (chain_start g) f Hb) (f g).
Proof.
split=> /=.
- by rewrite Hb.
- by [].
- exact: perm_refl.
- by split=> [[]//|hf]; split.
Qed.

(* The right unit law, in the same sense. *)
Lemma right_unit_equiv (m : chain L R) :
  chain_equiv (chain_bind m (fun x => chain_start x) erefl) m.
Proof.
split=> /=.
- by [].
- by [].
- by rewrite cats0 perm_refl.
- by split=> [[]//|hm]; split.
Qed.

End monad_laws.
