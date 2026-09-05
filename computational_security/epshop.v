From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.

(**md**************************************************************************)
(* # epsHop, a language for chains of hops graded by a loss                   *)
(*                                                                            *)
(* A chain is a morphism of a category whose objects are acceptance           *)
(* probabilities, elements of an abstract real type, and whose morphisms are  *)
(* graded by the loss monoid: a morphism from a to b carries a list of loss   *)
(* terms together with a proof that `| a - b | is at most the total of that   *)
(* list.  Composition concatenates the two lists and is partial, its side     *)
(* condition being that the second fragment starts where the first stopped,   *)
(* and the identity carries the empty list.  Every fragment carries its own   *)
(* proof, so a finished chain has no pending obligation and a client reads a  *)
(* bound off it without restating a triangle inequality.                      *)
(*                                                                            *)
(* A loss term is a label paired with a real.  The label names, through its   *)
(* own type, the assumption and the reduction a step invokes, so the loss of  *)
(* a finished chain is the list of assumptions its bound rests on, alongside  *)
(* their numeric total.  The label type L is a parameter of the whole file,   *)
(* so a client names its steps in whatever eqType it prefers.                 *)
(*                                                                            *)
(* ## The surface syntax                                                      *)
(*                                                                            *)
(* A chain is written in a custom entry, delimited by \epsilon{ }, whose four *)
(* statements are the four constructors.  The syntax is dual to piSMC of      *)
(* smc/pismc.v: piSMC writes what the parties do, epsHop writes what the      *)
(* security argument about them costs.                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* How to read a line of epsHop.                                              *)
(*                                                                            *)
(*   start g                the chain opens at game g, with no loss yet.      *)
(*   hop l e to g' by H     this hop invokes assumption l, loses e, reaches   *)
(*                         game g', guaranteed by H : |current - g'| <= e.    *)
(*   same to g' by H        the game is rewritten to g' at no loss,           *)
(*                         guaranteed by H : current = g'.                    *)
(*   s ;; bound l c by H    the chain is bounded: its last game is at most c, *)
(*                         a term labelled l, guaranteed by H : current <= c, *)
(*                         so the FIRST game is at most the total loss; the   *)
(*                         statement changes from a gap between two games     *)
(*                         to a bound on one.                                 *)
(*                                                                            *)
(* The label slot names the assumption invoked and where (dcr_g, cpa_bob),    *)
(* the cost slot is that assumption's epsilon, and the proof slot says        *)
(* whether the term is assumed (a class bound) or exact (an equality).        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## What the syntax costs, and the levels it is built at                    *)
(*                                                                            *)
(* A token of a custom entry that is not already a keyword enters the global  *)
(* lexer table, so the identifier it spells stops being readable as a term    *)
(* anywhere below.  This file spends five such identifiers, start, hop, same, *)
(* to and bound; by is already an ssreflect keyword and costs nothing.  A     *)
(* grep of every .v file of the development, comments and notation strings    *)
(* removed, finds bound at no site and to, start, hop and same only inside    *)
(* the epsHop chains of notes/probes/epshop_20260905.                         *)
(*                                                                            *)
(* Three levels are forced.  The proof slot sits at level 10, an application  *)
(* such as le_of_eq hop0_advantageE not parsing at level 0.  The label slot   *)
(* sits at level 0, where 0%N does not parse, so a client names its labels by *)
(* Definitions rather than writing numerals in the chain.  The terminal is a  *)
(* second closed notation on the same delimiter, separated by ;;, because it  *)
(* returns a chain_bound where every other statement returns a chain: it      *)
(* cannot be an operand of the level-90 separator, and that separator being   *)
(* right associative would swallow a single ; before the bound keyword.       *)
(*                                                                            *)
(* ```                                                                        *)
(*             loss_term L R == a label in L paired with a real cost          *)
(*          loss_term_cost a == the real cost of one loss term                *)
(*                  loss L R == a list of loss terms, the free monoid the     *)
(*                              category is graded by                         *)
(*               loss_eval s == the numeric total of a list of loss terms     *)
(*             loss_eval_nil == the empty loss costs zero                     *)
(*             loss_eval_cat == concatenation of losses adds their costs      *)
(*                loss_eval1 == a one-term loss totals that term              *)
(*                 chain L R == a first endpoint, a current endpoint, a loss, *)
(*                              and the proof that the loss bounds the        *)
(*                              distance between the endpoints                *)
(*             chain_start g == the identity at g, logging nothing            *)
(*        chain_hop l e g' H == the step to g' at cost e under the label l,   *)
(*                              justified by H, whose source endpoint is read *)
(*                              off H                                         *)
(*           chain_same g' H == the step to g' justified by an equality,      *)
(*                              logging nothing                               *)
(*      chain_then m frag Hb == m followed by frag, where Hb says frag        *)
(*                              starts where m stopped, logging the           *)
(*                              concatenated loss                             *)
(*               chain_bound == a first endpoint, a loss, and the proof that  *)
(*                              the loss bounds that endpoint                 *)
(*       chain_eval m l c Hc == the chain_bound obtained from m by charging   *)
(*                              LossTerm l c for its current endpoint         *)
(*            loss_term_code == a loss term read as a label and cost pair,    *)
(*                              the coding its eqType is copied along         *)
(*       chain_observable_eq == two chains agreeing on the three observable   *)
(*                              fields are equal                              *)
(*           chain_left_unit == composing a fragment after chain_start        *)
(*                              returns that fragment                         *)
(*          chain_right_unit == composing chain_start after a chain returns   *)
(*                              that chain                                    *)
(*               chain_assoc == the two groupings of a triple composition are *)
(*                              equal                                         *)
(*                  le_of_eq == an inequality out of an equality              *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section epshop.
Variable L : eqType.
Variable R : realType.

(* One term of a security loss: the label naming the assumption and the
   reduction that a step invokes, and the real that step costs. *)
Inductive loss_term := LossTerm of L & R.

(* The real a loss term contributes, its label discarded.  It is what
   loss_eval adds, so the numeric total of a loss forgets every label. *)
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

(* loss_eval is a monoid morphism.  Composing two fragments therefore adds
   their totals, which is what makes the total of a finished chain the sum of
   the epsilons its steps assume. *)
Lemma loss_eval_cat s1 s2 :
  loss_eval (s1 ++ s2) = loss_eval s1 + loss_eval s2.
Proof. by rewrite /loss_eval big_cat. Qed.

(* A one-term loss totals that term.  It is where the bound of a single hop
   is read as the epsilon its label names. *)
Lemma loss_eval1 l c : loss_eval [:: LossTerm l c] = c.
Proof. by rewrite /loss_eval big_cons big_nil addr0. Qed.

(* A chain fragment: where it starts, where it now is, what it logged, and
   the distance bound itself.  chain_sound is unconditional, so a fragment is
   a theorem rather than an implication awaiting a hypothesis, and the four
   statements below each supply their own justification as a term. *)
Record chain := Chain {
  chain_first : R ;
  chain_current : R ;
  chain_loss : loss ;
  chain_sound : `| chain_first - chain_current | <= loss_eval chain_loss }.

(* The identity morphism at g: it logs nothing and moves nothing.  It is
   where a chain opens, at the acceptance probability of a hybrid's first
   game. *)
Lemma start_sound (g : R) : `| g - g | <= loss_eval [::].
Proof. by rewrite subrr normr0 loss_eval_nil. Qed.

Definition chain_start (g : R) : chain :=
  {| chain_first := g ; chain_current := g ; chain_loss := [::] ;
     chain_sound := start_sound g |}.

(* One hop, from x to g' at e under the label l, justified by H.  It is the
   step that spends an assumption, the label naming which one, so every
   assumption-conditional term of a bound enters here.  The source endpoint x
   is determined by the type of H, which is what lets a chain leave it
   unwritten. *)
Lemma hop_sound (l : L) (e x g' : R) (H : `| x - g' | <= e) :
  `| x - g' | <= loss_eval [:: LossTerm l e].
Proof. by rewrite loss_eval1. Qed.

Definition chain_hop (l : L) (e x g' : R) (H : `| x - g' | <= e) : chain :=
  {| chain_first := x ; chain_current := g' ;
     chain_loss := [:: LossTerm l e] ;
     chain_sound := @hop_sound l e x g' H |}.

(* An exact step, from x to g', logging nothing.  It is the step an
   information-theoretic identity between two games takes, so an
   unconditional rewriting leaves the loss of a chain as it stands. *)
Lemma same_sound (x g' : R) (H : x = g') : `| x - g' | <= loss_eval [::].
Proof. by rewrite H subrr normr0 loss_eval_nil. Qed.

Definition chain_same (x g' : R) (H : x = g') : chain :=
  {| chain_first := x ; chain_current := g' ; chain_loss := [::] ;
     chain_sound := @same_sound x g' H |}.

(* Composition, sound only when the continuation starts where the previous
   fragment stopped, which is the side condition Hb.  It is the one triangle
   inequality of the development, discharged once here so that a chain of any
   length needs none. *)
Lemma then_sound (m frag : chain) (Hb : chain_first frag = chain_current m) :
  `| chain_first m - chain_current frag |
  <= loss_eval (chain_loss m ++ chain_loss frag).
Proof.
rewrite loss_eval_cat.
apply: le_trans (ler_distD (chain_current m) _ _) _.
apply: lerD; first exact: chain_sound.
by rewrite -[X in `| X - _ |]Hb; exact: chain_sound.
Qed.

Definition chain_then (m frag : chain)
    (Hb : chain_first frag = chain_current m) : chain :=
  {| chain_first := chain_first m ; chain_current := chain_current frag ;
     chain_loss := chain_loss m ++ chain_loss frag ;
     chain_sound := @then_sound m frag Hb |}.

(* Where the statement changes sort: from a distance between two acceptance
   probabilities to a bound on one.  This is the shape a security theorem is
   stated in, the endpoint of the chain having been bounded rather than
   compared. *)
Record chain_bound := ChainBound {
  bound_first : R ;
  bound_loss : loss ;
  bound_sound : bound_first <= loss_eval bound_loss }.

(* Charging the current endpoint at c under the label l turns a chain into
   such a bound: the distance the chain proved plus the bound on where it
   stopped is a bound on where it started. *)
Lemma eval_sound (m : chain) (l : L) (c : R) (Hc : chain_current m <= c) :
  chain_first m <= loss_eval (chain_loss m ++ [:: LossTerm l c]).
Proof.
rewrite loss_eval_cat loss_eval1.
rewrite -(subrK (chain_current m) (chain_first m)); apply: lerD Hc.
exact: le_trans (ler_norm _) (chain_sound m).
Qed.

Definition chain_eval (m : chain) (l : L) (c : R)
    (Hc : chain_current m <= c) : chain_bound :=
  {| bound_first := chain_first m ;
     bound_loss := chain_loss m ++ [:: LossTerm l c] ;
     bound_sound := @eval_sound m l c Hc |}.

End epshop.

Arguments chain_start {L R} g.
Arguments chain_hop {L R} l e {x} g' H.
Arguments chain_same {L R} {x} g' H.
Arguments chain_then {L R} m frag Hb.
Arguments chain_eval {L R} m l c Hc.

(* A loss term is a label and a cost, so its equality is that of the pair.
   The coding is what the eqType instance below is copied along. *)
Definition loss_term_code (L : eqType) (R : realType) (a : loss_term L R)
  : L * R := let: LossTerm l c := a in (l, c).

Definition loss_term_decode (L : eqType) (R : realType) (x : L * R)
  : loss_term L R := LossTerm x.1 x.2.

Lemma loss_term_codeK (L : eqType) (R : realType) :
  cancel (@loss_term_code L R) (@loss_term_decode L R).
Proof. by case. Qed.

HB.instance Definition _ (L : eqType) (R : realType) :=
  Equality.copy (loss_term L R) (can_type (@loss_term_codeK L R)).

Section chain_laws.
Variable L : eqType.
Variable R : realType.

(* Two chains agreeing on their three observable fields are equal.  The
   fourth field is a proof of a Boolean, whose uniqueness is bool_irrelevance,
   a lemma of mathcomp's eqtype; no proof irrelevance on Prop is needed, and
   the three laws below are therefore equalities of records rather than
   statements up to an equivalence. *)
Lemma chain_observable_eq (c1 c2 : chain L R) :
  chain_first c1 = chain_first c2 -> chain_current c1 = chain_current c2 ->
  chain_loss c1 = chain_loss c2 -> c1 = c2.
Proof.
case: c1 c2 => a1 b1 l1 s1 [a2 b2 l2 s2] /= Ha Hb Hl.
move: s1 s2; rewrite Ha Hb Hl => s1 s2.
by congr Chain; exact: bool_irrelevance.
Qed.

(* Left unit: composing a fragment after chain_start returns that fragment.
   The line that opens a chain therefore adds nothing to what follows it. *)
Lemma chain_left_unit (g : R) (frag : chain L R)
    (Hb : chain_first frag = g) :
  chain_then (chain_start g) frag Hb = frag.
Proof. by apply: chain_observable_eq; rewrite //= Hb. Qed.

(* Right unit: composing chain_start after a chain returns that chain, the
   loss half by cats0.  Closing a chain at the game it already stands at
   leaves the bound read off it. *)
Lemma chain_right_unit (m : chain L R) :
  chain_then m (chain_start (chain_current m)) erefl = m.
Proof. by apply: chain_observable_eq; rewrite //= cats0. Qed.

(* Associativity: the two groupings of a triple composition are equal, the
   loss half by catA and the two side conditions the same two proofs on both
   sides.  How the separators of a chain are grouped therefore leaves the
   assumptions it names and their total. *)
Lemma chain_assoc (m1 m2 m3 : chain L R)
    (H12 : chain_first m2 = chain_current m1)
    (H23 : chain_first m3 = chain_current m2) :
  chain_then (chain_then m1 m2 H12) m3 H23
  = chain_then m1 (chain_then m2 m3 H23) H12.
Proof. by apply: chain_observable_eq; rewrite //= catA. Qed.

End chain_laws.

(* An inequality out of an equality, for the hops whose gap is proved by an
   exact equality of advantages rather than bounded by an assumption.  It is
   what puts such a step in the shape chain_hop's justification takes. *)
Lemma le_of_eq (R : realType) (x y : R) : x = y -> x <= y.
Proof. by move=> ->. Qed.

Declare Scope epshop_scope.
Delimit Scope epshop_scope with eps.
Declare Custom Entry epshop.

(* The delimiter.  As in smc/pismc.v the brace form is prefixed, {| e |}
   being taken by the record syntax, and \epsilon{ is one lexer token. *)
Notation "'\epsilon{' e '}'" := e (e custom epshop at level 99) : epshop_scope.

(* Identifiers lift into the entry, so a named chain may stand as a
   statement. *)
Notation "x" := x (in custom epshop at level 0, x ident).

Notation "'start' g" := (chain_start g)
  (in custom epshop at level 80, g constr at level 0).

Notation "'hop' l e 'to' g' 'by' H" := (chain_hop l e g' H)
  (in custom epshop at level 80, l constr at level 0, e constr at level 0,
   g' constr at level 0, H constr at level 10).

Notation "'same' 'to' g' 'by' H" := (chain_same g' H)
  (in custom epshop at level 80, g' constr at level 0, H constr at level 10).

(* The statement separator.  The erefl discharges the side condition of
   chain_then by conversion, so two consecutive statements type-check exactly
   when the second opens at the game the first reached. *)
Notation "s1 ';' s2" := (chain_then s1 s2 erefl)
  (in custom epshop at level 90, right associativity).

(* The terminal, a second closed notation on the same delimiter. *)
Notation "'\epsilon{' s ';;' 'bound' l c 'by' H '}'" := (chain_eval s l c H)
  (s custom epshop at level 99, l constr at level 0, c constr at level 0,
   H constr at level 10) : epshop_scope.
