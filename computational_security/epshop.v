From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.

(**md**************************************************************************)
(* # epsHop, a language for chains of hops graded by a loss                   *)
(*                                                                            *)
(* A chain is a morphism of a category whose objects are acceptance           *)
(* probabilities, elements of an abstract real type, and whose morphisms are  *)
(* graded by the loss monoid: a morphism from a to b carries a list of        *)
(* labels together with a proof that `| a - b | is at most the total of that  *)
(* list.  Composition concatenates the two lists and is partial, its side     *)
(* condition being that the second fragment starts where the first stopped,   *)
(* and the identity carries the empty list.  Every fragment carries its own   *)
(* proof, so a finished chain has no pending obligation and a client reads a  *)
(* bound off it without restating a triangle inequality.                      *)
(*                                                                            *)
(* A label is an element of the parameter type L, and claim_of sends it to    *)
(* the claim it stands for: a source game, a target game and a cost, the      *)
(* claim asserting that the two games lie within that cost of each other.     *)
(* The loss of a chain is the list of the labels its steps invoked, so a      *)
(* finished chain names the assumptions its bound rests on and evaluates to   *)
(* their total.  A label fixing the data of the step it names is what makes   *)
(* the loss an assumption trail rather than a comment: the cost, the target   *)
(* and the justification written at a step are each checked against the       *)
(* label, and a step naming one assumption while proving another does not     *)
(* type-check.                                                                *)
(*                                                                            *)
(* The quantity a finished program bounds is called an advantage, after       *)
(* SSProve's AdvantageE G0 G1 A and adv_equiv and FCF's DistSingle_Adv: it    *)
(* is the distance between the game the chain opens at and the game it        *)
(* stops at, and a program that stops at the zero game therefore bounds the   *)
(* probability of the game it opened at.                                      *)
(*                                                                            *)
(* ## The surface syntax                                                      *)
(*                                                                            *)
(* A chain is written in a custom entry, delimited by \epsilon[ C ]{ }, whose *)
(* statements are its four constructors, the hop constructor spelled twice,   *)
(* and whose bracket carries the dictionary the program is read at.  The      *)
(* syntax is dual to piSMC of smc/pismc.v: piSMC writes what the parties do,  *)
(* epsHop writes what the security argument about them costs.                 *)
(*                                                                            *)
(* ```                                                                        *)
(* How to read a line of epsHop.                                              *)
(*                                                                            *)
(*   start g                the chain opens at game g, with no loss yet.      *)
(*   hop l e to g' by H     this hop invokes assumption l, loses e, reaches   *)
(*                         game g', guaranteed by H : |current - g'| <= e.    *)
(*                         Through claim_of, l fixes the source game, the     *)
(*                         target and the cost, and e, g' and H are each      *)
(*                         checked against it.                                *)
(*   same to g' by H        the game is rewritten to g' at no loss,           *)
(*                         guaranteed by H : current = g'.                    *)
(*   plus l c by H          hop l c to 0 by H, under a label whose target is  *)
(*                         the zero game: the last game lies within c of      *)
(*                         zero, so it is at most c and c enters the loss.    *)
(*                         Spelled plus so that a reader sees a term added    *)
(*                         rather than a hop taken.                           *)
(*   s ;; bound c by H      the chain returns its bound: the total of the     *)
(*                         loss is c, guaranteed by H : total = c, so the     *)
(*                         advantage of the chain, the distance between the   *)
(*                         game it opened at and the game it stopped at, is   *)
(*                         at most c, and c is still the total of the label   *)
(*                         list.                                              *)
(*                                                                            *)
(*   \epsilon[ C ]{ s }     the program s is read at the dictionary C, the    *)
(*                         claim function saying what each of its labels      *)
(*                         asserts.  A program with no terminal is a chain,   *)
(*                         and a chain named by a let enters a longer         *)
(*                         program as a statement.                            *)
(*                                                                            *)
(* The label slot names the assumption invoked and where (dcr_g, cpa_bob),    *)
(* the cost slot is that assumption's epsilon, and the proof slot says        *)
(* whether the term is assumed (a class bound) or exact (an equality).  All   *)
(* three are read back from the label's claim and compared with what was      *)
(* written.                                                                   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## What the syntax costs, and the levels it is built at                    *)
(*                                                                            *)
(* A token of a custom entry that lifts identifiers, as this one does, enters *)
(* the global lexer table, so the identifier it spells stops being readable   *)
(* as a term anywhere below.  This file spends five such identifiers, start,  *)
(* hop, same, to and plus; by is already an ssreflect keyword and costs       *)
(* nothing, and the terminal token bound, declared outside the entry, costs   *)
(* nothing either: below this file Locate start is a syntax error where       *)
(* Locate bound is not.  A scan of every .v file of the development names to, *)
(* start, hop and same at no site outside an epsHop chain, and plus only as a *)
(* bound variable of lib/bigop_ext.v, which does not require this file.  The  *)
(* first statement of that pair is spelled plus rather than add to keep the   *)
(* word of a chain clear of GRing.add, which benaloh_enc.v and paillier_enc.v *)
(* unfold.  The delimiter \epsilon[ is one lexer token, so it spends no       *)
(* identifier.  A named fragment enters a program as a statement through a    *)
(* bare identifier, the entry lifting an identifier and not an application,   *)
(* so a fragment applied to arguments has to be bound to a name first.  A     *)
(* frag statement rule taking a constr fragment would lift that restriction   *)
(* at the cost of one more global identifier, which is why there is none.     *)
(*                                                                            *)
(* Three levels are forced.  The proof slot sits at level 10, an application  *)
(* such as le_of_eq hop0_advantageE not parsing at level 0.  The label slot   *)
(* sits at level 0, where 0%N does not parse, so a client names its labels by *)
(* the constructors of a label type rather than writing numerals in the       *)
(* chain.  The terminal is a further closed notation on the same delimiter,   *)
(* separated by ;;, because it returns a chain_result where every other       *)
(* statement returns a chain: it cannot be an operand of the level-90         *)
(* separator, and that separator being right associative would swallow a      *)
(* single ; before the bound token.                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*                   claim R == what a label asserts: a source game, a        *)
(*                              target game and a cost, the assertion being   *)
(*                              that the two games lie within that cost of    *)
(*                              each other                                    *)
(*               Claim s t e == the claim that s and t lie within e of        *)
(*                              each other                                    *)
(*               claim_src c == the source game a claim names                 *)
(*               claim_tgt c == the target game a claim names                 *)
(*              claim_cost c == the cost a claim names, the summand the       *)
(*                              label contributes to a loss                   *)
(*          hop_obligation c == the proposition a claim asserts, and the      *)
(*                              type of the justification a hop supplies      *)
(*                    loss L == a list of labels, the free monoid the         *)
(*                              category is graded by                         *)
(*               loss_eval s == the numeric total of a list of labels, each   *)
(*                              label costing what its claim names            *)
(*             loss_eval_nil == the empty loss costs zero                     *)
(*             loss_eval_cat == concatenation of losses adds their costs      *)
(*                loss_eval1 == a one-label loss totals that label's cost     *)
(*              loss_total s == the same total as a left fold, which on a     *)
(*                              list of literal labels converts to a          *)
(*                              left-associated sum of their costs            *)
(*               foldl_lossE == a fold seeded at a totals a plus the loss     *)
(*                              it reads                                      *)
(*                loss_evalE == the sum and the fold agree                    *)
(*            chain claim_of == a head endpoint, a last endpoint, a loss,     *)
(*                              and the proof that the loss bounds the        *)
(*                              distance between the endpoints                *)
(*             chain_start g == the identity at g, logging nothing            *)
(*  chain_hop l e g' H He Hg == the step under the label l, whose source      *)
(*                              endpoint is the source of l's claim, at the   *)
(*                              cost e and to the target g' that He and Hg    *)
(*                              check against that claim, justified by H      *)
(*           chain_same g' H == the step to g' justified by an equality,      *)
(*                              logging nothing                               *)
(*      chain_then m frag Hb == m followed by frag, where Hb says frag        *)
(*                              starts where m stopped, logging the           *)
(*                              concatenated loss                             *)
(*              chain_result == an advantage, a loss, a bound, the proof      *)
(*                              that the bound bounds the advantage, and the  *)
(*                              proof that the bound is the total of the loss *)
(*          result_advantage == the quantity a result bounds, the             *)
(*                              distance between the two games of the         *)
(*                              program it came from                          *)
(*              result_total == the bound a result publishes is the total of  *)
(*                              its label list                                *)
(*  chain_result_of_chain m == the result a chain returns on its own, its     *)
(*                              advantage bounded by the total of its loss,   *)
(*                              a coercion inserted where a result is asked   *)
(*                              for of a program with no terminal             *)
(*         chain_bound b c H == b republished at the explicit bound c, which  *)
(*                              H says is the total b accumulated             *)
(*       chain_observable_eq == two chains agreeing on the three observable   *)
(*                              fields are equal                              *)
(*           chain_left_unit == composing a fragment after chain_start        *)
(*                              returns that fragment                         *)
(*          chain_right_unit == composing chain_start after a chain returns   *)
(*                              that chain                                    *)
(*               chain_assoc == the two groupings of a triple composition are *)
(*                              equal                                         *)
(*                  le_of_eq == an inequality out of an equality              *)
(*                   plus_le == a nonnegative quantity below c lies within c  *)
(*                              of the zero game                              *)
(*                advantage0 == the advantage of a nonnegative quantity       *)
(*                              against the zero game is that quantity        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* What a label asserts: its source game and its target game lie within its
   cost of each other.  The claim is the whole content of a label: it is what
   a step written under that label is checked against, so an
   assumption-conditional term of a bound cannot enter a chain under the name
   of a different assumption. *)
Record claim (R : realType) :=
  Claim { claim_src : R ; claim_tgt : R ; claim_cost : R }.

(* The proposition a claim asserts, and the type of the justification a hop
   supplies.  A step whose justification has this type is a step whose two
   games are the games its label is about. *)
Definition hop_obligation (R : realType) (c : claim R) : Prop :=
  `| claim_src c - claim_tgt c | <= claim_cost c.

(* An accumulated security loss, the free monoid on labels.  A list of labels
   rather than a real so that a finished chain still names the assumptions its
   bound rests on. *)
Definition loss (L : Type) := seq L.

Section epshop.
Variable L : Type.
Variable R : realType.
Variable claim_of : L -> claim R.

(* The numeric total of a loss, the monoid map to the additive reals along
   which every bound of this file is finally read.  A label costs what its
   claim names. *)
Definition loss_eval (s : loss L) : R := \sum_(l <- s) claim_cost (claim_of l).

(* The empty loss is the unit: a step that assumes nothing costs nothing. *)
Lemma loss_eval_nil : loss_eval [::] = 0.
Proof. by rewrite /loss_eval big_nil. Qed.

(* loss_eval is a monoid morphism.  Composing two fragments therefore adds
   their totals, which is what makes the total of a finished chain the sum of
   the epsilons its steps assume. *)
Lemma loss_eval_cat s1 s2 :
  loss_eval (s1 ++ s2) = loss_eval s1 + loss_eval s2.
Proof. by rewrite /loss_eval big_cat. Qed.

(* A one-label loss totals that label's cost.  It is where the bound of a
   single hop is read as the epsilon its label names. *)
Lemma loss_eval1 l : loss_eval [:: l] = claim_cost (claim_of l).
Proof. by rewrite /loss_eval big_cons big_nil addr0. Qed.

(* The same total as a left fold, seeded at the first label's cost.  On a
   list of literal labels it reduces by conversion to a left-associated sum
   of the epsilons those labels name, with no summation and no list left in
   it, which is what lets the terminal statement of a chain ask for a plain
   algebraic identity between that sum and the bound a client publishes. *)
Definition loss_total (s : loss L) : R :=
  if s is l :: s' then
    foldl (fun acc l' => acc + claim_cost (claim_of l'))
      (claim_cost (claim_of l)) s'
  else 0.

(* A fold seeded at a starts at a and adds the total of what it reads. *)
Lemma foldl_lossE a s :
  foldl (fun acc l => acc + claim_cost (claim_of l)) a s = a + loss_eval s.
Proof.
elim: s a => [|l s IH] a; first by rewrite loss_eval_nil addr0.
by rewrite /= IH /loss_eval big_cons addrA.
Qed.

(* The two readings of a loss agree.  The sum is the one a monoid morphism
   argument is run on, the fold is the one a concrete chain computes. *)
Lemma loss_evalE s : loss_eval s = loss_total s.
Proof.
case: s => [|l s]; first exact: loss_eval_nil.
by rewrite /loss_total foldl_lossE /loss_eval big_cons.
Qed.

(* A chain fragment: where it starts, where it now is, what it logged, and
   the distance bound itself.  The endpoints are named as a mathcomp path is,
   the head of the chain and the game it last reached.  chain_sound is
   unconditional, so a fragment is a theorem rather than an implication
   awaiting a hypothesis, and the four statements below each supply their own
   justification as a term. *)
Record chain := Chain {
  chain_head : R ;
  chain_last : R ;
  chain_loss : loss L ;
  chain_sound : `| chain_head - chain_last | <= loss_eval chain_loss }.

(* The identity morphism at g: it logs nothing and moves nothing.  It is
   where a chain opens, at the acceptance probability of a hybrid's first
   game. *)
Lemma start_sound (g : R) : `| g - g | <= loss_eval [::].
Proof. by rewrite subrr normr0 loss_eval_nil. Qed.

Definition chain_start (g : R) : chain :=
  {| chain_head := g ; chain_last := g ; chain_loss := [::] ;
     chain_sound := start_sound g |}.

(* One hop under the label l, justified by H.  It is the step that spends an
   assumption, the label naming which one, so every assumption-conditional
   term of a bound enters here.  The source endpoint is the source of l's
   claim, and the target g' is checked against that claim by Hg, so the games
   a hop joins are the games the assumption is about. *)
Lemma hop_sound (l : L) (g' : R) (H : hop_obligation (claim_of l))
    (Hg : g' = claim_tgt (claim_of l)) :
  `| claim_src (claim_of l) - g' | <= loss_eval [:: l].
Proof. by rewrite loss_eval1 Hg. Qed.

Definition chain_hop (l : L) (e g' : R) (H : hop_obligation (claim_of l))
    (He : e = claim_cost (claim_of l)) (Hg : g' = claim_tgt (claim_of l))
  : chain :=
  {| chain_head := claim_src (claim_of l) ; chain_last := g' ;
     chain_loss := [:: l] ; chain_sound := @hop_sound l g' H Hg |}.

(* An exact step, from x to g', logging nothing.  It is the step an
   information-theoretic identity between two games takes, so an
   unconditional rewriting leaves the loss of a chain as it stands. *)
Lemma same_sound (x g' : R) (H : x = g') : `| x - g' | <= loss_eval [::].
Proof. by rewrite H subrr normr0 loss_eval_nil. Qed.

Definition chain_same (x g' : R) (H : x = g') : chain :=
  {| chain_head := x ; chain_last := g' ; chain_loss := [::] ;
     chain_sound := @same_sound x g' H |}.

(* Composition, sound only when the continuation starts where the previous
   fragment stopped, which is the side condition Hb.  It is the one triangle
   inequality of the development, discharged once here so that a chain of any
   length needs none. *)
Lemma then_sound (m frag : chain) (Hb : chain_head frag = chain_last m) :
  `| chain_head m - chain_last frag |
  <= loss_eval (chain_loss m ++ chain_loss frag).
Proof.
rewrite loss_eval_cat.
apply: le_trans (ler_distD (chain_last m) _ _) _.
apply: lerD; first exact: chain_sound.
by rewrite -[X in `| X - _ |]Hb; exact: chain_sound.
Qed.

Definition chain_then (m frag : chain)
    (Hb : chain_head frag = chain_last m) : chain :=
  {| chain_head := chain_head m ; chain_last := chain_last frag ;
     chain_loss := chain_loss m ++ chain_loss frag ;
     chain_sound := @then_sound m frag Hb |}.

(* What a program returns: an advantage, a loss, a bound, the proof that the
   bound bounds the advantage, and the proof that the bound is the total of
   the loss.  This is the shape a security theorem is stated in, one number
   bounded rather than two compared.  The claim function indexes a result
   although no field reads it: it says which program the result came from,
   and it is what the elaborator solves from the type a client ascribes to
   its program before reading a single statement. *)
Record chain_result :=
  ChainResult {
    result_advantage : R ;
    result_loss : loss L ;
    result_bound : R ;
    result_sound : result_advantage <= result_bound ;
    (* The bound a result publishes is the total of its label list, so the
       loss stays the source of truth for that number after bound c by H
       republishes it.  This is what lets a reading along a family of
       security parameters sum the cost family of each label and land on the
       bound the program states. *)
    result_total : loss_total result_loss = result_bound }.

(* A chain returns the bound its loss totals, on the distance between the
   game it opened at and the game it stopped at.  That distance is the
   advantage of the chain: a program whose last game is the zero game
   therefore returns a bound on the probability of its head game.  This is
   the return of a program that ends without a terminal statement, and it is
   inserted by coercion where a result is asked for. *)
Lemma chain_result_sound (m : chain) :
  `| chain_head m - chain_last m | <= loss_total (chain_loss m).
Proof. by rewrite -loss_evalE; exact: chain_sound. Qed.

Definition chain_result_of_chain (m : chain) : chain_result :=
  {| result_advantage := `| chain_head m - chain_last m | ;
     result_loss := chain_loss m ; result_bound := loss_total (chain_loss m) ;
     result_sound := chain_result_sound m ; result_total := erefl |}.

(* The return statement: the result is republished at the explicit bound c,
   which H says is the total the loss accumulated.  Since loss_total on a
   list of literal labels converts to a left-associated sum of the epsilons
   those labels name, H is an algebraic identity between that sum and the
   number the client's theorem states, and no vocabulary of this file appears
   in it. *)
Lemma bound_sound (b : chain_result) (c : R)
    (H : result_bound b = c) :
  result_advantage b <= c.
Proof. by rewrite -H; exact: result_sound. Qed.

Definition chain_bound (b : chain_result) (c : R)
    (H : result_bound b = c) : chain_result :=
  {| result_advantage := result_advantage b ; result_loss := result_loss b ;
     result_bound := c ; result_sound := @bound_sound b c H ;
     result_total := etrans (result_total b) H |}.

End epshop.

Coercion chain_result_of_chain : chain >-> chain_result.

(* The claim function is solved from the expected type of a statement before
   its explicit arguments are elaborated, which is what the & records.  A
   client therefore names the claim function of its program once, in the
   bracket of \epsilon[ C ]{ }, and every label inside the program is read at
   that claim function. *)
Arguments chain_start {L R claim_of} & g.
Arguments chain_hop {L R claim_of} & l e g' H He Hg.
Arguments chain_same {L R claim_of} & {x} g' H.
Arguments chain_then {L R claim_of} & m frag Hb.
Arguments chain_result_of_chain {L R claim_of} & m.
Arguments chain_bound {L R claim_of} & b c H.

Section chain_laws.
Variable L : Type.
Variable R : realType.
Variable claim_of : L -> claim R.

(* Two chains agreeing on their three observable fields are equal.  The
   fourth field is a proof of a Boolean, whose uniqueness is bool_irrelevance,
   a lemma of mathcomp's eqtype; no proof irrelevance on Prop is needed, and
   the three laws below are therefore equalities of records rather than
   statements up to an equivalence. *)
Lemma chain_observable_eq (c1 c2 : chain claim_of) :
  chain_head c1 = chain_head c2 -> chain_last c1 = chain_last c2 ->
  chain_loss c1 = chain_loss c2 -> c1 = c2.
Proof.
case: c1 c2 => a1 b1 l1 s1 [a2 b2 l2 s2] /= Ha Hb Hl.
move: s1 s2; rewrite Ha Hb Hl => s1 s2.
by congr Chain; exact: bool_irrelevance.
Qed.

(* Left unit: composing a fragment after chain_start returns that fragment.
   The line that opens a chain therefore adds nothing to what follows it. *)
Lemma chain_left_unit (g : R) (frag : chain claim_of)
    (Hb : chain_head frag = g) :
  chain_then (chain_start g) frag Hb = frag.
Proof. by apply: chain_observable_eq; rewrite //= Hb. Qed.

(* Right unit: composing chain_start after a chain returns that chain, the
   loss half by cats0.  Closing a chain at the game it already stands at
   leaves the bound read off it. *)
Lemma chain_right_unit (m : chain claim_of) :
  chain_then m (chain_start (chain_last m)) erefl = m.
Proof. by apply: chain_observable_eq; rewrite //= cats0. Qed.

(* Associativity: the two groupings of a triple composition are equal, the
   loss half by catA and the two side conditions the same two proofs on both
   sides.  How the separators of a chain are grouped therefore leaves the
   assumptions it names and their total. *)
Lemma chain_assoc (m1 m2 m3 : chain claim_of)
    (H12 : chain_head m2 = chain_last m1)
    (H23 : chain_head m3 = chain_last m2) :
  chain_then (chain_then m1 m2 H12) m3 H23
  = chain_then m1 (chain_then m2 m3 H23) H12.
Proof. by apply: chain_observable_eq; rewrite //= catA. Qed.

End chain_laws.

(* An inequality out of an equality, for the hops whose gap is proved by an
   exact equality of advantages rather than bounded by an assumption.  It is
   what puts such a step in the shape chain_hop's justification takes. *)
Lemma le_of_eq (R : realType) (x y : R) : x = y -> x <= y.
Proof. by move=> ->. Qed.

(* A nonnegative quantity bounded by c lies within c of the zero game.  It is
   what puts a bound on one game in the shape the plus statement's
   justification takes, that statement being a hop whose target is zero.
   Naming: after the plus statement of the entry it justifies, not after the
   head symbol of its conclusion. *)
Lemma plus_le (R : realType) (x c : R) : 0 <= x -> x <= c -> `| x - 0 | <= c.
Proof. by move=> x0 xc; rewrite subr0 ger0_norm. Qed.

(* The advantage of a nonnegative quantity against the zero game is that
   quantity.  It is what reads a bound on the advantage of a program ending
   at the zero game back as a bound on the probability of its head game.
   Naming: [advantage] is the role this generic fact plays in the entry and
   [0] the zero game it is read against, neither being the head symbol of the
   equation. *)
Lemma advantage0 (R : realType) (x : R) : 0 <= x -> `| x - 0 | = x.
Proof. by move=> x0; rewrite subr0 ger0_norm. Qed.

Declare Scope epshop_scope.
Delimit Scope epshop_scope with eps.
Declare Custom Entry epshop.

(* Identifiers lift into the entry, so a named chain may stand as a
   statement. *)
Notation "x" := x (in custom epshop at level 0, x ident).

Notation "'start' g" := (chain_start g)
  (in custom epshop at level 80, g constr at level 0).

(* The two erefl are the checks that the cost and the target written here are
   the cost and the target the label's claim names. *)
Notation "'hop' l e 'to' g' 'by' H" := (chain_hop l e g' H erefl erefl)
  (in custom epshop at level 80, l constr at level 0, e constr at level 0,
   g' constr at level 0, H constr at level 10).

Notation "'same' 'to' g' 'by' H" := (chain_same g' H)
  (in custom epshop at level 80, g' constr at level 0, H constr at level 10).

(* plus l c by H is hop l c to 0 by H: the last game lies within c of the
   zero game, so its probability is at most c and c is added to the bound.
   Spelled plus so a reader sees a term added, not a hop taken. *)
Notation "'plus' l c 'by' H" := (chain_hop l c 0 H erefl erefl)
  (in custom epshop at level 80, l constr at level 0, c constr at level 0,
   H constr at level 10).

(* The statement separator.  The erefl discharges the side condition of
   chain_then by conversion, so two consecutive statements type-check exactly
   when the second opens at the game the first reached. *)
Notation "s1 ';' s2" := (chain_then s1 s2 erefl)
  (in custom epshop at level 90, right associativity).

(* The delimiter.  As in smc/pismc.v the brace form is prefixed, {| e |}
   being taken by the record syntax, and \epsilon[ is one lexer token.  The
   bracket carries the dictionary, the claim function saying what each label
   of the program asserts: a label is a bare constructor and names its claim
   through the dictionary alone, so the ascription the delimiter inserts is
   what lets the labels inside elaborate and a program needs no return type
   on its Definition.  A program with no terminal is a chain, composable as a
   fragment of a longer program, and where a result is asked for the coercion
   chain_result_of_chain reads off its advantage result. *)
Notation "'\epsilon[' C ']{' e '}'" := (e : chain C)
  (C constr at level 0, e custom epshop at level 99) : epshop_scope.

(* The terminal, a closed notation on the same delimiter: bound republishes
   the result at the explicit c its proof says the loss totals.  The chain
   reaching it is coerced to the result on its advantage, the distance
   between the game it opened at and the game it stopped at. *)
Notation "'\epsilon[' C ']{' s ';;' 'bound' c 'by' H '}'" :=
  ((chain_bound s c H : chain_result C))
  (C constr at level 0, s custom epshop at level 99, c constr at level 0,
   H constr at level 10) : epshop_scope.
