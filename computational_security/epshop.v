From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.

(**md**************************************************************************)
(* # epsHop, hopping scripts graded by a loss                                 *)
(*                                                                            *)
(* A script is a value of hop_script C a b s, indexed by the game a it opens  *)
(* at, the game b it stops at and the list s of labels it spends, and built   *)
(* from three steps only: a stop, a hop under a label, and an exact step.     *)
(* Its bound is `| a - b | <= loss_eval s, the distance between the two games *)
(* being at most the total of the labels it spent.  Nothing but the three     *)
(* steps inhabits hop_script C a b s, so every label of s has its claim       *)
(* proved (hop_script_obligations), and a client reads a bound off a finished *)
(* script without restating a triangle inequality.                            *)
(*                                                                            *)
(* A label is an element of the parameter type L, and claim_of sends it to    *)
(* the claim it stands for: the game it goes from, the game it goes to and a  *)
(* loss term, the claim asserting that the two games lie within that loss of  *)
(* each other.  The word is Bellare and Rogaway's, EUROCRYPT 2006, section    *)
(* 3.4: "for an additive lossy transformation, epsilon is the loss term", and *)
(* the bound of a script "is obtained by adding up all the loss terms".  FCF  *)
(* and CertiCrypt reserve cost for the running time of a program, which is    *)
(* why that word names nothing here.  The loss of a script is the list of the *)
(* labels its steps invoked, so a finished script names the assumptions its   *)
(* bound rests on and evaluates to their total.  A label fixing the data of   *)
(* the step it names is what makes the loss an assumption trail: the game a   *)
(* hop goes to and the justification written at it are each checked against   *)
(* the label, and a step naming one assumption while proving another does not *)
(* type-check.                                                                *)
(*                                                                            *)
(* The quantity a finished script bounds is called an advantage, after        *)
(* SSProve's AdvantageE G0 G1 A and adv_equiv and FCF's DistSingle_Adv: it is *)
(* the distance between the game the script opens at and the game it stops    *)
(* at, and a script that stops at the zero game therefore bounds the          *)
(* probability of the game it opened at.  epsHop is dual to piSMC of          *)
(* smc/pismc.v: piSMC writes what the parties do, epsHop writes what the      *)
(* security argument about them loses.                                        *)
(*                                                                            *)
(* ## The tactic surface                                                      *)
(*                                                                            *)
(* Module EpsHopTac, activated by Import, writes a script one tactic line per *)
(* step on a goal of type hop_script: hop l to g' by (H), same to g' by (H),  *)
(* plus l by (H), stop.  The residual goal after each line is the script type *)
(* of the rest, printed as \hops[ C ] `| g' - z | <= s.  A script type is     *)
(* written \hops[ C ] `| a - b | <= s, and a compound game or list in it is   *)
(* parenthesised.  The proof slots are elaborated against the goal, so a      *)
(* proof term with holes is written in parentheses.  The tokens hop, same,    *)
(* plus, stop and to stay free term identifiers below this file.  The         *)
(* normaliser of the target equation is cbn, which reduces a client           *)
(* dictionary in a millisecond where lazy and vm_compute run past 600 s and   *)
(* 125 s.                                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*                   claim R == what a label asserts: the game it goes from,  *)
(*                              the game it goes to and a loss term, the      *)
(*                              assertion being that the two games lie        *)
(*                              within that loss of each other                *)
(*               Claim s t e == the claim that s and t lie within e of        *)
(*                              each other                                    *)
(*              claim_from c == the game a claim goes from                    *)
(*                claim_to c == the game a claim goes to                      *)
(*              claim_loss c == the loss term a claim names, the summand the  *)
(*                              label contributes to a loss                   *)
(*          hop_obligation c == the proposition a claim asserts, and the      *)
(*                              type of the justification a hop supplies      *)
(*                    loss L == a list of labels, the free monoid the         *)
(*                              scripts are graded by                         *)
(*               loss_eval s == the numeric total of a list of labels, each   *)
(*                              label losing what its claim names             *)
(*             loss_eval_nil == the empty loss totals zero                    *)
(*             loss_eval_cat == concatenation of losses adds their totals     *)
(*                loss_eval1 == a one-label loss totals its label's loss term *)
(*              loss_total s == the same total as a left fold, which on a     *)
(*                              list of literal labels converts to a          *)
(*                              left-associated sum of their loss terms       *)
(*               foldl_lossE == a fold seeded at a totals a plus the loss     *)
(*                              it reads                                      *)
(*                loss_evalE == the sum and the fold agree                    *)
(*             script_result == what a script returns: an advantage, a        *)
(*                              loss, a bound, the proof that the bound       *)
(*                              bounds the advantage, and the proof that      *)
(*                              the bound is the total of the loss            *)
(*          result_advantage == the quantity a result bounds, the             *)
(*                              distance between the two games of the         *)
(*                              script it came from                           *)
(*              result_total == the bound a result publishes is the total of  *)
(*                              its label list                                *)
(*        hop_script C a b s == a script from game a to game b spending the   *)
(*                              labels of s, built from the three steps below *)
(*                              only, so each label of s had its claim proved *)
(*             script_stop g == the empty script at g, logging nothing        *)
(*    script_hop l g' H Hg p == the step under l from the game l's claim goes *)
(*                              from to g', which Hg checks against that      *)
(*                              claim, justified by H, followed by p          *)
(*        script_same g' H p == the step to g' justified by the equality H,   *)
(*                              followed by p, logging nothing                *)
(*          script_hop_sound == a hop under l followed by a bound on the rest *)
(*                              bounds the extended loss                      *)
(*          hop_script_sound == a script from a to b over s bounds | a - b |  *)
(*                              by loss_eval s                                *)
(*          hop_script_total == the same bound at loss_total s                *)
(*        loss_obligations s == the conjunction of the claims of the          *)
(*                              labels of s                                   *)
(*    hop_script_obligations == every label of a script has its claim proved  *)
(*            hop_script_nil == a script over [::] joins equal games          *)
(*      hop_script_not_total == some script type is uninhabited               *)
(*        result_of_script p == the result a script returns, its label list   *)
(*                              the index s of its type                       *)
(*  \hops[ C ] `|a - b| <= s == the type hop_script C a b s                   *)
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

(* What a label asserts: its two games lie within its loss term of each
   other.  A step is checked against its label's claim, so no term can enter
   under another assumption's name. *)
Record claim (R : realType) :=
  Claim {
    (* the game the label goes from *)
    claim_from : R ;
    (* the game the label goes to *)
    claim_to : R ;
    (* the loss term, the summand the label adds to a loss *)
    claim_loss : R }.

(* The proposition a claim asserts, and the type of the justification a hop
   supplies.  A step whose justification has this type is a step whose two
   games are the games its label is about. *)
Definition hop_obligation (R : realType) (c : claim R) : Prop :=
  `| claim_from c - claim_to c | <= claim_loss c.

(* An accumulated security loss, the free monoid on labels.  A list of
   labels, not a real, so a finished script still names its assumptions. *)
Definition loss (L : Type) := seq L.

Section epshop.
Variable L : Type.
Variable R : realType.
Variable claim_of : L -> claim R.

(* The numeric total of a loss, each label losing what its claim names.  It
   is the monoid map to the reals along which every bound of this file is
   finally read. *)
Definition loss_eval (s : loss L) : R := \sum_(l <- s) claim_loss (claim_of l).

(* The empty loss is the unit: a step that assumes nothing loses nothing. *)
Lemma loss_eval_nil : loss_eval [::] = 0.
Proof. by rewrite /loss_eval big_nil. Qed.

(* loss_eval is a monoid morphism.  Concatenating two losses adds their
   totals, so a finished script's total is the sum of its epsilons. *)
Lemma loss_eval_cat s1 s2 :
  loss_eval (s1 ++ s2) = loss_eval s1 + loss_eval s2.
Proof. by rewrite /loss_eval big_cat. Qed.

(* A one-label loss totals that label's loss term.  It is where the bound of
   a single hop is read as the epsilon its label names. *)
Lemma loss_eval1 l : loss_eval [:: l] = claim_loss (claim_of l).
Proof. by rewrite /loss_eval big_cons big_nil addr0. Qed.

(* The same total as a left fold, seeded at the first label's loss term.  On
   literal labels it computes a left-associated sum, the shape a theorem's
   bound converts to. *)
Definition loss_total (s : loss L) : R :=
  if s is l :: s' then
    foldl (fun acc l' => acc + claim_loss (claim_of l'))
      (claim_loss (claim_of l)) s'
  else 0.

(* A fold seeded at a starts at a and adds the total of what it reads. *)
Lemma foldl_lossE a s :
  foldl (fun acc l => acc + claim_loss (claim_of l)) a s = a + loss_eval s.
Proof.
elim: s a => [|l s IH] a; first by rewrite loss_eval_nil addr0.
by rewrite /= IH /loss_eval big_cons addrA.
Qed.

(* The two readings of a loss agree.  A monoid morphism argument runs on the
   sum, a concrete script computes the fold. *)
Lemma loss_evalE s : loss_eval s = loss_total s.
Proof.
case: s => [|l s]; first exact: loss_eval_nil.
by rewrite /loss_total foldl_lossE /loss_eval big_cons.
Qed.

(* | g - g | is within the empty loss.  It justifies the step where a
   script stops, logging nothing. *)
Lemma start_sound (g : R) : `| g - g | <= loss_eval [::].
Proof. by rewrite subrr normr0 loss_eval_nil. Qed.

(* What a script returns: an advantage, a loss, a bound, and the proofs
   relating the three.  A security theorem takes this shape, one number
   bounded. *)
Record script_result :=
  ScriptResult {
    (* the quantity the script bounds *)
    result_advantage : R ;
    (* the labels the script spent *)
    result_loss : loss L ;
    (* the number the script publishes *)
    result_bound : R ;
    (* the advantage is at most that bound *)
    result_sound : result_advantage <= result_bound ;
    (* the bound is the total of the label list, which stays its source *)
    result_total : loss_total result_loss = result_bound }.

End epshop.

(* An inequality out of an equality, for a hop proved by an exact equality of
   advantages.  It puts such a step in the shape a hop's justification
   takes. *)
Lemma le_of_eq (R : realType) (x y : R) : x = y -> x <= y.
Proof. by move=> ->. Qed.

(* A nonnegative quantity bounded by c satisfies | x - 0 | <= c.  It is the
   shape a plus step's justification takes, that step being a hop to
   zero. *)
Lemma plus_le (R : realType) (x c : R) : 0 <= x -> x <= c -> `| x - 0 | <= c.
Proof. by move=> x0 xc; rewrite subr0 ger0_norm. Qed.

(* | x - 0 | = x for nonnegative x: the advantage against the zero game is
   the quantity itself.  It reads a script ending at zero back as a bound on
   its opening game. *)
Lemma advantage0 (R : realType) (x : R) : 0 <= x -> `| x - 0 | = x.
Proof. by move=> x0; rewrite subr0 ger0_norm. Qed.

Declare Scope epshop_scope.
Delimit Scope epshop_scope with eps.

Section hop_script.
Variable L : Type.
Variable R : realType.
Variable claim_of : L -> claim R.

(* A hop under l followed by a bound from its target is bounded by the loss
   extended by l.  It spends assumption l first and leaves the rest of the
   script to bound. *)
Lemma script_hop_sound (l : L) (g' z : R) (s : loss L) :
  hop_obligation (claim_of l) -> g' = claim_to (claim_of l) ->
  `| g' - z | <= loss_eval claim_of s ->
  `| claim_from (claim_of l) - z | <= loss_eval claim_of (l :: s).
Proof.
move=> ob gE gz; rewrite -cat1s loss_eval_cat loss_eval1.
by apply: le_trans (ler_distD g' _ _) _; apply: lerD; rewrite // gE.
Qed.

(* A derivation that a goes to b spending the labels of s, one constructor
   per step.  Nothing but steps inhabits it, so its label list is the
   assumptions its bound rests on. *)
Inductive hop_script : R -> R -> loss L -> Type :=
| script_stop g : hop_script g g [::]
| script_hop l g' z s of hop_obligation (claim_of l)
    & g' = claim_to (claim_of l) & hop_script g' z s
  : hop_script (claim_from (claim_of l)) z (l :: s)
| script_same x g' z s of x = g' & hop_script g' z s : hop_script x z s.

(* A script from a to b over s bounds | a - b | by the sum of s.  It is the
   one triangle argument every script is read through. *)
Lemma hop_script_sound a b s :
  hop_script a b s -> `| a - b | <= loss_eval claim_of s.
Proof.
elim=> [|l g' z s' ob gE _ /(script_hop_sound ob gE) //|x g' z s' -> //].
exact: start_sound.
Qed.

(* A script from a to b over s bounds | a - b | by the fold of s.  On
   literal labels this total converts to the sum a theorem states. *)
Lemma hop_script_total a b s :
  hop_script a b s -> `| a - b | <= loss_total claim_of s.
Proof. rewrite -loss_evalE; exact: hop_script_sound. Qed.

(* The conjunction of the claims of a label list.  It is what a script
   certifies about the assumptions it names. *)
Fixpoint loss_obligations (s : loss L) : Prop :=
  if s is l :: s' then hop_obligation (claim_of l) /\ loss_obligations s'
  else True.

(* Every label of a script has its claim proved.  The label list of a script
   is therefore an assumption trail checked by the kernel. *)
Lemma hop_script_obligations a b s : hop_script a b s -> loss_obligations s.
Proof. by elim. Qed.

(* A script over the empty loss joins equal games.  A bound that spends no
   assumption is an identity of games. *)
Lemma hop_script_nil a b s : hop_script a b s -> s = [::] -> a = b.
Proof. by elim=> // x g' z s' -> _. Qed.

(* The result a script returns: its games' distance, its label list, their
   total.  The sequence terminal reads the labels off the index s. *)
Definition result_of_script a b s (p : hop_script a b s) :
  script_result claim_of :=
  ScriptResult (hop_script_total p) erefl.

End hop_script.

Arguments script_hop_sound {L R claim_of} l g' {z s}.
Arguments hop_script {L R} claim_of _ _ _.
Arguments script_stop {L R claim_of g}.
Arguments script_hop {L R claim_of} l g' {z s} _ _ _.
Arguments script_same {L R claim_of x} g' {z s} _ _.
Arguments hop_script_sound {L R claim_of a b s}.
Arguments hop_script_total {L R claim_of a b s}.
Arguments hop_script_obligations {L R claim_of a b s}.
Arguments hop_script_nil {L R claim_of a b s}.
Arguments result_of_script {L R claim_of a b s}.

(* Some script type is uninhabited: the empty loss over the games 0 and 1.
   A script is therefore a witness, and its label list is data read by
   result_of_script. *)
Lemma hop_script_not_total (R : realType) :
  (forall (C : unit -> claim R) a b s, hop_script C a b s) -> False.
Proof.
move=> /(_ (fun=> Claim 0 0 0) 0 1 [::]) /hop_script_nil /(_ erefl) /esym.
exact/eqP/oner_neq0.
Qed.

(* A script type displayed as the inequality it witnesses.  A compound game
   or list is written in parentheses, since the b slot reads x - y - z as
   x - (y - z). *)
Notation "'\hops[' C ']' '`|' a '-' b '|' '<=' s" := (hop_script C a b s)
  (at level 70, C constr at level 99, a constr at level 49,
   b constr at level 49, s constr at level 0,
   format "'[hv' \hops[  C  ]  `|  a  -  b  |  '/' <=  s ']'")
  : epshop_scope.

(* The tactic surface: one line per step on a hop_script goal, activated by
   Import EpsHopTac.  hop reads the dictionary off the goal and states the
   target equation first, so a wrong game is reported with both games. *)
Module EpsHopTac.

Tactic Notation "stop" := exact: script_stop.

Tactic Notation "hop" constr(l) "to" uconstr(g) "by" uconstr(H) :=
  lazymatch goal with
  | |- hop_script ?C _ _ _ =>
      let t := eval cbn in (claim_to (C l)) in
      let gE := fresh "gE" in
      have gE : g = t := erefl;
      refine (script_hop (claim_of := C) l g H gE _); clear gE
  end.

Tactic Notation "same" "to" uconstr(g) "by" uconstr(H) :=
  refine (script_same g H _).

Tactic Notation "plus" constr(l) "by" uconstr(H) :=
  hop l to 0 by H; stop.

End EpsHopTac.
