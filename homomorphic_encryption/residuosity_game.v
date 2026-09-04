From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.

(**md**************************************************************************)
(* # The e-th residuosity problem                                             *)
(*                                                                            *)
(* Fix a finite commutative unit ring T and an exponent e.  The e-th          *)
(* residuosity problem at T is to tell a uniform unit of T from the e-th      *)
(* power of a uniform unit.  A distinguisher is a record: a finite state      *)
(* type, a law over that type, and a Boolean decision on the state and the    *)
(* challenge ring element.  Its advantage is the absolute gap between the     *)
(* two acceptance probabilities, and an assumption is a Boolean class of      *)
(* distinguishers together with an epsilon every member's advantage stays     *)
(* below.                                                                     *)
(*                                                                            *)
(* Two readings.  At T = Z/n^2 Z and e = n the problem is decisional          *)
(* composite residuosity, Paillier 1999 Conjecture 1: the n-th powers in      *)
(* the units of Z/n^2 Z are the ciphertexts of the plaintext zero, and        *)
(* telling one from a uniform unit is telling a Paillier ciphertext of zero   *)
(* from a uniform ciphertext.  At T = Z/nZ and e = r it is Benaloh 1994's     *)
(* higher residuosity problem, r-th residues in the units of Z/nZ.  The two   *)
(* schemes therefore make the same assumption at two rings, which is why it   *)
(* is written once here and instantiated in the two scheme files.             *)
(*                                                                            *)
(* ## Role map                                                                *)
(*                                                                            *)
(* | role             | identifier                                          | *)
(* |------------------|-----------------------------------------------------| *)
(* | challenge laws   | unit_fdist, residue_fdist                           | *)
(* | distinguisher    | residuosity_distinguisher                           | *)
(* | advantage        | residuosity_advantage                               | *)
(* | assumption       | residuosity_assumption                              | *)
(* | key fact         | unit_fdist_translateE                               | *)
(* | textbook reading | unit_fdistE, residue_fdistE                         | *)
(* | inhabitant       | decide_constant_assumption                          | *)
(*                                                                            *)
(* The key fact is unit_fdist_translateE: multiplication by a unit is a       *)
(* bijection of the unit group, and a bijection fixes the uniform law, so     *)
(* pushing the unit challenge along x |-> val a * x returns the unit          *)
(* challenge.  This is Katz and Lindell 2015, Lemma 11.15, p. 400.  Its       *)
(* position in a reduction from a residue-class encryption scheme: a          *)
(* ciphertext of the plaintext m is g ^+ m times a ciphertext of zero, so     *)
(* once the challenge is a uniform unit rather than a residue, multiplying    *)
(* it by g ^+ m erases m, and the adversary's two experiments coincide.       *)
(* The reduction is then two calls to the assumption, one to move each        *)
(* experiment from the residue law to the unit law, which is where the        *)
(* factor two in the derived IND-CPA epsilon comes from.  Katz and Lindell    *)
(* 2015, Theorem 13.13, pp. 498-499, is that reduction at Paillier.           *)
(*                                                                            *)
(* unit_fdistE and residue_fdistE align the two laws with the textbook        *)
(* wording: each is the uniform law on a subset of T, the units and the       *)
(* e-th residues.  A reader who knows the problem in the form: tell a         *)
(* uniform element of the unit group from a uniform e-th residue, reads it    *)
(* off these two equations.                                                   *)
(*                                                                            *)
(* decide_constant_assumption inhabits the assumption record with content:    *)
(* a distinguisher whose verdict ignores the challenge has advantage zero,    *)
(* so that class carries epsilon zero and its bound is proved rather than     *)
(* assumed.  What it shows is that a statement restricted to a residuosity    *)
(* class is not empty for want of a record to read it at.  What it does not   *)
(* show is that a scheme's own class is inhabited at a useful epsilon.        *)
(*                                                                            *)
(* ```                                                                        *)
(*              ring_units T == the unit group of T as a finite type          *)
(*           card_ring_units == the unit group is nonempty, in the            *)
(*                              successor form fdist_uniform takes            *)
(*                unit_fdist == a uniform unit read as a ring element,        *)
(*                              the first challenge law                       *)
(*             residue_fdist == the e-th power of a uniform unit, the         *)
(*                              second challenge law                          *)
(* residuosity_distinguisher == a finite state, its law, and a Boolean        *)
(*                              verdict on the state and the challenge        *)
(*  residuosity_accept D law == the probability that D accepts a              *)
(*                              challenge drawn from law                      *)
(*       residuosity_acceptE == that probability, as an equation to           *)
(*                              rewrite with                                  *)
(*   residuosity_advantage D == the absolute gap between D's two              *)
(*                              acceptance probabilities                      *)
(*    residuosity_assumption == a distinguisher class, one epsilon, and       *)
(*                              the bound every classified                    *)
(*                              distinguisher obeys                           *)
(*     unit_fdist_translateE == multiplying the unit challenge by a           *)
(*                              unit leaves its law unchanged                 *)
(*  unit_fdistmap_translateE == that identity under a Boolean test            *)
(*                  unit_set == the units of T as a subset of T               *)
(*               residue_set == the e-th residues of T as a subset of T       *)
(*         card_unit_set_gt0 == the units are nonempty                        *)
(*      card_residue_set_gt0 == the e-th residues are nonempty                *)
(*               unit_fdistE == the first challenge is uniform on the         *)
(*                              units                                         *)
(*              unit_commute == two units of a commutative ring commute       *)
(*        residue_fiber_card == the fibers of the e-th power map over         *)
(*                              its image are equinumerous                    *)
(*            residue_fdistE == the second challenge is uniform on the        *)
(*                              e-th residues                                 *)
(*         decide_constant D == decides whether D's verdict ignores the       *)
(*                              challenge                                     *)
(* residuosity_advantage_decide_constant_eq0 ==                               *)
(*                              such a distinguisher has advantage zero       *)
(* residuosity_advantage_decide_constant_le0 ==                               *)
(*                              the same bound in the form the                *)
(*                              assumption record's field takes               *)
(* decide_constant_assumption ==                                              *)
(*                              that class at epsilon zero, an assumption     *)
(*                              whose bound is proved rather than assumed     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* The unit group of a finite unit ring, named as a finite type.  [#|{unit T}|]
   does not elaborate, unit_of carrying no predArgType, so every cardinality
   statement about the units passes through this name.  It is the space both
   challenges of the residuosity problem are drawn from, and at an encryption
   scheme it is the space of encryption coins. *)
Definition ring_units (T : finUnitRingType) : finType := {unit T}.

(* The unit group is nonempty, in the successor form the uniform law takes.
   This is the cardinality term a user with none of its own passes to the
   game.  A scheme that already fixes one passes that one instead: two proofs
   of this equation are propositionally equal and not convertible, and the
   uniform law is indexed by the proof. *)
Lemma card_ring_units (T : finUnitRingType) :
  #|ring_units T| = #|ring_units T|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

Section residuosity_game.
Context {R : realType}.
Variable T : finComUnitRingType.
Variable e : nat.
Hypothesis card_units : #|ring_units T| = #|ring_units T|.-1.+1.

(* The first challenge law: a uniform unit read as a ring element. *)
Definition unit_fdist : R.-fdist T :=
  fdistmap val (fdist_uniform (R := R) card_units).

Arguments unit_fdist : simpl never.

(* The second challenge law: the e-th power of a uniform unit.  At a
   residue-class encryption scheme whose coins are the units and whose
   plaintext count divides e, this is the law of a ciphertext of zero. *)
Definition residue_fdist : R.-fdist T :=
  fdistmap (fun u : ring_units T => val u ^+ e)
    (fdist_uniform (R := R) card_units).

(* A distinguisher of the two challenge laws: a finite state, its law, and a
   Boolean verdict read off the state and the challenge ring element.  It is
   the IND-CPA adversary of indcpa_game.v with the plaintext choice removed,
   the residuosity problem handing the adversary no message to choose. *)
Record residuosity_distinguisher := {
  state : finType ;
  state_fdist : R.-fdist state ;
  decide : state -> T -> bool }.

(* Under the file's Set Implicit Arguments the record argument of the two
   projections is inferable from their result types, hence implicit, and
   [decide D c] does not elaborate.  The post-section Arguments lines below
   restate this for use sites outside the section. *)
Arguments state_fdist : clear implicits.
Arguments decide : clear implicits.

(* The probability that D accepts a challenge drawn from law: sample its
   state, apply its verdict to the challenge, read the mass at true. *)
Definition residuosity_accept (D : residuosity_distinguisher)
    (law : R.-fdist T) : R :=
  Pr (state_fdist D >>= (fun c => fdistmap (decide D c) law)) [set true].

(* Acceptance as an equation.  A reduction rewrites with this rather than
   unfolding residuosity_accept, so that the nested fdistmap a later
   fdistmap_comp must match survives the step. *)
Lemma residuosity_acceptE (D : residuosity_distinguisher) (law : R.-fdist T) :
  residuosity_accept D law
  = Pr (state_fdist D >>= (fun c => fdistmap (decide D c) law)) [set true].
Proof. by []. Qed.

(* The absolute gap between D's two acceptance probabilities.  This is the
   quantity the e-th residuosity assumption bounds, and the currency a
   scheme's IND-CPA advantage is paid in once the reduction is written. *)
Definition residuosity_advantage (D : residuosity_distinguisher) : R :=
  `| residuosity_accept D residue_fdist - residuosity_accept D unit_fdist |.

(* An extensional class of distinguishers, one epsilon, and the promise that
   every classified distinguisher stays below that epsilon.  It mirrors
   indcpa_epsilon_assumption field for field: the classifier says which
   distinguishers a bound covers, while running time stays a property of a
   syntax it does not read. *)
Record residuosity_assumption := {
  residuosity_admissible : residuosity_distinguisher -> bool ;
  residuosity_assumption_epsilon : R ;
  residuosity_admissible_epsilon_le : forall D,
    residuosity_admissible D ->
    residuosity_advantage D <= residuosity_assumption_epsilon }.

(* The key fact of a reduction.  Multiplication by a unit is a bijection of
   the unit group, and a bijection fixes the uniform law: pushing unit_fdist
   along x |-> val a * x gives unit_fdist back.  This is Katz and Lindell
   Lemma 11.15.  Its position: once the challenge is a uniform unit,
   multiplying it by g ^+ m erases m, and that is where a residue-class
   ciphertext hides its plaintext.  Every other step of the reduction is an
   identity by unfolding or an appeal to the assumption.  The pointwise count
   Pr[a * x = y] = Pr[x = a^-1 * y] = 1/#|units| is done once, inside
   fdistmap_bij_uniform. *)
Lemma unit_fdist_translateE (a : ring_units T) :
  fdistmap (fun x => val a * x) unit_fdist = unit_fdist.
Proof.
(* Two pushforwards, draw u then multiply by val a, become one map. *)
rewrite /unit_fdist fdistmap_comp.
(* Ring multiplication by val a is group multiplication by a, read off
   through val; definitional, since val (a * u)%g = val a * val u. *)
have -> : (fun x => val a * x) \o val
        = val \o (fun u : ring_units T => (a * u)%g) by [].
(* Split again, group map first and val second.  The group map is a bijection
   of the unit group, so it fixes the uniform law.  This is the key step. *)
rewrite -fdistmap_comp (fdistmap_bij_uniform _ card_units) //.
(* The bijection's witness: the inverse is multiplication by a^-1. *)
by exists (fun u => (a^-1 * u)%g) => u; rewrite ?mulKg ?mulKVg.
Qed.

(* The key fact composed with a Boolean test: deciding on val a * x and
   deciding on x see the same law when x is a uniform unit.  This is the form
   the middle equality of a reduction's hybrid consumes. *)
Lemma unit_fdistmap_translateE (h : T -> bool) (a : ring_units T) :
  fdistmap (fun x => h (val a * x)) unit_fdist = fdistmap h unit_fdist.
Proof. by rewrite -[in RHS](unit_fdist_translateE a) [in RHS]fdistmap_comp. Qed.

(* The units of T as a subset of T, the set the first challenge of the
   textbook wording is drawn from. *)
Definition unit_set : {set T} := val @: [set: ring_units T].

(* The e-th residues of T as a subset of T, the set the second challenge of
   the textbook wording is drawn from. *)
Definition residue_set : {set T} :=
  (fun u : ring_units T => val u ^+ e) @: [set: ring_units T].

(* The units are nonempty, 1 being one of them. *)
Lemma card_unit_set_gt0 : (0 < #|unit_set|)%N.
Proof.
by apply/card_gt0P; exists (val (1%g : ring_units T)); apply: imset_f.
Qed.

(* The e-th residues are nonempty, 1 being one of them. *)
Lemma card_residue_set_gt0 : (0 < #|residue_set|)%N.
Proof.
by apply/card_gt0P; exists (val (1%g : ring_units T) ^+ e); apply: imset_f.
Qed.

(* The first challenge is uniform on the units: pushing a uniform unit through
   the subtype projection is the uniform law on the image, the projection
   being injective and every fiber a singleton.  With residue_fdistE this is
   the textbook wording of the problem, tell a uniform element of the unit
   group from a uniform e-th residue. *)
Lemma unit_fdistE : unit_fdist = fdist_uniform_supp R card_unit_set_gt0.
Proof.
have card1 (u : T) : u \in unit_set ->
    #|[set t : ring_units T | val t == u]| = 1%N.
  case/imsetP => t0 _ ->.
  have -> : [set t : ring_units T | val t == val t0] = [set t0].
    by apply/setP => t; rewrite !inE val_eqE.
  exact: cards1.
rewrite /unit_fdist; apply: fdistmap_uniform_supp_img => u u' Hu Hu'.
by rewrite (card1 _ Hu) (card1 _ Hu').
Qed.

(* Two units of a commutative ring commute, their values commuting and the
   projection being injective.  This is the one place commutativity of T is
   used, and hence why the problem is stated at finComUnitRingType. *)
Lemma unit_commute (a b : ring_units T) : commute a b.
Proof. by apply/val_inj; rewrite !FinRing.val_unitM mulrC. Qed.

(* The e-th power map on the unit group is a group homomorphism, so its fiber
   over the image point val t0 ^+ e is the left translate by t0 of its fiber
   over 1, and the two fibers have the same cardinality.  Equinumerous fibers
   are what makes the second challenge uniform on its image. *)
Lemma residue_fiber_card (u : T) : u \in residue_set ->
  #|[set t : ring_units T | val t ^+ e == u]|
  = #|[set t : ring_units T | (t ^+ e)%g == 1%g]|.
Proof.
case/imsetP => t0 _ ->.
have -> : [set t : ring_units T | val t ^+ e == val t0 ^+ e]
        = [set (t0 * t)%g | t in [set t : ring_units T | (t ^+ e)%g == 1%g]].
  apply/setP => t; apply/idP/imsetP => [|[s]]; last first.
    rewrite !in_set -!FinRing.val_unitX val_eqE => Hs ->.
    by rewrite (expgMn _ (unit_commute _ _)) (eqP Hs) mulg1.
  rewrite in_set -!FinRing.val_unitX val_eqE => Ht.
  exists (t0^-1 * t)%g; last by rewrite mulKVg.
  by rewrite in_set (expgMn _ (unit_commute _ _)) expVgn (eqP Ht) mulVg.
exact: (card_imset _ (mulgI t0)).
Qed.

(* The second challenge is uniform on the e-th residues, the second law of the
   textbook wording of the problem. *)
Lemma residue_fdistE :
  residue_fdist = fdist_uniform_supp R card_residue_set_gt0.
Proof.
rewrite /residue_fdist; apply: fdistmap_uniform_supp_img => u u' Hu Hu'.
by rewrite (residue_fiber_card Hu) (residue_fiber_card Hu').
Qed.

(* The distinguishers whose verdict reads the state alone and ignores the
   challenge. *)
Definition decide_constant (D : residuosity_distinguisher) : bool :=
  [forall c, [forall x, [forall y, decide D c x == decide D c y]]].

(* Such a distinguisher has advantage zero: at each state its verdict is a
   constant, both challenge laws are transported to the point mass at that
   constant, and the two acceptance probabilities coincide. *)
Lemma residuosity_advantage_decide_constant_eq0 D :
  decide_constant D -> residuosity_advantage D = 0.
Proof.
move=> /forallP Hc; rewrite /residuosity_advantage /residuosity_accept.
suff -> : (fun c => fdistmap (decide D c) residue_fdist)
        = (fun c => fdistmap (decide D c) unit_fdist) by rewrite subrr normr0.
apply/funext => c; have -> : decide D c = (fun=> decide D c 0).
  by apply/funext => x; apply/eqP; move: (Hc c) => /forallP/(_ x)/forallP/(_ 0).
by rewrite !fdistmap_cst.
Qed.

(* The same bound in the form the assumption record's third field takes. *)
Lemma residuosity_advantage_decide_constant_le0 D :
  decide_constant D -> residuosity_advantage D <= 0.
Proof. by move/residuosity_advantage_decide_constant_eq0 ->. Qed.

(* The class of challenge-ignoring distinguishers at epsilon zero: a
   residuosity assumption whose bound is proved rather than assumed.  A
   statement restricted to a residuosity class is therefore not empty for want
   of a record to read it at.  It does not show that a scheme's own class is
   inhabited at a useful epsilon. *)
Definition decide_constant_assumption : residuosity_assumption :=
  {| residuosity_admissible := decide_constant ;
     residuosity_assumption_epsilon := 0 ;
     residuosity_admissible_epsilon_le :=
       residuosity_advantage_decide_constant_le0 |}.

End residuosity_game.

(* Every declaration above discharges the section's Context {R} and its two
   Variables.  Under the file's Set Implicit Arguments the ring T is inferable
   from a later argument and is demoted to implicit, so a positional T is read
   as the exponent e; the record argument of the two distinguisher projections
   is demoted the same way, and [decide D c] stops elaborating.  Pinning T and
   e explicit and R implicit keeps every use site free of @ and fixes one
   spelling for the instance files: the ring, then the exponent, then the
   cardinality proof. *)
Arguments unit_fdist {R} T _.
Arguments residue_fdist {R} T e%_nat_scope _.
Arguments residuosity_distinguisher {R} T.
Arguments Build_residuosity_distinguisher {R} T _ _ _%_function_scope.
Arguments state {R} T _.
Arguments state_fdist {R} T _.
Arguments decide {R} T _ _ _.
Arguments residuosity_accept {R} T _ _.
Arguments residuosity_acceptE {R} T _ _.
Arguments residuosity_advantage {R} T e%_nat_scope _ _.
Arguments residuosity_assumption {R} T e%_nat_scope _.
Arguments Build_residuosity_assumption {R} T e%_nat_scope _
  _%_function_scope _ _.
Arguments residuosity_admissible {R} T e%_nat_scope _ _ _.
Arguments residuosity_assumption_epsilon {R} T e%_nat_scope _ _.
Arguments residuosity_admissible_epsilon_le {R} T e%_nat_scope _ _ _ _.
Arguments unit_fdist_translateE {R} T _ _.
Arguments unit_fdistmap_translateE {R} T _ _%_function_scope _.
Arguments unit_set T : clear implicits.
Arguments residue_set T e%_nat_scope : clear implicits.
Arguments card_unit_set_gt0 T : clear implicits.
Arguments card_residue_set_gt0 T e%_nat_scope : clear implicits.
Arguments unit_fdistE {R} T _.
Arguments unit_commute T _ _ : clear implicits.
Arguments residue_fiber_card T e%_nat_scope _ _ : clear implicits.
Arguments residue_fdistE {R} T e%_nat_scope _.
Arguments decide_constant {R} T _.
Arguments residuosity_advantage_decide_constant_eq0 {R} T e%_nat_scope _ _ _.
Arguments residuosity_advantage_decide_constant_le0 {R} T e%_nat_scope _ _ _.
Arguments decide_constant_assumption {R} T e%_nat_scope _.
