(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: the false-shuffle wreath group Z_7 wr S_2 as a PGG instance           *)
(*                                                                            *)
(* A 14-card deck of two piles of seven. The security group is the full       *)
(* wreath product Z_7 wr S_2 = Z_7^2 |x| S_2 of order 7^2 * 2! = 98, acting   *)
(* on 'I_14. Read as a stage-magic false shuffle (see note                    *)
(* pgg-smc/notes/20260603_205936_false_shuffle_magic_framing.md):             *)
(*                                                                            *)
(*   cut1   = the 7-cycle (0 1 2 3 4 5 6)   -- a free cut inside pile 1        *)
(*   cut2   = the 7-cycle (7 8 9 10 11 12 13) -- a free cut inside pile 2      *)
(*   wswap  = (0 7)(1 8)(2 9)(3 10)(4 11)(5 12)(6 13) -- the spectator's pile  *)
(*            swap, the top S_2 of the wreath                                  *)
(*                                                                            *)
(* The abelian core <<cut1, cut2>> = Z_7^2 is the reconstruction-symmetry      *)
(* group (carried in wreath_recovery.v); wswap is an anonymity operation, not  *)
(* a recovery symmetry. The whole group is the security carrier.              *)
(*                                                                            *)
(* PGG parameters: m = 2 (3 generators), n = 12 (N = n+2 = 14 sheets)         *)
(*   M_wreath = Gen_PGGTypes [tuple cut1; cut2; wswap]                         *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
Require Import pgg_interface.
From pgg_smc Require Import pgg_weval_inj.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Generators on 'I_14: two within-pile cuts and the pile swap            *)
(******************************************************************************)

Local Notation o0  := (Ordinal (n:=14) (isT : 0  < 14)).
Local Notation o1  := (Ordinal (n:=14) (isT : 1  < 14)).
Local Notation o2  := (Ordinal (n:=14) (isT : 2  < 14)).
Local Notation o3  := (Ordinal (n:=14) (isT : 3  < 14)).
Local Notation o4  := (Ordinal (n:=14) (isT : 4  < 14)).
Local Notation o5  := (Ordinal (n:=14) (isT : 5  < 14)).
Local Notation o6  := (Ordinal (n:=14) (isT : 6  < 14)).
Local Notation o7  := (Ordinal (n:=14) (isT : 7  < 14)).
Local Notation o8  := (Ordinal (n:=14) (isT : 8  < 14)).
Local Notation o9  := (Ordinal (n:=14) (isT : 9  < 14)).
Local Notation o10 := (Ordinal (n:=14) (isT : 10 < 14)).
Local Notation o11 := (Ordinal (n:=14) (isT : 11 < 14)).
Local Notation o12 := (Ordinal (n:=14) (isT : 12 < 14)).
Local Notation o13 := (Ordinal (n:=14) (isT : 13 < 14)).

(** cut1 — the within-pile cut on pile 1, the 7-cycle (0 1 2 3 4 5 6).
    Kind: instance.
    Why: a free cut of the first seven cards; one of the two abelian-core
    generators whose joint span is the reconstruction-symmetry group Z_7^2. *)
Definition cut1 : {perm 'I_14} :=
  (tperm o0 o1 * tperm o0 o2 * tperm o0 o3 *
   tperm o0 o4 * tperm o0 o5 * tperm o0 o6)%g.

(** cut2 — the within-pile cut on pile 2, the 7-cycle (7 8 9 10 11 12 13).
    Kind: instance.
    Why: a free cut of the second seven cards; the other abelian-core
    generator. Disjoint support from cut1, so the two commute. *)
Definition cut2 : {perm 'I_14} :=
  (tperm o7 o8 * tperm o7 o9 * tperm o7 o10 *
   tperm o7 o11 * tperm o7 o12 * tperm o7 o13)%g.

(** wswap — the pile swap (0 7)(1 8)(2 9)(3 10)(4 11)(5 12)(6 13), the top S_2.
    Kind: instance.
    Why: the spectator's pile exchange; the non-abelian generator that lifts
    the abelian core to the full wreath. An anonymity move, not a recovery
    symmetry. *)
Definition wswap : {perm 'I_14} :=
  (tperm o0 o7 * tperm o1 o8 * tperm o2 o9 * tperm o3 o10 *
   tperm o4 o11 * tperm o5 o12 * tperm o6 o13)%g.

(** wreath_gens — the three generators of Z_7 wr S_2 as a tuple.
    Kind: instance.
    Why: the generator tuple fed to Gen_PGGTypes to build the monodromy. *)
Definition wreath_gens : 3.-tuple {perm 'I_14} := [tuple cut1; cut2; wswap].

(******************************************************************************)
(** * PGG instance                                                            *)
(******************************************************************************)

(** M_wreath — the Z_7 wr S_2 monodromy instance on a 14-card deck.
    Kind: instance.
    Why: the security carrier; pgg_G M_wreath is the full wreath, pgg_rho is
    the deck shuffle action. *)
Definition M_wreath : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 2 12 wreath_gens.

(** wreath_deck — the deck has 14 cards.
    Kind: helper.
    Why: pins the sheet count for the pgl_bound and recovery arithmetic.
    Used by: rigidity_wreath_instance. *)
Lemma wreath_deck : (pgg_N' M_wreath).+1 = 14.
Proof. by []. Qed.

(******************************************************************************)
(** * Word-eval injectivity via a nat-level mirror                            *)
(******************************************************************************)

(** wreath_gens_nat — nat-level mirror of the three generators for reflection.
    Kind: helper.
    Why: feeds the weval_inj_of_natB reflection so vm_compute can discharge
    word-eval injectivity.
    Used by: wreath_gens_agree, wreath_weval_inj1. *)
Definition wreath_gens_nat (i x : nat) : nat :=
  match i with
  | 0 => match x with
         | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 0
         | _ => x end
  | 1 => match x with
         | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 11 | 11 => 12 | 12 => 13 | 13 => 7
         | _ => x end
  | _ => match x with
         | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 12 | 6 => 13
         | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 5 | 13 => 6
         | _ => x end
  end.

(** wreath_gens_agree — the nat mirror agrees with the perm action.
    Kind: helper.
    Why: reflection bridge for weval_inj_of_natB; proven by deciding the finite
    double quantifier with vm_compute.
    Used by: wreath_weval_inj1. *)
Lemma wreath_gens_agree (i : 'I_3) (x : 'I_14) :
  wreath_gens_nat (val i) (val x) = val (tnth wreath_gens i x).
Proof.
rewrite /wreath_gens /cut1 /cut2 /wswap.
case: i => -[|[|[|]]] Hi //;
  rewrite (tnth_nth 1%g) /=;
  case: x => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]] Hx;
  rewrite ?permM ?permE /=; by [].
Qed.

(** wreath_weval_inj1 — word-eval injectivity at L = 1.
    Kind: helper.
    Why: required by the fiber security witness (security_witness_fiber).
    Used by: wreath_security. *)
Lemma wreath_weval_inj1 : @weval_inj M_wreath 1.
Proof. apply: (weval_inj_of_natB wreath_gens_agree). by vm_compute. Qed.

(******************************************************************************)
(** * Group order (axiom) and non-abelianness (proven)                        *)
(******************************************************************************)

(** card_wreath — the order of Z_7 wr S_2 is 7^2 * 2! = 98.
    Kind: axiom.
    Why: the exact cardinality of #|<<generators>>| is infeasible to evaluate
    in the kernel (the orbit/coset proof is out of scope); the anonymity
    headline is |G| = 98, so it is stated as a justified axiom, mirroring the
    accepted precedent s5_group_order_eq in rigidity_s5_instance.v. This is the
    only custom axiom of the wreath7 instance; it is used only to discharge the
    order inequality wreath_pgl_lt_card. *)
Axiom card_wreath : #|pgg_G M_wreath| = 98.

(** Single-point generator actions, reduced cheaply via permM/permE.
    Kind: helper.
    Why: building blocks for wreath_nonabelian; each is one generator applied to
    one card, so the perm tower stays short (<= 7 transpositions).
    Used by: wreath_nonabelian. *)
Lemma cut1o0 : cut1 o0 = o1.
Proof. by apply/val_inj; rewrite /cut1 ?permM ?permE /=. Qed.

Lemma cut1o7 : cut1 o7 = o7.
Proof. by apply/val_inj; rewrite /cut1 ?permM ?permE /=. Qed.

Lemma wswapo0 : wswap o0 = o7.
Proof. by apply/val_inj; rewrite /wswap ?permM ?permE /=. Qed.

Lemma wswapo1 : wswap o1 = o8.
Proof. by apply/val_inj; rewrite /wswap ?permM ?permE /=. Qed.

(** cut1_in_G, wswap_in_G — the cut and the pile swap lie in the wreath group.
    Kind: helper.
    Why: generator membership, via the generic sigmas_in_G; needed to feed the
    non-commuting pair into the abelian centraliser.
    Used by: wreath_nonabelian. *)
Lemma cut1_in_G : cut1 \in pgg_G M_wreath.
Proof. have := sigmas_in_G (M := M_wreath) (@Ordinal 3 0 isT). by rewrite (tnth_nth 1%g). Qed.

Lemma wswap_in_G : wswap \in pgg_G M_wreath.
Proof. have := sigmas_in_G (M := M_wreath) (@Ordinal 3 2 isT). by rewrite (tnth_nth 1%g). Qed.

(** wreath_nonabelian — Z_7 wr S_2 is non-abelian.
    Kind: main.
    Why: the security character of the instance. The order |G| = 98 alone does
    not force non-abelianness, so it is proven, not assumed: a cut and the pile
    swap fail to commute (witnessed at card 0). Closes the audit gap that
    non-abelianness was asserted-only. *)
Lemma wreath_nonabelian : ~~ abelian (pgg_G M_wreath).
Proof.
apply/negP => Hab.
have Hcomm : commute cut1 wswap.
  by apply: (centP (subsetP Hab _ cut1_in_G)); exact: wswap_in_G.
move: Hcomm => /(f_equal (fun p : {perm 'I_14} => val (p o0))) H.
by rewrite permM permM cut1o0 wswapo0 wswapo1 cut1o7 in H.
Qed.
