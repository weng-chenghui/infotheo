(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: S_5 × S_5 Instance (Product of Coxeter A_4 × A_4)                   *)
(*                                                                            *)
(* Two independent copies of adjacent transposition generators on disjoint    *)
(* supports {0..4} and {5..9}, acting on 'I_10.                              *)
(*                                                                            *)
(*   Tg = 8 generators: (01),(12),(23),(34),(56),(67),(78),(89)               *)
(*   N = 10 sheets                                                           *)
(*   Commutation: generators from different piles always commute;            *)
(*     within-pile commutation follows path graph (|i-j| >= 2)              *)
(*   |G| = |S_5|^2 = 14400                                                  *)
(*                                                                            *)
(* This is NOT a RAAG — the Coxeter braid relations s_i s_j s_i = s_j s_i s_j*)
(* are not RAAG relations. The RAAG trace machinery gives upper bounds only. *)
(*                                                                            *)
(* Contents:                                                                  *)
(*   s5x5_gens_nat      == nat-level generator function for vm_compute       *)
(*   s5x5_gen_tuple     == 8.-tuple {perm 'I_10} of generators              *)
(*   s5x5_gens_agree    == agreement between nat and perm levels             *)
(*   M_s5x5 / R_s5x5   == Gen_PGGTypes instance                             *)
(*   s5x5_weval_inj1    == word-eval injectivity at L=1                      *)
(*   s5x5_comm_nat      == commutation predicate for trace counting          *)
(*   s5x5_nt_L*         == trace count demonstrations                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Nat-level generators for vm_compute                                    *)
(******************************************************************************)

(* 8 generators: 0..3 are adjacent transpositions on {0..4},
                 4..7 are adjacent transpositions on {5..9}. *)
Definition s5x5_gens_nat (i x : nat) : nat :=
  match i with
  | 0 => match x with 0 => 1 | 1 => 0 | _ => x end
  | 1 => match x with 1 => 2 | 2 => 1 | _ => x end
  | 2 => match x with 2 => 3 | 3 => 2 | _ => x end
  | 3 => match x with 3 => 4 | 4 => 3 | _ => x end
  | 4 => match x with 5 => 6 | 6 => 5 | _ => x end
  | 5 => match x with 6 => 7 | 7 => 6 | _ => x end
  | 6 => match x with 7 => 8 | 8 => 7 | _ => x end
  | _ => match x with 8 => 9 | 9 => 8 | _ => x end
  end.

(******************************************************************************)
(*     Generator tuple                                                        *)
(******************************************************************************)

Section s5x5_gens.

Let N := 10.

(* Helper ordinals in 'I_10 *)
Local Notation o0 := (Ordinal (n:=N) (isT : 0 < N)).
Local Notation o1 := (Ordinal (n:=N) (isT : 1 < N)).
Local Notation o2 := (Ordinal (n:=N) (isT : 2 < N)).
Local Notation o3 := (Ordinal (n:=N) (isT : 3 < N)).
Local Notation o4 := (Ordinal (n:=N) (isT : 4 < N)).
Local Notation o5 := (Ordinal (n:=N) (isT : 5 < N)).
Local Notation o6 := (Ordinal (n:=N) (isT : 6 < N)).
Local Notation o7 := (Ordinal (n:=N) (isT : 7 < N)).
Local Notation o8 := (Ordinal (n:=N) (isT : 8 < N)).
Local Notation o9 := (Ordinal (n:=N) (isT : 9 < N)).

Definition s5x5_gen_tuple : 8.-tuple {perm 'I_N} :=
  [tuple tperm o0 o1; tperm o1 o2; tperm o2 o3; tperm o3 o4;
         tperm o5 o6; tperm o6 o7; tperm o7 o8; tperm o8 o9].

End s5x5_gens.

(******************************************************************************)
(*     Agreement with nat-level generators                                    *)
(******************************************************************************)

Lemma s5x5_gens_agree (i : 'I_8) (x : 'I_10) :
  s5x5_gens_nat (val i) (val x) = val (tnth s5x5_gen_tuple i x).
Proof.
by case: i => [[|[|[|[|[|[|[|[|?]]]]]]]] Hi];
  case: x => [[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]] Hx];
  rewrite /s5x5_gen_tuple ?tnth_mktuple ?permE.
Qed.

(******************************************************************************)
(*     PGG instance                                                           *)
(******************************************************************************)

Definition M_s5x5 := @Gen_PGGTypes 7 8 s5x5_gen_tuple.
Definition R_s5x5 : GeneratedMonodromyReprType := M_s5x5.

(******************************************************************************)
(*     Word-eval injectivity at L=1                                           *)
(******************************************************************************)

Lemma s5x5_weval_inj1 : @weval_inj M_s5x5 1.
Proof. apply: (weval_inj_of_natB s5x5_gens_agree). by vm_compute. Qed.

(******************************************************************************)
(*     Commutation predicate for RAAG trace counting                          *)
(******************************************************************************)

(* Generators i and j commute iff they are from different piles or
   non-adjacent in the same pile. *)
Definition s5x5_comm_nat (i j : nat) : bool :=
  match i, j with
  (* Pile 1: path graph — commute iff |i-j| >= 2 *)
  | 0, 2 | 2, 0 | 0, 3 | 3, 0 | 1, 3 | 3, 1 => true
  (* Cross-pile: always commute *)
  | 0, 4 | 0, 5 | 0, 6 | 0, 7 => true
  | 1, 4 | 1, 5 | 1, 6 | 1, 7 => true
  | 2, 4 | 2, 5 | 2, 6 | 2, 7 => true
  | 3, 4 | 3, 5 | 3, 6 | 3, 7 => true
  | 4, 0 | 4, 1 | 4, 2 | 4, 3 => true
  | 5, 0 | 5, 1 | 5, 2 | 5, 3 => true
  | 6, 0 | 6, 1 | 6, 2 | 6, 3 => true
  | 7, 0 | 7, 1 | 7, 2 | 7, 3 => true
  (* Pile 2: path graph — commute iff |i-j| >= 2 (indices shifted by 4) *)
  | 4, 6 | 6, 4 | 4, 7 | 7, 4 | 5, 7 | 7, 5 => true
  | _, _ => false
  end.

(******************************************************************************)
(*     Trace count demonstrations                                             *)
(******************************************************************************)

Lemma s5x5_nt_L1 : n_traces_natB 8 1 s5x5_comm_nat = 8.
Proof. by vm_compute. Qed.

Lemma s5x5_nt_L2 : n_traces_natB 8 2 s5x5_comm_nat = 42.
Proof. by vm_compute. Qed.
