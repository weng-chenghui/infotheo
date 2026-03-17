(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_raag_path pgg_raag_clique.

(******************************************************************************)
(* PGG-SMC: Concrete S_5 RAAG Instance (Adjacent Transpositions)              *)
(*                                                                            *)
(* Specialization of the path-graph RAAG at m=3, giving:                      *)
(*   T = 4 generators: s0=(01), s1=(12), s2=(23), s3=(34)                    *)
(*   N = 5 sheets                                                             *)
(*   Commutation: s_i s_j = s_j s_i iff |i-j| >= 2                          *)
(*   Independence graph: {(0,2), (0,3), (1,3)}                               *)
(*                                                                            *)
(* This is the Coxeter type A_4 presentation of S_5.                          *)
(*                                                                            *)
(* Contents:                                                                  *)
(*   s5_gens_nat == nat-level generator function for vm_compute               *)
(*   s5_gens_agree == agreement with path_gen at m=3                          *)
(*   s5_weval_inj1 == word-eval injectivity at L=1 (via vm_compute)           *)
(*   s5_nt_L* == vm_compute trace counts                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Nat-level generator function for vm_compute:
   gen i swaps i and i+1 (adjacent transposition) *)
Definition s5_gens_nat (i x : nat) : nat :=
  match i with
  | 0 => match x with 0 => 1 | 1 => 0 | _ => x end
  | 1 => match x with 1 => 2 | 2 => 1 | _ => x end
  | 2 => match x with 2 => 3 | 3 => 2 | _ => x end
  | _ => match x with 3 => 4 | 4 => 3 | _ => x end
  end.

Lemma s5_gens_agree (i : 'I_4) (x : 'I_5) :
  s5_gens_nat (val i) (val x) = val (tnth (path_gen_tuple 3) i x).
Proof.
by case: i => [[|[|[|[|?]]]] Hi];
  case: x => [[|[|[|[|[|?]]]]] Hx];
  rewrite ?gen_tuple_ofE /path_gen /path_lo /path_hi ?permE.
Qed.

(* Word-eval injectivity via nat-level boolean check + vm_compute *)
Lemma s5_weval_inj1 : @weval_inj (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 1.
Proof. apply: (weval_inj_of_natB s5_gens_agree). by vm_compute. Qed.

(* Note: word-eval injectivity at L=2 fails because adjacent transpositions are involutions
   (s_i^2 = 1 for all i), so words [i,i] all evaluate to the identity. *)

(* vm_compute trace count demonstrations *)
(* N=5, Tg=4, comm = path (|i-j| >= 2) *)

Lemma s5_nt_L1 : n_traces_natB 4 1 path_comm_nat = 4.
Proof. by vm_compute. Qed.

Lemma s5_nt_L2 : n_traces_natB 4 2 path_comm_nat = 13.
Proof. by vm_compute. Qed.

Lemma s5_nt_L3 : n_traces_natB 4 3 path_comm_nat = 40.
Proof. by vm_compute. Qed.
