From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* General algebra lemmas, used by the dumas2017dual and the                  *)
(* computational_security files                                               *)
(*                                                                            *)
(* This file contains lemmas that are more general than DSDP-specific:        *)
(*   - Modulus bounds                                                         *)
(*   - Bigop lemmas                                                           *)
(*   - Z/mZ unit characterization lemmas                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                        Moduli greater than one                              *)
(* ========================================================================== *)

(* A product of two naturals above one is above one.  It is the condition the
   Paillier and Benaloh packagings take their modulus at. *)
Lemma pq_gt1 (p q : nat) : (1 < p)%N -> (1 < q)%N -> (1 < p * q)%N.
Proof. by move=> p1 q1; rewrite (leq_trans p1) // leq_pmulr // (ltnW q1). Qed.

(* A natural above one is the second successor of its double predecessor.
   The equality is propositional, so it transports a statement written at
   a.+2 rather than converting it. *)
Lemma pred2K (n : nat) : (1 < n)%N -> n.-2.+2 = n.
Proof. by case: n => [|[|n]]. Qed.

(* ========================================================================== *)
(*                           Bigop lemmas                                      *)
(* ========================================================================== *)

Section bigop_extra.

(* Extract a term from a filtered big operation.  When j is in r and satisfies
   P, F j factors out of the operation over the filtered sequence. *)
Lemma bigD1_filter {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- [seq x <- r | P x]) F i = 
    op (F j) (\big[op/idx]_(i <- [seq x <- r | P x] | i != j) F i).
Proof.
Proof.
move=> j_in Pj uniq_r.
apply: bigD1_seq; last by apply: filter_uniq.
by rewrite mem_filter Pj j_in.
Qed.

(* Extract a term from a conditional big operation over a sequence.
   Similar to bigD1 but for conditional sums: factors out F(j) when j
   satisfies P, leaving the rest with an additional (i != j) condition. *)
Lemma bigD1_seq_cond {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- r | P i) F i = 
    op (F j) (\big[op/idx]_(i <- r | P i && (i != j)) F i).
Proof.
move=> j_in Pj uniq_r.
rewrite (big_rem_AC op idx P F j_in) Pj /=.
congr (op (F j) _).
rewrite (rem_filter _ uniq_r).
rewrite -(@big_filter _ _ _ _ r (predI P (predC1 j)) F).
rewrite -(@big_filter _ _ _ _ [seq x <- r | predC1 j x] P F).
congr (\big[op/idx]_(i <- _) F i).
by rewrite filter_predI.
Qed.

End bigop_extra.

(* ========================================================================== *)
(*                    Z/mZ unit characterization lemmas                        *)
(* ========================================================================== *)

Section Zp_unit_extra.

(* 
   Helper lemmas for unit characterization in Z/mZ rings.
   
   In 'Z_m (integers mod m), an element x is a unit (invertible)
   if and only if gcd(x, m) = 1, i.e., coprime x m.
   
   This is fundamental for CRT-based analysis where we work with
   composite moduli m = p*q and need to establish invertibility
   from coprimality conditions.
   
   Mathematical proof:
   - Forward (coprime -> unit): By Bezout's identity, coprime x m means
     exists s,t: s*x + t*m = 1. In Z/m, this gives s*x ≡ 1, so s is inverse.
   - Backward (unit -> coprime): If x*y = 1 in Z/m, then x*y ≡ 1 (mod m),
     so m | (x*y - 1). Any common divisor d of x and m must divide 1.
     
   Technical note: These proofs require careful handling of:
   - egcdn/egcdnP for Bezout coefficients
   - Modular arithmetic (modnMml, modnDml)
   - Conversion between 'Z_m and nat (nat_of_ord, inZp)
*)

(* coprime x m implies x is a unit in 'Z_m (when m > 1) *)
(* 
   Key lemma from MathComp: unitZpE
   (x%:R : 'Z_m) \is a GRing.unit = coprime m x  (when 1 < m)
   
   For x : 'Z_m, we have x = (nat_of_ord x)%:R, so we can apply unitZpE directly.
*)
Lemma coprime_Zp_unit (m : nat) (x : 'Z_m) :
  (1 < m)%N -> coprime x m -> x \is a GRing.unit.
Proof.
move=> Hm_gt1 Hcoprime.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* The converse: unit in 'Z_m implies coprime (when m > 1) *)
(* 
   Uses unitZpE in reverse: (x%:R) \is a GRing.unit = coprime m x
*)
Lemma Zp_unit_coprime (m : nat) (x : 'Z_m) :
  (1 < m)%N -> x \is a GRing.unit -> coprime x m.
Proof.
move=> Hm_gt1 Hunit.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by move: Hunit; rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* Equivalence form: unit status iff coprime (when m > 1) *)
Lemma Zp_unitP (m : nat) (x : 'Z_m) :
  (1 < m)%N -> (x \is a GRing.unit) = coprime x m.
Proof.
move=> Hm_gt1.
apply/idP/idP; [exact: (Zp_unit_coprime Hm_gt1) | exact: (coprime_Zp_unit Hm_gt1)].
Qed.

End Zp_unit_extra.

(* ========================================================================== *)
(*              Z/mZ and F_m cardinality / field equivalence                   *)
(* ========================================================================== *)

Section Zp_Fp_equivalence.

Context {R : realType}.

(* The plaintext ring at modulus p * q has p * q elements whenever both
   factors are above one.  This value form is what the entropy statements
   downstream read their log at. *)
Lemma card_Zp_pq (p q : nat) :
  (1 < p)%N -> (1 < q)%N -> #|'Z_(p * q)| = (p * q)%N.
Proof. by move=> p_gt1 q_gt1; rewrite card_ord Zp_cast// pq_gt1. Qed.

(* The same count in the successor form fdist_uniform takes its argument in.
   At an abstract modulus the two forms separate, the product no longer being
   a successor by conversion. *)
Lemma card_Zp_pq_prednK (p q : nat) :
  (1 < p)%N -> (1 < q)%N -> #|'Z_(p * q)| = (p * q).-1.+1.
Proof.
by move=> p_gt1 q_gt1; rewrite (card_Zp_pq p_gt1 q_gt1) prednK// ltnW// pq_gt1.
Qed.

(* A pair of plaintexts, counted in the successor form the generic fiber
   framework takes its cardinality argument in. *)
Lemma card_Zp_pq_pair_prednK (p q : nat) :
  (1 < p)%N -> (1 < q)%N ->
  #|((('Z_(p * q)) * ('Z_(p * q)))%type : finType)| = (((p * q) ^ 2).-1).+1.
Proof.
move=> p_gt1 q_gt1; rewrite card_prod (card_Zp_pq p_gt1 q_gt1) expnS expn1.
by rewrite prednK// muln_gt0 (ltnW (pq_gt1 p_gt1 q_gt1)).
Qed.

(* When m is prime, 'Z_m and 'F_m have the same cardinality *)
Lemma Zp_Fp_card_eq (a : nat) :
  let m := a.+2 in
  prime m ->
  #|'Z_m| = #|'F_m|.
Proof.
move=> /= Hprime.
rewrite card_ord.
by rewrite card_Fp // pdiv_id.
Qed.

End Zp_Fp_equivalence.

