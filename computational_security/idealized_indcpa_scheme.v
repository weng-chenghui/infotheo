From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra finalg.
Require Import homomorphic_encryption idealized_ahe.
Require Import indcpa_game.

(**md**************************************************************************)
(* # The idealized AHE scheme as an IND-CPA scheme                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* The one-element coin space has successor cardinality. *)
Fact card_renc_ord1 : #|'I_1| = #|'I_1|.-1.+1.
Proof. by rewrite card_ord. Qed.

(* The idealized AHE scheme is an IND-CPA scheme whose encryption returns the
   plaintext. *)
Definition idealized_indcpa_scheme (msgT : finComUnitRingType) :
    indcpa_scheme := {|
  scheme_AHE          := Idealized_HETypes msgT ;
  scheme_renc         := 'I_1 ;
  scheme_card_renc    := card_renc_ord1 ;
  scheme_rand_of_renc := fun _ => 0 |}.
