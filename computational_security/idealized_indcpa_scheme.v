From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finalg zmodp.
From mathcomp Require Import reals.
Require Import homomorphic_encryption idealized_ahe.
Require Import negligible indcpa_game indcpa_scheme_sequence.

(**md**************************************************************************)
(* # The idealized AHE scheme as an IND-CPA scheme                            *)
(*                                                                            *)
(* The idealized encryption of idealized_ahe.v returns its plaintext, so its  *)
(* IND-CPA advantage is zero at every adversary and the one-element coin      *)
(* space carries no randomness.  Read along the security parameter it gives   *)
(* an inhabitant of indcpa_scheme_sequence under no assumption at all, which  *)
(* is what answers the vacuity question a class-conditional bound leaves      *)
(* open: the hypotheses of such a bound hold together at least once.          *)
(*                                                                            *)
(* The plaintext space at k is Z/((k+2)^(k+2))Z, which grows past every       *)
(* polynomial and so has at least k bits, so the sequence meets the key       *)
(* length reading of the parameter as well.                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*           card_renc_ord1 == the one-element coin space has successor       *)
(*                             cardinality                                    *)
(*   idealized_indcpa_scheme == the idealized AHE scheme as an IND-CPA        *)
(*                             scheme, at a plaintext ring                    *)
(*         idealized_scheme == that scheme at the plaintext ring              *)
(*                             Z/((k+2)^(k+2))Z                               *)
(*     card_plain_idealized == the plaintext space at k has cardinality       *)
(*                             (k+2)^(k+2)                                    *)
(*         idealized_keygen == the one-element seed space and the zero        *)
(*                             private key at each k                          *)
(* idealized_size_negligible == the inverse plaintext cardinality along the   *)
(*                             sequence is negligible                         *)
(* idealized_scheme_sequence == that sequence as an indcpa_scheme_sequence,   *)
(*                             built under no assumption                      *)
(* ```                                                                        *)
(*                                                                            *)
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

(* The idealized scheme at the security parameter k, over a plaintext space of
   cardinality (k+2)^(k+2).  That cardinality is what leaves the guessing
   bound along the sequence a nonzero number rather than zero. *)
Definition idealized_scheme (k : nat) : indcpa_scheme :=
  idealized_indcpa_scheme 'Z_((k.+2) ^ k.+2).

(* The plaintext space at k has cardinality (k+2)^(k+2). *)
Lemma card_plain_idealized (k : nat) :
  #|plain (scheme_AHE (idealized_scheme k))| = ((k.+2) ^ k.+2)%N.
Proof. by rewrite card_ord Zp_cast // -{1}(expn0 k.+2) ltn_exp2l. Qed.

(* The idealized key material: a one-element seed space and the zero private
   key at every k.  Key generation carries no secret here, which is what makes
   the sequence an inhabitant rather than a proposal. *)
Definition idealized_keygen :
    keygen_sequence (fun k => scheme_AHE (idealized_scheme k)) :=
  @Build_keygen_sequence (fun k => scheme_AHE (idealized_scheme k))
    (fun _ => 'I_1) (fun _ => card_renc_ord1) (fun _ _ => 0).

Section idealized_scheme_sequence.
Context {R : realType}.

(* The inverse plaintext cardinality along the idealized sequence is
   negligible, its plaintext spaces growing as (k+2)^(k+2). *)
Lemma idealized_size_negligible :
  negligible_fun (f_size_scheme (R:=R) idealized_scheme).
Proof.
apply: negligible_fun_le negligible_fun_inv_expnn => k.
by rewrite /f_size_scheme card_plain_idealized.
Qed.

(* The idealized sequence, an inhabitant of indcpa_scheme_sequence under no
   assumption at all.  Its assumed advantage is zero at every k, leaving a
   bound read along it only its information-theoretic term. *)
Definition idealized_scheme_sequence : indcpa_scheme_sequence R := {|
  scheme_at := idealized_scheme ;
  scheme_assumption := fun k =>
    cipher_constant_assumption (R:=R) (idealized_scheme k) ;
  scheme_keygen := idealized_keygen ;
  scheme_size_negligible := idealized_size_negligible ;
  scheme_adv_negligible := negligible_fun_cst0 |}.

End idealized_scheme_sequence.
