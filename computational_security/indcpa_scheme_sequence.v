From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finalg.
From mathcomp Require Import reals.
Require Import homomorphic_encryption.
Require Import negligible indcpa_game.

(**md**************************************************************************)
(* # A sequence of IND-CPA schemes as one record                              *)
(*                                                                            *)
(* A scheme sequence is the AHE-layer object a protocol file assumes as one   *)
(* record: an IND-CPA scheme at each security parameter, the assumption made  *)
(* at it, the key material its parties draw their private keys from, and the  *)
(* two asymptotic facts every bound read along the sequence carries.  One     *)
(* argument of this type replaces a scheme variable, an assumption variable   *)
(* and two negligibility hypotheses at each file that states a bound in the   *)
(* security parameter.                                                        *)
(*                                                                            *)
(* The parameter k is read as a key length: each concrete record of this      *)
(* directory carries the bit length of its modulus at k, and the negligibility*)
(* of the inverse plaintext cardinality is derived from that bit length       *)
(* rather than assumed.  The seed type is where a key generation law would    *)
(* live, priv_key being a bare Type over which no distribution is             *)
(* well-typed.                                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*           keygen_sequence == the seed space at each security parameter,    *)
(*                              its nonemptiness, and the private key a seed  *)
(*                              generates                                     *)
(*              keygen_seedT == the seed type at k                            *)
(*          keygen_card_seed == nonemptiness of that type, in the successor   *)
(*                              form fdist_uniform takes                      *)
(*           keygen_priv_key == the private key a seed generates              *)
(*           f_size_scheme S == the inverse plaintext-cardinality sequence    *)
(*                              along the schemes S                           *)
(*            f_adv_scheme A == the advantage sequence the assumptions A      *)
(*                              assume                                        *)
(*    indcpa_scheme_sequence == the four data above as one record over a      *)
(*                              real type                                     *)
(*                 scheme_at == the IND-CPA scheme at k                       *)
(*         scheme_assumption == the IND-CPA assumption made at the scheme     *)
(*                              at k                                          *)
(*             scheme_keygen == the key material along the sequence           *)
(*    scheme_size_negligible == the unconditional term vanishes               *)
(*     scheme_adv_negligible == the assumption-conditional term vanishes      *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* The key material of a scheme sequence: a finite seed space at each security
   parameter.  The private key of a party at k is what its seed generates
   there. *)
Record keygen_sequence (S : nat -> AHEncType) := {
  (* the seed type at k *)
  keygen_seedT : nat -> finType ;
  (* that type is nonempty, in the successor form fdist_uniform takes *)
  keygen_card_seed : forall k, #|keygen_seedT k| = #|keygen_seedT k|.-1.+1 ;
  (* the private key a seed generates *)
  keygen_priv_key : forall k, keygen_seedT k -> priv_key (S k) }.

(* A call site names the record it reads a key off and the parameter it reads
   at, the seed alone leaving both to unification. *)
Arguments keygen_seedT {S} K k : rename.
Arguments keygen_card_seed {S} K k : rename.
Arguments keygen_priv_key {S} K k : rename.

Section scheme_sequence_terms.
Context {R : realType}.

(* The inverse plaintext cardinality along a sequence of schemes.  It is the
   unconditional term of every guessing bound read along the sequence. *)
Definition f_size_scheme (S : nat -> indcpa_scheme) (k : nat) : R :=
  (#|plain (scheme_AHE (S k))|%:R : R)^-1.

(* The advantage a sequence of IND-CPA assumptions assumes at k.  It is the
   assumption-conditional term of every such bound. *)
Definition f_adv_scheme (S : nat -> indcpa_scheme)
    (A : forall k, indcpa_epsilon_assumption (R:=R) (S k)) (k : nat) : R :=
  indcpa_assumption_epsilon (A k).

End scheme_sequence_terms.

(* A sequence of IND-CPA schemes, with the assumption, the key material and
   two asymptotic facts at each security parameter.  The assumption at k is
   made about the scheme value the record carries, pinning one coin space. *)
Record indcpa_scheme_sequence (R : realType) := {
  (* the IND-CPA scheme at the security parameter k *)
  scheme_at : nat -> indcpa_scheme ;
  (* the IND-CPA assumption made at the scheme at k *)
  scheme_assumption : forall k, indcpa_epsilon_assumption (R:=R) (scheme_at k) ;
  (* the seed spaces and private keys along the sequence *)
  scheme_keygen : keygen_sequence (fun k => scheme_AHE (scheme_at k)) ;
  (* the unconditional term: the inverse plaintext cardinality vanishes *)
  scheme_size_negligible : negligible_fun (f_size_scheme (R:=R) scheme_at) ;
  (* the assumption-conditional term: the assumed advantage vanishes *)
  scheme_adv_negligible : negligible_fun (f_adv_scheme scheme_assumption) }.

(* The record stays an explicit argument of the scheme projection, for the same
   reason it does on the key material above. *)
Arguments scheme_at {R} Q k : rename.
