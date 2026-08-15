(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Type Definitions                       *)
(*                                                                            *)
(* This file defines the base types for party-labeled homomorphic encryption: *)
(*   - key_type type (Dec | Enc) with HB instances                                 *)
(*   - HETypes record bundling carrier types                                  *)
(*                                                                            *)
(* == Types ==                                                                *)
(*                                                                            *)
(*   HETypes bundles five types:                                              *)
(*     - plain : finComNzRingType   (message/plaintext space)                 *)
(*     - rand : Type                (randomness; ops from the isAHEnc mixin)  *)
(*     - cipher : finNzRingType     (raw ciphertext without party label)      *)
(*     - pub_key : Type             (public key space)                        *)
(*     - priv_key : Type            (private key space)                       *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   enc_dec.v       - Encryption/decryption mixin (isEncDec)                 *)
(*   ahe_enc.v       - Homomorphic operations mixin (isAHEnc)                 *)
(*   ahe_algebra.v   - Algebraic properties mixin (isAHEAlgebra)              *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Record HETypes := MkHE {
  plain : finComNzRingType ;    (* message/plaintext space *)
  rand : Type ;                 (* different HE schemes have different
                                   rand requirements, like {unit 'Z_n}
                                   for Benaloh, {unit 'Z_n2} for Paillier *)
  cipher : finNzRingType ;      (* raw ciphertext values without party label *)
  pub_key : Type ;              
  priv_key : Type;
}.
