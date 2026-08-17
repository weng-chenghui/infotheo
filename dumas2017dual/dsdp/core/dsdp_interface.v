From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import smc_interpreter smc_session_types homomorphic_encryption.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Data Interface                                                        *)
(*                                                                            *)
(* This file provides a unified interface for DSDP protocol data types,       *)
(* eliminating duplication across dsdp_program.v, dsdp_correctness.v,         *)
(* dsdp_program_alt_syntax.v, and dsdp_entropy_trace.v.                       *)
(*                                                                            *)
(* Components:                                                                *)
(*   Recv_param      - Single parametric receive combinator                   *)
(*   DSDP_Interface  - Record bundling data type and operations               *)
(*   Standard_DSDP_Interface - Canonical sum-type implementation              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proc_scope.

(* ========================================================================== *)
(* Parameterized Recv combinator - instantiated in two ways:                  *)
(*   1. Recv-and-decrypt: extract ciphertext, decrypt, continue with plaintext*)
(*   2. Recv-for-HE: extract ciphertext, continue with it for HE computation  *)
(* ========================================================================== *)

Section Recv_param.

Variable (T : Type).
Variable (data : Type).
Variable (extract : data -> option T).

(* Recv_param: receive data, extract value of type T, continue with it *)
Definition Recv_param (frm : nat) (f : T -> proc data) : proc data :=
  Recv frm (oapp f Fail \o extract).

End Recv_param.

Arguments Recv_param {T} data extract frm f.

(* ========================================================================== *)
(* Session Data Type Kind (outside section - no AHE dependency)               *)
(* ========================================================================== *)

(* Only encrypted values are communicated - single dtype suffices *)
Inductive dsdp_dtype : Type := DT_Enc.

(* Decidable equality for dsdp_dtype *)
Definition dsdp_dtype_eqb (d1 d2 : dsdp_dtype) : bool := true.

Lemma dsdp_dtype_eqP : Equality.axiom dsdp_dtype_eqb.
Proof.
move=> [] [].
constructor.
reflexivity.
Qed.

HB.instance Definition _ := hasDecEq.Build dsdp_dtype dsdp_dtype_eqP.

(* ========================================================================== *)
(* DSDP Interface Record                                                      *)
(* ========================================================================== *)

(** Standalone record bundling all DSDP data types and operations.

    This record carries its own message/cipher/randomness/key carriers as
    fields (no AHEncType parameter), so a non-AHE symbolic instance can be
    built alongside the standard cryptographic one.  It eliminates the need
    to repeat data/conversion/operation definitions in every DSDP file. *)
Record DSDP_Interface := MkDSDP_Interface {
  (* Carrier types *)
  di_msgT      : Type ;  (* plaintext scalars *)
  di_cipherT   : Type ;  (* ciphertexts *)
  di_randT     : Type ;  (* encryption randomness *)
  di_priv_keyT : Type ;  (* private keys *)
  di_pub_keyT  : Type ;  (* public keys *)
  di_data      : Type ;  (* the unified carrier a [proc] passes around, holding
                            a value of any of the five carriers above *)

  (* Injectors: wrap a typed value into the unified data carrier.
     Naming: MathComp X_of_Y total-conversion form (the [di_data] of a plain/
     cipher/key); the 5 underscore segments of the *_priv_key/*_pub_key fields
     are the multi-word key sorts, not grammar drift. *)
  di_data_of_plain    : di_msgT      -> di_data ;
  di_data_of_cipher   : di_cipherT   -> di_data ;
  di_data_of_priv_key : di_priv_keyT -> di_data ;
  di_data_of_pub_key  : di_pub_keyT  -> di_data ;

  (* Extractor: get a ciphertext out of the data carrier *)
  di_get_cipher : di_data -> option di_cipherT ;
    (* the ciphertext a carrier holds, when it holds one *)

  (* Encryption and homomorphic operations *)
  di_encrypt : di_pub_keyT -> di_msgT -> di_randT -> di_cipherT ;
    (* encryption of a plaintext under a public key with given randomness *)
  di_emul : di_cipherT -> di_cipherT -> di_cipherT ;
    (* the homomorphic product, an encryption of the sum of the plaintexts *)
  di_epow : di_cipherT -> di_msgT -> di_cipherT ;
    (* the homomorphic power, an encryption of the plaintext scaled by a
       plaintext scalar *)

  (* Plaintext ring operations used by the parties' final reconstruction *)
  di_add : di_msgT -> di_msgT -> di_msgT ;  (* plaintext addition *)
  di_sub : di_msgT -> di_msgT -> di_msgT ;  (* plaintext subtraction *)
  di_mul : di_msgT -> di_msgT -> di_msgT ;  (* plaintext multiplication *)

  (* Specialized Recv operations (proc is unindexed) *)
  di_Recv_dec :
    nat -> di_priv_keyT -> (di_msgT -> proc di_data) ->
    proc di_data ;
    (* receive from the given party, decrypt the ciphertext with the private
       key, and continue on the resulting plaintext *)
  di_Recv_enc :
    nat -> (di_cipherT -> proc di_data) ->
    proc di_data ;
    (* receive from the given party and continue on the ciphertext itself, for
       homomorphic computation under the sender's public key *)
}.

(* Keep the interface argument explicit on every field projection.
   Under [Set Implicit Arguments] the leading DSDP_Interface argument
   would otherwise be inferred from a later carrier-typed argument,
   which breaks [field DI x] applications. *)
Arguments di_data_of_plain : clear implicits.
Arguments di_data_of_cipher : clear implicits.
Arguments di_data_of_priv_key : clear implicits.
Arguments di_data_of_pub_key : clear implicits.
Arguments di_get_cipher : clear implicits.
Arguments di_encrypt : clear implicits.
Arguments di_emul : clear implicits.
Arguments di_epow : clear implicits.
Arguments di_add : clear implicits.
Arguments di_sub : clear implicits.
Arguments di_mul : clear implicits.
Arguments di_Recv_dec : clear implicits.
Arguments di_Recv_enc : clear implicits.

(* ========================================================================== *)
(* Standard DSDP Interface using Sum Types                                    *)
(* ========================================================================== *)

Section Standard_DSDP_Interface.

Variable AHE : AHEncType.

Let msgT := plain AHE.
Let encT := cipher AHE.
Let randT := rand AHE.
Let priv_keyT := priv_key AHE.
Let pub_keyT := pub_key AHE.
Let D := @dec AHE.

(* Standard sum-type data encoding.
   Naming: the std_data_of_* injectors mirror the interface's di_data_of_*
   X_of_Y total-conversion fields; the 5-segment *_priv_key/*_pub_key names
   carry the multi-word key sort, not grammar drift. *)
Definition std_data := (msgT + encT + priv_keyT + pub_keyT)%type.
Definition std_data_of_plain (x : msgT) : std_data := inl (inl (inl x)).
Definition std_data_of_cipher (x : encT) : std_data := inl (inl (inr x)).
Definition std_data_of_priv_key (x : priv_keyT) : std_data := inl (inr x).
Definition std_data_of_pub_key (x : pub_keyT) : std_data := inr x.
Definition std_get_cipher (x : std_data) : option encT :=
  if x is inl (inl (inr v)) then Some v else None.

(* Recv-and-decrypt: extract ciphertext, decrypt, continue with plaintext *)
Definition std_Recv_dec (frm : nat) (dk : priv_keyT)
    (f : msgT -> proc std_data) : proc std_data :=
  Recv_param std_data (obind (D dk) \o std_get_cipher) frm f.

(* Recv-for-HE: extract ciphertext, continue with it for HE computation *)
(* We assume public key of the sender is known to the receiver,
   so we don't explicitly send it along with the ciphertext.
   Rather, the receiver uses the public key of the sender
  to perform the HE computation inside the function f.
*)
Definition std_Recv_enc (frm : nat)
    (f : encT -> proc std_data) : proc std_data :=
  Recv_param std_data std_get_cipher frm f.

(** The canonical standard interface instance.
    di_data stays definitionally std_data (the sum carrier) since
    downstream proofs pattern-match that shape. *)
Definition Standard_DSDP_Interface : DSDP_Interface := {|
  di_msgT := msgT ;
  di_cipherT := encT ;
  di_randT := randT ;
  di_priv_keyT := priv_keyT ;
  di_pub_keyT := pub_keyT ;
  di_data := std_data ;
  di_data_of_plain := std_data_of_plain ;
  di_data_of_cipher := std_data_of_cipher ;
  di_data_of_priv_key := std_data_of_priv_key ;
  di_data_of_pub_key := std_data_of_pub_key ;
  di_get_cipher := std_get_cipher ;
  di_encrypt := @enc AHE ;
  di_emul := @Emul AHE ;
  di_epow := @Epow AHE ;
  di_add := +%R ;
  di_sub := (fun a b => a - b) ;
  di_mul := *%R ;
  di_Recv_dec := @std_Recv_dec ;
  di_Recv_enc := @std_Recv_enc ;
|}.

End Standard_DSDP_Interface.

(* ========================================================================== *)
(* Correctness Lemmas for Standard Interface                                  *)
(* ========================================================================== *)

Section Standard_Interface_Properties.

Variable AHE : AHEncType.
Let DI := Standard_DSDP_Interface AHE.

(* At the Standard instance, [di_get_cipher] recovers a ciphertext from a
   [di_data_of_cipher] injection (std_get_cipher_e) and fails with [None] on a
   plaintext (std_get_cipher_d) or private-key (std_get_cipher_k) injection.
   The [_e]/[_d]/[_k] suffix names the injected sort (enc/data/key). *)
Lemma std_get_cipher_e (x : cipher AHE) :
  di_get_cipher DI (di_data_of_cipher DI x) = Some x.
Proof. by []. Qed.

Lemma std_get_cipher_d (x : plain AHE) :
  di_get_cipher DI (di_data_of_plain DI x) = None.
Proof. by []. Qed.

Lemma std_get_cipher_k (x : priv_key AHE) :
  di_get_cipher DI (di_data_of_priv_key DI x) = None.
Proof. by []. Qed.

End Standard_Interface_Properties.

(* ========================================================================== *)
(* Notation shortcuts for use in client files                                 *)
(* ========================================================================== *)

(* These can be used with: Let data := di_data DI. etc. *)
Notation "'data_of' DI" := (di_data DI) (at level 10, only parsing).
Notation "'d_of' DI" := (di_data_of_plain DI) (at level 10, only parsing).
Notation "'e_of' DI" := (di_data_of_cipher DI) (at level 10, only parsing).
Notation "'priv_key_of' DI" := (di_data_of_priv_key DI) (at level 10, only parsing).
Notation "'pub_key_of' DI" := (di_data_of_pub_key DI) (at level 10, only parsing).
