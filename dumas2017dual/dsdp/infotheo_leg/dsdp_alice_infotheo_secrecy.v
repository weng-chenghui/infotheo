(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, infotheo axis                              *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_infotheo_secrecy.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variable pkey_of_party : party_id -> pub_key AHE.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).

End dsdp_alice_infotheo_secrecy.
