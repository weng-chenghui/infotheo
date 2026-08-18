From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp finmap matrix lra reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import homomorphic_encryption.
Require Import paillier_ahe.

(**md**************************************************************************)
(* # Paillier fdist instance packaging                                        *)
(*                                                                            *)
(* The Paillier scheme of paillier_ahe.v packaged as the bundled structures   *)
(* the fdist-axis DSDP results quantify over, with the plaintext cardinality  *)
(* facts those results consume. The randomness carrier of this instance is    *)
(* the finite unit group {unit 'Z_(n*n)}, so a distribution on it is          *)
(* well-typed here, unlike at the generic carrier of he_types.v, whose        *)
(* rand is a bare Type.                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*            Paillier_EncDec == the Paillier EncDecType at modulus n         *)
(*             Paillier_AHEnc == the Paillier AHEncType at modulus n > 1      *)
(*        card_plain_paillier == the plaintext space of that packaging has    *)
(*                              cardinality n                                 *)
(* paillier_rand_pushforward_idfunE ==                                        *)
(*                              the pushforward of the uniform law on the     *)
(*                              instance's randomness carrier along the       *)
(*                              identity coin map is itself; a statability    *)
(*                              witness, not a scheme property                *)
(*     card_plain_paillier_pq == at modulus n := p * q the plaintext space    *)
(*                              has cardinality p * q, discharging the        *)
(*                              cardinality hypothesis of the 1/(pq)          *)
(*                              specializations                               *)
(* ```                                                                       *)
(******************************************************************************)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section paillier_fdist_instance.
Context {R : realType}.
Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

(* The Paillier EncDecType packaging at modulus n. *)
Definition Paillier_EncDec : EncDecType :=
  @EncDec.Pack (PaillierHETypes n)
    (@EncDec.Class (PaillierHETypes n) (@Paillier_isEncDec n)).

(* The Paillier AHEncType packaging at modulus n > 1. *)
Definition Paillier_AHEnc : AHEncType :=
  @AHEnc.Pack (PaillierHETypes n)
    (@AHEnc.Class (PaillierHETypes n)
      (@Paillier_isEncDec n) (@Paillier_isAHEnc n n_gt1)).

(* The plaintext space of the Paillier packaging has cardinality n. *)
Lemma card_plain_paillier : #|plain Paillier_AHEnc| = n.
Proof. by rewrite card_ord Zp_cast. Qed.

(* With the coin-index type equal to the instance's randomness carrier and
   the identity coin map, the pushforward of the uniform law is the uniform
   law: a statability witness for the fixed-key uniform-randomness reading,
   carrying no Paillier content beyond the finiteness of the carrier. *)
Example paillier_rand_pushforward_idfunE (m : nat)
    (card_rand : #|{: rand Paillier_AHEnc}| = m.+1) :
  fdistmap idfun (fdist_uniform (R:=R) card_rand)
  = fdist_uniform (R:=R) card_rand.
Proof. by rewrite fdistmap_id. Qed.

End paillier_fdist_instance.

Section paillier_fdist_instance_pq.
Variables p q : nat.
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.

Let pq_gt1 : (1 < p * q)%N.
Proof. by rewrite (leq_trans p_gt1) // leq_pmulr // (ltnW q_gt1). Qed.

(* At modulus n := p * q the plaintext space has cardinality p * q, which
   discharges the cardinality hypothesis of the 1/(pq) specializations. *)
Lemma card_plain_paillier_pq :
  #|plain (Paillier_AHEnc pq_gt1)| = (p * q)%N.
Proof. exact: card_plain_paillier. Qed.

End paillier_fdist_instance_pq.
