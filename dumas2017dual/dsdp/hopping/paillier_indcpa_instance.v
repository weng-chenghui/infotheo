From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import paillier_enc paillier_ahe paillier_fdist_instance.
Require Import indcpa_game.

(**md**************************************************************************)
(* # Paillier as an IND-CPA instance                                          *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v quantifies over an AHEncType, a finite   *)
(* coin-index type, a proof that its cardinality is a successor, and a map    *)
(* from coin indices to the scheme's randomness.  This file supplies all      *)
(* four at the Paillier packaging of paillier_fdist_instance.v, states the    *)
(* IND-CPA assumption of Paillier at that packaging, and indexes the whole    *)
(* instance by a security parameter.  No protocol enters: the file is the     *)
(* scheme side of every computational bound the DSDP files read off at        *)
(* Paillier, and dsdp_instance_family.v is where those bounds are read off.   *)
(*                                                                            *)
(* At this instance the coin index type is the scheme's own randomness, the   *)
(* finite unit group of Z/(pq)^2 Z, and the coin map is the identity.  The    *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* The game and the scheme meet at one constant.  The challenger's law        *)
(* enc_fdist is, at this packaging, the pushforward of the uniform law on     *)
(* the unit group along paillier_enc, the encryption of paillier_enc.v; the   *)
(* two are one term, and enc_fdist_paillierE records it.  The homomorphic     *)
(* operations of the packaging play no part in the game; they are what the    *)
(* DSDP protocol runs on.                                                     *)
(*                                                                            *)
(* The advantage stays a parameter.  A record of type                         *)
(* indcpa_epsilon_assumption carries an adversary class, one epsilon, and     *)
(* the assumption that every classified adversary stays below that epsilon,   *)
(* and this file assumes such a record rather than proving one exists for     *)
(* Paillier.  At a modulus that is the product of two distinct primes, a      *)
(* condition this file does not impose, decisional composite residuosity is   *)
(* the assumption a proof of one would start from.                            *)
(*                                                                            *)
(* Along a family of moduli every datum above becomes a function of the       *)
(* security parameter k, and two hypotheses give the family its asymptotic    *)
(* content: the moduli outgrow every polynomial, and the assumed advantages   *)
(* fall below every inverse polynomial.                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*                    pq_gt1 == the modulus bound the packaging is taken at   *)
(*             renc_paillier == the coin index type of this instantiation,    *)
(*                              the unit group of Z/(pq)^2 Z                  *)
(*     rand_of_renc_paillier == the coin map, the identity                    *)
(*        card_renc_paillier == the successor form of that cardinality, in    *)
(*                              one pinned proof term                         *)
(*       enc_fdist_paillierE == the IND-CPA challenger at this packaging      *)
(*                              encrypts with paillier_enc under uniform      *)
(*                              unit-group randomness                         *)
(* paillier_indcpa_assumption == the adversary class and epsilon assumed of   *)
(*                              Paillier at this modulus                      *)
(* paillier_indcpa_epsilon_le ==                                              *)
(*                              the assumed bound with the Paillier           *)
(*                              experiment written out: acceptance of an      *)
(*                              encryption of the chosen plaintext and of     *)
(*                              zero differ by at most epsilon                *)
(*                  f_inv_pq == the inverse modulus family 1/(p k * q k)      *)
(*           f_size_paillier == the inverse plaintext-cardinality family at   *)
(*                              Paillier                                      *)
(*            f_adv_paillier == the assumed-advantage family                  *)
(*          f_bound_paillier == f_inv_pq plus twice f_adv_paillier            *)
(* f_size_paillier_negligible ==                                              *)
(*                             superpolynomial growth of p k * q k makes      *)
(*                             f_size_paillier negligible                     *)
(* f_bound_paillier_negligible ==                                             *)
(*                             f_bound_paillier is negligible when f_inv_pq   *)
(*                             and f_adv_paillier are                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section paillier_indcpa_instance.
Context {R : realType}.
Variables p q : nat.
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.

(* The modulus bound the Paillier packaging is taken at.  It is a Lemma
   rather than a section Let because the exported statements below mention
   the scheme, hence this proof term; a downstream file restating that bound
   at its own proof of the same inequality needs a name to write. *)
Lemma pq_gt1 : (1 < p * q)%N.
Proof. by rewrite (leq_trans p_gt1) // leq_pmulr // (ltnW q_gt1). Qed.

Local Notation AHE := (Paillier_AHEnc pq_gt1).

(* The coin index type of this instantiation: the scheme's own randomness
   carrier, the unit group of Z/(pq)^2 Z.  The abstract development draws
   encryption randomness from a finite type and maps it into rand, because
   the generic rand of he_types.v is a bare Type and carries no distribution;
   at a concrete scheme the two coincide.
   Naming: [renc] is the coin-index token of the abstract development, with
   the scheme named after it. *)
Definition renc_paillier : finType := {unit 'Z_((p * q) * (p * q))}.

(* The coin map of this instantiation is the identity: the coin index type
   above is definitionally the scheme's randomness, so a coin is already the
   randomness the encryption consumes. *)
Definition rand_of_renc_paillier : renc_paillier -> rand AHE := idfun.

(* The coin space is nonempty, written in the successor form the uniform
   distribution of the abstract development takes.
   Every statement below is instantiated at this one proof term.  A second
   proof of the same equation is propositionally equal to this one and not
   convertible with it, so bounds stated at the two would compose only
   through a rewrite. *)
Lemma card_renc_paillier : #|renc_paillier| = #|renc_paillier|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The IND-CPA challenger at this packaging is the Paillier encryption of
   paillier_enc.v under uniform unit-group randomness.  The game's enc is
   the packaging's enc and the coin map is the identity, so the two laws are
   one term.  This is the point where the game of indcpa_game.v and the
   scheme of paillier_ahe.v meet: every advantage measured below is measured
   against this law, and so against c = g^m * u^n mod (pq)^2 with u
   uniform in the unit group. *)
Lemma enc_fdist_paillierE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) card_renc_paillier rand_of_renc_paillier pk v
  = fdistmap (paillier_enc (pub_gen pk) v) (fdist_uniform card_renc_paillier).
Proof. by []. Qed.

(* The IND-CPA assumption of Paillier: a classified adversary has
   real-or-zero advantage at most that epsilon at every key built from a
   private key.

   If a real proof of the small epsilon is done,
   replace this `Variable paillier_indcpa_assumption` with a real
   `indcpa_epsilon_assumption` definition like this:

      Definition paillier_dcr_assumption :
         indcpa_epsilon_assumption card_renc_paillier
                                   rand_of_renc_paillier :=
       {| indcpa_admissible :=
            (* the Boolean adversary class the DCR reduction covers *) ;
          indcpa_assumption_epsilon :=
            (* the concrete bound, a function of the real advantage *) ;
          indcpa_admissible_epsilon_le :=
            (* the Qed lemma: every classified adversary keeps advantage
               at most that epsilon at every key from a private key *) |}.

   cipher_constant_assumption in indcpa_game.v is such an inhabitant, with
   a computable class and epsilon zero. *)
Variable paillier_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_paillier rand_of_renc_paillier.

(* What the assumption says of Paillier, with the experiment written out.
   For every private key and every adversary the class admits, the
   probability that the adversary accepts an encryption of its chosen
   plaintext under the key's generator and the probability that it accepts
   an encryption of zero differ by at most the assumed epsilon.  The key
   ranges over every PaillierPrivKey record, so the bound is universal over
   keys rather than averaged over a key-generation law, and the adversary
   holds the public key alone. *)
Lemma paillier_indcpa_epsilon_le (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) AHE) :
  indcpa_admissible paillier_indcpa_assumption adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_paillier))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) 0)
              (fdist_uniform card_renc_paillier))) [set true] |
  <= indcpa_assumption_epsilon paillier_indcpa_assumption.
Proof.
move=> Hadm; have := indcpa_admissible_epsilon_le dk Hadm.
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
           !enc_fdist_paillierE.
Qed.

End paillier_indcpa_instance.

Section paillier_indcpa_family.
Context {R : realType}.
Variables p q : nat -> nat.
Hypothesis p_gt1 : forall k, (1 < p k)%N.
Hypothesis q_gt1 : forall k, (1 < q k)%N.

(* The Paillier IND-CPA instance at parameter k is the fixed instance above
   taken at p k and q k: the packaging Paillier_AHEnc (pq_gt1 (p_gt1 k)
   (q_gt1 k)), the coin type renc_paillier (p k) (q k), the pinned
   cardinality card_renc_paillier (p k) (q k), and the coin map
   rand_of_renc_paillier (p_gt1 k) (q_gt1 k).  A family of assumption
   records at those types is the per-k form of paillier_indcpa_assumption. *)
Variable A : forall k,
  indcpa_epsilon_assumption (R:=R) (card_renc_paillier (p k) (q k))
    (rand_of_renc_paillier (p_gt1 k) (q_gt1 k)).

(* The inverse modulus family 1/(p k * q k), the form a growth condition on
   the moduli is stated in. *)
Definition f_inv_pq k : R := (((p k * q k)%N)%:R : R)^-1.

(* The inverse plaintext-cardinality family at Paillier: the
   information-theoretic summand of every guessing bound read off along the
   family. *)
Definition f_size_paillier k : R :=
  (#|plain (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))|%:R : R)^-1.

(* The assumed-advantage family: the epsilon A k assumes at each k. *)
Definition f_adv_paillier k : R := indcpa_assumption_epsilon (A k).

(* The bound family 1/(p k * q k) + 2 * eps k: the shape of the
   class-conditional guessing bound at each k, before any protocol is
   named. *)
Definition f_bound_paillier k : R := f_inv_pq k + 2 * f_adv_paillier k.

(* The moduli outgrow every polynomial in k.  At Paillier the modulus is the
   plaintext cardinality, so this is the growth of the plaintext space, and
   negligible is the asymptotic acceptance criterion for the guessing
   residue an inverse plaintext cardinality concedes. *)
Hypothesis inv_pq_negligible : negligible_fun f_inv_pq.

(* The advantage the assumption family assumes is negligible: the
   asymptotic IND-CPA reading of decisional composite residuosity. *)
Hypothesis assumption_epsilon_negligible : negligible_fun f_adv_paillier.

(* The inverse plaintext cardinality along the family is negligible: the
   plaintext space at k is Z/(p k * q k)Z, so modulus growth is plaintext
   growth.  This is the scheme-side summand of every guessing bound of the
   shape 1/#|plain| + 2 * eps read off along the family. *)
Lemma f_size_paillier_negligible : negligible_fun f_size_paillier.
Proof.
rewrite /f_size_paillier.
under eq_fun => k do rewrite (card_plain_paillier_pq (p_gt1 k) (q_gt1 k)).
exact: inv_pq_negligible.
Qed.

(* The bound family is negligible.  This is the whole asymptotic content of
   the Paillier IND-CPA instance family, stated before any protocol is
   named: a bound of this shape at each k, whatever protocol produced it,
   vanishes in the security parameter. *)
Lemma f_bound_paillier_negligible : negligible_fun f_bound_paillier.
Proof.
exact: negligible_fun_predictor_bound inv_pq_negligible
         assumption_epsilon_negligible.
Qed.

End paillier_indcpa_family.
