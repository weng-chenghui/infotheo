From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import benaloh_enc benaloh_ahe.
Require Import indcpa_game.

(**md**************************************************************************)
(* # Benaloh as an IND-CPA instance                                           *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v quantifies over an AHEncType, a finite   *)
(* coin-index type, a proof that its cardinality is a successor, and a map    *)
(* from coin indices to the scheme's randomness.  This file supplies all      *)
(* four at the Benaloh packaging of benaloh_ahe.v, states the IND-CPA         *)
(* assumption of Benaloh at that packaging, and indexes the whole instance    *)
(* by a security parameter.  No protocol enters: the file is the scheme side  *)
(* of every computational bound the DSDP files read off at Benaloh, and       *)
(* dsdp_instance_family.v is where those bounds are read off.                 *)
(*                                                                            *)
(* At this instance the coin index type is the scheme's own randomness, the   *)
(* finite unit group of Z/nZ, and the coin map is the identity.  The          *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* The game and the scheme meet at one constant.  The challenger's law        *)
(* enc_fdist is, at this packaging, the pushforward of the uniform law on     *)
(* the unit group along benaloh_enc, the encryption of benaloh_enc.v; the     *)
(* two are one term, and enc_fdist_benalohE records it.  The homomorphic      *)
(* operations of the packaging play no part in the game; they are what the    *)
(* DSDP protocol runs on.                                                     *)
(*                                                                            *)
(* The advantage stays a parameter.  A record of type                         *)
(* indcpa_epsilon_assumption carries an adversary class, one epsilon, and     *)
(* the assumption that every classified adversary stays below that epsilon,   *)
(* and this file assumes such a record rather than proving one exists for     *)
(* Benaloh.  At a modulus n = p * q with p and q distinct primes and a prime  *)
(* r dividing p - 1 and coprime to (p - 1) * (q - 1) / r, conditions this     *)
(* file does not impose, r-th residuosity is the assumption a proof of one    *)
(* would start from.                                                          *)
(*                                                                            *)
(* Along a family of parameters every datum above becomes a function of the   *)
(* security parameter k, and two hypotheses give the family its asymptotic    *)
(* content: the block sizes outgrow every polynomial, and the assumed         *)
(* advantages fall below every inverse polynomial.  It is the block size r,   *)
(* the plaintext space Z/rZ, that must grow, and not the modulus n, which     *)
(* sizes the ciphertext space.                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*              Benaloh_AHEnc == the Benaloh AHEncType at modulus n and       *)
(*                               block size r                                 *)
(*               renc_benaloh == the coin index type of this instantiation,   *)
(*                               the unit group of Z/nZ                       *)
(*       rand_of_renc_benaloh == the coin map, the identity                   *)
(*          card_renc_benaloh == the successor form of that cardinality, in   *)
(*                               one pinned proof term                        *)
(*         enc_fdist_benalohE == the IND-CPA challenger at this packaging     *)
(*                               encrypts with benaloh_enc under uniform      *)
(*                               unit-group randomness                        *)
(*  benaloh_indcpa_assumption == the adversary class and epsilon assumed of   *)
(*                               Benaloh at these parameters                  *)
(*  benaloh_indcpa_epsilon_le == the assumed bound with the Benaloh           *)
(*                               experiment written out: acceptance of an     *)
(*                               encryption of the chosen plaintext and of    *)
(*                               zero differ by at most epsilon               *)
(*                    f_inv_r == the inverse block-size family 1/(r k)       *)
(*             f_size_benaloh == the inverse plaintext-cardinality family at  *)
(*                               Benaloh                                      *)
(*              f_adv_benaloh == the assumed-advantage family                 *)
(*            f_bound_benaloh == f_inv_r plus twice f_adv_benaloh             *)
(* f_size_benaloh_negligible ==                                             *)
(*                              superpolynomial growth of r k makes         *)
(*                              f_size_benaloh negligible                   *)
(* f_bound_benaloh_negligible ==                                            *)
(*                              f_bound_benaloh is negligible when f_inv_r  *)
(*                              and f_adv_benaloh are                       *)
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

Section benaloh_indcpa_instance.
Context {R : realType}.
Variables n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* The Benaloh AHEncType at modulus n and block size r: the encryption and
   decryption pair of benaloh_ahe.v together with the additively homomorphic
   structure the DSDP protocol runs on.  The homomorphic mixin is built at
   r > 1, which is why r_gt1 enters the packaging.  The modulus condition
   n > 1 is the standing requirement on the key space, weaker than the
   composite modulus the scheme's security rests on and consumed by neither
   the packaging nor the bound below. *)
Definition Benaloh_AHEnc : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r) (@Benaloh_isEncDec n r)
      (@Benaloh_isAHEnc n r r_gt1)).

Local Notation AHE := Benaloh_AHEnc.

(* The coin index type of this instantiation: the scheme's own randomness
   carrier, the unit group of Z/nZ.  The abstract development draws
   encryption randomness from a finite type and maps it into rand, because
   the generic rand of he_types.v is a bare Type and carries no distribution;
   at a concrete scheme the two coincide.
   Naming: [renc] is the coin-index token of the abstract development, with
   the scheme named after it. *)
Definition renc_benaloh : finType := {unit 'Z_n}.

(* The coin map of this instantiation is the identity: the coin index type
   above is definitionally the scheme's randomness, so a coin is already the
   randomness the encryption consumes. *)
Definition rand_of_renc_benaloh : renc_benaloh -> rand AHE := idfun.

(* The coin space is nonempty, written in the successor form the uniform
   distribution of the abstract development takes.
   Every statement below is instantiated at this one proof term.  A second
   proof of the same equation is propositionally equal to this one and not
   convertible with it, so bounds stated at the two would compose only
   through a rewrite. *)
Lemma card_renc_benaloh : #|renc_benaloh| = #|renc_benaloh|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The IND-CPA challenger at this packaging is the Benaloh encryption of
   benaloh_enc.v under uniform unit-group randomness.  The game's enc is the
   packaging's enc and the coin map is the identity, so the two laws are one
   term.  This is the point where the game of indcpa_game.v and the scheme
   of benaloh_ahe.v meet: every advantage measured below is measured against
   this law, and so against c = y^m * u^r mod n with u uniform in the unit
   group. *)
Lemma enc_fdist_benalohE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) card_renc_benaloh rand_of_renc_benaloh pk v
  = fdistmap (benaloh_enc (pub_gen pk) v) (fdist_uniform card_renc_benaloh).
Proof. by []. Qed.

(* The IND-CPA assumption of Benaloh: a classified adversary has
   real-or-zero advantage at most that epsilon at every key built from a
   private key.

   If a real proof of the small epsilon is done,
   replace this `Variable benaloh_indcpa_assumption` with a real
   `indcpa_epsilon_assumption` definition like this:

     Definition benaloh_hr_assumption :
         indcpa_epsilon_assumption card_renc_benaloh
                                   rand_of_renc_benaloh :=
       {| indcpa_admissible :=
            (* the Boolean adversary class the residuosity reduction
               covers *) ;
          indcpa_assumption_epsilon :=
            (* the concrete bound, a function of the r-th residuosity
               advantage *) ;
          indcpa_admissible_epsilon_le :=
            (* the Qed lemma: every classified adversary keeps advantage
               at most that epsilon at every key from a private key *) |}.

   cipher_constant_assumption in indcpa_game.v is such an inhabitant, with a
   computable class and epsilon zero. *)
Variable benaloh_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_benaloh rand_of_renc_benaloh.

(* What the assumption says of Benaloh, with the experiment written out.
   For every private key and every adversary the class admits, the
   probability that the adversary accepts an encryption of its chosen
   plaintext under the key's generator and the probability that it accepts
   an encryption of zero differ by at most the assumed epsilon.  The key
   ranges over every BenalohPrivKey record, so the bound is universal over
   keys rather than averaged over a key-generation law, and the adversary
   holds the public key alone. *)
Lemma benaloh_indcpa_epsilon_le (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) AHE) :
  indcpa_admissible benaloh_indcpa_assumption adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_benaloh))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (0 : plain AHE))
              (fdist_uniform card_renc_benaloh))) [set true] |
  <= indcpa_assumption_epsilon benaloh_indcpa_assumption.
Proof.
move=> Hadm; have := indcpa_admissible_epsilon_le dk Hadm.
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
           !enc_fdist_benalohE.
Qed.

End benaloh_indcpa_instance.

Section benaloh_indcpa_family.
Context {R : realType}.
Variables n r : nat -> nat.
Hypothesis n_gt1 : forall k, (1 < n k)%N.
Hypothesis r_gt1 : forall k, (1 < r k)%N.

(* The Benaloh IND-CPA instance at parameter k is the fixed instance above
   taken at n k and r k: the packaging Benaloh_AHEnc (n k) (r_gt1 k), the
   coin type renc_benaloh (n k), the pinned cardinality
   card_renc_benaloh (n k), and the coin map rand_of_renc_benaloh (r_gt1 k).
   A family of assumption records at those types is the per-k form of
   benaloh_indcpa_assumption. *)
Variable A : forall k,
  indcpa_epsilon_assumption (R:=R) (card_renc_benaloh (n k))
    (rand_of_renc_benaloh (n:=n k) (r_gt1 k)).

(* The inverse block-size family 1/(r k), the form a growth condition on
   the block sizes is stated in. *)
Definition f_inv_r k : R := ((r k)%:R : R)^-1.

(* The inverse plaintext-cardinality family at Benaloh: the
   information-theoretic summand of every guessing bound read off along the
   family. *)
Definition f_size_benaloh k : R :=
  (#|plain (Benaloh_AHEnc (n k) (r_gt1 k))|%:R : R)^-1.

(* The assumed-advantage family: the epsilon A k assumes at each k. *)
Definition f_adv_benaloh k : R := indcpa_assumption_epsilon (A k).

(* The bound family 1/(r k) + 2 * eps k: the shape of the class-conditional
   guessing bound at each k, before any protocol is named. *)
Definition f_bound_benaloh k : R := f_inv_r k + 2 * f_adv_benaloh k.

(* The block sizes outgrow every polynomial in k.  At Benaloh the block size
   is the plaintext cardinality, so this is the growth of the plaintext
   space, and negligible is the asymptotic acceptance criterion for the
   guessing residue an inverse plaintext cardinality concedes. *)
Hypothesis inv_r_negligible : negligible_fun f_inv_r.

(* The advantage the assumption family assumes is negligible: the
   asymptotic IND-CPA reading of r-th residuosity. *)
Hypothesis assumption_epsilon_negligible : negligible_fun f_adv_benaloh.

(* The inverse plaintext cardinality along the family is negligible: the
   plaintext space at k is Z/(r k)Z, so block-size growth is plaintext
   growth.  This is the scheme-side summand of every guessing bound of the
   shape 1/#|plain| + 2 * eps read off along the family. *)
Lemma f_size_benaloh_negligible : negligible_fun f_size_benaloh.
Proof.
rewrite /f_size_benaloh.
under eq_fun => k do rewrite card_ord (Zp_cast (r_gt1 k)).
exact: inv_r_negligible.
Qed.

(* The bound family is negligible.  This is the whole asymptotic content of
   the Benaloh IND-CPA instance family, stated before any protocol is named:
   a bound of this shape at each k, whatever protocol produced it, vanishes
   in the security parameter. *)
Lemma f_bound_benaloh_negligible : negligible_fun f_bound_benaloh.
Proof.
exact: negligible_fun_predictor_bound inv_r_negligible
         assumption_epsilon_negligible.
Qed.

End benaloh_indcpa_family.
