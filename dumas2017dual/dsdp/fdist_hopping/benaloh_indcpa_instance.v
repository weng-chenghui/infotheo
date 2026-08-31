From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import benaloh_ahe.
Require Import indcpa_game dsdp_alice_fdist_secrecy dsdp_alice_trace_link.
Require Import dsdp_instance_family.

(**md**************************************************************************)
(* # Benaloh as the encryption scheme of the DSDP trace bound                 *)
(*                                                                            *)
(* The DSDP corrupted-Alice results quantify over an abstract AHEncType, a    *)
(* finite coin-index type, a proof that its cardinality is a successor, and   *)
(* a map from coin indices to the scheme's randomness.  This file supplies    *)
(* all four at the Benaloh packaging of benaloh_ahe.v and reads the           *)
(* class-conditional guessing bound off at that instance.                     *)
(*                                                                            *)
(* At this instance the coin index type is the scheme's own randomness, the   *)
(* finite unit group of Z/nZ, and the coin map is the identity.  The          *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
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
(* This is a DSDP corollary specialized at Benaloh rather than a property of  *)
(* the scheme, which is why it lives with the DSDP files and not with the     *)
(* scheme library.                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*              Benaloh_AHEnc == the Benaloh AHEncType at modulus n and       *)
(*                               block size r                                 *)
(*               renc_benaloh == the coin index type of this instantiation,   *)
(*                               the unit group of Z/nZ                       *)
(*       rand_of_renc_benaloh == the coin map, the identity                   *)
(*          card_renc_benaloh == the successor form of that cardinality, in   *)
(*                               one pinned proof term                        *)
(*  benaloh_indcpa_assumption == the adversary class and epsilon assumed of   *)
(*                               Benaloh at these parameters                  *)
(* dsdp_alice_trace_guess_V2_admissible_benaloh_le ==                         *)
(*                               the class-conditional DSDP trace guessing    *)
(*                               bound with 1/r as its information-theoretic  *)
(*                               term                                         *)
(*           benaloh_instance == the DSDP instance family carried by a       *)
(*                               family of Benaloh block sizes                *)
(* dsdp_alice_trace_guess_V2_admissible_benaloh_negligible ==                 *)
(*                               the asymptotic form of that bound, under     *)
(*                               block-size growth and an assumed negligible  *)
(*                               advantage family                             *)
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
   through a rewrite.
   Naming: [card_renc] is the abstract development's name for this
   hypothesis, so the successor form is what the name denotes here; it is a
   nonemptiness statement rather than a cardinality value, unlike
   card_plain_r. *)
Lemma card_renc_benaloh : #|renc_benaloh| = #|renc_benaloh|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The plaintext space of this instantiation is Z/rZ, so its cardinality is
   the block size r.  It is r, not the modulus n, that the information-
   theoretic term of the bound below is read off: at Benaloh the plaintext
   space is the block Z/rZ fixed by the order condition on the private key's
   generator, while n sizes the ciphertext space. *)
Let card_plain_r : #|plain AHE| = r.
Proof. by rewrite card_ord Zp_cast. Qed.

Variables (v1 u1 u2 u3 : plain AHE).

(* Charlie's weight is invertible in Z/rZ.  This is what makes the DSDP
   solution fiber a bijective image of the plaintext space, and so what turns
   the leaked output into the 1/r term of the bound below rather than into a
   determination of Bob's input. *)
Hypothesis u3_unit : u3 \is a GRing.unit.

Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : renc_benaloh).

(* The IND-CPA assumption made of Benaloh at these parameters: an adversary
   class, one epsilon, and the assumption that every classified adversary has
   real-or-zero advantage at most that epsilon at every key built from a
   private key.
   The class and the epsilon live in the record's fields.  The two type
   indices card_renc_benaloh and rand_of_renc_benaloh only site the record at
   this Benaloh packaging, typing the challenger's uniform coin; they carry
   none of the cryptographic content.
   It is a parameter, and every bound stated through it is conditional on a
   record being supplied.  Once a real proof lands, from r-th residuosity,
   also called higher residuosity, at a modulus n = p * q with p and q
   distinct primes and a prime r dividing p - 1 and coprime to
   (p - 1) * (q - 1) / r, a strengthening of this section's n, r > 1
   hypotheses, it discharges this Variable by a concrete term built at this
   same card_renc_benaloh proof term:

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
   computable class, epsilon zero, and the promise field discharged by
   cipher_constant_epsilon_le.  Under a concrete term the corollary below
   computes its epsilon with its proof unchanged, and its two class premises
   become membership proofs of the two reduction adversaries.
   Naming: [indcpa] is in the name because the record is an IND-CPA
   advantage assumption; a bare benaloh_assumption would read as the
   scheme's own hardness assumption, r-th residuosity, which this record
   neither is nor implies. *)
Variable benaloh_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_benaloh rand_of_renc_benaloh.

Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* The inverse plaintext cardinality at the Benaloh block size. *)
Let inv_r_cardE : (r%:R : R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_r. Qed.

(* A predictor reading Alice's executed DSDP trace at the Benaloh
   instantiation returns Bob's input with probability at most 1/r plus twice
   the assumed advantage.  The three currencies of the abstract bound land
   here as follows: 1/r is information-theoretic and unconditional, the
   residue of the leaked output along the DSDP solution fiber at a plaintext
   space of size r; 2 * epsilon is conditional on benaloh_indcpa_assumption,
   and prices the two ciphertext replacements at Bob's key and at Charlie's;
   the two premises are conditional on the class, and assert membership of
   the two reduction adversaries without proving it.
   Naming: extends [alice_trace_guess_V2_admissible_le] with the scheme
   token before [le], keeping [admissible], which is what marks the bound
   class-conditional against the unconditional sibling
   [alice_trace_guess_V2_le]. *)
Corollary dsdp_alice_trace_guess_V2_admissible_benaloh_le
    (predict : predictor AHE (dsdp_traceT AHE)) :
  indcpa_admissible benaloh_indcpa_assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)) ->
  indcpa_admissible benaloh_indcpa_assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)) ->
  alice_trace_guess_V2_pr predict
    <= (r%:R : R)^-1
       + 2 * indcpa_assumption_epsilon benaloh_indcpa_assumption.
Proof.
rewrite inv_r_cardE.
exact: (alice_trace_guess_V2_admissible_le u3_unit w_rb2).
Qed.

End benaloh_indcpa_instance.

Section benaloh_instance_family.
Context {R : realType}.
Variables n r : nat -> nat.
Hypothesis n_gt1 : forall k, (1 < n k)%N.
Hypothesis r_gt1 : forall k, (1 < r k)%N.
Variables (v1f u1f u2f u3f :
  forall k, plain (Benaloh_AHEnc (n k) (r_gt1 k))).
Hypothesis u3f_unit : forall k, u3f k \is a GRing.unit.
Variables (dkaf dkbf dkcf :
  forall k, priv_key (Benaloh_AHEnc (n k) (r_gt1 k))).
Variables (wb2f wc2f : forall k, renc_benaloh (n k)).

(* The Benaloh instance at parameter k: the existing packaging, coin type,
   pinned cardinality, and coin map of this file, with the weights, keys,
   and coins supplied as families.  Everything number-theoretic about the
   modulus and the block size beyond 1 < n, r stays assumed, as in the
   fixed-instance section above. *)
Definition benaloh_instance (k : nat) : dsdp_instance := {|
  inst_AHE          := Benaloh_AHEnc (n k) (r_gt1 k) ;
  inst_renc         := renc_benaloh (n k) ;
  inst_card_renc    := card_renc_benaloh (n k) ;
  inst_rand_of_renc := rand_of_renc_benaloh (n:=n k) (r_gt1 k) ;
  inst_v1 := v1f k ; inst_u1 := u1f k ; inst_u2 := u2f k ;
  inst_u3 := u3f k ; inst_u3_unit := u3f_unit k ;
  inst_dk_a := dkaf k ; inst_dk_b := dkbf k ; inst_dk_c := dkcf k ;
  inst_w_rb2 := wb2f k ; inst_w_rc2 := wc2f k |}.

Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (benaloh_instance k))
    (@inst_rand_of_renc (benaloh_instance k)).
Variable predict : forall k, predictor (inst_AHE (benaloh_instance k))
    (dsdp_traceT (inst_AHE (benaloh_instance k))).
Arguments predict : clear implicits.

(* The plaintext cardinality at k, in the form the block-size growth
   hypothesis is stated in. *)
Let card_plain_r_at (k : nat) :
  #|plain (inst_AHE (benaloh_instance k))| = r k.
Proof. by rewrite card_ord (Zp_cast (r_gt1 k)). Qed.

(* The class of the assumption family admits the Bob-side reduction
   adversary induced by every predictor in the family. *)
Hypothesis bob_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (bob_trace_adversary_at (I:=benaloh_instance)
       (distinguisher_of_predictor (predict k))).

(* The Charlie-side twin of bob_reduction_admissible. *)
Hypothesis charlie_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (charlie_trace_adversary_at (I:=benaloh_instance)
       (distinguisher_of_predictor (predict k))).

(* The probability bounded here is that of a predictor reading Alice's
   executed trace, the encoding of her real hopping tuple
   ((R2, R3), (RA1, RA2), Sout, hop0_cipher, hop1_cipher): her two masks,
   her two combine coins, the leaked output, and the ciphertext slots
   carrying Bob's V2 and Charlie's V3.  Even with the two ciphertext slots
   idealized to encrypt zero, Sout still confines the uniform V2 to the
   solution fiber, so a blind guess succeeds with probability 1/#|plain|,
   a floor no quality of encryption lowers.  At Benaloh the plaintext
   space is the block Z/rZ at block size r k, so requiring that floor to
   vanish is requiring the block size to outgrow every polynomial in k,
   which is what this hypothesis supplies to the negligibility
   corollary. *)
Hypothesis inv_r_negligible :
  negligible_fun (fun k => ((r k)%:R : R)^-1).

(* The advantage the assumption family assumes is negligible: the
   asymptotic IND-CPA reading of r-th residuosity. *)
Hypothesis assumption_epsilon_negligible :
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)).

(* The conclusion is negligible_fun of the family k |-> Pr_k, where Pr_k
   is the probability that the k-th predictor guesses Bob's input V2 at
   the k-th Benaloh instance.

   It follows from the four hypotheses in three steps.  At each k the two
   class premises yield the bound of alice_trace_guess_V2_admissible_le,
   Pr_k <= 1/(r k) + 2 * eps k, with eps k the advantage A k assumes.
   The two negligibility hypotheses make both summand families vanish, so
   the upper-bound family is negligible by negligible_fun_predictor_bound.
   negligible_fun_le then transfers negligibility from that dominating
   family down to Pr_k.

   The assumption family is the per-k form of benaloh_indcpa_assumption;
   r-th residuosity remains the source a proved record family would start
   from. *)
Corollary dsdp_alice_trace_guess_V2_admissible_benaloh_negligible :
  negligible_fun (fun k =>
     alice_trace_guess_V2_pr_at (R:=R) (I:=benaloh_instance) (predict k)).
Proof.
apply: (alice_trace_guess_V2_admissible_negligible
          bob_reduction_admissible charlie_reduction_admissible _
          assumption_epsilon_negligible).
by under eq_fun do rewrite card_plain_r_at.
Qed.

End benaloh_instance_family.
