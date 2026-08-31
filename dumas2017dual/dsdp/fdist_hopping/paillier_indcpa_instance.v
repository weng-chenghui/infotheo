From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import paillier_ahe paillier_fdist_instance.
Require Import indcpa_game dsdp_alice_fdist_secrecy dsdp_alice_trace_link.
Require Import dsdp_instance_family.

(**md**************************************************************************)
(* # Paillier as the encryption scheme of the DSDP trace bound                *)
(*                                                                            *)
(* The DSDP corrupted-Alice results quantify over an abstract AHEncType, a    *)
(* finite coin-index type, a proof that its cardinality is a successor, and   *)
(* a map from coin indices to the scheme's randomness.  This file supplies    *)
(* all four at the Paillier packaging of paillier_fdist_instance.v and reads  *)
(* the class-conditional guessing bound off at that instance.                 *)
(*                                                                            *)
(* At this instance the coin index type is the scheme's own randomness, the   *)
(* finite unit group of Z/(pq)^2 Z, and the coin map is the identity.  The    *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* The advantage stays a parameter.  A record of type                         *)
(* indcpa_epsilon_assumption carries an adversary class, one epsilon, and     *)
(* the assumption that every classified adversary stays below that epsilon,   *)
(* and this file assumes such a record rather than proving one exists for     *)
(* Paillier.  At a modulus that is the product of two distinct primes, a      *)
(* condition this file does not impose, decisional composite residuosity is   *)
(* the assumption a proof of one would start from.                            *)
(*                                                                            *)
(* This is a DSDP corollary specialized at Paillier rather than a property   *)
(* of the scheme, which is why it lives with the DSDP files and not with the  *)
(* scheme library.                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*                    pq_gt1 == the modulus bound the packaging is taken at   *)
(*             renc_paillier == the coin index type of this instantiation,    *)
(*                              the unit group of Z/(pq)^2 Z                  *)
(*     rand_of_renc_paillier == the coin map, the identity                    *)
(*        card_renc_paillier == the successor form of that cardinality, in    *)
(*                              one pinned proof term                         *)
(* paillier_indcpa_assumption == the adversary class and epsilon assumed of   *)
(*                              Paillier at this modulus                      *)
(* dsdp_alice_trace_guess_V2_admissible_paillier_le ==                        *)
(*                              the class-conditional DSDP trace guessing     *)
(*                              bound with 1/(p * q) as its                   *)
(*                              information-theoretic term                    *)
(*         paillier_instance == the rung of a DSDP instance family carried    *)
(*                              by a family of Paillier moduli                *)
(* dsdp_alice_trace_guess_V2_admissible_paillier_negligible ==                *)
(*                              the asymptotic form of that bound, under      *)
(*                              modulus growth and an assumed negligible      *)
(*                              advantage family                              *)
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
   rather than a section Let because the exported statement below mentions
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
   through a rewrite.
   Naming: [card_renc] is the abstract development's name for this
   hypothesis, so the successor form is what the name denotes here; it is a
   nonemptiness statement rather than a cardinality value, unlike
   card_plain_paillier. *)
Lemma card_renc_paillier : #|renc_paillier| = #|renc_paillier|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The plaintext space of this instantiation has cardinality p * q, the form
   the composite-modulus DSDP bounds consume. *)
Let card_plain_pq : #|plain AHE| = (p * q)%N.
Proof. exact: card_plain_paillier_pq. Qed.

Variables (v1 u1 u2 u3 : plain AHE).

(* Charlie's weight is invertible.  This is what makes the DSDP solution
   fiber a bijective image of the plaintext space, and so what turns the
   leaked output into the 1/(p * q) term of the bound below rather than into
   a determination of Bob's input. *)
Hypothesis u3_unit : u3 \is a GRing.unit.

Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : renc_paillier).

(* The IND-CPA assumption made of Paillier at this modulus: an adversary
   class, one epsilon, and the assumption that every classified adversary has
   real-or-zero advantage at most that epsilon at every key built from a
   private key.
   The class and the epsilon live in the record's fields.  The two type
   indices card_renc_paillier and rand_of_renc_paillier only site the record
   at this Paillier packaging, typing the challenger's uniform coin; they
   carry none of the cryptographic content.
   It is a parameter, and every bound stated through it is conditional on a
   record being supplied.  Once a real proof lands, from decisional
   composite residuosity (DCR) at a modulus that is the product of two
   distinct primes, a strengthening of this section's p, q > 1 hypotheses,
   it discharges this Variable by a concrete term built at this same
   card_renc_paillier proof term:

     Definition paillier_dcr_assumption :
         indcpa_epsilon_assumption card_renc_paillier
                                   rand_of_renc_paillier :=
       {| indcpa_admissible :=
            (* the Boolean adversary class the DCR reduction covers *) ;
          indcpa_assumption_epsilon :=
            (* the concrete bound, a function of the DCR advantage *) ;
          indcpa_admissible_epsilon_le :=
            (* the Qed lemma: every classified adversary keeps advantage
               at most that epsilon at every key from a private key *) |}.

   cipher_constant_assumption in indcpa_game.v is such an inhabitant, with a
   computable class, epsilon zero, and the promise field discharged by
   cipher_constant_epsilon_le.  Under a concrete term the corollary below
   computes its epsilon with its proof unchanged, and its two class premises
   become membership proofs of the two reduction adversaries.
   Naming: [indcpa] is in the name because the record is an IND-CPA
   advantage assumption; the bare name paillier_assumption is the literature
   term for decisional composite residuosity, which this record neither is
   nor implies. *)
Variable paillier_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_paillier rand_of_renc_paillier.

Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* A predictor reading Alice's executed DSDP trace at the Paillier
   instantiation returns Bob's input with probability at most 1/(p * q) plus
   twice the assumed advantage.  The three currencies of the abstract bound
   land here as follows: 1/(p * q) is information-theoretic and
   unconditional, the residue of the leaked output along the DSDP solution
   fiber at a plaintext space of size p * q; 2 * epsilon is conditional on
   paillier_indcpa_assumption, and prices the two ciphertext replacements at
   Bob's key and at Charlie's; the two premises are conditional on the class,
   and assert membership of the two reduction adversaries without proving it.
   Naming: extends [alice_trace_guess_V2_admissible_pq_le] with
   the scheme in place of the [pq] variant token, keeping [admissible], which
   is what marks the bound class-conditional against the unconditional
   sibling [dsdp_alice_trace_guess_V2_pq_le]. *)
Corollary dsdp_alice_trace_guess_V2_admissible_paillier_le
    (predict : predictor AHE (dsdp_traceT AHE)) :
  indcpa_admissible paillier_indcpa_assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)) ->
  indcpa_admissible paillier_indcpa_assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)) ->
  alice_trace_guess_V2_pr predict
    <= ((p%:R : R) * q%:R)^-1
       + 2 * indcpa_assumption_epsilon paillier_indcpa_assumption.
Proof.
exact: (alice_trace_guess_V2_admissible_pq_le
          u3_unit w_rb2 card_plain_pq).
Qed.

End paillier_indcpa_instance.

Section paillier_instance_family.
Context {R : realType}.
Variables p q : nat -> nat.
Hypothesis p_gt1 : forall k, (1 < p k)%N.
Hypothesis q_gt1 : forall k, (1 < q k)%N.
Variables (v1f u1f u2f u3f :
  forall k, plain (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))).
Hypothesis u3f_unit : forall k, u3f k \is a GRing.unit.
Variables (dkaf dkbf dkcf :
  forall k, priv_key (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))).
Variables (wb2f wc2f : forall k, renc_paillier (p k) (q k)).

(* The Paillier rung at parameter k: the existing packaging, coin type,
   pinned cardinality, and coin map of this file, with the weights, keys,
   and coins supplied as families.  Everything number-theoretic about the
   moduli beyond 1 < p, q stays assumed, as in the fixed-instance section
   above. *)
Definition paillier_instance (k : nat) : dsdp_instance := {|
  inst_AHE          := Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)) ;
  inst_renc         := renc_paillier (p k) (q k) ;
  inst_card_renc    := card_renc_paillier (p k) (q k) ;
  inst_rand_of_renc := rand_of_renc_paillier (p_gt1 k) (q_gt1 k) ;
  inst_v1 := v1f k ; inst_u1 := u1f k ; inst_u2 := u2f k ;
  inst_u3 := u3f k ; inst_u3_unit := u3f_unit k ;
  inst_dk_a := dkaf k ; inst_dk_b := dkbf k ; inst_dk_c := dkcf k ;
  inst_w_rb2 := wb2f k ; inst_w_rc2 := wc2f k |}.

Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (paillier_instance k))
    (@inst_rand_of_renc (paillier_instance k)).
Variable predict : forall k, predictor (inst_AHE (paillier_instance k))
    (dsdp_traceT (inst_AHE (paillier_instance k))).
Arguments predict : clear implicits.

(* The plaintext cardinality at rung k, in the form the modulus-growth
   hypothesis is stated in. *)
Let card_plain_pq_at (k : nat) :
  #|plain (inst_AHE (paillier_instance k))| = (p k * q k)%N.
Proof. exact: card_plain_paillier_pq. Qed.

(* The asymptotic form of this file's corollary: the guessing family is
   negligible once the modulus family makes 1/(p q) negligible and the
   assumed per-rung advantages are negligible.  The assumption family is
   the per-k form of paillier_indcpa_assumption; decisional composite
   residuosity remains the source a proved record family would start
   from. *)
Corollary dsdp_alice_trace_guess_V2_admissible_paillier_negligible :
  (forall k, indcpa_admissible (A k)
     (bob_trace_adversary_at (I:=paillier_instance)
        (distinguisher_of_predictor (predict k)))) ->
  (forall k, indcpa_admissible (A k)
     (charlie_trace_adversary_at (I:=paillier_instance)
        (distinguisher_of_predictor (predict k)))) ->
  negligible_fun (fun k => (((p k * q k)%N)%:R : R)^-1) ->
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)) ->
  negligible_fun (fun k =>
     alice_trace_guess_V2_pr_at (R:=R) (I:=paillier_instance) (predict k)).
Proof.
move=> HB HC Hpq Heps.
apply: (alice_trace_guess_V2_admissible_negligible HB HC _ Heps).
apply: negligible_fun_le Hpq => k.
by rewrite card_plain_pq_at.
Qed.

End paillier_instance_family.
