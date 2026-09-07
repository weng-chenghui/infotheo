From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba.
Require Import extra_algebra.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption residuosity_game.
Require Import idealized_ahe paillier_fdist_instance.
Require Import negligible epshop epshop_sequence.
Require Import indcpa_game indcpa_scheme_sequence idealized_indcpa_scheme.
Require Import paillier_indcpa_scheme benaloh_indcpa_scheme.
Require Import dsdp_instance.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.
Require Import dsdp_alice_main.

(**md**************************************************************************)
(* # Concrete readings of DSDP corrupted-Alice secrecy                       *)
(*                                                                            *)
(* The abstract Alice bounds are read at the idealized, Paillier and Benaloh  *)
(* scheme sequences of computational_security/.  Each section takes one       *)
(* scheme-sequence record, Alice's four weights and the three key seeds, and  *)
(* assumes nothing further about the scheme: the IND-CPA assumption at each   *)
(* security parameter and the two negligibility facts an asymptotic           *)
(* statement carries come with that record.                                   *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope proc_scope.
Local Open Scope sproc_scope.

(* The vacuity question the abstract bounds leave open, answered on the
   idealized scheme sequence of idealized_indcpa_scheme.v.  Every hypothesis
   of the guessing headline is discharged at once there, the assumed advantage
   being zero at every k. *)
Section idealized.
Context {R : realType}.

(* The idealized sequence: the schemes of idealized_indcpa_scheme.v, zero
   weights with a unit on Charlie's input, and one seed per key space. *)
Definition idealized_instance_sequence : dsdp_instance_sequence R :=
  mk_dsdp_instance_sequence (idealized_scheme_sequence (R:=R))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
    (fun _ => GRing.unitr1 _) (fun _ => ord0) (fun _ => ord0) (fun _ => ord0).

(* The idealized instance at k, over a plaintext space of cardinality
   (k+2)^(k+2).  Its guessing probability is 1/#|plain| rather than 0, so the
   bound has content. *)
Definition idealized_instance (k : nat) : dsdp_instance :=
  sequence_instance idealized_instance_sequence k.

(* The two negligibility facts about that sequence, discharged rather
   than assumed.  Its assumed advantage is zero at every k, leaving only the
   1/#|plain| term. *)
Definition idealized_asymptotic :
    dsdp_asymptotic idealized_instance_sequence :=
  mk_dsdp_asymptotic (idealized_scheme_sequence (R:=R))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
    (fun _ => GRing.unitr1 _) (fun _ => ord0) (fun _ => ord0) (fun _ => ord0).

(* The constant predictor's distinguisher reads only the state slot.  Its
   Bob-key reduction ignores the challenge ciphertext, so the cipher-constant
   class admits it. *)
Lemma idealized_bob_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (bob_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of idealized_bob_cipher_constant. *)
Lemma idealized_charlie_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (charlie_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The hypotheses of alice_trace_guess_V2_negligible hold together at least
   once, on the idealized sequence.  The constant predictor's two reductions
   are in the cipher-constant class at every k. *)
Corollary alice_trace_guess_V2_idealized_negligible :
  negligible_fun (fun k =>
    alice_trace_guess_V2_pr (R:=R) (I:=idealized_instance k) (fun _ => 0)).
Proof.
apply: (alice_trace_guess_V2_negligible (Q := idealized_instance_sequence)
          (predict := fun k => fun _ => 0) _ _ idealized_asymptotic).
- exact: idealized_bob_cipher_constant.
- exact: idealized_charlie_cipher_constant.
Qed.

End idealized.

(* The Paillier reading of the corrupted-Alice bounds: one paillier_sequence
   record, and the DSDP data Alice's execution adds to it, her four weights
   and the three key seeds.  At this scheme both terms of the abstract bound
   have number-theoretic values, 1/(p k * q k) for the plaintext count and
   twice the residuosity epsilon for the assumed advantage. *)
Section paillier.
Context {R : realType}.
Variable P : paillier_sequence R.

(* The Paillier packaging at the k-th modulus, pinned once under the name
   paillier_indcpa_scheme.v exports it by. *)
Local Notation AHE k :=
  (Paillier_AHEnc (pq_gt1 (paillier_p_gt1 P k) (paillier_q_gt1 P k))).

Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).

(* Charlie's weight is invertible.  This is what makes the DSDP solution
   fiber a bijective image of the plaintext space, and so what turns the
   leaked output into the 1/(p k * q k) term of the bounds below rather than
   into a determination of Bob's input. *)
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

(* The seeds Alice's, Bob's and Charlie's private keys at k are generated
   from.  The keys enter the execution through the key material the record P
   carries, so no key of the sequence is assumed on its own. *)
Variables (sa sb sc : forall k, keygen_seedT (paillier_keygen P) k).

(* The plaintext space at k has cardinality p k * q k, the form the
   composite-modulus DSDP bounds consume. *)
Let card_plain_pq k :
  #|plain (AHE k)| = (paillier_p P k * paillier_q P k)%N.
Proof.
exact: (card_plain_paillier_pq (paillier_p_gt1 P k) (paillier_q_gt1 P k)).
Qed.

(* The inverse plaintext cardinality at the composite modulus. *)
Let inv_pq_cardE k :
  ((paillier_p P k * paillier_q P k)%N%:R : R)^-1
  = (#|plain (AHE k)|%:R : R)^-1.
Proof. by rewrite card_plain_pq. Qed.

(* The Paillier instance sequence: the Paillier scheme sequence of
   paillier_indcpa_scheme.v with Alice's weights and the three key seeds.  It
   is the sequence alice_trace_guess_V2_negligible is applied at below. *)
Definition paillier_instance_sequence : dsdp_instance_sequence R :=
  mk_dsdp_instance_sequence (paillier_scheme_sequence P)
    v1 u1 u2 u3 u3_unit sa sb sc.

(* The DSDP instance at k on the Paillier IND-CPA scheme.  Everything
   number-theoretic about the moduli beyond the fields of P stays assumed. *)
Definition paillier_instance (k : nat) : dsdp_instance :=
  sequence_instance paillier_instance_sequence k.

(* The assumption at k is the one paillier_indcpa_scheme.v derives from the
   residuosity record P carries.  The equation holds by unfolding, so the
   identification is a conversion. *)
Lemma paillier_assumption_at_dcrE k :
  sequence_assumption paillier_instance_sequence k
  = paillier_indcpa_assumption (paillier_p_gt1 P k) (paillier_q_gt1 P k)
      (paillier_dcr P k).
Proof. by []. Qed.

(* The epsilon at k is twice the residuosity epsilon, one call per hop.  It
   restates a Paillier bound in decisional composite residuosity epsilons. *)
Lemma paillier_epsilon_at_dcrE k :
  indcpa_assumption_epsilon (sequence_assumption paillier_instance_sequence k)
  = 2 * dcr_epsilon (paillier_dcr P k).
Proof. by []. Qed.

(* The two negligibility facts about the Paillier sequence, both read off P.
   The unconditional one is derived from the modulus bit length, the other
   from the asymptotic form of residuosity. *)
Definition paillier_asymptotic :
    dsdp_asymptotic paillier_instance_sequence :=
  mk_dsdp_asymptotic (paillier_scheme_sequence P)
    v1 u1 u2 u3 u3_unit sa sb sc.

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter, with the two class premises every trace bound below is
   conditional on: the class the residuosity record induces at k admits the
   two reduction adversaries the k-th predictor induces.  The restriction
   lands on those two adversaries and never on the predictor itself, which is
   what leaves the trace-decrypting predictor outside the bounds rather than
   inside them. *)
Variable predict : forall k, predictor (paillier_instance k)
    (alice_traceT (paillier_instance k)).
Arguments predict : clear implicits.

Hypothesis bob_admissible : forall k,
  indcpa_admissible (sequence_assumption paillier_instance_sequence k)
    (bob_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

Hypothesis charlie_admissible : forall k,
  indcpa_admissible (sequence_assumption paillier_instance_sequence k)
    (charlie_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

(* The trace guessing bound at k: 1/#|plain| plus 4 residuosity epsilons, two
   calls per key.  The first summand is unconditional, the second conditional
   on the residuosity record. *)
Corollary paillier_trace_guess_V2_admissible_le k :
  alice_trace_guess_V2_pr (I:=paillier_instance k) (predict k)
  <= (#|plain (AHE k)|%:R : R)^-1 + 4 * dcr_epsilon (paillier_dcr P k).
Proof.
have := alice_trace_guess_V2_admissible_le (I:=paillier_instance k)
          (bob_admissible k) (charlie_admissible k).
by rewrite paillier_epsilon_at_dcrE mulrA -(natrM R 2 2).
Qed.

(* The same bound with its unconditional summand written 1/(p k * q k), the
   plaintext count at the Paillier modulus. *)
Corollary paillier_trace_guess_V2_admissible_pq_le k :
  alice_trace_guess_V2_pr (I:=paillier_instance k) (predict k)
  <= ((paillier_p P k * paillier_q P k)%N%:R : R)^-1
     + 4 * dcr_epsilon (paillier_dcr P k).
Proof.
rewrite inv_pq_cardE; exact: paillier_trace_guess_V2_admissible_le.
Qed.

(* The constant predictor's Bob-key reduction is in the class the residuosity
   record induces.  Its epsilon is zero, so the class premises of the bounds
   above are satisfiable. *)
Lemma paillier_bob_decide_constant_admissible k :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R)
       'Z_((paillier_p P k * paillier_q P k)
           * (paillier_p P k * paillier_q P k))
       (paillier_p P k * paillier_q P k)
       (card_renc_paillier (paillier_p P k) (paillier_q P k)))
    (bob_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of paillier_bob_decide_constant_admissible, so
   that both class premises hold at the same record and the same predictor. *)
Lemma paillier_charlie_decide_constant_admissible k :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R)
       'Z_((paillier_p P k * paillier_q P k)
           * (paillier_p P k * paillier_q P k))
       (paillier_p P k * paillier_q P k)
       (card_renc_paillier (paillier_p P k) (paillier_q P k)))
    (charlie_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k.  The two negligibility
   facts of P exclude the predictor whose guessing probability is 1. *)
Corollary paillier_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption paillier_instance_sequence k)
      (bob_trace_adversary (I:=paillier_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=paillier_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF paillier_asymptotic).
Qed.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=paillier_instance_sequence) predict).

(* The k-th predictor's guessing probability at the k-th Paillier instance is
   negligible in k.  Its whole computational content is decisional composite
   residuosity along the moduli p k q k. *)
Corollary paillier_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
(* At each k the two class premises yield the bound of
   alice_trace_guess_V2_admissible_le, Pr_k <= 1/(p k * q k) + 2 * eps k,
   with eps k the advantage the residuosity record assumes.  The two fields of
   paillier_asymptotic make f_size and f_adv negligible, f_size through the
   k-bit modulus of P read as a k-bit plaintext space.  Those two are the loss
   terms the three labels of the program carry, so the terminal over the
   security parameter reads the bound off the label list and transfers
   negligibility to f_guess_V2. *)
exact: (alice_trace_guess_V2_negligible (Q := paillier_instance_sequence)
          bob_admissible charlie_admissible paillier_asymptotic).
Qed.

End paillier.

(* The Benaloh reading of the corrupted-Alice bounds: one benaloh_sequence
   record, and the DSDP data Alice's execution adds to it.  The plaintext
   count here is the block size r k and not the modulus n k, which sizes the
   ciphertext space, so the information-theoretic term reads 1/r k. *)
Section benaloh.
Context {R : realType}.
Variable B : benaloh_sequence R.

(* The Benaloh packaging at the k-th modulus and block size, pinned once under
   the name benaloh_indcpa_scheme.v exports it by. *)
Local Notation AHE k := (Benaloh_AHEnc (benaloh_n B k) (benaloh_r_gt1 B k)).

Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).

(* Charlie's weight is invertible in Z/rZ.  This is what makes the DSDP
   solution fiber a bijective image of the plaintext space, and so what turns
   the leaked output into the 1/r k term of the bounds below rather than into
   a determination of Bob's input. *)
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

(* The seeds Alice's, Bob's and Charlie's private keys at k are generated
   from.  The keys enter the execution through the key material the record B
   carries, so no key of the sequence is assumed on its own. *)
Variables (sa sb sc : forall k, keygen_seedT (benaloh_keygen B) k).

(* The plaintext space at k is Z/(r k)Z, so its cardinality is the block size
   r k.  The unconditional term below is read off r k, where n k sizes the
   ciphertext space. *)
Let card_plain_r k : #|plain (AHE k)| = benaloh_r B k.
Proof. by rewrite card_ord (Zp_cast (benaloh_r_gt1 B k)). Qed.

(* The inverse plaintext cardinality at the Benaloh block size. *)
Let inv_r_cardE k :
  ((benaloh_r B k)%:R : R)^-1 = (#|plain (AHE k)|%:R : R)^-1.
Proof. by rewrite card_plain_r. Qed.

(* The Benaloh instance sequence: the Benaloh scheme sequence of
   benaloh_indcpa_scheme.v with Alice's weights and the three key seeds.  It
   is the sequence alice_trace_guess_V2_negligible is applied at below. *)
Definition benaloh_instance_sequence : dsdp_instance_sequence R :=
  mk_dsdp_instance_sequence (benaloh_scheme_sequence B)
    v1 u1 u2 u3 u3_unit sa sb sc.

(* The DSDP instance at k on the Benaloh IND-CPA scheme.  Everything
   number-theoretic about the modulus and the block size beyond the fields of
   B stays assumed. *)
Definition benaloh_instance (k : nat) : dsdp_instance :=
  sequence_instance benaloh_instance_sequence k.

(* The assumption at k is the one benaloh_indcpa_scheme.v derives from the
   residuosity record B carries.  The equation holds by unfolding, so the
   identification is a conversion. *)
Lemma benaloh_assumption_at_residuosityE k :
  sequence_assumption benaloh_instance_sequence k
  = benaloh_indcpa_assumption (benaloh_r_gt1 B k) (benaloh_residuosity B k).
Proof. by []. Qed.

(* The epsilon at k is twice the residuosity epsilon, one call per hop.  It
   restates a Benaloh bound in r-th residuosity epsilons. *)
Lemma benaloh_epsilon_at_residuosityE k :
  indcpa_assumption_epsilon (sequence_assumption benaloh_instance_sequence k)
  = 2 * benaloh_residuosity_epsilon (benaloh_residuosity B k).
Proof. by []. Qed.

(* The two negligibility facts about the Benaloh sequence, both read off B.
   The unconditional one is derived from the block-size bit length, the other
   from the asymptotic form of residuosity. *)
Definition benaloh_asymptotic :
    dsdp_asymptotic benaloh_instance_sequence :=
  mk_dsdp_asymptotic (benaloh_scheme_sequence B)
    v1 u1 u2 u3 u3_unit sa sb sc.

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter, with the two class premises every trace bound below is
   conditional on: the class the residuosity record induces at k admits the
   two reduction adversaries the k-th predictor induces.  The restriction
   lands on those two adversaries and never on the predictor itself, which is
   what leaves the trace-decrypting predictor outside the bounds rather than
   inside them. *)
Variable predict : forall k, predictor (benaloh_instance k)
    (alice_traceT (benaloh_instance k)).
Arguments predict : clear implicits.

Hypothesis bob_admissible : forall k,
  indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
    (bob_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

Hypothesis charlie_admissible : forall k,
  indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
    (charlie_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

(* The trace guessing bound at k: 1/#|plain| plus 4 residuosity epsilons, two
   calls per key.  The first summand is unconditional, the second conditional
   on the residuosity record. *)
Corollary benaloh_trace_guess_V2_admissible_le k :
  alice_trace_guess_V2_pr (I:=benaloh_instance k) (predict k)
  <= (#|plain (AHE k)|%:R : R)^-1
     + 4 * benaloh_residuosity_epsilon (benaloh_residuosity B k).
Proof.
have := alice_trace_guess_V2_admissible_le (I:=benaloh_instance k)
          (bob_admissible k) (charlie_admissible k).
by rewrite benaloh_epsilon_at_residuosityE mulrA -(natrM R 2 2).
Qed.

(* The same bound at a block size written as a product p * q.  The hypothesis
   r k = p * q is the only link between the two readings. *)
Corollary benaloh_trace_guess_V2_admissible_pq_le k (p q : nat)
    (r_pq : benaloh_r B k = (p * q)%N) :
  alice_trace_guess_V2_pr (I:=benaloh_instance k) (predict k)
  <= ((p * q)%N%:R : R)^-1
     + 4 * benaloh_residuosity_epsilon (benaloh_residuosity B k).
Proof.
rewrite -r_pq inv_r_cardE; exact: benaloh_trace_guess_V2_admissible_le.
Qed.

(* The constant predictor's Bob-key reduction is in the class the residuosity
   record induces.  Its epsilon is zero, so the class premises of the bounds
   above are satisfiable. *)
Lemma benaloh_bob_decide_constant_admissible k :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_(benaloh_n B k) (benaloh_r B k)
       (card_renc_benaloh (benaloh_n B k)))
    (bob_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of benaloh_bob_decide_constant_admissible, so
   that both class premises hold at the same record and the same predictor. *)
Lemma benaloh_charlie_decide_constant_admissible k :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_(benaloh_n B k) (benaloh_r B k)
       (card_renc_benaloh (benaloh_n B k)))
    (charlie_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k.  The two negligibility
   facts of B exclude the predictor whose guessing probability is 1. *)
Corollary benaloh_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
      (bob_trace_adversary (I:=benaloh_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=benaloh_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF benaloh_asymptotic).
Qed.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=benaloh_instance_sequence) predict).

(* The k-th predictor's guessing probability at the k-th Benaloh instance is
   negligible in k.  Its whole computational content is r-th residuosity along
   the moduli n k. *)
Corollary benaloh_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
(* At each k the two class premises yield the bound of
   alice_trace_guess_V2_admissible_le, Pr_k <= 1/(r k) + 2 * eps k, with
   eps k the advantage the residuosity record assumes.  The two fields of
   benaloh_asymptotic make f_size and f_adv negligible, f_size through the
   k-bit block size of B read as a k-bit plaintext space.  Those two are the
   loss terms the three labels of the program carry, so the terminal over the
   security parameter reads the bound off the label list and transfers
   negligibility to f_guess_V2. *)
exact: (alice_trace_guess_V2_negligible (Q := benaloh_instance_sequence)
          bob_admissible charlie_admissible benaloh_asymptotic).
Qed.

End benaloh.
