From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba entropy.
Require Import homomorphic_encryption.
Require Import paillier_fdist_instance.
Require Import indcpa_game paillier_indcpa_scheme benaloh_indcpa_scheme.
Require Import dsdp_instance_sequence.
Require Import dsdp_setting dsdp_security.

(**md**************************************************************************)
(* # Three DSDP settings and the twenty-six statements read off at each       *)
(*                                                                            *)
(* Three values of dsdp_setting of dsdp_setting.v with their parameters fed,  *)
(* and the twenty-six fields of dsdp_security of dsdp_security.v projected at *)
(* each: Paillier, Benaloh at block size p * q, and the idealized scheme.     *)
(* Nothing is proved here.  The proofs are the theorems of the two axis       *)
(* directions, counting/dsdp_entropy.v, counting/dsdp_relay_secrecy.v and     *)
(* counting/dsdp_malicious_dotp.v on the counting side and                    *)
(* hopping/dsdp_alice_hop_secrecy.v and hopping/dsdp_alice_trace_link.v on    *)
(* the hopping side; dsdp_securityP applies them at the projections of a      *)
(* setting, and every corollary below is one projection of that value, with   *)
(* its statement written out at the instance rather than named.               *)
(*                                                                            *)
(* ## What each instance takes, and how each added premise is classified      *)
(*                                                                            *)
(* Paillier takes the plaintext modulus at k as its two factors, held as      *)
(* p_minus_2 k and q_minus_2 k so that the modulus is a double successor in   *)
(* both factors; Alice's four weights; the three private keys; the two        *)
(* encryption coins; the sequence of IND-CPA assumptions; and two             *)
(* negligibility facts.  Its added premises are prime (p k), prime (q k) and  *)
(* p k != q k.  They are fundamental to the scheme: a Paillier modulus is a   *)
(* product of two distinct primes, which paillier_indcpa_scheme.v leaves      *)
(* unimposed and which decisional composite residuosity starts from.          *)
(*                                                                            *)
(* Benaloh takes its ciphertext modulus n k in addition, and its block size   *)
(* is fixed to r k = p k * q k at two distinct primes.  That is fundamental   *)
(* to the counting axis, whose fiber count is a CRT count over the two prime  *)
(* factors, and at the same time a restriction on Benaloh, whose scheme,      *)
(* correctness and game ask only 1 < r.                                       *)
(*                                                                            *)
(* At both schemes the three private keys are assumed values: no key record   *)
(* is constructed anywhere, the divisibility and injectivity conditions a key *)
(* carries being left to the instantiation.  At both, the sequence of IND-CPA *)
(* assumptions and the two negligibility facts, one on the inverse modulus    *)
(* and one on the assumed advantage, are assumed, and every epsilon in the    *)
(* corollaries below is the advantage that sequence assumes at k.             *)
(*                                                                            *)
(* The counting side of both scheme instances is uniform_inputs at Alice's    *)
(* own hopping weights: the three inputs and the two masks are five uniform   *)
(* coordinates of the plaintext ring, and the three constant counting weights *)
(* are the weights u1, u2, u3 the scheme instance carries.  No cast is        *)
(* needed, the plaintext space of either scheme at a modulus written as       *)
(* p_minus_2 k .+2 * q_minus_2 k .+2 being the counting side's own ring       *)
(* 'Z_(p k * q k).  So the two axes read one query at every instance.         *)
(*                                                                            *)
(* The idealized instance takes no parameter: idealized_setting of            *)
(* dsdp_setting.v carries the composite-modulus idealized sequence, whose     *)
(* assumed advantage is zero at every k, so each hopping corollary there is   *)
(* its unconditional term alone.  Its query corollaries are premise-free, the *)
(* honest one at idealized_honest_query and the corrupted one at the sibling  *)
(* value corrupted_setting; its class-conditional corollaries are at          *)
(* idealized_admissible, the constant predictor, which is the only predictor  *)
(* the cipher-constant class admits.                                          *)
(*                                                                            *)
(* Three restrictions hold at all three instances, and dsdp_setting.v's       *)
(* header states them: the counting fields hold in the honest-sampling        *)
(* setting, card_plain together with sequence_size_negligible forces the      *)
(* modulus to grow superpolynomially, and the two axes share one cardinality  *)
(* and not one execution.                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*             paillier_dsdp == the Paillier instance, its parameters, its    *)
(*                              setting and its twenty-six corollaries        *)
(*          paillier_setting == the setting the Paillier parameters make      *)
(*         paillier_security == the twenty-six statements at it               *)
(*              benaloh_dsdp == the same at Benaloh with block size p * q     *)
(*           benaloh_setting, benaloh_security == its two values              *)
(*            idealized_dsdp == the same at the idealized scheme, where every *)
(*                              corollary is premise-free                     *)
(*        idealized_security == the twenty-six statements at it               *)
(* ```                                                                        *)
(*                                                                            *)
(* The twenty-six corollary stems, carried by all three sections under the    *)
(* prefixes paillier_, benaloh_ and idealized_, except that the corrupted     *)
(* query is read at corrupted_setting and so is named                         *)
(* corrupted_centropy_V2_dotp_eq0 there:                                      *)
(*                                                                            *)
(* ```                                                                        *)
(* centropy_uniform, centropy_V2_dotp_eq0, bob_privacy_V1,                    *)
(* charlie_privacy_V1, bob_privacy_V3, charlie_privacy_V2,                    *)
(* tuple_guess_V2_le, unpredictability_ge, predictor_unpredictability_ge,     *)
(* sim_advantage_le, view_guess_V2_le, centropy_V2_Sout_logm,                 *)
(* centropy_V2_all_zero_logm, trace_guess_V2_le, trace_unpredictability_ge,   *)
(* trace_sim_advantage_le, centropy_V2_trace_tupleE,                          *)
(* centropy_V2_view_tupleE, centropy_V2_trace_eq0,                            *)
(* trace_guess_V2_admissible_le, trace_guess_V2_admissible_pq_le,             *)
(* decrypt_epsilon_sum_ge, decrypt_bob_epsilon_ge,                            *)
(* decrypt_reduction_admissibleF, decrypt_guess_V2_premise_free_lt,           *)
(* trace_guess_V2_negligible                                                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(* =================================================================          *)
(* Paillier                                                                   *)
(* =================================================================          *)

Section paillier_dsdp.
Local Open Scope reals_ext_scope.
Context {R : realType}.
Local Notation Paillier_AHEnc := paillier_fdist_instance.Paillier_AHEnc.

(* The plaintext modulus at k as the two factors whose product it is, each
   held as a double successor so that the scheme's plaintext space and the
   counting side's residue ring 'Z_(p k * q k) are one type. *)
Variables p_minus_2 q_minus_2 : nat -> nat.

Let p (k : nat) : nat := (p_minus_2 k).+2.
Let q (k : nat) : nat := (q_minus_2 k).+2.

(* The two factors are distinct primes.  Added premises, fundamental to the
   scheme: a Paillier modulus is a product of two distinct primes, which
   paillier_indcpa_scheme.v leaves unimposed and which decisional composite
   residuosity starts from.  The counting axis spends them on its fiber
   count; the hopping axis needs only 1 < p k, q k, which they give. *)
Hypothesis p_prime : forall k, prime (p_minus_2 k).+2.
Hypothesis q_prime : forall k, prime (q_minus_2 k).+2.
Hypothesis pq_neq : forall k, (p_minus_2 k).+2 != (q_minus_2 k).+2.

Let p_gt1 (k : nat) : (1 < p k)%N := isT.
Let q_gt1 (k : nat) : (1 < q k)%N := isT.

Local Notation AHE k := (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k))).

(* Alice's four query weights at k, in the scheme's plaintext space, her
   weight on Charlie's input invertible.  That unit is what leaves the leaked
   output a 1/(p k * q k) residue instead of a determination of Bob's
   input. *)
Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

(* The three private keys and the two encryption coins as assumed values: no
   Paillier key is constructed anywhere, the conditions a key carries being
   left to the instantiation. *)
Variables (dk_a dk_b dk_c : forall k, priv_key (AHE k)).
Variables (rb2 rc2 : forall k, renc_paillier (p k) (q k)).

Local Notation PI :=
  (paillier_instance v1 u1 u2 u3_unit dk_a dk_b dk_c rb2 rc2).

(* The IND-CPA assumption made at the k-th Paillier instance, the section's
   only computational hypothesis: every epsilon below is the advantage it
   assumes at its own k. *)
Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (PI k)) (inst_rand_of_renc (I:=PI k)).

(* The inverse modulus falls below every inverse polynomial.  It is the
   unconditional half of the asymptotic bound, the residue the leaked output
   concedes at every k. *)
Hypothesis f_pq_negligible : negligible_fun (f_pq (R:=R) p q).

(* The assumed advantage falls below every inverse polynomial: the asymptotic
   IND-CPA reading of decisional composite residuosity. *)
Hypothesis f_adv_negligible :
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)).

Local Notation PQ :=
  (paillier_instance_sequence f_pq_negligible f_adv_negligible).

(* Two distinct primes are coprime, which is what makes the solution fiber of
   the DSDP constraint have exactly p k * q k points. *)
Let paillier_coprime_pq k : coprime (p_minus_2 k).+2 (q_minus_2 k).+2.
Proof.
rewrite prime_coprime ?p_prime // dvdn_prime2 ?p_prime ?q_prime //.
Qed.

(* The one number the two axes share: the k-th Paillier plaintext space is
   counted by the composite modulus the counting side is carried at. *)
Let paillier_card_plain k :
  #|plain (inst_AHE (sequence_instance PQ k))|
  = ((p_minus_2 k).+2 * (q_minus_2 k).+2)%N.
Proof. exact: card_plain_paillier_pq. Qed.

(* The setting those parameters make: the Paillier sequence on the hopping
   side, and on the counting side the uniform five-coordinate law at Alice's
   own weights, so that the two axes read one query at every k. *)
Definition paillier_setting : dsdp_setting R := {|
  instance_sequence := PQ ;
  dsdp_setting.p_minus_2 := p_minus_2 ;
  dsdp_setting.q_minus_2 := q_minus_2 ;
  prime_p := p_prime ;
  prime_q := q_prime ;
  coprime_pq := paillier_coprime_pq ;
  card_plain := paillier_card_plain ;
  inputs := fun k =>
    uniform_inputs (p_minus_2 k) (q_minus_2 k) (u1 k) (u2 k) (u3 k) |}.

(* The twenty-six statements at that setting, each an axis theorem applied to
   its projections by dsdp_securityP. *)
Definition paillier_security : dsdp_security paillier_setting :=
  dsdp_securityP paillier_setting.

(* Alice's uncertainty about the relay pair, given her own inputs and the
   output she computes, is exactly the logarithm of the Paillier modulus p
   k * q k. *)
Corollary paillier_centropy_uniform k
    (h : dsdp_honest_query paillier_setting k) :
  `H(VarRV paillier_setting k | CondRV paillier_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R).
Proof. exact: (centropy_uniform paillier_security h). Qed.

(* At Alice's corrupted query the output is Bob's input itself, so her whole
   dot-product view determines it. *)
Corollary paillier_centropy_V2_dotp_eq0 k
    (h : dsdp_corrupted_query paillier_setting k) :
  `H( V2 (inputs paillier_setting k) | AliceDotpView_at paillier_setting k )
    = 0.
Proof. exact: (centropy_V2_dotp_eq0 paillier_security h). Qed.

(* Bob's whole view leaves the full logarithm of the Paillier modulus p
   k * q k of uncertainty about Alice's input, and no assumption is spent. *)
Corollary paillier_bob_privacy_V1 k :
  `H(V1 (inputs paillier_setting k) | BobView_at paillier_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs paillier_setting k) | BobView_at paillier_setting k) > 0.
Proof. exact: (bob_privacy_V1 paillier_security k). Qed.

(* The same for Charlie's whole view about Alice's input. *)
Corollary paillier_charlie_privacy_V1 k :
  `H(V1 (inputs paillier_setting k) | CharlieView_at paillier_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs paillier_setting k)
        | CharlieView_at paillier_setting k) > 0.
Proof. exact: (charlie_privacy_V1 paillier_security k). Qed.

(* Bob learns nothing about Charlie's input either. *)
Corollary paillier_bob_privacy_V3 k :
  `H(V3 (inputs paillier_setting k) | BobView_at paillier_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V3 (inputs paillier_setting k) | BobView_at paillier_setting k) > 0.
Proof. exact: (bob_privacy_V3 paillier_security k). Qed.

(* And Charlie learns nothing about Bob's input, which is what makes the two
   relays curious parties rather than a coalition. *)
Corollary paillier_charlie_privacy_V2 k :
  `H(V2 (inputs paillier_setting k) | CharlieView_at paillier_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V2 (inputs paillier_setting k)
        | CharlieView_at paillier_setting k) > 0.
Proof. exact: (charlie_privacy_V2 paillier_security k). Qed.

(* A corrupted Alice guessing Bob's input from her hopping tuple: the
   unconditional residue is 1/(p k * q k) and each of the two summands after
   it is a Paillier IND-CPA advantage at one key. *)
Corollary paillier_tuple_guess_V2_le k
    (predict : predictor (AHE_at paillier_setting k)
                 (hop_tupleT_at paillier_setting k)) :
  Pr (hop_fdist_at paillier_setting k)
     [set t | (predict `o AliceRealTuple_at paillier_setting k) t
              == hop_V2_at paillier_setting k t]
  <= (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
     + indcpa_epsilon_at paillier_setting k (bob_pkey_at paillier_setting k)
         (bob_challenge_adversary_at paillier_setting k
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at paillier_setting k
         (charlie_pkey_at paillier_setting k)
         (charlie_challenge_adversary_at paillier_setting k
            (distinguisher_of_predictor predict)).
Proof. exact: (tuple_guess_V2_le paillier_security predict). Qed.

(* The same bound as a lower bound on minus the logarithm of her success
   probability, under a positive success probability. *)
Corollary paillier_unpredictability_ge k
    (predict : predictor (AHE_at paillier_setting k)
                 (hop_tupleT_at paillier_setting k)) :
  0 < Pr (hop_fdist_at paillier_setting k)
         [set t | (predict `o AliceRealTuple_at paillier_setting k) t
                  == hop_V2_at paillier_setting k t] ->
  log (#|plain (AHE_at paillier_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at paillier_setting k)|%:R
               * (bob_predictor_epsilon_at paillier_setting k predict
                  + charlie_predictor_epsilon_at paillier_setting k predict))
  <= - log (Pr (hop_fdist_at paillier_setting k)
               [set t | (predict `o AliceRealTuple_at paillier_setting k) t
                        == hop_V2_at paillier_setting k t]).
Proof. move=> hpos; exact: (unpredictability_ge paillier_security hpos). Qed.

(* The same lower bound at the named unpredictability quantity. *)
Corollary paillier_predictor_unpredictability_ge k
    (predict : predictor (AHE_at paillier_setting k)
                 (hop_tupleT_at paillier_setting k)) :
  0 < Pr (hop_fdist_at paillier_setting k)
         [set t | (predict `o AliceRealTuple_at paillier_setting k) t
                  == hop_V2_at paillier_setting k t] ->
  log (#|plain (AHE_at paillier_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at paillier_setting k)|%:R
               * (bob_predictor_epsilon_at paillier_setting k predict
                  + charlie_predictor_epsilon_at paillier_setting k predict))
  <= alice_predictor_unpredictability_at paillier_setting k predict.
Proof.
move=> hpos; exact: (predictor_unpredictability_ge paillier_security hpos).
Qed.

(* Her tuple against the simulator's law, per distinguisher, at the two hop
   advantages. *)
Corollary paillier_sim_advantage_le k
    (D : distinguisher (hop_jointT_at paillier_setting k)) :
  `| Pr (`p_ [% hop_V2_at paillier_setting k, hop_V3_at paillier_setting k,
                AliceRealTuple_at paillier_setting k]) [set x | D x]
     - Pr (alice_ideal_joint_at paillier_setting k) [set x | D x] |
  <= indcpa_epsilon_at paillier_setting k (bob_pkey_at paillier_setting k)
       (bob_challenge_adversary_at paillier_setting k D)
     + indcpa_epsilon_at paillier_setting k
         (charlie_pkey_at paillier_setting k)
         (charlie_challenge_adversary_at paillier_setting k D).
Proof. exact: (sim_advantage_le paillier_security D). Qed.

(* The tuple guessing bound carried to Alice's whole view. *)
Corollary paillier_view_guess_V2_le k
    (predict : predictor (AHE_at paillier_setting k)
                 (viewT_at paillier_setting k)) :
  Pr (hop_fdist_at paillier_setting k)
     [set t | (predict `o AliceView_at paillier_setting k) t
              == hop_V2_at paillier_setting k t]
  <= (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
     + indcpa_epsilon_at paillier_setting k (bob_pkey_at paillier_setting k)
         (bob_view_adversary_at paillier_setting k predict)
     + indcpa_epsilon_at paillier_setting k
         (charlie_pkey_at paillier_setting k)
         (charlie_view_adversary_at paillier_setting k predict).
Proof. exact: (view_guess_V2_le paillier_security predict). Qed.

(* The protocol output alone leaves Bob's input with the whole logarithm of
   the plaintext count of uncertainty. *)
Corollary paillier_centropy_V2_Sout_logm k :
  `H( hop_V2_at paillier_setting k | Sout_at paillier_setting k )
    = log (#|plain (AHE_at paillier_setting k)|%:R : R).
Proof. exact: (centropy_V2_Sout_logm paillier_security k). Qed.

(* So does the all-zero endpoint of the hop ladder, the ideal side the two
   advantages of the guessing bounds pay to reach. *)
Corollary paillier_centropy_V2_all_zero_logm k :
  `H( hop_V2_at paillier_setting k | AliceHopTuple_at paillier_setting k 2 )
    = log (#|plain (AHE_at paillier_setting k)|%:R : R).
Proof. exact: (centropy_V2_all_zero_logm paillier_security k). Qed.

(* The tuple guessing bound at Alice's executed piSMC trace. *)
Corollary paillier_trace_guess_V2_le k
    (predict : predictor (AHE_at paillier_setting k)
                 (traceT_at paillier_setting k)) :
  Pr (hop_fdist_at paillier_setting k)
     [set t | (predict `o AliceTrace_at paillier_setting k) t
              == hop_V2_at paillier_setting k t]
  <= (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
     + indcpa_epsilon_at paillier_setting k (bob_pkey_at paillier_setting k)
         (bob_trace_adversary_at (R:=R) (Q:=PQ)
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at paillier_setting k
         (charlie_pkey_at paillier_setting k)
         (charlie_trace_adversary_at (R:=R) (Q:=PQ)
            (distinguisher_of_predictor predict)).
Proof. exact: (trace_guess_V2_le paillier_security predict). Qed.

(* Its logarithmic form at the executed trace. *)
Corollary paillier_trace_unpredictability_ge k
    (predict : predictor (AHE_at paillier_setting k)
                 (traceT_at paillier_setting k)) :
  0 < Pr (hop_fdist_at paillier_setting k)
         [set t | (predict `o AliceTrace_at paillier_setting k) t
                  == hop_V2_at paillier_setting k t] ->
  log (#|plain (AHE_at paillier_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at paillier_setting k)|%:R
               * (bob_trace_predictor_epsilon_at paillier_setting k predict
                  + charlie_trace_predictor_epsilon_at paillier_setting k
                      predict))
  <= alice_trace_unpredictability_at paillier_setting k predict.
Proof.
move=> hpos; exact: (trace_unpredictability_ge paillier_security hpos).
Qed.

(* Simulation security of the executed trace, per distinguisher. *)
Corollary paillier_trace_sim_advantage_le k
    (D : distinguisher (trace_jointT_at paillier_setting k)) :
  `| Pr (`p_ [% hop_V2_at paillier_setting k, hop_V3_at paillier_setting k,
                AliceTrace_at paillier_setting k]) [set x | D x]
     - Pr (alice_trace_ideal_joint_at paillier_setting k) [set x | D x] |
  <= indcpa_epsilon_at paillier_setting k (bob_pkey_at paillier_setting k)
       (bob_trace_adversary_at (R:=R) (Q:=PQ) D)
     + indcpa_epsilon_at paillier_setting k
         (charlie_pkey_at paillier_setting k)
         (charlie_trace_adversary_at (R:=R) (Q:=PQ) D).
Proof. exact: (trace_sim_advantage_le paillier_security D). Qed.

(* Her executed trace and her hopping tuple leave the same conditional
   entropy about Bob's input. *)
Corollary paillier_centropy_V2_trace_tupleE k :
  `H( hop_V2_at paillier_setting k | AliceTrace_at paillier_setting k )
    = `H( hop_V2_at paillier_setting k
        | AliceRealTuple_at paillier_setting k ).
Proof. exact: (centropy_V2_trace_tupleE paillier_security k). Qed.

(* The same equality at her whole view. *)
Corollary paillier_centropy_V2_view_tupleE k :
  `H( hop_V2_at paillier_setting k | AliceView_at paillier_setting k )
    = `H( hop_V2_at paillier_setting k
        | AliceRealTuple_at paillier_setting k ).
Proof. exact: (centropy_V2_view_tupleE paillier_security k). Qed.

(* At the executed trace that entropy is zero: the trace carries Alice's own
   key beside the aggregate ciphertext, so she recovers Bob's input.  This
   is the leakage the class restriction answers. *)
Corollary paillier_centropy_V2_trace_eq0 k :
  `H( hop_V2_at paillier_setting k | AliceTrace_at paillier_setting k ) = 0.
Proof. exact: (centropy_V2_trace_eq0 paillier_security k). Qed.

(* Both ciphertext hops charged to the single epsilon the Paillier sequence
   assumes at k, on the two class premises the admissible-predictor record
   carries. *)
Corollary paillier_trace_guess_V2_admissible_le k
    (a : dsdp_admissible_predictor paillier_setting k) :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=PQ) (predict a)
  <= (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at paillier_setting k).
Proof. exact: (trace_guess_V2_admissible_le paillier_security a). Qed.

(* The same bound with its unconditional summand read as 1/(p k * q k), the
   counting axis's reading of the shared cardinality. *)
Corollary paillier_trace_guess_V2_admissible_pq_le k
    (a : dsdp_admissible_predictor paillier_setting k) :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=PQ) (predict a)
  <= (((p_minus_2 k).+2%:R : R) * (q_minus_2 k).+2%:R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at paillier_setting k).
Proof. exact: (trace_guess_V2_admissible_pq_le paillier_security a). Qed.

(* The decrypting predictor drives the sum of its two reduction advantages
   to at least 1 - 1/(p k * q k). *)
Corollary paillier_decrypt_epsilon_sum_ge k :
  1 - (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at paillier_setting k
       (bob_decrypt_predictor_at paillier_setting k)
     + charlie_trace_predictor_epsilon_at paillier_setting k
         (bob_decrypt_predictor_at paillier_setting k).
Proof. exact: (decrypt_epsilon_sum_ge paillier_security k). Qed.

(* The Bob-key half alone already reaches that value. *)
Corollary paillier_decrypt_bob_epsilon_ge k :
  1 - (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at paillier_setting k
       (bob_decrypt_predictor_at paillier_setting k).
Proof. exact: (decrypt_bob_epsilon_ge paillier_security k). Qed.

(* No assumption promising an epsilon below that value admits the Bob-key
   reduction, at every assumption at k rather than at the one the Paillier
   sequence makes. *)
Corollary paillier_decrypt_reduction_admissibleF k :
  forall A : indcpa_assumptionT_at paillier_setting k,
  indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at paillier_setting k)|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary_at (R:=R) (Q:=PQ)
       (distinguisher_of_predictor
          (bob_decrypt_predictor_at paillier_setting k)))
  = false.
Proof.
move=> ? heps.
exact: (decrypt_reduction_admissibleF paillier_security heps).
Qed.

(* Dropping the two class premises leaves the trace guessing bound false,
   which places its truth in the class restriction rather than in the size
   of the epsilon. *)
Corollary paillier_decrypt_guess_V2_premise_free_lt k :
  forall A : indcpa_assumptionT_at paillier_setting k,
  2 * indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at paillier_setting k)|%:R : R)^-1 ->
  (#|plain (AHE_at paillier_setting k)|%:R : R)^-1
    + 2 * indcpa_assumption_epsilon A
  < alice_trace_guess_V2_pr_at (R:=R) (Q:=PQ)
      (bob_decrypt_predictor_at paillier_setting k).
Proof.
move=> ? heps.
exact: (decrypt_guess_V2_premise_free_lt paillier_security heps).
Qed.

(* Along the Paillier sequence, an admissible predictor at every k makes the
   trace guessing probability a negligible sequence. *)
Corollary paillier_trace_guess_V2_negligible
    (adv : forall k, dsdp_admissible_predictor paillier_setting k) :
  negligible_fun
    (f_guess_V2 (R:=R) (Q:=PQ) (fun k => predict (adv k))).
Proof. exact: (trace_guess_V2_negligible paillier_security adv). Qed.
End paillier_dsdp.

(* =================================================================          *)
(* Benaloh at block size p * q                                                *)
(* =================================================================          *)

Section benaloh_dsdp.
Local Open Scope reals_ext_scope.
Context {R : realType}.

(* The Benaloh ciphertext modulus at k, which sizes the ciphertext space
   alone and is unrelated to the block size below. *)
Variable n : nat -> nat.

(* The block size at k as the two factors whose product it is, each held as a
   double successor so that the scheme's plaintext space and the counting
   side's residue ring 'Z_(p k * q k) are one type. *)
Variables p_minus_2 q_minus_2 : nat -> nat.

Let r (k : nat) : nat := ((p_minus_2 k).+2 * (q_minus_2 k).+2)%N.

(* The two factors of the block size are distinct primes.  Added premises,
   fundamental to the counting axis, whose fiber count is a CRT count over
   the two prime factors, and at the same time a restriction on Benaloh,
   whose scheme, correctness and game ask only 1 < r k. *)
Hypothesis p_prime : forall k, prime (p_minus_2 k).+2.
Hypothesis q_prime : forall k, prime (q_minus_2 k).+2.
Hypothesis pq_neq : forall k, (p_minus_2 k).+2 != (q_minus_2 k).+2.

Let r_gt1 (k : nat) : (1 < r k)%N := isT.

Local Notation AHE k := (Benaloh_AHEnc (n k) (r_gt1 k)).

(* Alice's four query weights at k, in the scheme's plaintext space, her
   weight on Charlie's input invertible.  That unit is what leaves the leaked
   output a 1/(p k * q k) residue instead of a determination of Bob's
   input. *)
Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

(* The three private keys and the two encryption coins as assumed values: no
   Benaloh key is constructed anywhere, the divisibility and injectivity
   conditions a key carries being left to the instantiation. *)
Variables (dk_a dk_b dk_c : forall k, priv_key (AHE k)).
Variables (rb2 rc2 : forall k, renc_benaloh (n k)).

Local Notation BI :=
  (benaloh_instance v1 u1 u2 u3_unit dk_a dk_b dk_c rb2 rc2).

(* The IND-CPA assumption made at the k-th Benaloh instance, the section's
   only computational hypothesis: every epsilon below is the advantage it
   assumes at its own k. *)
Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (BI k)) (inst_rand_of_renc (I:=BI k)).

(* The inverse block size falls below every inverse polynomial.  It is the
   unconditional half of the asymptotic bound, the residue the leaked output
   concedes at every k. *)
Hypothesis f_r_negligible : negligible_fun (f_r (R:=R) r).

(* The assumed advantage falls below every inverse polynomial: the asymptotic
   IND-CPA reading of r-th residuosity. *)
Hypothesis f_adv_negligible :
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)).

Local Notation BQ :=
  (benaloh_instance_sequence f_r_negligible f_adv_negligible).

(* Two distinct primes are coprime, which is what makes the solution fiber of
   the DSDP constraint have exactly p k * q k points. *)
Let benaloh_coprime_pq k : coprime (p_minus_2 k).+2 (q_minus_2 k).+2.
Proof.
rewrite prime_coprime ?p_prime // dvdn_prime2 ?p_prime ?q_prime //.
Qed.

(* The one number the two axes share: the k-th Benaloh plaintext space is the
   block, counted by the composite modulus the counting side is carried at,
   and not by the ciphertext modulus n k. *)
Let benaloh_card_plain k :
  #|plain (inst_AHE (sequence_instance BQ k))|
  = ((p_minus_2 k).+2 * (q_minus_2 k).+2)%N.
Proof. by rewrite card_ord (Zp_cast (r_gt1 k)). Qed.

(* The setting those parameters make: the Benaloh sequence at block size
   p k * q k on the hopping side, and on the counting side the uniform
   five-coordinate law at Alice's own weights, so that the two axes read one
   query at every k. *)
Definition benaloh_setting : dsdp_setting R := {|
  instance_sequence := BQ ;
  dsdp_setting.p_minus_2 := p_minus_2 ;
  dsdp_setting.q_minus_2 := q_minus_2 ;
  prime_p := p_prime ;
  prime_q := q_prime ;
  coprime_pq := benaloh_coprime_pq ;
  card_plain := benaloh_card_plain ;
  inputs := fun k =>
    uniform_inputs (p_minus_2 k) (q_minus_2 k) (u1 k) (u2 k) (u3 k) |}.

(* The twenty-six statements at that setting, each an axis theorem applied to
   its projections by dsdp_securityP. *)
Definition benaloh_security : dsdp_security benaloh_setting :=
  dsdp_securityP benaloh_setting.

(* Alice's uncertainty about the relay pair, given her own inputs and the
   output she computes, is exactly the logarithm of the Benaloh block size p
   k * q k. *)
Corollary benaloh_centropy_uniform k
    (h : dsdp_honest_query benaloh_setting k) :
  `H(VarRV benaloh_setting k | CondRV benaloh_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R).
Proof. exact: (centropy_uniform benaloh_security h). Qed.

(* At Alice's corrupted query the output is Bob's input itself, so her whole
   dot-product view determines it. *)
Corollary benaloh_centropy_V2_dotp_eq0 k
    (h : dsdp_corrupted_query benaloh_setting k) :
  `H( V2 (inputs benaloh_setting k) | AliceDotpView_at benaloh_setting k )
    = 0.
Proof. exact: (centropy_V2_dotp_eq0 benaloh_security h). Qed.

(* Bob's whole view leaves the full logarithm of the Benaloh block size p
   k * q k of uncertainty about Alice's input, and no assumption is spent. *)
Corollary benaloh_bob_privacy_V1 k :
  `H(V1 (inputs benaloh_setting k) | BobView_at benaloh_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs benaloh_setting k) | BobView_at benaloh_setting k) > 0.
Proof. exact: (bob_privacy_V1 benaloh_security k). Qed.

(* The same for Charlie's whole view about Alice's input. *)
Corollary benaloh_charlie_privacy_V1 k :
  `H(V1 (inputs benaloh_setting k) | CharlieView_at benaloh_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs benaloh_setting k)
        | CharlieView_at benaloh_setting k) > 0.
Proof. exact: (charlie_privacy_V1 benaloh_security k). Qed.

(* Bob learns nothing about Charlie's input either. *)
Corollary benaloh_bob_privacy_V3 k :
  `H(V3 (inputs benaloh_setting k) | BobView_at benaloh_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V3 (inputs benaloh_setting k) | BobView_at benaloh_setting k) > 0.
Proof. exact: (bob_privacy_V3 benaloh_security k). Qed.

(* And Charlie learns nothing about Bob's input, which is what makes the two
   relays curious parties rather than a coalition. *)
Corollary benaloh_charlie_privacy_V2 k :
  `H(V2 (inputs benaloh_setting k) | CharlieView_at benaloh_setting k)
    = log ((((p_minus_2 k).+2 * (q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V2 (inputs benaloh_setting k)
        | CharlieView_at benaloh_setting k) > 0.
Proof. exact: (charlie_privacy_V2 benaloh_security k). Qed.

(* A corrupted Alice guessing Bob's input from her hopping tuple: the
   unconditional residue is 1/(p k * q k), the block size and each of the
   two summands after it is a Benaloh IND-CPA advantage at one key. *)
Corollary benaloh_tuple_guess_V2_le k
    (predict : predictor (AHE_at benaloh_setting k)
                 (hop_tupleT_at benaloh_setting k)) :
  Pr (hop_fdist_at benaloh_setting k)
     [set t | (predict `o AliceRealTuple_at benaloh_setting k) t
              == hop_V2_at benaloh_setting k t]
  <= (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
     + indcpa_epsilon_at benaloh_setting k (bob_pkey_at benaloh_setting k)
         (bob_challenge_adversary_at benaloh_setting k
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at benaloh_setting k
         (charlie_pkey_at benaloh_setting k)
         (charlie_challenge_adversary_at benaloh_setting k
            (distinguisher_of_predictor predict)).
Proof. exact: (tuple_guess_V2_le benaloh_security predict). Qed.

(* The same bound as a lower bound on minus the logarithm of her success
   probability, under a positive success probability. *)
Corollary benaloh_unpredictability_ge k
    (predict : predictor (AHE_at benaloh_setting k)
                 (hop_tupleT_at benaloh_setting k)) :
  0 < Pr (hop_fdist_at benaloh_setting k)
         [set t | (predict `o AliceRealTuple_at benaloh_setting k) t
                  == hop_V2_at benaloh_setting k t] ->
  log (#|plain (AHE_at benaloh_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at benaloh_setting k)|%:R
               * (bob_predictor_epsilon_at benaloh_setting k predict
                  + charlie_predictor_epsilon_at benaloh_setting k predict))
  <= - log (Pr (hop_fdist_at benaloh_setting k)
               [set t | (predict `o AliceRealTuple_at benaloh_setting k) t
                        == hop_V2_at benaloh_setting k t]).
Proof. move=> hpos; exact: (unpredictability_ge benaloh_security hpos). Qed.

(* The same lower bound at the named unpredictability quantity. *)
Corollary benaloh_predictor_unpredictability_ge k
    (predict : predictor (AHE_at benaloh_setting k)
                 (hop_tupleT_at benaloh_setting k)) :
  0 < Pr (hop_fdist_at benaloh_setting k)
         [set t | (predict `o AliceRealTuple_at benaloh_setting k) t
                  == hop_V2_at benaloh_setting k t] ->
  log (#|plain (AHE_at benaloh_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at benaloh_setting k)|%:R
               * (bob_predictor_epsilon_at benaloh_setting k predict
                  + charlie_predictor_epsilon_at benaloh_setting k predict))
  <= alice_predictor_unpredictability_at benaloh_setting k predict.
Proof.
move=> hpos; exact: (predictor_unpredictability_ge benaloh_security hpos).
Qed.

(* Her tuple against the simulator's law, per distinguisher, at the two hop
   advantages. *)
Corollary benaloh_sim_advantage_le k
    (D : distinguisher (hop_jointT_at benaloh_setting k)) :
  `| Pr (`p_ [% hop_V2_at benaloh_setting k, hop_V3_at benaloh_setting k,
                AliceRealTuple_at benaloh_setting k]) [set x | D x]
     - Pr (alice_ideal_joint_at benaloh_setting k) [set x | D x] |
  <= indcpa_epsilon_at benaloh_setting k (bob_pkey_at benaloh_setting k)
       (bob_challenge_adversary_at benaloh_setting k D)
     + indcpa_epsilon_at benaloh_setting k
         (charlie_pkey_at benaloh_setting k)
         (charlie_challenge_adversary_at benaloh_setting k D).
Proof. exact: (sim_advantage_le benaloh_security D). Qed.

(* The tuple guessing bound carried to Alice's whole view. *)
Corollary benaloh_view_guess_V2_le k
    (predict : predictor (AHE_at benaloh_setting k)
                 (viewT_at benaloh_setting k)) :
  Pr (hop_fdist_at benaloh_setting k)
     [set t | (predict `o AliceView_at benaloh_setting k) t
              == hop_V2_at benaloh_setting k t]
  <= (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
     + indcpa_epsilon_at benaloh_setting k (bob_pkey_at benaloh_setting k)
         (bob_view_adversary_at benaloh_setting k predict)
     + indcpa_epsilon_at benaloh_setting k
         (charlie_pkey_at benaloh_setting k)
         (charlie_view_adversary_at benaloh_setting k predict).
Proof. exact: (view_guess_V2_le benaloh_security predict). Qed.

(* The protocol output alone leaves Bob's input with the whole logarithm of
   the plaintext count of uncertainty. *)
Corollary benaloh_centropy_V2_Sout_logm k :
  `H( hop_V2_at benaloh_setting k | Sout_at benaloh_setting k )
    = log (#|plain (AHE_at benaloh_setting k)|%:R : R).
Proof. exact: (centropy_V2_Sout_logm benaloh_security k). Qed.

(* So does the all-zero endpoint of the hop ladder, the ideal side the two
   advantages of the guessing bounds pay to reach. *)
Corollary benaloh_centropy_V2_all_zero_logm k :
  `H( hop_V2_at benaloh_setting k | AliceHopTuple_at benaloh_setting k 2 )
    = log (#|plain (AHE_at benaloh_setting k)|%:R : R).
Proof. exact: (centropy_V2_all_zero_logm benaloh_security k). Qed.

(* The tuple guessing bound at Alice's executed piSMC trace. *)
Corollary benaloh_trace_guess_V2_le k
    (predict : predictor (AHE_at benaloh_setting k)
                 (traceT_at benaloh_setting k)) :
  Pr (hop_fdist_at benaloh_setting k)
     [set t | (predict `o AliceTrace_at benaloh_setting k) t
              == hop_V2_at benaloh_setting k t]
  <= (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
     + indcpa_epsilon_at benaloh_setting k (bob_pkey_at benaloh_setting k)
         (bob_trace_adversary_at (R:=R) (Q:=BQ)
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at benaloh_setting k
         (charlie_pkey_at benaloh_setting k)
         (charlie_trace_adversary_at (R:=R) (Q:=BQ)
            (distinguisher_of_predictor predict)).
Proof. exact: (trace_guess_V2_le benaloh_security predict). Qed.

(* Its logarithmic form at the executed trace. *)
Corollary benaloh_trace_unpredictability_ge k
    (predict : predictor (AHE_at benaloh_setting k)
                 (traceT_at benaloh_setting k)) :
  0 < Pr (hop_fdist_at benaloh_setting k)
         [set t | (predict `o AliceTrace_at benaloh_setting k) t
                  == hop_V2_at benaloh_setting k t] ->
  log (#|plain (AHE_at benaloh_setting k)|%:R : R)
    - log (1 + #|plain (AHE_at benaloh_setting k)|%:R
               * (bob_trace_predictor_epsilon_at benaloh_setting k predict
                  + charlie_trace_predictor_epsilon_at benaloh_setting k
                      predict))
  <= alice_trace_unpredictability_at benaloh_setting k predict.
Proof.
move=> hpos; exact: (trace_unpredictability_ge benaloh_security hpos).
Qed.

(* Simulation security of the executed trace, per distinguisher. *)
Corollary benaloh_trace_sim_advantage_le k
    (D : distinguisher (trace_jointT_at benaloh_setting k)) :
  `| Pr (`p_ [% hop_V2_at benaloh_setting k, hop_V3_at benaloh_setting k,
                AliceTrace_at benaloh_setting k]) [set x | D x]
     - Pr (alice_trace_ideal_joint_at benaloh_setting k) [set x | D x] |
  <= indcpa_epsilon_at benaloh_setting k (bob_pkey_at benaloh_setting k)
       (bob_trace_adversary_at (R:=R) (Q:=BQ) D)
     + indcpa_epsilon_at benaloh_setting k
         (charlie_pkey_at benaloh_setting k)
         (charlie_trace_adversary_at (R:=R) (Q:=BQ) D).
Proof. exact: (trace_sim_advantage_le benaloh_security D). Qed.

(* Her executed trace and her hopping tuple leave the same conditional
   entropy about Bob's input. *)
Corollary benaloh_centropy_V2_trace_tupleE k :
  `H( hop_V2_at benaloh_setting k | AliceTrace_at benaloh_setting k )
    = `H( hop_V2_at benaloh_setting k
        | AliceRealTuple_at benaloh_setting k ).
Proof. exact: (centropy_V2_trace_tupleE benaloh_security k). Qed.

(* The same equality at her whole view. *)
Corollary benaloh_centropy_V2_view_tupleE k :
  `H( hop_V2_at benaloh_setting k | AliceView_at benaloh_setting k )
    = `H( hop_V2_at benaloh_setting k
        | AliceRealTuple_at benaloh_setting k ).
Proof. exact: (centropy_V2_view_tupleE benaloh_security k). Qed.

(* At the executed trace that entropy is zero: the trace carries Alice's own
   key beside the aggregate ciphertext, so she recovers Bob's input.  This
   is the leakage the class restriction answers. *)
Corollary benaloh_centropy_V2_trace_eq0 k :
  `H( hop_V2_at benaloh_setting k | AliceTrace_at benaloh_setting k ) = 0.
Proof. exact: (centropy_V2_trace_eq0 benaloh_security k). Qed.

(* Both ciphertext hops charged to the single epsilon the Benaloh sequence
   assumes at k, on the two class premises the admissible-predictor record
   carries. *)
Corollary benaloh_trace_guess_V2_admissible_le k
    (a : dsdp_admissible_predictor benaloh_setting k) :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=BQ) (predict a)
  <= (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at benaloh_setting k).
Proof. exact: (trace_guess_V2_admissible_le benaloh_security a). Qed.

(* The same bound with its unconditional summand read as 1/(p k * q k), the
   block size, the counting axis's reading of the shared cardinality. *)
Corollary benaloh_trace_guess_V2_admissible_pq_le k
    (a : dsdp_admissible_predictor benaloh_setting k) :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=BQ) (predict a)
  <= (((p_minus_2 k).+2%:R : R) * (q_minus_2 k).+2%:R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at benaloh_setting k).
Proof. exact: (trace_guess_V2_admissible_pq_le benaloh_security a). Qed.

(* The decrypting predictor drives the sum of its two reduction advantages
   to at least 1 - 1/(p k * q k), the block size. *)
Corollary benaloh_decrypt_epsilon_sum_ge k :
  1 - (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at benaloh_setting k
       (bob_decrypt_predictor_at benaloh_setting k)
     + charlie_trace_predictor_epsilon_at benaloh_setting k
         (bob_decrypt_predictor_at benaloh_setting k).
Proof. exact: (decrypt_epsilon_sum_ge benaloh_security k). Qed.

(* The Bob-key half alone already reaches that value. *)
Corollary benaloh_decrypt_bob_epsilon_ge k :
  1 - (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at benaloh_setting k
       (bob_decrypt_predictor_at benaloh_setting k).
Proof. exact: (decrypt_bob_epsilon_ge benaloh_security k). Qed.

(* No assumption promising an epsilon below that value admits the Bob-key
   reduction, at every assumption at k rather than at the one the Benaloh
   sequence makes. *)
Corollary benaloh_decrypt_reduction_admissibleF k :
  forall A : indcpa_assumptionT_at benaloh_setting k,
  indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary_at (R:=R) (Q:=BQ)
       (distinguisher_of_predictor
          (bob_decrypt_predictor_at benaloh_setting k)))
  = false.
Proof.
move=> ? heps.
exact: (decrypt_reduction_admissibleF benaloh_security heps).
Qed.

(* Dropping the two class premises leaves the trace guessing bound false,
   which places its truth in the class restriction rather than in the size
   of the epsilon. *)
Corollary benaloh_decrypt_guess_V2_premise_free_lt k :
  forall A : indcpa_assumptionT_at benaloh_setting k,
  2 * indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1 ->
  (#|plain (AHE_at benaloh_setting k)|%:R : R)^-1
    + 2 * indcpa_assumption_epsilon A
  < alice_trace_guess_V2_pr_at (R:=R) (Q:=BQ)
      (bob_decrypt_predictor_at benaloh_setting k).
Proof.
move=> ? heps.
exact: (decrypt_guess_V2_premise_free_lt benaloh_security heps).
Qed.

(* Along the Benaloh sequence, an admissible predictor at every k makes the
   trace guessing probability a negligible sequence. *)
Corollary benaloh_trace_guess_V2_negligible
    (adv : forall k, dsdp_admissible_predictor benaloh_setting k) :
  negligible_fun
    (f_guess_V2 (R:=R) (Q:=BQ) (fun k => predict (adv k))).
Proof. exact: (trace_guess_V2_negligible benaloh_security adv). Qed.
End benaloh_dsdp.

(* =================================================================          *)
(* The idealized scheme, where every corollary is premise-free                *)
(* =================================================================          *)

Section idealized_dsdp.
Local Open Scope reals_ext_scope.
Context {R : realType}.

(* The setting of dsdp_setting.v at Alice's honest query e_3, and its sibling
   at her corrupted query e_1.  Both carry the composite-modulus idealized
   sequence, whose assumed advantage is zero at every k, so every hopping
   bound below is its unconditional term alone. *)
Local Notation IS := (idealized_setting : dsdp_setting R).
Local Notation CS := (corrupted_setting : dsdp_setting R).

(* The twenty-six statements at a setting that takes no parameter, so every
   corollary below is premise-free. *)
Definition idealized_security : dsdp_security IS := dsdp_securityP IS.

(* Alice's honest query holds at the idealized setting at every k, her
   weight on Charlie's input being the unit residue, so the equality is
   stated with no premise. *)
Corollary idealized_centropy_uniform k :
  `H(VarRV IS k | CondRV IS k)
    = log ((((idealized_p_minus_2 k).+2
             * (idealized_q_minus_2 k).+2)%N)%:R : R).
Proof.
exact: (centropy_uniform idealized_security (idealized_honest_query k)).
Qed.

(* Read at corrupted_setting, the sibling value carrying Alice's corrupted
   query e_1, since no value of dsdp_random_inputs satisfies both queries at
   one k. *)
Corollary corrupted_centropy_V2_dotp_eq0 k :
  `H( V2 (inputs CS k) | AliceDotpView_at CS k ) = 0.
Proof.
exact: (centropy_V2_dotp_eq0 (dsdp_securityP CS) (corrupted_query k)).
Qed.

(* Bob's whole view leaves the full logarithm of the composite modulus of
   the idealized sequence of uncertainty about Alice's input, and no
   assumption is spent. *)
Corollary idealized_bob_privacy_V1 k :
  `H(V1 (inputs IS k) | BobView_at IS k)
    = log ((((idealized_p_minus_2 k).+2
             * (idealized_q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs IS k) | BobView_at IS k) > 0.
Proof. exact: (bob_privacy_V1 idealized_security k). Qed.

(* The same for Charlie's whole view about Alice's input. *)
Corollary idealized_charlie_privacy_V1 k :
  `H(V1 (inputs IS k) | CharlieView_at IS k)
    = log ((((idealized_p_minus_2 k).+2
             * (idealized_q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V1 (inputs IS k)
        | CharlieView_at IS k) > 0.
Proof. exact: (charlie_privacy_V1 idealized_security k). Qed.

(* Bob learns nothing about Charlie's input either. *)
Corollary idealized_bob_privacy_V3 k :
  `H(V3 (inputs IS k) | BobView_at IS k)
    = log ((((idealized_p_minus_2 k).+2
             * (idealized_q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V3 (inputs IS k) | BobView_at IS k) > 0.
Proof. exact: (bob_privacy_V3 idealized_security k). Qed.

(* And Charlie learns nothing about Bob's input, which is what makes the two
   relays curious parties rather than a coalition. *)
Corollary idealized_charlie_privacy_V2 k :
  `H(V2 (inputs IS k) | CharlieView_at IS k)
    = log ((((idealized_p_minus_2 k).+2
             * (idealized_q_minus_2 k).+2)%N)%:R : R)
  /\ `H(V2 (inputs IS k)
        | CharlieView_at IS k) > 0.
Proof. exact: (charlie_privacy_V2 idealized_security k). Qed.

(* A corrupted Alice guessing Bob's input from her hopping tuple: the
   unconditional residue is 1/(p k * q k) and each of the two summands after
   it is an advantage the idealized sequence assumes to be zero at one key. *)
Corollary idealized_tuple_guess_V2_le k
    (predict : predictor (AHE_at IS k)
                 (hop_tupleT_at IS k)) :
  Pr (hop_fdist_at IS k)
     [set t | (predict `o AliceRealTuple_at IS k) t
              == hop_V2_at IS k t]
  <= (#|plain (AHE_at IS k)|%:R : R)^-1
     + indcpa_epsilon_at IS k (bob_pkey_at IS k)
         (bob_challenge_adversary_at IS k
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at IS k
         (charlie_pkey_at IS k)
         (charlie_challenge_adversary_at IS k
            (distinguisher_of_predictor predict)).
Proof. exact: (tuple_guess_V2_le idealized_security predict). Qed.

(* The same bound as a lower bound on minus the logarithm of her success
   probability, under a positive success probability. *)
Corollary idealized_unpredictability_ge k
    (predict : predictor (AHE_at IS k)
                 (hop_tupleT_at IS k)) :
  0 < Pr (hop_fdist_at IS k)
         [set t | (predict `o AliceRealTuple_at IS k) t
                  == hop_V2_at IS k t] ->
  log (#|plain (AHE_at IS k)|%:R : R)
    - log (1 + #|plain (AHE_at IS k)|%:R
               * (bob_predictor_epsilon_at IS k predict
                  + charlie_predictor_epsilon_at IS k predict))
  <= - log (Pr (hop_fdist_at IS k)
               [set t | (predict `o AliceRealTuple_at IS k) t
                        == hop_V2_at IS k t]).
Proof. move=> hpos; exact: (unpredictability_ge idealized_security hpos). Qed.

(* The same lower bound at the named unpredictability quantity. *)
Corollary idealized_predictor_unpredictability_ge k
    (predict : predictor (AHE_at IS k)
                 (hop_tupleT_at IS k)) :
  0 < Pr (hop_fdist_at IS k)
         [set t | (predict `o AliceRealTuple_at IS k) t
                  == hop_V2_at IS k t] ->
  log (#|plain (AHE_at IS k)|%:R : R)
    - log (1 + #|plain (AHE_at IS k)|%:R
               * (bob_predictor_epsilon_at IS k predict
                  + charlie_predictor_epsilon_at IS k predict))
  <= alice_predictor_unpredictability_at IS k predict.
Proof.
move=> hpos; exact: (predictor_unpredictability_ge idealized_security hpos).
Qed.

(* Her tuple against the simulator's law, per distinguisher, at the two hop
   advantages. *)
Corollary idealized_sim_advantage_le k
    (D : distinguisher (hop_jointT_at IS k)) :
  `| Pr (`p_ [% hop_V2_at IS k, hop_V3_at IS k,
                AliceRealTuple_at IS k]) [set x | D x]
     - Pr (alice_ideal_joint_at IS k) [set x | D x] |
  <= indcpa_epsilon_at IS k (bob_pkey_at IS k)
       (bob_challenge_adversary_at IS k D)
     + indcpa_epsilon_at IS k
         (charlie_pkey_at IS k)
         (charlie_challenge_adversary_at IS k D).
Proof. exact: (sim_advantage_le idealized_security D). Qed.

(* The tuple guessing bound carried to Alice's whole view. *)
Corollary idealized_view_guess_V2_le k
    (predict : predictor (AHE_at IS k)
                 (viewT_at IS k)) :
  Pr (hop_fdist_at IS k)
     [set t | (predict `o AliceView_at IS k) t
              == hop_V2_at IS k t]
  <= (#|plain (AHE_at IS k)|%:R : R)^-1
     + indcpa_epsilon_at IS k (bob_pkey_at IS k)
         (bob_view_adversary_at IS k predict)
     + indcpa_epsilon_at IS k
         (charlie_pkey_at IS k)
         (charlie_view_adversary_at IS k predict).
Proof. exact: (view_guess_V2_le idealized_security predict). Qed.

(* The protocol output alone leaves Bob's input with the whole logarithm of
   the plaintext count of uncertainty. *)
Corollary idealized_centropy_V2_Sout_logm k :
  `H( hop_V2_at IS k | Sout_at IS k )
    = log (#|plain (AHE_at IS k)|%:R : R).
Proof. exact: (centropy_V2_Sout_logm idealized_security k). Qed.

(* So does the all-zero endpoint of the hop ladder, the ideal side the two
   advantages of the guessing bounds pay to reach. *)
Corollary idealized_centropy_V2_all_zero_logm k :
  `H( hop_V2_at IS k | AliceHopTuple_at IS k 2 )
    = log (#|plain (AHE_at IS k)|%:R : R).
Proof. exact: (centropy_V2_all_zero_logm idealized_security k). Qed.

(* The tuple guessing bound at Alice's executed piSMC trace. *)
Corollary idealized_trace_guess_V2_le k
    (predict : predictor (AHE_at IS k)
                 (traceT_at IS k)) :
  Pr (hop_fdist_at IS k)
     [set t | (predict `o AliceTrace_at IS k) t
              == hop_V2_at IS k t]
  <= (#|plain (AHE_at IS k)|%:R : R)^-1
     + indcpa_epsilon_at IS k (bob_pkey_at IS k)
         (bob_trace_adversary_at (R:=R) (Q:=idealized_pq_sequence)
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at IS k
         (charlie_pkey_at IS k)
         (charlie_trace_adversary_at (R:=R) (Q:=idealized_pq_sequence)
            (distinguisher_of_predictor predict)).
Proof. exact: (trace_guess_V2_le idealized_security predict). Qed.

(* Its logarithmic form at the executed trace. *)
Corollary idealized_trace_unpredictability_ge k
    (predict : predictor (AHE_at IS k)
                 (traceT_at IS k)) :
  0 < Pr (hop_fdist_at IS k)
         [set t | (predict `o AliceTrace_at IS k) t
                  == hop_V2_at IS k t] ->
  log (#|plain (AHE_at IS k)|%:R : R)
    - log (1 + #|plain (AHE_at IS k)|%:R
               * (bob_trace_predictor_epsilon_at IS k predict
                  + charlie_trace_predictor_epsilon_at IS k
                      predict))
  <= alice_trace_unpredictability_at IS k predict.
Proof.
move=> hpos; exact: (trace_unpredictability_ge idealized_security hpos).
Qed.

(* Simulation security of the executed trace, per distinguisher. *)
Corollary idealized_trace_sim_advantage_le k
    (D : distinguisher (trace_jointT_at IS k)) :
  `| Pr (`p_ [% hop_V2_at IS k, hop_V3_at IS k,
                AliceTrace_at IS k]) [set x | D x]
     - Pr (alice_trace_ideal_joint_at IS k) [set x | D x] |
  <= indcpa_epsilon_at IS k (bob_pkey_at IS k)
       (bob_trace_adversary_at (R:=R) (Q:=idealized_pq_sequence) D)
     + indcpa_epsilon_at IS k
         (charlie_pkey_at IS k)
         (charlie_trace_adversary_at (R:=R) (Q:=idealized_pq_sequence) D).
Proof. exact: (trace_sim_advantage_le idealized_security D). Qed.

(* Her executed trace and her hopping tuple leave the same conditional
   entropy about Bob's input. *)
Corollary idealized_centropy_V2_trace_tupleE k :
  `H( hop_V2_at IS k | AliceTrace_at IS k )
    = `H( hop_V2_at IS k
        | AliceRealTuple_at IS k ).
Proof. exact: (centropy_V2_trace_tupleE idealized_security k). Qed.

(* The same equality at her whole view. *)
Corollary idealized_centropy_V2_view_tupleE k :
  `H( hop_V2_at IS k | AliceView_at IS k )
    = `H( hop_V2_at IS k
        | AliceRealTuple_at IS k ).
Proof. exact: (centropy_V2_view_tupleE idealized_security k). Qed.

(* At the executed trace that entropy is zero: the trace carries Alice's own
   key beside the aggregate ciphertext, so she recovers Bob's input.  This
   is the leakage the class restriction answers. *)
Corollary idealized_centropy_V2_trace_eq0 k :
  `H( hop_V2_at IS k | AliceTrace_at IS k ) = 0.
Proof. exact: (centropy_V2_trace_eq0 idealized_security k). Qed.

(* At idealized_admissible, the constant predictor, whose two reduction
   adversaries the cipher-constant class admits; the idealized sequence's
   epsilon is zero, so the bound is its residue alone. *)
Corollary idealized_trace_guess_V2_admissible_le k :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=idealized_pq_sequence)
    (predict (idealized_admissible k))
  <= (#|plain (AHE_at IS k)|%:R : R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at IS k).
Proof.
exact: (trace_guess_V2_admissible_le idealized_security
          (idealized_admissible k)).
Qed.

(* The same at the composite modulus, again at the constant predictor. *)
Corollary idealized_trace_guess_V2_admissible_pq_le k :
  alice_trace_guess_V2_pr_at (R:=R) (Q:=idealized_pq_sequence)
    (predict (idealized_admissible k))
  <= (((idealized_p_minus_2 k).+2%:R : R)
      * (idealized_q_minus_2 k).+2%:R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at IS k).
Proof.
exact: (trace_guess_V2_admissible_pq_le idealized_security
          (idealized_admissible k)).
Qed.

(* The decrypting predictor drives the sum of its two reduction advantages
   to at least 1 - 1/(p k * q k). *)
Corollary idealized_decrypt_epsilon_sum_ge k :
  1 - (#|plain (AHE_at IS k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at IS k
       (bob_decrypt_predictor_at IS k)
     + charlie_trace_predictor_epsilon_at IS k
         (bob_decrypt_predictor_at IS k).
Proof. exact: (decrypt_epsilon_sum_ge idealized_security k). Qed.

(* The Bob-key half alone already reaches that value. *)
Corollary idealized_decrypt_bob_epsilon_ge k :
  1 - (#|plain (AHE_at IS k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at IS k
       (bob_decrypt_predictor_at IS k).
Proof. exact: (decrypt_bob_epsilon_ge idealized_security k). Qed.

(* No assumption promising an epsilon below that value admits the Bob-key
   reduction, at every assumption at k rather than at the one the idealized
   sequence makes. *)
Corollary idealized_decrypt_reduction_admissibleF k :
  forall A : indcpa_assumptionT_at IS k,
  indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at IS k)|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary_at (R:=R) (Q:=idealized_pq_sequence)
       (distinguisher_of_predictor
          (bob_decrypt_predictor_at IS k)))
  = false.
Proof.
move=> ? heps.
exact: (decrypt_reduction_admissibleF idealized_security heps).
Qed.

(* Dropping the two class premises leaves the trace guessing bound false,
   which places its truth in the class restriction rather than in the size
   of the epsilon. *)
Corollary idealized_decrypt_guess_V2_premise_free_lt k :
  forall A : indcpa_assumptionT_at IS k,
  2 * indcpa_assumption_epsilon A
    < 1 - (#|plain (AHE_at IS k)|%:R : R)^-1 ->
  (#|plain (AHE_at IS k)|%:R : R)^-1
    + 2 * indcpa_assumption_epsilon A
  < alice_trace_guess_V2_pr_at (R:=R) (Q:=idealized_pq_sequence)
      (bob_decrypt_predictor_at IS k).
Proof.
move=> ? heps.
exact: (decrypt_guess_V2_premise_free_lt idealized_security heps).
Qed.

(* At the constant predictor, whose class premises are theorems here, so the
   negligible sequence is asserted with nothing assumed. *)
Corollary idealized_trace_guess_V2_negligible :
  negligible_fun
    (f_guess_V2 (R:=R) (Q:=idealized_pq_sequence)
       (fun k => predict (idealized_admissible k))).
Proof.
exact: (trace_guess_V2_negligible idealized_security idealized_admissible).
Qed.
End idealized_dsdp.
