From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid spp_proba.
Require Import extra_proba extra_algebra extra_entropy.
Require Import homomorphic_encryption.
Require Import dsdp_entropy dsdp_relay_secrecy dsdp_malicious_dotp.
Require Import indcpa_game.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.
Require Import dsdp_instance_sequence.
Require Import dsdp_setting.

(**md**************************************************************************)
(* # What a DSDP setting proves                                               *)
(*                                                                            *)
(* A value of dsdp_security X is the twenty-six statements below at the       *)
(* setting X, with one proof each, and dsdp_securityP X is the value every    *)
(* setting has, after du2002's pair scalar_product_is_leakage_free /          *)
(* scalar_product_is_leakage_freeP.  What separates this file from            *)
(* dsdp_setting.v is that every declaration here names an adversary or states *)
(* a bound, while everything that exists before an adversary is named lives   *)
(* there.                                                                     *)
(*                                                                            *)
(* The record does not say that X is secure in any wider sense.               *)
(*                                                                            *)
(* Eight of the twenty-six are leakage or obstruction results rather than     *)
(* secrecy, and each is read at the conditioner that makes it one.            *)
(* centropy_V2_dotp_eq0 and centropy_V2_trace_eq0 are zero conditional        *)
(* entropies: Alice's corrupted-query view and her executed trace each        *)
(* determine Bob's input.  centropy_V2_trace_tupleE and                       *)
(* centropy_V2_view_tupleE carry that zero to her hopping tuple and to her    *)
(* whole view.  The four decrypt_ fields show that the class restriction the  *)
(* trace bounds are conditional on cannot be widened.  Next to                *)
(* centropy_V2_all_zero_logm, which is log #|plain|, this reads as a          *)
(* contradiction unless the conditioner of each is named: the all-zero        *)
(* endpoint of the hop ladder on one side, the executed trace on the other.   *)
(*                                                                            *)
(* Bob and Charlie appear only as unconditional counting adversaries, whose   *)
(* views are plaintexts and abstract ciphertexts; the computational axis is   *)
(* Alice's alone.                                                             *)
(*                                                                            *)
(* Every epsilon is single-query and per-distinguisher, as indcpa_game.v      *)
(* defines it, so the record prices one execution against one named           *)
(* adversary.                                                                 *)
(*                                                                            *)
(* Three restrictions come from the setting and are stated in dsdp_setting.v: *)
(* the counting fields hold in the honest-sampling setting, the two axes      *)
(* share one cardinality and not one execution, and card_plain together with  *)
(* sequence_size_negligible forces the modulus to grow superpolynomially.     *)
(*                                                                            *)
(* At a Benaloh instance the fields prime_p, prime_q and coprime_pq factor    *)
(* the block size rather than a hardness modulus; they are there for the      *)
(* fiber count of the counting axis only.                                     *)
(*                                                                            *)
(* Thirteen field names coincide with the axis theorem the field cites:       *)
(* bob_privacy_V1, charlie_privacy_V1, bob_privacy_V3, charlie_privacy_V2,    *)
(* centropy_V2_Sout_logm, centropy_V2_all_zero_logm,                          *)
(* centropy_V2_trace_tupleE, centropy_V2_view_tupleE, centropy_V2_trace_eq0,  *)
(* decrypt_epsilon_sum_ge, decrypt_bob_epsilon_ge,                            *)
(* decrypt_reduction_admissibleF and decrypt_guess_V2_premise_free_lt.  The   *)
(* field wins the short name, so inside this file the axis theorems are cited *)
(* qualified, as dsdp_alice_trace_link.centropy_V2_trace_eq0; downstream of   *)
(* this file the bare name is the field.                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*          indcpa_epsilon_at == the IND-CPA advantage of one adversary at    *)
(*                              one public key of the k-th instance           *)
(* bob_challenge_adversary_at, charlie_challenge_adversary_at == the two      *)
(*                              reduction adversaries a tuple distinguisher   *)
(*                              induces                                       *)
(* bob_view_adversary_at, charlie_view_adversary_at == the two a view         *)
(*                              predictor induces                             *)
(* bob_predictor_epsilon_at, charlie_predictor_epsilon_at == the two          *)
(*                              advantages a tuple predictor buys             *)
(* alice_predictor_unpredictability_at == the unpredictability those two      *)
(*                              advantages correct                            *)
(* bob_trace_predictor_epsilon_at, charlie_trace_predictor_epsilon_at == the  *)
(*                              two advantages a trace predictor buys         *)
(* alice_trace_unpredictability_at == the unpredictability at the executed    *)
(*                              trace                                         *)
(*   bob_decrypt_predictor_at == the trace predictor that decrypts with       *)
(*                              Alice's key                                   *)
(* dsdp_admissible_predictor == a trace predictor whose two reduction         *)
(*                              adversaries the sequence's assumption admits  *)
(*                    predict == that predictor                               *)
(* bob_admissible, charlie_admissible == the two class premises               *)
(*             dsdp_security == the twenty-six statements one setting proves  *)
(*           centropy_uniform == log m of uncertainty about the relay pair at *)
(*                              Alice's honest query                          *)
(*       centropy_V2_dotp_eq0 == her corrupted-query view determines Bob's    *)
(*                              input                                         *)
(* bob_privacy_V1, charlie_privacy_V1 == neither relay learns Alice's input   *)
(* bob_privacy_V3, charlie_privacy_V2 == neither relay learns the other's     *)
(*                              input                                         *)
(*         tuple_guess_V2_le == guessing Bob's input from Alice's hopping     *)
(*                              tuple, priced at two hop advantages           *)
(* unpredictability_ge, predictor_unpredictability_ge == the same bound as a  *)
(*                              logarithmic lower bound                       *)
(*          sim_advantage_le == the tuple against the simulator's law         *)
(*          view_guess_V2_le == the guessing bound at Alice's whole view      *)
(*     centropy_V2_Sout_logm == the output alone leaves Bob's input fully     *)
(*                              uncertain                                     *)
(* centropy_V2_all_zero_logm == so does the all-zero endpoint of the ladder   *)
(* trace_guess_V2_le, trace_unpredictability_ge, trace_sim_advantage_le ==    *)
(*                              the same three bounds at the executed trace   *)
(* centropy_V2_trace_tupleE, centropy_V2_view_tupleE == the trace and the     *)
(*                              view leave the tuple's conditional entropy    *)
(*      centropy_V2_trace_eq0 == that entropy is zero at the executed trace   *)
(* trace_guess_V2_admissible_le == the trace guessing bound conditional on    *)
(*                              the two class premises                        *)
(* trace_guess_V2_admissible_pq_le == the same at the composite modulus       *)
(* decrypt_epsilon_sum_ge, decrypt_bob_epsilon_ge == the decrypting predictor *)
(*                              forces an epsilon of at least 1 - 1/#|plain|  *)
(* decrypt_reduction_admissibleF == no assumption below that value admits its *)
(*                              Bob-key reduction                             *)
(* decrypt_guess_V2_premise_free_lt == the bound without its class premises   *)
(*                              is false                                      *)
(* trace_guess_V2_negligible == the trace guessing probability is negligible  *)
(*                              along the sequence                            *)
(*            dsdp_securityP == the value of dsdp_security every setting has  *)
(* idealized_bob_admissible, idealized_charlie_admissible == the two class    *)
(*                              premises at the idealized sequence and the    *)
(*                              constant predictor                            *)
(*      idealized_admissible == that predictor as an admissible predictor at  *)
(*                              every k                                       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(* =================================================================          *)
(* The adversary-side objects of one setting at one security parameter        *)
(* =================================================================          *)

(* Each declaration below names an object of the hopping axis at the k-th
   instance of the sequence X carries, on the side of that axis which
   mentions an adversary: the advantage functional, the four reduction
   adversaries a distinguisher or a predictor induces, the advantages and
   unpredictability quantities they buy, and the predictor that decrypts.
   The adversary-free objects of the same instance are in dsdp_setting.v. *)
Section dsdp_hopping_adversaries.
Local Unset Implicit Arguments.
Context {R : realType}.
Variable X : dsdp_setting R.
Variable k : nat.

Local Notation Inst := (sequence_instance (instance_sequence X) k).
Local Notation AHE := (inst_AHE Inst).
Local Notation card_renc := (inst_card_renc Inst).
Local Notation rand_of_renc := (@inst_rand_of_renc Inst).
Local Notation pkey_of_party := (inst_pkey_of_party Inst).
Local Notation v1 := (inst_v1 Inst).
Local Notation u1 := (inst_u1 Inst).
Local Notation u2 := (inst_u2 Inst).
Local Notation u3 := (inst_u3 Inst).
Local Notation dk_a := (inst_dk_a Inst).
Local Notation dk_b := (inst_dk_b Inst).
Local Notation dk_c := (inst_dk_c Inst).
Local Notation rb2 := (inst_rb2 Inst).
Local Notation rc2 := (inst_rc2 Inst).

(* The IND-CPA advantage of one adversary at one public key of the k-th
   instance, the unit every hopping bound is priced in. *)
Definition indcpa_epsilon_at (pk : pub_key AHE) (adv : indcpa_adversary AHE)
    : R :=
  indcpa_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc pk adv.

(* The two reduction adversaries a distinguisher of Alice's hopping tuple
   induces, one at Bob's key and one at Charlie's. *)
Definition bob_challenge_adversary_at (D : distinguisher (hop_jointT_at X k))
    : indcpa_adversary AHE :=
  bob_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 D.
Definition charlie_challenge_adversary_at
    (D : distinguisher (hop_jointT_at X k)) : indcpa_adversary AHE :=
  charlie_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 D.

(* The two a predictor of Bob's input at Alice's whole view induces. *)
Definition bob_view_adversary_at
    (predict : predictor AHE (viewT_at X k)) : indcpa_adversary AHE :=
  bob_view_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 predict.
Definition charlie_view_adversary_at
    (predict : predictor AHE (viewT_at X k)) : indcpa_adversary AHE :=
  charlie_view_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 predict.

(* The two advantages a predictor at Alice's hopping tuple buys, and the
   unpredictability those two advantages correct. *)
Definition bob_predictor_epsilon_at
    (predict : predictor AHE (hop_tupleT_at X k)) : R :=
  bob_predictor_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 predict.
Definition charlie_predictor_epsilon_at
    (predict : predictor AHE (hop_tupleT_at X k)) : R :=
  charlie_predictor_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 predict.
Definition alice_predictor_unpredictability_at
    (predict : predictor AHE (hop_tupleT_at X k)) : R :=
  alice_predictor_unpredictability (R:=R) (AHE:=AHE) card_renc rand_of_renc
    pkey_of_party v1 u1 u2 u3 predict.

(* The same three quantities at Alice's executed trace. *)
Definition bob_trace_predictor_epsilon_at
    (predict : predictor AHE (traceT_at X k)) : R :=
  bob_trace_predictor_epsilon (R:=R) card_renc rand_of_renc
    v1 u1 u2 u3 dk_a dk_b dk_c rc2 predict.
Definition charlie_trace_predictor_epsilon_at
    (predict : predictor AHE (traceT_at X k)) : R :=
  charlie_trace_predictor_epsilon (R:=R) card_renc rand_of_renc
    v1 u1 u2 u3 dk_a dk_b dk_c rc2 predict.
Definition alice_trace_unpredictability_at
    (predict : predictor AHE (traceT_at X k)) : R :=
  alice_trace_unpredictability (R:=R) card_renc rand_of_renc
    v1 u1 u2 u3 dk_a dk_b dk_c rb2 rc2 predict.

(* The trace predictor that decrypts the aggregate ciphertext with Alice's
   own key, the one no class restriction admits. *)
Definition bob_decrypt_predictor_at : predictor AHE (traceT_at X k) :=
  bob_decrypt_predictor rand_of_renc dk_a dk_b dk_c rc2.

End dsdp_hopping_adversaries.

(* =================================================================          *)
(* The predictor class the trace bounds are conditional on                    *)
(* =================================================================          *)

(* A predictor of Bob's input at Alice's executed trace of the k-th instance,
   together with the two premises the trace bound is conditional on: the two
   reduction adversaries this predictor induces, one at Bob's key and one at
   Charlie's, are both admitted by the assumption the sequence makes at k.
   The two fields assert nothing of the predictor itself, only of the two
   adversaries it induces, which is what leaves room for a predictor whose
   own success probability is one while its reductions stay outside the
   class. *)
Record dsdp_admissible_predictor (R : realType) (X : dsdp_setting R)
    (k : nat) := {
  predict : predictor (AHE_at X k) (traceT_at X k) ;
  bob_admissible :
    indcpa_admissible (assumption_at X k)
      (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X)
         (distinguisher_of_predictor predict)) ;
  charlie_admissible :
    indcpa_admissible (assumption_at X k)
      (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence X)
         (distinguisher_of_predictor predict)) }.

(* =================================================================          *)
(* What one setting proves                                                    *)
(* =================================================================          *)

Section dsdp_security_record.
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Context {R : realType}.

(* The twenty-six statements a setting proves, each at the projections of X.
   The scope of the collection, and the eight fields that are leakage or
   obstruction rather than secrecy, are described in the header. *)
Record dsdp_security (X : dsdp_setting R) := {

  (* Alice's residual uncertainty about the relay pair, given her own inputs
     and the output she computes, is exactly log m: her honest query leaves
     the pair uniform on the m-point fiber her output cuts.  Unconditional,
     at that query. *)
  centropy_uniform : forall k, dsdp_honest_query X k ->
    `H(VarRV X k | CondRV X k)
      = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R) ;

  (* At Alice's corrupted query the protocol output is Bob's input itself, so
     her whole dot-product view determines it.  Leakage, unconditional, and
     conditional on the query rather than on any encryption. *)
  centropy_V2_dotp_eq0 : forall k, dsdp_corrupted_query X k ->
    `H( V2 (inputs X k) | AliceDotpView_at X k ) = 0 ;

  (* Bob's whole real view leaves log m of uncertainty about Alice's input,
     hence a positive amount.  Unconditional: the masks are one-time pads,
     and no assumption is spent. *)
  bob_privacy_V1 : forall k,
    `H(V1 (inputs X k) | BobView_at X k)
      = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
    /\ `H(V1 (inputs X k) | BobView_at X k) > 0 ;

  (* The same for Charlie's whole real view about Alice's input. *)
  charlie_privacy_V1 : forall k,
    `H(V1 (inputs X k) | CharlieView_at X k)
      = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
    /\ `H(V1 (inputs X k) | CharlieView_at X k) > 0 ;

  (* Bob learns nothing about Charlie's input either, at the same
     unconditional log m. *)
  bob_privacy_V3 : forall k,
    `H(V3 (inputs X k) | BobView_at X k)
      = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
    /\ `H(V3 (inputs X k) | BobView_at X k) > 0 ;

  (* And Charlie learns nothing about Bob's input, which is what makes the
     two relays honest-but-curious parties rather than a coalition. *)
  charlie_privacy_V2 : forall k,
    `H(V2 (inputs X k) | CharlieView_at X k)
      = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
    /\ `H(V2 (inputs X k) | CharlieView_at X k) > 0 ;

  (* A corrupted Alice guessing Bob's input from her hopping tuple does no
     better than the uniform residue plus the two advantages her predictor's
     reduction adversaries buy.  The residue is unconditional; each epsilon
     is the per-distinguisher advantage of one named reduction, one at Bob's
     key and one at Charlie's. *)
  tuple_guess_V2_le : forall k
      (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
    Pr (hop_fdist_at X k)
       [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t]
    <= (#|plain (AHE_at X k)|%:R : R)^-1
       + indcpa_epsilon_at X k (bob_pkey_at X k)
           (bob_challenge_adversary_at X k
              (distinguisher_of_predictor predict))
       + indcpa_epsilon_at X k (charlie_pkey_at X k)
           (charlie_challenge_adversary_at X k
              (distinguisher_of_predictor predict)) ;

  (* The same bound read logarithmically: minus the log of her success
     probability is at least log #|plain| corrected by the two advantages.
     A positive success probability is the premise. *)
  unpredictability_ge : forall k
      (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
    0 < Pr (hop_fdist_at X k)
           [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t] ->
    log (#|plain (AHE_at X k)|%:R : R)
      - log (1 + #|plain (AHE_at X k)|%:R
                 * (bob_predictor_epsilon_at X k predict
                    + charlie_predictor_epsilon_at X k predict))
    <= - log (Pr (hop_fdist_at X k)
                 [set t | (predict `o AliceRealTuple_at X k) t
                          == hop_V2_at X k t]) ;

  (* The same lower bound at the named unpredictability quantity of the
     predictor, which is that negated logarithm under its own name. *)
  predictor_unpredictability_ge : forall k
      (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
    0 < Pr (hop_fdist_at X k)
           [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t] ->
    log (#|plain (AHE_at X k)|%:R : R)
      - log (1 + #|plain (AHE_at X k)|%:R
                 * (bob_predictor_epsilon_at X k predict
                    + charlie_predictor_epsilon_at X k predict))
    <= alice_predictor_unpredictability_at X k predict ;

  (* No distinguisher separates the real joint law of the two relay inputs
     with Alice's tuple from the simulator's law by more than the two hop
     advantages: simulation security of the tuple, per distinguisher, and
     conditional on nothing beyond the two epsilons it names. *)
  sim_advantage_le : forall k (D : distinguisher (hop_jointT_at X k)),
    `| Pr (`p_ [% hop_V2_at X k, hop_V3_at X k, AliceRealTuple_at X k])
          [set x | D x]
       - Pr (alice_ideal_joint_at X k) [set x | D x] |
    <= indcpa_epsilon_at X k (bob_pkey_at X k)
         (bob_challenge_adversary_at X k D)
       + indcpa_epsilon_at X k (charlie_pkey_at X k)
           (charlie_challenge_adversary_at X k D) ;

  (* The tuple guessing bound carried to Alice's whole view, priced at the
     two advantages her view adversaries buy. *)
  view_guess_V2_le : forall k
      (predict : predictor (AHE_at X k) (viewT_at X k)),
    Pr (hop_fdist_at X k)
       [set t | (predict `o AliceView_at X k) t == hop_V2_at X k t]
    <= (#|plain (AHE_at X k)|%:R : R)^-1
       + indcpa_epsilon_at X k (bob_pkey_at X k)
           (bob_view_adversary_at X k predict)
       + indcpa_epsilon_at X k (charlie_pkey_at X k)
           (charlie_view_adversary_at X k predict) ;

  (* Conditioned on the protocol output alone, Bob's input keeps its whole
     log #|plain| of uncertainty.  Information-theoretic, no epsilon spent. *)
  centropy_V2_Sout_logm : forall k,
    `H( hop_V2_at X k | Sout_at X k )
      = log (#|plain (AHE_at X k)|%:R : R) ;

  (* The same whole uncertainty at the all-zero endpoint of the hop ladder,
     the hybrid in which both ciphertexts carry zero.  This is the ideal side
     the two epsilons of the guessing bounds pay to reach. *)
  centropy_V2_all_zero_logm : forall k,
    `H( hop_V2_at X k | AliceHopTuple_at X k 2 )
      = log (#|plain (AHE_at X k)|%:R : R) ;

  (* The tuple guessing bound at Alice's executed piSMC trace, at the two
     advantages the trace reduction adversaries buy. *)
  trace_guess_V2_le : forall k
      (predict : predictor (AHE_at X k) (traceT_at X k)),
    Pr (hop_fdist_at X k)
       [set t | (predict `o AliceTrace_at X k) t == hop_V2_at X k t]
    <= (#|plain (AHE_at X k)|%:R : R)^-1
       + indcpa_epsilon_at X k (bob_pkey_at X k)
           (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X)
              (distinguisher_of_predictor predict))
       + indcpa_epsilon_at X k (charlie_pkey_at X k)
           (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence X)
              (distinguisher_of_predictor predict)) ;

  (* That bound read logarithmically at the executed trace, under a positive
     success probability. *)
  trace_unpredictability_ge : forall k
      (predict : predictor (AHE_at X k) (traceT_at X k)),
    0 < Pr (hop_fdist_at X k)
           [set t | (predict `o AliceTrace_at X k) t == hop_V2_at X k t] ->
    log (#|plain (AHE_at X k)|%:R : R)
      - log (1 + #|plain (AHE_at X k)|%:R
                 * (bob_trace_predictor_epsilon_at X k predict
                    + charlie_trace_predictor_epsilon_at X k predict))
    <= alice_trace_unpredictability_at X k predict ;

  (* Simulation security of the executed trace, per distinguisher, at the
     same two advantages. *)
  trace_sim_advantage_le : forall k
      (D : distinguisher (trace_jointT_at X k)),
    `| Pr (`p_ [% hop_V2_at X k, hop_V3_at X k, AliceTrace_at X k])
          [set x | D x]
       - Pr (alice_trace_ideal_joint_at X k) [set x | D x] |
    <= indcpa_epsilon_at X k (bob_pkey_at X k)
         (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X) D)
       + indcpa_epsilon_at X k (charlie_pkey_at X k)
           (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence X) D) ;

  (* Alice's executed trace and her hopping tuple leave the same conditional
     entropy about Bob's input: the trace holds no coordinate the tuple
     lacks, which is what transports a tuple bound to the trace.
     Unconditional. *)
  centropy_V2_trace_tupleE : forall k,
    `H( hop_V2_at X k | AliceTrace_at X k )
      = `H( hop_V2_at X k | AliceRealTuple_at X k ) ;

  (* The same equality at Alice's whole view. *)
  centropy_V2_view_tupleE : forall k,
    `H( hop_V2_at X k | AliceView_at X k )
      = `H( hop_V2_at X k | AliceRealTuple_at X k ) ;

  (* At the executed trace that entropy is zero: the trace carries Alice's
     private key alongside the aggregate ciphertext, so she recovers Bob's
     input.  Leakage, unconditional, and the reason the trace guessing bound
     is stated only for a class of predictors. *)
  centropy_V2_trace_eq0 : forall k,
    `H( hop_V2_at X k | AliceTrace_at X k ) = 0 ;

  (* The trace guessing bound with both ciphertext hops charged to the single
     epsilon of the assumption the sequence makes at k.  The residue
     1/#|plain| is unconditional; the term 2 * epsilon is conditional on that
     assumption, and the whole bound on the two class premises the
     admissible-predictor record carries. *)
  trace_guess_V2_admissible_le : forall k
      (a : dsdp_admissible_predictor X k),
    alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X) (predict a)
    <= (#|plain (AHE_at X k)|%:R : R)^-1
       + 2 * indcpa_assumption_epsilon (assumption_at X k) ;

  (* The same bound with its unconditional term written at the composite
     modulus p * q, which is the counting axis's reading of the cardinality
     the two axes share. *)
  trace_guess_V2_admissible_pq_le : forall k
      (a : dsdp_admissible_predictor X k),
    alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X) (predict a)
    <= (((p_minus_2 X k).+2%:R : R) * (q_minus_2 X k).+2%:R)^-1
       + 2 * indcpa_assumption_epsilon (assumption_at X k) ;

  (* The decrypting predictor drives the sum of its two reduction advantages
     to at least 1 - 1/#|plain|, so an assumption admitting it must assume an
     epsilon that large.  This is the obstruction the class restriction
     answers, and it is unconditional. *)
  decrypt_epsilon_sum_ge : forall k,
    1 - (#|plain (AHE_at X k)|%:R : R)^-1
    <= bob_trace_predictor_epsilon_at X k (bob_decrypt_predictor_at X k)
       + charlie_trace_predictor_epsilon_at X k
           (bob_decrypt_predictor_at X k) ;

  (* The Bob-key half alone already reaches that value, so the obstruction is
     not an artifact of summing the two hops. *)
  decrypt_bob_epsilon_ge : forall k,
    1 - (#|plain (AHE_at X k)|%:R : R)^-1
    <= bob_trace_predictor_epsilon_at X k (bob_decrypt_predictor_at X k) ;

  (* No assumption promising an epsilon below 1 - 1/#|plain| admits the
     Bob-key reduction the decrypting predictor induces.  The quantifier runs
     over every assumption at k rather than over the sequence's own, which is
     what makes this a statement about the class restriction. *)
  decrypt_reduction_admissibleF : forall k (A : indcpa_assumptionT_at X k),
    indcpa_assumption_epsilon A < 1 - (#|plain (AHE_at X k)|%:R : R)^-1 ->
    indcpa_admissible A
      (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X)
         (distinguisher_of_predictor (bob_decrypt_predictor_at X k)))
    = false ;

  (* Dropping the two class premises leaves the trace guessing bound false at
     every assumption promising a small epsilon, which places its truth in
     the class restriction rather than in the size of the epsilon. *)
  decrypt_guess_V2_premise_free_lt :
    forall k (A : indcpa_assumptionT_at X k),
    2 * indcpa_assumption_epsilon A
      < 1 - (#|plain (AHE_at X k)|%:R : R)^-1 ->
    (#|plain (AHE_at X k)|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A
    < alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X)
        (bob_decrypt_predictor_at X k) ;

  (* Along the sequence, an admissible predictor at every k makes the trace
     guessing probability a negligible sequence.  This is the asymptotic
     form, spending the sequence's own assumption at each k together with its
     negligible plaintext size sequence. *)
  trace_guess_V2_negligible :
    forall adv : forall k, dsdp_admissible_predictor X k,
    negligible_fun
      (f_guess_V2 (R:=R) (Q:=instance_sequence X)
         (fun k => predict (adv k))) }.

End dsdp_security_record.

(* =================================================================          *)
(* Every setting proves them                                                  *)
(* =================================================================          *)

(* The one value of the results record, after du2002's pair
   scalar_product_is_leakage_free / scalar_product_is_leakage_freeP: each of
   the twenty-six fields is an application of the axis theorem of its own
   file to the projections of X, so the record adds no mathematical content
   to the axes and only fixes the setting they are read at.  Thirteen of the
   citations are qualified, the field having taken the short name. *)
Section dsdp_securityP.
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Context {R : realType}.
Variable X : dsdp_setting R.

Local Notation Inst k := (sequence_instance (instance_sequence X) k).
Local Notation card_renc k := (inst_card_renc (Inst k)).
Local Notation rand_of_renc k := (@inst_rand_of_renc (Inst k)).
Local Notation pkey_of_party k := (inst_pkey_of_party (Inst k)).
Local Notation v1 k := (inst_v1 (Inst k)).
Local Notation u1 k := (inst_u1 (Inst k)).
Local Notation u2 k := (inst_u2 (Inst k)).
Local Notation u3 k := (inst_u3 (Inst k)).
Local Notation u3_unit k := (inst_u3_unit (Inst k)).
Local Notation dk_a k := (inst_dk_a (Inst k)).
Local Notation dk_b k := (inst_dk_b (Inst k)).
Local Notation dk_c k := (inst_dk_c (Inst k)).
Local Notation rb2 k := (inst_rb2 (Inst k)).
Local Notation rc2 k := (inst_rc2 (Inst k)).

Let centropy_uniform_holds : forall k, dsdp_honest_query X k ->
  `H(VarRV X k | CondRV X k)
    = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R).
Proof.
move=> k [h0 hlt].
exact: (dsdp_centropy_uniform_direct (prime_p X k) (prime_q X k)
          (coprime_pq X k) (dsdp_constraint_holds X k) (VarRV_uniform X k)
          (VarRV_indep_inputs X k) h0 hlt).
Qed.

Let centropy_V2_dotp_eq0_holds : forall k, dsdp_corrupted_query X k ->
  `H( V2 (inputs X k) | AliceDotpView_at X k ) = 0.
Proof.
move=> k [h2 h3].
exact: (US_e1_centropy_V2_eq0 (V1 (inputs X k)) (V2 (inputs X k))
          (V3 (inputs X k)) (U1 (inputs X k)) (R2 (inputs X k))
          (R3 (inputs X k)) (Dk_a (inputs X k)) h2 h3).
Qed.

Let bob_privacy_V1_holds : forall k,
  `H(V1 (inputs X k) | BobView_at X k)
    = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
  /\ `H(V1 (inputs X k) | BobView_at X k) > 0.
Proof.
move=> k.
exact: (dsdp_relay_secrecy.bob_privacy_V1 (pV1_unif (inputs X k))
          (bob_inputs_indep_V1 X k)).
Qed.

Let charlie_privacy_V1_holds : forall k,
  `H(V1 (inputs X k) | CharlieView_at X k)
    = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
  /\ `H(V1 (inputs X k) | CharlieView_at X k) > 0.
Proof.
move=> k.
exact: (dsdp_relay_secrecy.charlie_privacy_V1 (pV1_unif (inputs X k))
          (charlie_inputs_indep_V1 X k)).
Qed.

Let bob_privacy_V3_holds : forall k,
  `H(V3 (inputs X k) | BobView_at X k)
    = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
  /\ `H(V3 (inputs X k) | BobView_at X k) > 0.
Proof.
move=> k.
exact: (dsdp_relay_secrecy.bob_privacy_V3 (pV3_unif (inputs X k))
          (pR3_unif (inputs X k)) (R3_indep_VU3_V3 X k)
          (bob_data_indep_charlie X k)).
Qed.

Let charlie_privacy_V2_holds : forall k,
  `H(V2 (inputs X k) | CharlieView_at X k)
    = log ((((p_minus_2 X k).+2 * (q_minus_2 X k).+2)%N)%:R : R)
  /\ `H(V2 (inputs X k) | CharlieView_at X k) > 0.
Proof.
move=> k.
exact: (dsdp_relay_secrecy.charlie_privacy_V2 (pV2_unif (inputs X k))
          (pR2_unif (inputs X k)) (R2_indep_VU2_V2 X k)
          (R2_indep_VU2_VU3R_V2 X k) (Dk_c_V3_indep_V2_E_charlie_d3 X k)).
Qed.

Let tuple_guess_V2_le_holds : forall k
    (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
  Pr (hop_fdist_at X k)
     [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t]
  <= (#|plain (AHE_at X k)|%:R : R)^-1
     + indcpa_epsilon_at X k (bob_pkey_at X k)
         (bob_challenge_adversary_at X k (distinguisher_of_predictor predict))
     + indcpa_epsilon_at X k (charlie_pkey_at X k)
         (charlie_challenge_adversary_at X k
            (distinguisher_of_predictor predict)).
Proof.
move=> k predict.
exact: (alice_tuple_guess_V2_le (card_renc k) (rand_of_renc k)
          (pkey_of_party k) (v1 k) (u1 k) (u2 k) (u3_unit k) predict).
Qed.

Let unpredictability_ge_holds : forall k
    (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
  0 < Pr (hop_fdist_at X k)
         [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t] ->
  log (#|plain (AHE_at X k)|%:R : R)
    - log (1 + #|plain (AHE_at X k)|%:R
               * (bob_predictor_epsilon_at X k predict
                  + charlie_predictor_epsilon_at X k predict))
  <= - log (Pr (hop_fdist_at X k)
               [set t | (predict `o AliceRealTuple_at X k) t
                        == hop_V2_at X k t]).
Proof.
move=> k predict hpos.
exact: (alice_unpredictability_ge (u3_unit k) hpos).
Qed.

Let predictor_unpredictability_ge_holds : forall k
    (predict : predictor (AHE_at X k) (hop_tupleT_at X k)),
  0 < Pr (hop_fdist_at X k)
         [set t | (predict `o AliceRealTuple_at X k) t == hop_V2_at X k t] ->
  log (#|plain (AHE_at X k)|%:R : R)
    - log (1 + #|plain (AHE_at X k)|%:R
               * (bob_predictor_epsilon_at X k predict
                  + charlie_predictor_epsilon_at X k predict))
  <= alice_predictor_unpredictability_at X k predict.
Proof.
move=> k predict hpos.
exact: (alice_predictor_unpredictability_ge (u3_unit k) hpos).
Qed.

Let sim_advantage_le_holds : forall k
    (D : distinguisher (hop_jointT_at X k)),
  `| Pr (`p_ [% hop_V2_at X k, hop_V3_at X k, AliceRealTuple_at X k])
        [set x | D x]
     - Pr (alice_ideal_joint_at X k) [set x | D x] |
  <= indcpa_epsilon_at X k (bob_pkey_at X k)
       (bob_challenge_adversary_at X k D)
     + indcpa_epsilon_at X k (charlie_pkey_at X k)
         (charlie_challenge_adversary_at X k D).
Proof.
move=> k D.
exact: (alice_sim_advantage_le (card_renc k) (rand_of_renc k)
          (pkey_of_party k) (v1 k) (u1 k) (u2 k) (u3 k) D).
Qed.

Let view_guess_V2_le_holds : forall k
    (predict : predictor (AHE_at X k) (viewT_at X k)),
  Pr (hop_fdist_at X k)
     [set t | (predict `o AliceView_at X k) t == hop_V2_at X k t]
  <= (#|plain (AHE_at X k)|%:R : R)^-1
     + indcpa_epsilon_at X k (bob_pkey_at X k)
         (bob_view_adversary_at X k predict)
     + indcpa_epsilon_at X k (charlie_pkey_at X k)
         (charlie_view_adversary_at X k predict).
Proof.
move=> k predict.
exact: (alice_view_guess_V2_le (card_renc k) (rand_of_renc k)
          (pkey_of_party k) (v1 k) (u1 k) (u2 k) (u3_unit k) predict).
Qed.

Let centropy_V2_Sout_logm_holds : forall k,
  `H( hop_V2_at X k | Sout_at X k ) = log (#|plain (AHE_at X k)|%:R : R).
Proof.
move=> k.
exact: (dsdp_alice_hop_secrecy.centropy_V2_Sout_logm (card_renc k) (v1 k)
          (u1 k) (u2 k) (u3_unit k)).
Qed.

Let centropy_V2_all_zero_logm_holds : forall k,
  `H( hop_V2_at X k | AliceHopTuple_at X k 2 )
    = log (#|plain (AHE_at X k)|%:R : R).
Proof.
move=> k.
exact: (dsdp_alice_hop_secrecy.centropy_V2_all_zero_logm (card_renc k)
          (rand_of_renc k) (pkey_of_party k) (v1 k) (u1 k) (u2 k)
          (u3_unit k)).
Qed.

Let trace_guess_V2_le_holds : forall k
    (predict : predictor (AHE_at X k) (traceT_at X k)),
  Pr (hop_fdist_at X k)
     [set t | (predict `o AliceTrace_at X k) t == hop_V2_at X k t]
  <= (#|plain (AHE_at X k)|%:R : R)^-1
     + indcpa_epsilon_at X k (bob_pkey_at X k)
         (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X)
            (distinguisher_of_predictor predict))
     + indcpa_epsilon_at X k (charlie_pkey_at X k)
         (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence X)
            (distinguisher_of_predictor predict)).
Proof.
move=> k predict.
exact: (alice_trace_guess_V2_le (card_renc k) (rand_of_renc k) (v1 k) (u1 k)
          (u2 k) (u3_unit k) (dk_a k) (dk_b k) (dk_c k) (rb2 k) (rc2 k)
          predict).
Qed.

Let trace_unpredictability_ge_holds : forall k
    (predict : predictor (AHE_at X k) (traceT_at X k)),
  0 < Pr (hop_fdist_at X k)
         [set t | (predict `o AliceTrace_at X k) t == hop_V2_at X k t] ->
  log (#|plain (AHE_at X k)|%:R : R)
    - log (1 + #|plain (AHE_at X k)|%:R
               * (bob_trace_predictor_epsilon_at X k predict
                  + charlie_trace_predictor_epsilon_at X k predict))
  <= alice_trace_unpredictability_at X k predict.
Proof.
move=> k predict hpos.
exact: (alice_trace_unpredictability_ge (u3_unit k) hpos).
Qed.

Let trace_sim_advantage_le_holds : forall k
    (D : distinguisher (trace_jointT_at X k)),
  `| Pr (`p_ [% hop_V2_at X k, hop_V3_at X k, AliceTrace_at X k])
        [set x | D x]
     - Pr (alice_trace_ideal_joint_at X k) [set x | D x] |
  <= indcpa_epsilon_at X k (bob_pkey_at X k)
       (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X) D)
     + indcpa_epsilon_at X k (charlie_pkey_at X k)
         (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence X) D).
Proof.
move=> k D.
exact: (alice_trace_sim_advantage_le (card_renc k) (rand_of_renc k) (v1 k)
          (u1 k) (u2 k) (u3 k) (dk_a k) (dk_b k) (dk_c k) (rb2 k) (rc2 k) D).
Qed.

Let centropy_V2_trace_tupleE_holds : forall k,
  `H( hop_V2_at X k | AliceTrace_at X k )
    = `H( hop_V2_at X k | AliceRealTuple_at X k ).
Proof.
move=> k.
exact: (dsdp_alice_trace_link.centropy_V2_trace_tupleE (card_renc k)
          (rand_of_renc k) (v1 k) (u1 k) (u2 k) (u3 k) (dk_a k) (dk_b k)
          (dk_c k) (rb2 k) (rc2 k)).
Qed.

Let centropy_V2_view_tupleE_holds : forall k,
  `H( hop_V2_at X k | AliceView_at X k )
    = `H( hop_V2_at X k | AliceRealTuple_at X k ).
Proof.
move=> k.
exact: (dsdp_alice_trace_link.centropy_V2_view_tupleE (card_renc k)
          (rand_of_renc k) (v1 k) (u1 k) (u2 k) (u3 k) (dk_a k) (dk_b k)
          (dk_c k)).
Qed.

Let centropy_V2_trace_eq0_holds : forall k,
  `H( hop_V2_at X k | AliceTrace_at X k ) = 0.
Proof.
move=> k.
exact: (dsdp_alice_trace_link.centropy_V2_trace_eq0 (card_renc k)
          (rand_of_renc k) (v1 k) (u1 k) (u2 k) (u3 k) (dk_a k) (dk_b k)
          (dk_c k) (rb2 k) (rc2 k)).
Qed.

Let trace_guess_V2_admissible_le_holds : forall k
    (a : dsdp_admissible_predictor X k),
  alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X) (predict a)
  <= (#|plain (AHE_at X k)|%:R : R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at X k).
Proof.
move=> k a.
exact: (alice_trace_guess_V2_admissible_le (u3_unit k) (rb2 k)
          (bob_admissible a) (charlie_admissible a)).
Qed.

Let trace_guess_V2_admissible_pq_le_holds : forall k
    (a : dsdp_admissible_predictor X k),
  alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X) (predict a)
  <= (((p_minus_2 X k).+2%:R : R) * (q_minus_2 X k).+2%:R)^-1
     + 2 * indcpa_assumption_epsilon (assumption_at X k).
Proof.
move=> k a.
have -> : (((p_minus_2 X k).+2%:R : R) * (q_minus_2 X k).+2%:R)^-1
        = (#|plain (AHE_at X k)|%:R : R)^-1.
  by rewrite /AHE_at (card_plain X k) natrM.
exact: (trace_guess_V2_admissible_le_holds a).
Qed.

Let decrypt_epsilon_sum_ge_holds : forall k,
  1 - (#|plain (AHE_at X k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at X k (bob_decrypt_predictor_at X k)
     + charlie_trace_predictor_epsilon_at X k (bob_decrypt_predictor_at X k).
Proof.
move=> k.
exact: (dsdp_alice_trace_link.decrypt_epsilon_sum_ge (card_renc k)
          (rand_of_renc k) (v1 k) (u1 k) (u2 k) (u3_unit k) (dk_a k)
          (dk_b k) (dk_c k) (rb2 k) (rc2 k)).
Qed.

Let decrypt_bob_epsilon_ge_holds : forall k,
  1 - (#|plain (AHE_at X k)|%:R : R)^-1
  <= bob_trace_predictor_epsilon_at X k (bob_decrypt_predictor_at X k).
Proof.
move=> k.
exact: (dsdp_alice_trace_link.decrypt_bob_epsilon_ge (card_renc k)
          (rand_of_renc k) (v1 k) (u1 k) (u2 k) (u3_unit k) (dk_a k)
          (dk_b k) (dk_c k) (rb2 k) (rc2 k)).
Qed.

Let decrypt_reduction_admissibleF_holds : forall k
    (A : indcpa_assumptionT_at X k),
  indcpa_assumption_epsilon A < 1 - (#|plain (AHE_at X k)|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary_at (R:=R) (Q:=instance_sequence X)
       (distinguisher_of_predictor (bob_decrypt_predictor_at X k)))
  = false.
Proof.
move=> k A heps.
exact: (dsdp_alice_trace_link.decrypt_reduction_admissibleF (v1 k) (u1 k)
          (u2 k) (u3_unit k) (dk_a k) (dk_b k) (dk_c k) (rb2 k) (rc2 k)
          heps).
Qed.

Let decrypt_guess_V2_premise_free_lt_holds : forall k
    (A : indcpa_assumptionT_at X k),
  2 * indcpa_assumption_epsilon A < 1 - (#|plain (AHE_at X k)|%:R : R)^-1 ->
  (#|plain (AHE_at X k)|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A
  < alice_trace_guess_V2_pr_at (R:=R) (Q:=instance_sequence X)
      (bob_decrypt_predictor_at X k).
Proof.
move=> k A heps.
exact: (dsdp_alice_trace_link.decrypt_guess_V2_premise_free_lt (v1 k)
          (u1 k) (u2 k) (u3 k) (dk_a k) (dk_b k) (dk_c k) (rb2 k) (rc2 k)
          heps).
Qed.

Let trace_guess_V2_negligible_holds :
  forall adv : forall k, dsdp_admissible_predictor X k,
  negligible_fun
    (f_guess_V2 (R:=R) (Q:=instance_sequence X) (fun k => predict (adv k))).
Proof.
move=> adv.
exact: (alice_trace_guess_V2_negligible (fun k => bob_admissible (adv k))
          (fun k => charlie_admissible (adv k))).
Qed.

Definition dsdp_securityP : dsdp_security X := {|
  centropy_uniform := centropy_uniform_holds ;
  centropy_V2_dotp_eq0 := centropy_V2_dotp_eq0_holds ;
  bob_privacy_V1 := bob_privacy_V1_holds ;
  charlie_privacy_V1 := charlie_privacy_V1_holds ;
  bob_privacy_V3 := bob_privacy_V3_holds ;
  charlie_privacy_V2 := charlie_privacy_V2_holds ;
  tuple_guess_V2_le := tuple_guess_V2_le_holds ;
  unpredictability_ge := unpredictability_ge_holds ;
  predictor_unpredictability_ge := predictor_unpredictability_ge_holds ;
  sim_advantage_le := sim_advantage_le_holds ;
  view_guess_V2_le := view_guess_V2_le_holds ;
  centropy_V2_Sout_logm := centropy_V2_Sout_logm_holds ;
  centropy_V2_all_zero_logm := centropy_V2_all_zero_logm_holds ;
  trace_guess_V2_le := trace_guess_V2_le_holds ;
  trace_unpredictability_ge := trace_unpredictability_ge_holds ;
  trace_sim_advantage_le := trace_sim_advantage_le_holds ;
  centropy_V2_trace_tupleE := centropy_V2_trace_tupleE_holds ;
  centropy_V2_view_tupleE := centropy_V2_view_tupleE_holds ;
  centropy_V2_trace_eq0 := centropy_V2_trace_eq0_holds ;
  trace_guess_V2_admissible_le := trace_guess_V2_admissible_le_holds ;
  trace_guess_V2_admissible_pq_le := trace_guess_V2_admissible_pq_le_holds ;
  decrypt_epsilon_sum_ge := decrypt_epsilon_sum_ge_holds ;
  decrypt_bob_epsilon_ge := decrypt_bob_epsilon_ge_holds ;
  decrypt_reduction_admissibleF := decrypt_reduction_admissibleF_holds ;
  decrypt_guess_V2_premise_free_lt :=
    decrypt_guess_V2_premise_free_lt_holds ;
  trace_guess_V2_negligible := trace_guess_V2_negligible_holds |}.

End dsdp_securityP.

(* =================================================================          *)
(* The class premises are theorems at the idealized setting                   *)
(* =================================================================          *)

(* The idealized sequence assumes the cipher-constant classifier, which
   admits an adversary whose verdict ignores the challenge ciphertext.  At
   the constant predictor the two reduction adversaries have that shape, so
   both class premises are theorems there and the trace bounds hold at the
   idealized setting with nothing assumed.
   The restriction to that predictor is not an artifact of the proof:
   decrypt_reduction_admissibleF says that the reduction the decrypting
   predictor induces is admitted by no assumption promising a small epsilon,
   so no value of dsdp_admissible_predictor exists at that predictor. *)
Section dsdp_security_idealized.
Local Set Default Goal Selector "1".
Context {R : realType}.

Local Notation IS := (idealized_setting : dsdp_setting R).

(* The Bob-key class premise at the composite-modulus idealized sequence.
   idealized_bob_cipher_constant of dsdp_instance_sequence.v states the same
   fact at idealized_instance, whose plaintext ring is 'Z_((k+2)^(k+2)); the
   setting's sequence is built from idealized_pq_instance, so the fact is
   restated here at that instance. *)
Lemma idealized_bob_admissible (k : nat) :
  indcpa_admissible (assumption_at IS k)
    (bob_trace_adversary_at (R:=R) (Q:=instance_sequence IS) (k:=k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key class premise at the same sequence and predictor. *)
Lemma idealized_charlie_admissible (k : nat) :
  indcpa_admissible (assumption_at IS k)
    (charlie_trace_adversary_at (R:=R) (Q:=instance_sequence IS) (k:=k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The constant predictor as an admissible predictor at every k, with both
   class premises discharged. *)
Definition idealized_admissible (k : nat) :
    dsdp_admissible_predictor IS k := {|
  predict := fun _ => 0 ;
  bob_admissible := idealized_bob_admissible k ;
  charlie_admissible := idealized_charlie_admissible k |}.

End dsdp_security_idealized.
