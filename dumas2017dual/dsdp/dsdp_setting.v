From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid spp_proba.
Require Import extra_proba extra_algebra.
Require Import homomorphic_encryption.
Require Import dsdp_entropy.
Require Import indcpa_game.
Require Import dsdp_instance_sequence.

(**md**************************************************************************)
(* # The setting a DSDP security statement is made over                       *)
(*                                                                            *)
(* A value of dsdp_setting R is a setting, not a proof: the data a 3-party    *)
(* DSDP security statement is made over, at every security parameter at once, *)
(* with the security properties proved over it in the results file            *)
(* dsdp_security.v.                                                           *)
(* One sample space with one law per k, the eleven random inputs of a         *)
(* 3-party run together with their independence and uniformity, the composite *)
(* plaintext modulus held as two primes, and the sequence of IND-CPA scheme   *)
(* instances the hopping bounds are stated at.                                *)
(*                                                                            *)
(* The two axes share one number, not one execution.  The counting side's     *)
(* random variables land in 'Z_(p k * q k); the hopping side's data lands in  *)
(* plain (inst_AHE (sequence_instance instance_sequence k)), a different      *)
(* type.  card_plain says the two have the same cardinality, so the entropy   *)
(* log m of the counting axis and the guessing residue 1/#|plain| of the      *)
(* hopping axis are measured on spaces of one size.  Nothing identifies the   *)
(* two message spaces, and nothing relates the counting side's weight random  *)
(* variable U3 to the hopping side's fixed weight inst_u3.  The weights and   *)
(* the keys therefore occur twice as unrelated objects, as random variables   *)
(* on the counting side and as values on the hopping side, and the laws       *)
(* sample_fdist X k at distinct k are unrelated laws on unrelated sample      *)
(* spaces, as the instance sequence already says of its instances.            *)
(*                                                                            *)
(* Three things stay outside.  The adversary and its two class premises,      *)
(* which restrict the reduction adversaries a predictor induces and so speak  *)
(* about the adversary rather than about the setting.  Alice's query, in      *)
(* both of its forms: the honest range 0 < U3 t < min p q of the log m        *)
(* entropy theorem, and the corrupted choice U2 = 1, U3 = 0 of the leakage    *)
(* theorem.  Those are opposite conditions on the same weight, so the         *)
(* weight's condition cannot be a property of the setting: were the honest    *)
(* range a field, the corrupted theorem would hold vacuously at every value   *)
(* of the record.  And the output, which is a function of the inputs and so   *)
(* enters below as a Definition with the linear constraint proved, rather     *)
(* than as a field with the constraint assumed.                               *)
(*                                                                            *)
(* Two consequences of the field set.  The each-against-the-rest fields       *)
(* reach Alice's three weights, so over this record the log m entropy         *)
(* equality covers the honest-sampling setting, where her weights are         *)
(* independent of her input and of one another; the general form, assuming    *)
(* nothing about their joint law, stays at dsdp_centropy_uniform_direct of    *)
(* counting/dsdp_entropy.v.  And card_plain together with the hopping side's  *)
(* sequence_size_negligible forces p k * q k to grow superpolynomially, so no *)
(* value of this record carries a fixed modulus, although each counting       *)
(* equality is exact at every fixed composite modulus.                        *)
(*                                                                            *)
(* ```                                                                        *)
(*               dsdp_setting == the data a 3-party DSDP security statement   *)
(*                               is made over, at every security parameter    *)
(*          instance_sequence == the sequence of IND-CPA scheme instances the *)
(*                               hopping bounds are stated at                 *)
(*        p_minus_2, q_minus_2 == the plaintext modulus at k as its two       *)
(*                               primes, in successor form                    *)
(*     prime_p, prime_q, coprime_pq == primality and coprimality of the two   *)
(*                               factors                                      *)
(*                 card_plain == the k-th scheme's plaintext count is p * q   *)
(*      sampleT, sample_fdist == the sample space at k and the law on it      *)
(*   V1, V2, V3, U1, U2, U3, R2, R3 == the eight plaintext inputs of a run    *)
(*        Dk_a, Dk_b, Dk_c == the three private keys as random variables      *)
(*   V1_indep .. Dk_c_indep == each input independent of the joint of the     *)
(*                               other ten                                    *)
(* pV1_unif, pV2_unif, pV3_unif, pR2_unif, pR3_unif == uniformity of the      *)
(*                               three plaintext inputs and the two masks     *)
(*                     output == the output Alice computes from the inputs    *)
(*                     CondRV == her conditioner, inputs and output           *)
(*                     VarRV == the relay input pair                          *)
(*                   InputRV == her inputs without the output                 *)
(*      dsdp_constraint_holds == the linear DSDP relation at that output      *)
(*               V2_indep_V3 == the two relay inputs are independent          *)
(*              VarRV_uniform == the relay pair is uniform on the product     *)
(*        VarRV_indep_inputs == the relay pair is independent of Alice's      *)
(*                               inputs                                       *)
(*        bob_inputs_indep_V1 == Bob's clean data is independent of V1        *)
(*    charlie_inputs_indep_V1 == Charlie's clean data is independent of V1    *)
(*           R3_indep_VU3_V3 == the second mask is fresh against Charlie's    *)
(*                               weighted input                               *)
(*     bob_data_indep_charlie == Bob's clean data is independent of the       *)
(*                               whole Charlie group                          *)
(*           R2_indep_VU2_V2 == the first mask is fresh against Bob's         *)
(*                               weighted input                               *)
(*      R2_indep_VU2_VU3R_V2 == the same mask against the pair Alice's first  *)
(*                               combine enters                               *)
(* Dk_c_V3_indep_V2_E_charlie_d3 ==                                           *)
(*                               Charlie's key and input are independent of   *)
(*                               Bob's input with the aggregate ciphertext    *)
(*          idealized_setting == the value of dsdp_setting the two sides      *)
(*                               below make together                          *)
(*   idealized_p, idealized_q == the two prime factors of the witness         *)
(*                               plaintext modulus at k                       *)
(* idealized_p_gt, idealized_q_gt ==                                          *)
(*                               the smaller factor exceeds (k+2)^(k+2), the  *)
(*                               larger exceeds it                            *)
(*              prime_minus2K == a prime in the successor-of-successor form   *)
(*                               the modulus fields take                      *)
(* idealized_p_minus_2, idealized_q_minus_2 ==                                *)
(*                               those two primes as the record's two modulus *)
(*                               fields                                       *)
(* idealized_pE, idealized_qE == the round trip from a modulus field back to  *)
(*                               its prime                                    *)
(* idealized_prime_p, idealized_prime_q, idealized_coprime_pq ==              *)
(*                               primality and coprimality of the witness     *)
(*                               modulus                                      *)
(*      idealized_pq_instance == the idealized scheme at the composite        *)
(*                               modulus, as one DSDP instance                *)
(*       idealized_card_plain == that instance's plaintext count is p * q     *)
(*  idealized_size_negligible == its inverse plaintext cardinalities are a    *)
(*                               negligible sequence                          *)
(*      idealized_pq_sequence == the sequence of those instances under the    *)
(*                               cipher-constant assumption                   *)
(* idealized_card_msg, idealized_card_sample, idealized_card_rest ==          *)
(*                               the counts of the plaintext ring, of the     *)
(*                               sample and of seven coordinates              *)
(* idealized_sampleT, idealized_sample_fdist ==                               *)
(*                               eight coordinates of the plaintext ring,     *)
(*                               drawn uniformly                              *)
(*    idealized_sample_fdistE == that law as a product of eight uniform       *)
(*                               coordinate laws                              *)
(* idealized_coord, idealized_rest ==                                         *)
(*                               the letter at one coordinate and the seven   *)
(*                               others                                       *)
(*            idealized_split == one coordinate against the seven others,     *)
(*                               with both marginals uniform                  *)
(* idealized_view, idealized_rest_view ==                                     *)
(*                               the seven other coordinates as one view of   *)
(*                               ten, independent of the pivot                *)
(* idealized_V1 .. idealized_R3 ==                                            *)
(*                               the eight plaintext inputs as the eight      *)
(*                               coordinates                                  *)
(* idealized_Dk_a, idealized_Dk_b, idealized_Dk_c ==                          *)
(*                               the three private keys as constants          *)
(* idealized_V1_indep .. idealized_Dk_c_indep ==                              *)
(*                               the eleven each-against-the-rest facts at    *)
(*                               that law                                     *)
(* idealized_pV1_unif .. idealized_pR3_unif ==                                *)
(*                               uniformity of the three plaintext inputs and *)
(*                               the two masks                                *)
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

(* =================================================================          *)
(* The setting                                                                *)
(* =================================================================          *)

(* Set Strict Implicit brackets the record: {RV P -> A} unfolds to a function
   type whose domain mentions k, so under the file's ambient Unset Strict
   Implicit every k-indexed field would take the record value and k
   implicitly and V1 X k would not typecheck. *)
Set Strict Implicit.

(* The data a 3-party DSDP security statement is made over, at every security
   parameter at once: one sample space with one law per k, the eleven random
   inputs of a run with their independence and uniformity, the plaintext
   modulus as two primes, and the sequence of scheme instances the hopping
   bounds are stated at.  A value of it is a setting, not a proof.
   The two axes share one number, not one execution: card_plain equates two
   cardinalities and nothing identifies the two message spaces, so the
   weights and the keys occur twice as unrelated objects, as random variables
   here and as values inside instance_sequence.
   The adversary and its class premises, Alice's query in both its honest and
   its corrupted form, and the output stay outside. *)
Record dsdp_setting (R : realType) := {
  (* The sequence of scheme instances the hopping bounds are stated at,
     carrying the only computational hypothesis in the record; every other
     field is information-theoretic. *)
  instance_sequence : dsdp_instance_sequence R ;

  (* The plaintext modulus at k, held as the two primes whose product it is,
     because the fiber count the counting axis rests on needs p and q
     separately. *)
  p_minus_2 : nat -> nat ;
  q_minus_2 : nat -> nat ;

  (* Primality and coprimality are what make the solution fiber of the DSDP
     constraint have exactly m points, the whole content of the log m
     bound. *)
  prime_p : forall k, prime (p_minus_2 k).+2 ;
  prime_q : forall k, prime (q_minus_2 k).+2 ;
  coprime_pq : forall k, coprime (p_minus_2 k).+2 (q_minus_2 k).+2 ;

  (* The k-th scheme's plaintext space has p * q elements, so the entropy
     log m of the counting axis and the residue 1/#|plain| of the hopping
     axis are measured on spaces of one size. *)
  card_plain : forall k,
    #|plain (inst_AHE (sequence_instance instance_sequence k))|
      = ((p_minus_2 k).+2 * (q_minus_2 k).+2)%N ;

  (* The sample space at k and the law on it: every random variable below is
     a function on this space and every bound is an average over this law. *)
  sampleT : nat -> finType ;
  sample_fdist : forall k, R.-fdist (sampleT k) ;

  (* The entire randomness of a 3-party run at k.  Every message and every
     party view is a deterministic function of these eleven, which is what
     lets a bound proved at the inputs transfer to a view. *)
  V1 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  V2 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  V3 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  U1 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  U2 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  U3 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  R2 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  R3 : forall k, {RV (sample_fdist k) ->
    ('Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  Dk_a : forall k, {RV (sample_fdist k) -> (Alice.-key Dec
    'Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  Dk_b : forall k, {RV (sample_fdist k) -> (Bob.-key Dec
    'Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;
  Dk_c : forall k, {RV (sample_fdist k) -> (Charlie.-key Dec
    'Z_((p_minus_2 k).+2 * (q_minus_2 k).+2))} ;

  (* Each input independent of the joint of the other ten, stated
     each-against-the-rest because every derived fact below is one of these
     pushed through inde_RV_comp. *)
  V1_indep : forall k, sample_fdist k |=
    [% V2 k, V3 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ V1 k ;
  V2_indep : forall k, sample_fdist k |=
    [% V1 k, V3 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ V2 k ;
  V3_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ V3 k ;
  U1_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ U1 k ;
  U2_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ U2 k ;
  U3_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, R2 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ U3 k ;
  R2_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, U3 k, R3 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ R2 k ;
  R3_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, U3 k, R2 k,
       Dk_a k, Dk_b k, Dk_c k] _|_ R3 k ;
  Dk_a_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_b k, Dk_c k] _|_ Dk_a k ;
  Dk_b_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_c k] _|_ Dk_b k ;
  Dk_c_indep : forall k, sample_fdist k |=
    [% V1 k, V2 k, V3 k, U1 k, U2 k, U3 k, R2 k, R3 k,
       Dk_a k, Dk_b k] _|_ Dk_c k ;

  (* Uniformity of R2 and R3 is what makes the relay bounds unconditional,
     one-time-pad masking rather than encryption hardness hiding V2 and V3;
     uniformity of V1, V2, V3 is what makes the conditional entropy equal
     log m rather than merely positive.  Alice's three weights carry no law:
     they are her chosen query, not a sample. *)
  pV1_unif : forall k, `p_ (V1 k)
    = fdist_uniform (card_Zp_pq (p_minus_2 k) (q_minus_2 k)) ;
  pV2_unif : forall k, `p_ (V2 k)
    = fdist_uniform (card_Zp_pq (p_minus_2 k) (q_minus_2 k)) ;
  pV3_unif : forall k, `p_ (V3 k)
    = fdist_uniform (card_Zp_pq (p_minus_2 k) (q_minus_2 k)) ;
  pR2_unif : forall k, `p_ (R2 k)
    = fdist_uniform (card_Zp_pq (p_minus_2 k) (q_minus_2 k)) ;
  pR3_unif : forall k, `p_ (R3 k)
    = fdist_uniform (card_Zp_pq (p_minus_2 k) (q_minus_2 k)) }.
Unset Strict Implicit.

(* =================================================================          *)
(* The laws of one setting at one security parameter                          *)
(* =================================================================          *)

Section dsdp_setting_laws.
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Context {R : realType}.
Variable X : dsdp_setting R.
Variable k : nat.

Local Notation p_minus_2 := (p_minus_2 X k).
Local Notation q_minus_2 := (q_minus_2 X k).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.
Local Notation P := (sample_fdist X k).
Local Notation V1 := (V1 X k).
Local Notation V2 := (V2 X k).
Local Notation V3 := (V3 X k).
Local Notation U1 := (U1 X k).
Local Notation U2 := (U2 X k).
Local Notation U3 := (U3 X k).
Local Notation R2 := (R2 X k).
Local Notation R3 := (R3 X k).
Local Notation Dk_a := (Dk_a X k).
Local Notation Dk_b := (Dk_b X k).
Local Notation Dk_c := (Dk_c X k).

(* The joint of the ten inputs other than one plaintext input: the domain
   every each-against-the-rest projection below reads from. *)
Local Notation rest10 := (msg * msg * msg * msg * msg * msg * msg *
  (Alice.-key Dec msg) * (Bob.-key Dec msg) * (Charlie.-key Dec msg))%type.

(* Bob's input under Alice's query weight U2, reaching the aggregate only
   through D2. *)
Let VU2 : {RV P -> msg} := V2 \* U2.

(* Charlie's input under Alice's query weight U3, reaching the aggregate only
   through VU3R. *)
Let VU3 : {RV P -> msg} := V3 \* U3.

(* Charlie's weighted input under Alice's mask R3, the plaintext of the second
   combine Alice sends to Bob.  R3 is Alice's own, so it lies outside Bob's
   view. *)
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's weighted input under Alice's mask R2, the plaintext Bob decrypts from
   Alice's first combine.  R2 lies outside Charlie's view. *)
Let D2 : {RV P -> msg} := VU2 \+ R2.

(* The aggregate Charlie decrypts, carrying both relay inputs under Alice's
   two masks. *)
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* The aggregate Bob forwards to Charlie under Charlie's key, the one
   ciphertext Charlie's view contains. *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' Charlie `o D3.

(* The output Alice computes: she strips both of her masks from the aggregate
   Charlie returns and adds her own weighted input.  It is a function of the
   record's inputs, which is what turns the linear constraint the counting
   axis assumes today into a theorem below. *)
Definition output : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

(* Alice's conditioner: her own input, her three weights, and the output she
   computes.  The counting bound conditions on plaintexts only, so her key,
   her masks and the ciphertext hops stay out of it. *)
Definition CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, output].

(* The pair of relay inputs, the quantity whose residual uncertainty the
   counting bound measures. *)
Definition VarRV : {RV P -> (msg * msg)} := [% V2, V3].

(* Alice's inputs without the output, the left side of the independence the
   fiber-counting bound consumes. *)
Definition InputRV : {RV P -> (msg * msg * msg * msg)} := [% V1, U1, U2, U3].

(* The linear DSDP relation between Alice's conditioner and the relay inputs
   holds pointwise at the output she computes, so the counting axis needs no
   field assuming it. *)
Lemma dsdp_constraint_holds :
  forall t, dsdp_constraint (CondRV t) (VarRV t).
Proof.
move=> t; rewrite /dsdp_constraint /CondRV /VarRV /output.
by rewrite /D3 /D2 /VU3R /VU3 /VU2 /=; apply/eqP; ring.
Qed.

(* Bob's input and Charlie's input are independent, the V3 field projected
   onto V2 alone.  It is what makes the relay pair's joint law a product. *)
Lemma V2_indep_V3 : P |= V2 _|_ V3.
Proof.
have h := inde_RV_comp (fun w : rest10 => w.1.1.1.1.1.1.1.1.2) idfun
  (V3_indep X k).
by rewrite /comp_RV /= in h *.
Qed.

(* The relay pair is uniform on the product of two copies of the plaintext
   ring, at the cardinality proof the counting sections carry.  Uniformity of
   the pair, not merely of each side, is what makes the conditional entropy
   equal log m. *)
Lemma VarRV_uniform :
  `p_ VarRV
  = fdist_uniform (dsdp_entropy.card_msg_pair_subproof p_minus_2 q_minus_2).
Proof.
rewrite /VarRV (inde_dist_of_RV2 V2_indep_V3) (pV2_unif X k) (pV3_unif X k).
exact: esym (fdist_uniform_prod _ _ _).
Qed.

(* Alice's four plaintext inputs are independent of the relay pair, the V2 and
   V3 fields projected and joined by one contraction.  It is the hypothesis
   the fiber-counting argument conditions on. *)
Lemma VarRV_indep_inputs : P |= InputRV _|_ VarRV.
Proof.
rewrite /InputRV /VarRV; apply: inde_RV_contraction.
- have h := inde_RV_comp
    (fun w : rest10 => (((w.1.1.1.1.1.1.1.1.1, w.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.2), w.1.1.1.1.1.2)) idfun
    (V2_indep X k).
  by rewrite /comp_RV /= in h *.
- have h := inde_RV_comp
    (fun w : rest10 => ((((w.1.1.1.1.1.1.1.1.1, w.1.1.1.1.1.1.1.2),
                          w.1.1.1.1.1.1.2), w.1.1.1.1.1.2),
                        w.1.1.1.1.1.1.1.1.2)) idfun
    (V3_indep X k).
  by rewrite /comp_RV /= in h *.
Qed.

(* Bob's key, his own input and the two combines he handles are independent of
   Alice's input V1: V1 occurs in no protocol message, so the V1 field
   projected onto those four suffices. *)
Lemma bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1.
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.1),
                       w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2 + w.1.1.1.2),
                      w.1.1.1.1.1.1.1.1.1 * w.1.1.1.1.1.1.2 + w.1.1.1.1.2))
  idfun (V1_indep X k).
by rewrite /comp_RV /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* Charlie's key, his own input and the aggregate he decrypts are independent
   of Alice's input V1, the same projection of the V1 field on his side. *)
Lemma charlie_inputs_indep_V1 : P |= [% Dk_c, V3, D3] _|_ V1.
Proof.
have h := inde_RV_comp
  (fun w : rest10 => ((w.2, w.1.1.1.1.1.1.1.1.2),
                      w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2 + w.1.1.1.2
                      + (w.1.1.1.1.1.1.1.1.1 * w.1.1.1.1.1.1.2
                         + w.1.1.1.1.2)))
  idfun (V1_indep X k).
by rewrite /comp_RV /D3 /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* Alice's second mask is independent of Charlie's weighted input and of
   Charlie's input itself, the R3 field projected onto that pair.  R3 is the
   pad that hides V3 from Bob. *)
Lemma R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.2)) idfun (R3_indep X k).
rewrite /comp_RV /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* Bob's key, his input and the combine he decrypts are independent of
   Charlie's input, weighted input and mask together.  The V3, U3 and R3
   fields are projected and joined by two contractions, then reshaped, since
   contracting on VU3 directly is unavailable: VU3 shares V3 with the left
   side. *)
Lemma bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3].
Proof.
have hv3 : P |= [% Dk_b, V2, D2] _|_ V3.
  have h := inde_RV_comp
    (fun w : rest10 => ((w.1.2, w.1.1.1.1.1.1.1.1.2),
                        w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.1.2
                        + w.1.1.1.1.2)) idfun (V3_indep X k).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hu3 : P |= [% [% Dk_b, V2, D2], V3] _|_ U3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.1.2), w.1.1.1.1.1.1.1.2))
    idfun (U3_indep X k).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hr3 : P |= [% [% Dk_b, V2, D2], [% V3, U3]] _|_ R3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.2), (w.1.1.1.1.1.1.1.2,
                                        w.1.1.1.1.2)))
    idfun (R3_indep X k).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hstep := inde_RV_contraction (inde_RV_contraction hv3 hu3) hr3.
have h := inde_RV_comp idfun
  (fun w : (msg * msg * msg)%type => ((w.1.1, w.1.1 * w.1.2), w.2)) hstep.
by rewrite /comp_RV /VU3 /= in h *.
Qed.

(* Alice's first mask is independent of Bob's weighted input and of Bob's
   input itself, the R2 field projected onto that pair.  R2 is the pad that
   hides V2 from Charlie. *)
Lemma R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.1.2)) idfun (R2_indep X k).
rewrite /comp_RV /VU2 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* The same mask against the whole pair Alice's first combine enters, the R2
   field projected one coordinate wider. *)
Lemma R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [% VU3R, V2]].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                       w.1.1.1.1.1.1.1.1.2))) idfun (R2_indep X k).
rewrite /comp_RV /VU2 /VU3R /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* Charlie's key and input are independent of Bob's input together with the
   aggregate ciphertext Charlie receives.  Two one-time-pad steps: R2 is a
   fresh pad inside D2, and D2 is then a fresh pad inside D3, so the whole
   aggregate carries nothing about V2 and neither does its encryption. *)
Lemma Dk_c_V3_indep_V2_E_charlie_d3 :
  P |= [% Dk_c, V3] _|_ [% V2, E_charlie_d3].
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR2_adj : `p_ R2 = fdist_uniform card_TZ.
  by rewrite (pR2_unif X k); congr fdist_uniform; exact: eq_irrelevance.
have r2_rest : P |= R2 _|_ [% VU2, [% VU3R, [% [% Dk_c, V3], V2]]].
  have h := inde_RV_comp
    (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                        (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                         ((w.2, w.1.1.1.1.1.1.1.2),
                          w.1.1.1.1.1.1.1.1.2)))) idfun (R2_indep X k).
  rewrite /comp_RV /VU2 /VU3R /VU3 /= in h *.
  by rewrite inde_RV_sym.
have d2_rest : P |= D2 _|_ [% VU3R, [% [% Dk_c, V3], V2]].
  exact: (lemma_3_5' r2_rest pR2_adj).
have pD2_unif : `p_ D2 = fdist_uniform card_TZ.
  have vu2_r2 : P |= VU2 _|_ R2.
    rewrite inde_RV_sym.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/r2_rest.
  exact: (add_RV_unif VU2 R2 card_TZ pR2_adj vu2_r2).
have d3_rest : P |= D3 _|_ [% [% Dk_c, V3], V2].
  exact: (lemma_3_5' d2_rest pD2_unif).
have he : P |= [% [% Dk_c, V3], V2] _|_ E_charlie_d3.
  have hsym : P |= [% [% Dk_c, V3], V2] _|_ D3 by rewrite inde_RV_sym.
  have h := inde_RV_comp idfun (E' Charlie) hsym.
  by rewrite /E_charlie_d3 /comp_RV /= in h *.
apply: inde_RV_contraction; last exact: he.
have h := inde_RV_comp (fun w : rest10 => (w.2, w.1.1.1.1.1.1.1.1.2)) idfun
  (V2_indep X k).
by rewrite /comp_RV /= in h *.
Qed.

End dsdp_setting_laws.

(* Every declaration above has a discharged type that unfolds to a product
   whose binder mentions the setting and the security parameter: a random
   variable is a function on the sample space, and an independence is a
   quantification over two of its values.  Under the file's ambient Unset
   Strict Implicit both arguments would therefore be implicit.  Pinning them
   explicit keeps every use site free of @. *)
Arguments output {R} X k.
Arguments CondRV {R} X k.
Arguments VarRV {R} X k.
Arguments InputRV {R} X k.
Arguments dsdp_constraint_holds {R} X k.
Arguments V2_indep_V3 {R} X k.
Arguments VarRV_uniform {R} X k.
Arguments VarRV_indep_inputs {R} X k.
Arguments bob_inputs_indep_V1 {R} X k.
Arguments charlie_inputs_indep_V1 {R} X k.
Arguments R3_indep_VU3_V3 {R} X k.
Arguments bob_data_indep_charlie {R} X k.
Arguments R2_indep_VU2_V2 {R} X k.
Arguments R2_indep_VU2_VU3R_V2 {R} X k.
Arguments Dk_c_V3_indep_V2_E_charlie_d3 {R} X k.

(* =================================================================          *)
(* An inhabitant                                                              *)
(* =================================================================          *)

(* The record is inhabited.  On this value the hopping side is the idealized
   scheme of idealized_ahe.v under the cipher-constant assumption, whose
   assumed advantage is zero at every k, so every hopping bound stated over
   it is its unconditional 1/#|plain| term alone; the counting side is the
   uniform law on eight coordinates of the plaintext ring, on which every
   counting bound is exact at log (p k * q k).
   Every declaration carries the idealized_ stem of the value it builds,
   since the record's own projections hold the bare names, with idealized_pq_
   on the two that would otherwise collide with idealized_instance and
   idealized_instance_sequence of dsdp_instance_sequence.v; prime_minus2K is
   a general fact about primes and keeps its bare name. *)
Section dsdp_setting_witness.
Local Set Default Goal Selector "1".
Local Open Scope vec_ext_scope.
Context {R : realType}.

(* A k-indexed random variable's type unfolds to a function type whose domain
   mentions k, so under the file's ambient Set Implicit Arguments the index
   would be inferred implicit and idealized_V1 k would not typecheck. *)
Local Unset Implicit Arguments.

(* The smaller prime factor of the plaintext modulus at k, taken above
   (k+2)^(k+2) so that the modulus grows fast enough for the inverse
   plaintext cardinality to be negligible. *)
Definition idealized_p (k : nat) : nat := s2val (prime_above (k.+2 ^ k.+2)).

(* The larger prime factor, taken above the smaller one, which is what makes
   the two distinct and hence coprime. *)
Definition idealized_q (k : nat) : nat := s2val (prime_above (idealized_p k)).

Lemma idealized_p_prime k : prime (idealized_p k).
Proof. exact: (s2valP' (prime_above (k.+2 ^ k.+2))). Qed.

Lemma idealized_q_prime k : prime (idealized_q k).
Proof. exact: (s2valP' (prime_above (idealized_p k))). Qed.

(* The growth the size negligibility field is read off: the modulus at k
   already exceeds (k+2)^(k+2) through its smaller factor. *)
Lemma idealized_p_gt k : (k.+2 ^ k.+2 < idealized_p k)%N.
Proof. exact: (s2valP (prime_above (k.+2 ^ k.+2))). Qed.

(* The two factors are ordered, which is what tells them apart. *)
Lemma idealized_q_gt k : (idealized_p k < idealized_q k)%N.
Proof. exact: (s2valP (prime_above (idealized_p k))). Qed.

(* A prime in the successor-of-successor form the record's two modulus fields
   take, the round trip that lets a prime be supplied to a field holding a
   predecessor. *)
Lemma prime_minus2K (n : nat) : prime n -> n.-2.+2 = n.
Proof.
move=> pn; have n_gt1 : (1 < n)%N := prime_gt1 pn.
have n_gt0 : (0 < n.-1)%N by rewrite ltn_predRL.
by rewrite (prednK n_gt0) (prednK (ltnW n_gt1)).
Qed.

Definition idealized_p_minus_2 (k : nat) : nat := (idealized_p k).-2.
Definition idealized_q_minus_2 (k : nat) : nat := (idealized_q k).-2.

Lemma idealized_pE k : (idealized_p_minus_2 k).+2 = idealized_p k.
Proof. exact/prime_minus2K/idealized_p_prime. Qed.

Lemma idealized_qE k : (idealized_q_minus_2 k).+2 = idealized_q k.
Proof. exact/prime_minus2K/idealized_q_prime. Qed.

Lemma idealized_prime_p k : prime (idealized_p_minus_2 k).+2.
Proof. by rewrite idealized_pE idealized_p_prime. Qed.

Lemma idealized_prime_q k : prime (idealized_q_minus_2 k).+2.
Proof. by rewrite idealized_qE idealized_q_prime. Qed.

Lemma idealized_coprime_pq k :
  coprime (idealized_p_minus_2 k).+2 (idealized_q_minus_2 k).+2.
Proof.
rewrite idealized_pE idealized_qE prime_coprime ?idealized_p_prime //.
rewrite dvdn_prime2 ?idealized_p_prime ?idealized_q_prime //.
by apply/negP => /eqP pq_eq; move: (idealized_q_gt k); rewrite pq_eq ltnn.
Qed.

Local Notation pq k :=
  ((idealized_p_minus_2 k).+2 * (idealized_q_minus_2 k).+2)%N.
Local Notation msg k :=
  ('Z_((idealized_p_minus_2 k).+2 * (idealized_q_minus_2 k).+2)).

(* The instance at k: the idealized scheme over the composite modulus, the
   first three weights zero, Charlie's weight one, zero keys and the single
   coin.  It is idealized_instance again at a plaintext ring the counting
   axis can also be carried on, which is what lets one value fill both
   sides. *)
Definition idealized_pq_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := idealized_indcpa_scheme (msg k) ;
  inst_v1 := 0 ; inst_u1 := 0 ; inst_u2 := 0 ; inst_u3 := 1 ;
  inst_u3_unit      := GRing.unitr1 _ ;
  inst_dk_a := 0 ; inst_dk_b := 0 ; inst_dk_c := 0 ;
  inst_rb2 := ord0 ; inst_rc2 := ord0 |}.

(* The one number the two axes share: the k-th plaintext space is counted by
   the counting axis's composite modulus. *)
Lemma idealized_card_plain (k : nat) :
  #|plain (inst_AHE (idealized_pq_instance k))| = pq k.
Proof. by rewrite card_ord Zp_cast. Qed.

(* The unconditional currency of the sequence: its plaintext spaces grow at
   least as (k+2)^(k+2), so their inverse cardinalities fall below every
   inverse polynomial. *)
Lemma idealized_size_negligible :
  negligible_fun (fun k =>
    (#|plain (inst_AHE (idealized_pq_instance k))|%:R : R)^-1).
Proof.
have -> : (fun k => (#|plain (inst_AHE (idealized_pq_instance k))|%:R : R)^-1)
        = (fun k => ((pq k)%:R : R)^-1).
  by apply/funext => k; rewrite idealized_card_plain.
apply: negligible_fun_inv_ge_expnn => k.
rewrite idealized_pE idealized_qE.
apply: leq_trans (ltnW (idealized_p_gt k)) _.
by rewrite leq_pmulr // prime_gt0 // idealized_q_prime.
Qed.

(* The sequence: the composite-modulus idealized instances, the
   cipher-constant assumption at each k, and the two negligibility facts
   discharged rather than assumed.  Its advantage currency is zero at every
   k, which is what leaves each hopping bound along it with only its
   information-theoretic term. *)
Definition idealized_pq_sequence : dsdp_instance_sequence R := {|
  sequence_instance := idealized_pq_instance ;
  sequence_assumption := fun k =>
    cipher_constant_assumption (inst_card_renc (idealized_pq_instance k))
      (@inst_rand_of_renc (idealized_pq_instance k)) ;
  sequence_size_negligible := idealized_size_negligible ;
  sequence_adv_negligible := negligible_fun_cst0 |}.

Local Notation ord8 j := (@Ordinal 8 j erefl).
Local Notation ord7 j := (@Ordinal 7 j erefl).

(* The plaintext count at k in the form fdist_uniform takes its argument. *)
Definition idealized_card_msg (k : nat) : #|msg k| = pq k :=
  card_Zp_pq (idealized_p_minus_2 k) (idealized_q_minus_2 k).

(* The counts of the whole sample and of the seven coordinates other than a
   pivot, the two the split below reads its uniform laws at. *)
Lemma idealized_card_sample (k : nat) :
  #|'rV[msg k]_8| = (((pq k) ^ 8).-1).+1.
Proof. by rewrite card_mx mul1n (idealized_card_msg k) prednK. Qed.

Lemma idealized_card_rest (k : nat) :
  #|'rV[msg k]_7| = (((pq k) ^ 7).-1).+1.
Proof. by rewrite card_mx mul1n (idealized_card_msg k) prednK. Qed.

(* The counting sample space at k: eight coordinates of the plaintext ring
   drawn uniformly, so that the record's each-input-against-the-other-ten
   fields are the coordinate-against-the-rest decomposition of one uniform
   row vector. *)
Definition idealized_sampleT (k : nat) : finType := 'rV[msg k]_8.

Definition idealized_sample_fdist (k : nat) :
    R.-fdist (idealized_sampleT k) :=
  fdist_uniform (idealized_card_sample k).

Local Notation P k := (idealized_sample_fdist k).

(* The sample law as the product of eight uniform coordinate laws: drawing
   the vector and drawing the eight plaintexts independently are the same
   experiment. *)
Lemma idealized_sample_fdistE (k : nat) :
  P k = (fdist_uniform (idealized_card_msg k) : R.-fdist (msg k)) `^ 8.
Proof.
exact: esym (fdist_rV_uniform (idealized_card_msg k)
               (idealized_card_sample k)).
Qed.

(* The letter at coordinate i and the seven letters other than it, the two
   statistics of the sample every field below is read through. *)
Definition idealized_coord (k : nat) (i : 'I_8) : {RV (P k) -> msg k} :=
  fun v => v ``_ i.

Definition idealized_rest (k : nat) (i : 'I_8) :
    {RV (P k) -> 'rV[msg k]_7} :=
  rV_drop i.

(* One coordinate against the seven others, with both marginals uniform.
   The whole counting side of the record is this one fact at eight pivots. *)
Lemma idealized_split (k : nat) (i : 'I_8) :
  [/\ P k |= idealized_rest k i _|_ idealized_coord k i,
      `p_ (idealized_rest k i) = fdist_uniform (idealized_card_rest k)
    & `p_ (idealized_coord k i) = fdist_uniform (idealized_card_msg k)].
Proof.
have bij_split : bijective (fun t => (idealized_rest k i t,
                                      idealized_coord k i t)).
  exact: (rV_split_bij (msg k) i).
exact: (uniform_bij_indep (idealized_card_rest k) (idealized_card_msg k)
          bij_split).
Qed.

(* The ten-component view of the seven coordinates other than a pivot: the
   seven plaintexts in increasing coordinate order, then the three constant
   private keys.  Reshaping the seven-vector this way is what turns one
   coordinate split into one each-against-the-rest field. *)
Definition idealized_view (k : nat) (w : 'rV[msg k]_7) :=
  (w ``_ (ord7 0), w ``_ (ord7 1), w ``_ (ord7 2), w ``_ (ord7 3),
   w ``_ (ord7 4), w ``_ (ord7 5), w ``_ (ord7 6),
   @KeyOf Alice Dec (msg k) 0, @KeyOf Bob Dec (msg k) 0,
   @KeyOf Charlie Dec (msg k) 0).

(* The ten-component view of the seven other coordinates stays independent of
   the pivot, the single fact the eight coordinate fields below reshape. *)
Lemma idealized_rest_view (k : nat) (i : 'I_8) :
  P k |= (idealized_view k `o idealized_rest k i) _|_ idealized_coord k i.
Proof.
have [ind _ _] := idealized_split k i.
exact: inde_RV_comp (idealized_view k) idfun ind.
Qed.

(* The eight plaintext inputs of a run at k are the eight coordinates, in the
   order the record lists them. *)
Definition idealized_V1 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 0).

Definition idealized_V2 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 1).

Definition idealized_V3 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 2).

Definition idealized_U1 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 3).

Definition idealized_U2 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 4).

Definition idealized_U3 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 5).

Definition idealized_R2 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 6).

Definition idealized_R3 (k : nat) : {RV (P k) -> msg k} :=
  idealized_coord k (ord8 7).

(* The three private keys are constants, which is the weakest way to fill the
   three key fields: a constant is independent of everything, so no key
   correlates with any input. *)
Definition idealized_Dk_a (k : nat) :
    {RV (P k) -> (Alice.-key Dec (msg k))} :=
  fun _ => @KeyOf Alice Dec _ 0.

Definition idealized_Dk_b (k : nat) :
    {RV (P k) -> (Bob.-key Dec (msg k))} :=
  fun _ => @KeyOf Bob Dec _ 0.

Definition idealized_Dk_c (k : nat) :
    {RV (P k) -> (Charlie.-key Dec (msg k))} :=
  fun _ => @KeyOf Charlie Dec _ 0.

Lemma idealized_V1_indep (k : nat) :
  P k |=
    [% idealized_V2 k, idealized_V3 k, idealized_U1 k, idealized_U2 k,
       idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_V1 k.
Proof.
have e0 : lift (ord8 0) (ord7 0) = ord8 1 by apply/val_inj.
have e1 : lift (ord8 0) (ord7 1) = ord8 2 by apply/val_inj.
have e2 : lift (ord8 0) (ord7 2) = ord8 3 by apply/val_inj.
have e3 : lift (ord8 0) (ord7 3) = ord8 4 by apply/val_inj.
have e4 : lift (ord8 0) (ord7 4) = ord8 5 by apply/val_inj.
have e5 : lift (ord8 0) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 0) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V2 k, idealized_V3 k, idealized_U1 k, idealized_U2 k,
     idealized_U3 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 0).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_V2_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V3 k, idealized_U1 k, idealized_U2 k,
       idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_V2 k.
Proof.
have e0 : lift (ord8 1) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 1) (ord7 1) = ord8 2 by apply/val_inj.
have e2 : lift (ord8 1) (ord7 2) = ord8 3 by apply/val_inj.
have e3 : lift (ord8 1) (ord7 3) = ord8 4 by apply/val_inj.
have e4 : lift (ord8 1) (ord7 4) = ord8 5 by apply/val_inj.
have e5 : lift (ord8 1) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 1) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V3 k, idealized_U1 k, idealized_U2 k,
     idealized_U3 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 1).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_V3_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_U1 k, idealized_U2 k,
       idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_V3 k.
Proof.
have e0 : lift (ord8 2) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 2) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 2) (ord7 2) = ord8 3 by apply/val_inj.
have e3 : lift (ord8 2) (ord7 3) = ord8 4 by apply/val_inj.
have e4 : lift (ord8 2) (ord7 4) = ord8 5 by apply/val_inj.
have e5 : lift (ord8 2) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 2) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_U1 k, idealized_U2 k,
     idealized_U3 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 2).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_U1_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U2 k,
       idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_U1 k.
Proof.
have e0 : lift (ord8 3) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 3) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 3) (ord7 2) = ord8 2 by apply/val_inj.
have e3 : lift (ord8 3) (ord7 3) = ord8 4 by apply/val_inj.
have e4 : lift (ord8 3) (ord7 4) = ord8 5 by apply/val_inj.
have e5 : lift (ord8 3) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 3) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U2 k,
     idealized_U3 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 3).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_U2_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_U2 k.
Proof.
have e0 : lift (ord8 4) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 4) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 4) (ord7 2) = ord8 2 by apply/val_inj.
have e3 : lift (ord8 4) (ord7 3) = ord8 3 by apply/val_inj.
have e4 : lift (ord8 4) (ord7 4) = ord8 5 by apply/val_inj.
have e5 : lift (ord8 4) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 4) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
     idealized_U3 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 4).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_U3_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_U3 k.
Proof.
have e0 : lift (ord8 5) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 5) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 5) (ord7 2) = ord8 2 by apply/val_inj.
have e3 : lift (ord8 5) (ord7 3) = ord8 3 by apply/val_inj.
have e4 : lift (ord8 5) (ord7 4) = ord8 4 by apply/val_inj.
have e5 : lift (ord8 5) (ord7 5) = ord8 6 by apply/val_inj.
have e6 : lift (ord8 5) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
     idealized_U2 k, idealized_R2 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 5).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_R2_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_U3 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_R2 k.
Proof.
have e0 : lift (ord8 6) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 6) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 6) (ord7 2) = ord8 2 by apply/val_inj.
have e3 : lift (ord8 6) (ord7 3) = ord8 3 by apply/val_inj.
have e4 : lift (ord8 6) (ord7 4) = ord8 4 by apply/val_inj.
have e5 : lift (ord8 6) (ord7 5) = ord8 5 by apply/val_inj.
have e6 : lift (ord8 6) (ord7 6) = ord8 7 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
     idealized_U2 k, idealized_U3 k, idealized_R3 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 6).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_R3_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_U3 k, idealized_R2 k,
       idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_R3 k.
Proof.
have e0 : lift (ord8 7) (ord7 0) = ord8 0 by apply/val_inj.
have e1 : lift (ord8 7) (ord7 1) = ord8 1 by apply/val_inj.
have e2 : lift (ord8 7) (ord7 2) = ord8 2 by apply/val_inj.
have e3 : lift (ord8 7) (ord7 3) = ord8 3 by apply/val_inj.
have e4 : lift (ord8 7) (ord7 4) = ord8 4 by apply/val_inj.
have e5 : lift (ord8 7) (ord7 5) = ord8 5 by apply/val_inj.
have e6 : lift (ord8 7) (ord7 6) = ord8 6 by apply/val_inj.
have -> :
  [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
     idealized_U2 k, idealized_U3 k, idealized_R2 k,
     idealized_Dk_a k, idealized_Dk_b k, idealized_Dk_c k]
  = idealized_view k `o idealized_rest k (ord8 7).
  apply/funext => v.
  by rewrite /comp_RV /idealized_view /idealized_rest /rV_drop !mxE
    e0 e1 e2 e3 e4 e5 e6.
exact: idealized_rest_view.
Qed.

Lemma idealized_Dk_a_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_b k, idealized_Dk_c k]
  _|_ idealized_Dk_a k.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma idealized_Dk_b_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_c k]
  _|_ idealized_Dk_b k.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma idealized_Dk_c_indep (k : nat) :
  P k |=
    [% idealized_V1 k, idealized_V2 k, idealized_V3 k, idealized_U1 k,
       idealized_U2 k, idealized_U3 k, idealized_R2 k, idealized_R3 k,
       idealized_Dk_a k, idealized_Dk_b k]
  _|_ idealized_Dk_c k.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

(* The three plaintext inputs and the two masks are uniform, each the third
   component of its own coordinate split. *)
Lemma idealized_pV1_unif (k : nat) :
  `p_ (idealized_V1 k) = fdist_uniform (idealized_card_msg k).
Proof. by have [_ _ unif] := idealized_split k (ord8 0). Qed.

Lemma idealized_pV2_unif (k : nat) :
  `p_ (idealized_V2 k) = fdist_uniform (idealized_card_msg k).
Proof. by have [_ _ unif] := idealized_split k (ord8 1). Qed.

Lemma idealized_pV3_unif (k : nat) :
  `p_ (idealized_V3 k) = fdist_uniform (idealized_card_msg k).
Proof. by have [_ _ unif] := idealized_split k (ord8 2). Qed.

Lemma idealized_pR2_unif (k : nat) :
  `p_ (idealized_R2 k) = fdist_uniform (idealized_card_msg k).
Proof. by have [_ _ unif] := idealized_split k (ord8 6). Qed.

Lemma idealized_pR3_unif (k : nat) :
  `p_ (idealized_R3 k) = fdist_uniform (idealized_card_msg k).
Proof. by have [_ _ unif] := idealized_split k (ord8 7). Qed.

(* The setting the two sides make together, and the answer to whether
   dsdp_setting has any value at all: the composite-modulus idealized
   sequence on the hopping side, the uniform eight-coordinate law on the
   counting side, and card_plain joining them.  It is named for its hopping
   side, after idealized_instance_sequence of dsdp_instance_sequence.v, which
   it repeats at a plaintext ring the counting side can also be carried on. *)
Definition idealized_setting : dsdp_setting R := {|
  instance_sequence := idealized_pq_sequence ;
  p_minus_2 := idealized_p_minus_2 ;
  q_minus_2 := idealized_q_minus_2 ;
  prime_p := idealized_prime_p ;
  prime_q := idealized_prime_q ;
  coprime_pq := idealized_coprime_pq ;
  card_plain := idealized_card_plain ;
  sampleT := idealized_sampleT ;
  sample_fdist := idealized_sample_fdist ;
  V1 := idealized_V1 ;
  V2 := idealized_V2 ;
  V3 := idealized_V3 ;
  U1 := idealized_U1 ;
  U2 := idealized_U2 ;
  U3 := idealized_U3 ;
  R2 := idealized_R2 ;
  R3 := idealized_R3 ;
  Dk_a := idealized_Dk_a ;
  Dk_b := idealized_Dk_b ;
  Dk_c := idealized_Dk_c ;
  V1_indep := idealized_V1_indep ;
  V2_indep := idealized_V2_indep ;
  V3_indep := idealized_V3_indep ;
  U1_indep := idealized_U1_indep ;
  U2_indep := idealized_U2_indep ;
  U3_indep := idealized_U3_indep ;
  R2_indep := idealized_R2_indep ;
  R3_indep := idealized_R3_indep ;
  Dk_a_indep := idealized_Dk_a_indep ;
  Dk_b_indep := idealized_Dk_b_indep ;
  Dk_c_indep := idealized_Dk_c_indep ;
  pV1_unif := idealized_pV1_unif ;
  pV2_unif := idealized_pV2_unif ;
  pV3_unif := idealized_pV3_unif ;
  pR2_unif := idealized_pR2_unif ;
  pR3_unif := idealized_pR3_unif |}.

End dsdp_setting_witness.
