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
(* A value of dsdp_security R is a setting, not a proof: the data a 3-party   *)
(* DSDP security statement is made over, at every security parameter at once. *)
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
(*              dsdp_security == the data a 3-party DSDP security statement   *)
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
Record dsdp_security (R : realType) := {
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

Section dsdp_security_laws.
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Context {R : realType}.
Variable X : dsdp_security R.
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

End dsdp_security_laws.

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
