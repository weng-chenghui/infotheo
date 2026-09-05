From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid spp_proba.
Require Import extra_proba extra_algebra.
Require Import homomorphic_encryption.
Require Import dsdp_entropy dsdp_relay_secrecy dsdp_malicious_dotp.
Require Import negligible indcpa_game.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.
Require Import dsdp_instance_sequence.

(**md**************************************************************************)
(* # The setting a DSDP security statement is made over                       *)
(*                                                                            *)
(* A value of dsdp_setting R is a setting, not a proof: the data a 3-party    *)
(* DSDP security statement is made over, at every security parameter at once. *)
(* One sample space with one law per k, the eleven random inputs of a 3-party *)
(* run together with their independence and uniformity, the composite         *)
(* plaintext modulus held as two primes, and the sequence of IND-CPA scheme   *)
(* instances the hopping bounds are stated at.  The counting side at a fixed  *)
(* modulus is the record dsdp_random_inputs, of which a setting carries one   *)
(* per k.  The properties proved over a setting are the fields of the results *)
(* record dsdp_security of dsdp_security.v.                                   *)
(*                                                                            *)
(* The sequence field carries an IND-CPA assumption at each k, whatever its   *)
(* source.  At the two scheme settings of dsdp_main.v that assumption is      *)
(* derived rather than assumed: paillier_setting reads it off a decisional    *)
(* composite residuosity record at modulus p k q k and benaloh_setting off an *)
(* r-th residuosity record at modulus n k, at twice the residuosity epsilon.  *)
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
(* sample_fdist (inputs X k) at distinct k are unrelated laws on unrelated    *)
(* sample spaces, as the instance sequence already says of its instances.     *)
(*                                                                            *)
(* Three things stay outside the record.  The adversary and its two class     *)
(* premises, which restrict the reduction adversaries a predictor induces and *)
(* so speak about the adversary rather than about the setting.  Alice's       *)
(* query, in both of its forms: the honest range 0 < U3 t < min p q of the    *)
(* log m entropy equality, and the corrupted choice U2 = 1, U3 = 0 of the     *)
(* leakage theorem, which enter as the two records dsdp_honest_query and      *)
(* dsdp_corrupted_query below.  Those are opposite conditions on the same     *)
(* weight, so the weight's condition cannot be a field: were the honest range *)
(* a field, the corrupted theorem would hold vacuously at every value of the  *)
(* record.  And the output, which is a function of the inputs and so enters   *)
(* below as a Definition with the linear constraint proved, rather than as a  *)
(* field with the constraint assumed.                                         *)
(*                                                                            *)
(* Two consequences of the field set.  The each-against-the-rest fields reach *)
(* Alice's three weights, so over this record the log m entropy equality      *)
(* covers the honest-sampling setting, where her weights are independent of   *)
(* her input and of one another; the general form, assuming nothing about     *)
(* their joint law, stays at dsdp_centropy_uniform_direct of                  *)
(* counting/dsdp_entropy.v.  And card_plain together with the hopping side's  *)
(* sequence_size_negligible forces p k * q k to grow superpolynomially, so no *)
(* value of this record carries a fixed modulus, although each counting       *)
(* equality is exact at every fixed composite modulus.                        *)
(*                                                                            *)
(* ```                                                                        *)
(*        dsdp_random_inputs == the counting side of a 3-party run at one     *)
(*                              fixed plaintext modulus                       *)
(*      sampleT, sample_fdist == the sample space and the law on it           *)
(*   V1, V2, V3, U1, U2, U3, R2, R3 == the eight plaintext inputs of a run    *)
(*           Dk_a, Dk_b, Dk_c == the three private keys as random variables   *)
(*     V1_indep .. Dk_c_indep == each input independent of the joint of the   *)
(*                              other ten                                     *)
(* pV1_unif, pV2_unif, pV3_unif, pR2_unif, pR3_unif == uniformity of the      *)
(*                              three plaintext inputs and the two masks      *)
(*              dsdp_setting == the data a 3-party DSDP security statement is *)
(*                              made over, at every security parameter        *)
(*         instance_sequence == the sequence of IND-CPA scheme instances the  *)
(*                              hopping bounds are stated at                  *)
(*      p_minus_2, q_minus_2 == the plaintext modulus at k as its two primes, *)
(*                              in successor form                             *)
(* prime_p, prime_q, coprime_pq == primality and coprimality of the two       *)
(*                              factors                                       *)
(*                card_plain == the k-th scheme's plaintext count is p * q    *)
(*                    inputs == the counting side of the run at k             *)
(*        dsdp_honest_query == Alice's weight on Charlie's input inside the   *)
(*                              range the log m entropy equality reads        *)
(*        U3_gt0, U3_lt_minn == the two ends of that range                    *)
(*      dsdp_corrupted_query == Alice's query fixed to the basis vector e_1   *)
(*            U2_eq1, U3_eq0 == the two weights that choice fixes             *)
(*                    output == the output Alice computes from the inputs     *)
(*                    CondRV == her conditioner, inputs and output            *)
(*                     VarRV == the relay input pair                          *)
(*                   InputRV == her inputs without the output                 *)
(*      dsdp_constraint_holds == the linear DSDP relation at that output      *)
(*               V2_indep_V3 == the two relay inputs are independent          *)
(*             VarRV_uniform == the relay pair is uniform on the product      *)
(*        VarRV_indep_inputs == the relay pair is independent of Alice's      *)
(*                              inputs                                        *)
(*       bob_inputs_indep_V1 == Bob's clean data is independent of V1         *)
(*   charlie_inputs_indep_V1 == Charlie's clean data is independent of V1     *)
(*           R3_indep_VU3_V3 == the second mask is fresh against Charlie's    *)
(*                              weighted input                                *)
(*    bob_data_indep_charlie == Bob's clean data is independent of the whole  *)
(*                              Charlie group                                 *)
(*           R2_indep_VU2_V2 == the first mask is fresh against Bob's         *)
(*                              weighted input                                *)
(*      R2_indep_VU2_VU3R_V2 == the same mask against the pair Alice's first  *)
(*                              combine enters                                *)
(* Dk_c_V3_indep_V2_E_charlie_d3 == Charlie's key and input are independent   *)
(*                              of Bob's input with the aggregate ciphertext  *)
(*           AHE_at, Renc_at == the k-th scheme and its coin index type       *)
(* hop_tupleT_at, hop_jointT_at, viewT_at, traceT_at, trace_jointT_at == the  *)
(*                              five carriers the hopping bounds quantify     *)
(*                              predictors over                               *)
(* hop_fdist_at, hop_V2_at, hop_V3_at == the corrupted-Alice sample space and *)
(*                              its two honest relay inputs                   *)
(* AliceRealTuple_at, AliceAllZeroTuple_at, AliceView_at, AliceTrace_at ==    *)
(*                              the conditioners of the hopping ladder        *)
(*                   Sout_at == the output the hopping side leaks             *)
(*  bob_pkey_at, charlie_pkey_at == the two public keys the ladder prices at  *)
(* alice_ideal_joint_at, alice_trace_ideal_joint_at == the simulator's law at *)
(*                              the tuple and at the executed trace           *)
(* indcpa_assumptionT_at, assumption_at == the IND-CPA assumption type at k   *)
(*                              and the assumption the sequence makes there   *)
(* BobView_at, CharlieView_at, AliceDotpView_at == the three counting views   *)
(*                              at the inputs of X at k                       *)
(*            uniform_inputs == the counting side at any modulus, three       *)
(*                              inputs and two masks uniform and the query    *)
(*                              weights held at three constants               *)
(*    uniform_card_msg, uniform_card_sample, uniform_card_rest == the counts  *)
(*                              of the plaintext ring, of the sample and of   *)
(*                              four coordinates                              *)
(* uniform_sampleT, uniform_sample_fdist == five coordinates of the plaintext *)
(*                              ring, drawn uniformly                         *)
(* uniform_coord, uniform_rest == the letter at one coordinate and the four   *)
(*                              others                                        *)
(*             uniform_split == one coordinate against the four others, with  *)
(*                              both marginals uniform                        *)
(* uniform_view_input, uniform_view_mask == the four other coordinates as one *)
(*                              view of ten, from an input and from a mask    *)
(*    uniform_V1 .. uniform_R3 == the three inputs and the two masks as the   *)
(*                              five coordinates                              *)
(* uniform_U1, uniform_U2, uniform_U3 == Alice's three query weights as       *)
(*                              constants of the sample space                 *)
(* uniform_Dk_a, uniform_Dk_b, uniform_Dk_c == the three private keys as      *)
(*                              constants                                     *)
(* uniform_V1_indep .. uniform_Dk_c_indep == the eleven each-against-the-rest *)
(*                              facts at that law                             *)
(* uniform_pV1_unif .. uniform_pR3_unif == uniformity of the three plaintext  *)
(*                              inputs and the two masks                      *)
(*    idealized_p, idealized_q == the two prime factors of the witness        *)
(*                              plaintext modulus at k                        *)
(* idealized_p_gt, idealized_q_gt == the smaller factor exceeds (k+2)^(k+2),  *)
(*                              the larger exceeds it                         *)
(*             prime_minus2K == a prime in the successor-of-successor form    *)
(*                              the modulus fields take                       *)
(* idealized_p_minus_2, idealized_q_minus_2 == those two primes as the        *)
(*                              record's two modulus fields                   *)
(* idealized_pE, idealized_qE == the round trip from a modulus field back to  *)
(*                              its prime                                     *)
(* idealized_prime_p, idealized_prime_q, idealized_coprime_pq == primality    *)
(*                              and coprimality of the witness modulus        *)
(*     idealized_pq_instance == the idealized scheme at the composite         *)
(*                              modulus, as one DSDP instance                 *)
(*      idealized_card_plain == that instance's plaintext count is p * q      *)
(*  idealized_size_negligible == its inverse plaintext cardinalities are a    *)
(*                              negligible sequence                           *)
(*     idealized_pq_sequence == the sequence of those instances under the     *)
(*                              cipher-constant assumption                    *)
(*              val_Zp_pq1 == the unit residue of the composite modulus has   *)
(*                              natural number value one                      *)
(*         idealized_setting == the value of dsdp_setting the two sides below *)
(*                              make together, at Alice's honest query        *)
(*   idealized_honest_query == that query at every k                          *)
(*         corrupted_setting == the same value at Alice's corrupted query     *)
(*           corrupted_query == that query at every k                         *)
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

(* =================================================================          *)
(* The counting side of a run at one modulus                                  *)
(* =================================================================          *)

(* Set Strict Implicit brackets the record: {RV P -> A} unfolds to a function
   type whose domain mentions the record, so under the file's ambient Unset
   Strict Implicit every field would take the record value implicitly and
   V1 I would not typecheck. *)
Set Strict Implicit.

(* The counting side of a 3-party run at the fixed plaintext modulus
   a.+2 * b.+2, after du2002's scalar_product_random_inputs: one sample space
   with one law on it, the eleven random inputs of the run, their
   independence each against the joint of the other ten, and the uniformity
   of the three plaintext inputs and the two masks.
   The record is named for the counting side's reading of the eleven, where
   the weights and the keys are drawn together with the inputs; the hopping
   side of the same security parameter carries its own weights and keys as
   fixed values inside its scheme instance, and nothing relates the two. *)
Record dsdp_random_inputs (R : realType) (a b : nat) := {
  (* The sample space and the law on it: every random variable below is a
     function on this space and every bound is an average over this law. *)
  sampleT : finType ;
  sample_fdist : R.-fdist sampleT ;

  (* The entire randomness of a 3-party run at this modulus.  Every message
     and every party view is a deterministic function of these eleven, which
     is what lets a bound proved at the inputs transfer to a view. *)
  V1 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  V2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  V3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U1 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  R2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  R3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  Dk_a : {RV (sample_fdist) -> (Alice.-key Dec 'Z_(a.+2 * b.+2))} ;
  Dk_b : {RV (sample_fdist) -> (Bob.-key Dec 'Z_(a.+2 * b.+2))} ;
  Dk_c : {RV (sample_fdist) -> (Charlie.-key Dec 'Z_(a.+2 * b.+2))} ;

  (* Each input independent of the joint of the other ten, stated
     each-against-the-rest because every derived fact below is one of these
     pushed through inde_RV_comp. *)
  V1_indep : sample_fdist |=
    [% V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V1 ;
  V2_indep : sample_fdist |=
    [% V1, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V2 ;
  V3_indep : sample_fdist |=
    [% V1, V2, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V3 ;
  U1_indep : sample_fdist |=
    [% V1, V2, V3, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U1 ;
  U2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U2 ;
  U3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U3 ;
  R2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R3, Dk_a, Dk_b, Dk_c] _|_ R2 ;
  R3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, Dk_a, Dk_b, Dk_c] _|_ R3 ;
  Dk_a_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_b, Dk_c] _|_ Dk_a ;
  Dk_b_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_c] _|_ Dk_b ;
  Dk_c_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b] _|_ Dk_c ;

  (* Uniformity of R2 and R3 is what makes the relay bounds unconditional,
     one-time-pad masking rather than encryption hardness hiding V2 and V3;
     uniformity of V1, V2, V3 is what makes the conditional entropy equal
     log m rather than merely positive.  Alice's three weights carry no law:
     they are her chosen query, not a sample. *)
  pV1_unif : `p_ V1 = fdist_uniform (card_Zp_pq a b) ;
  pV2_unif : `p_ V2 = fdist_uniform (card_Zp_pq a b) ;
  pV3_unif : `p_ V3 = fdist_uniform (card_Zp_pq a b) ;
  pR2_unif : `p_ R2 = fdist_uniform (card_Zp_pq a b) ;
  pR3_unif : `p_ R3 = fdist_uniform (card_Zp_pq a b) }.
Unset Strict Implicit.

(* =================================================================          *)
(* The setting                                                                *)
(* =================================================================          *)

(* The data a 3-party DSDP security statement is made over, at every security
   parameter at once: the plaintext modulus as two primes, one counting side
   per security parameter at that modulus, and the sequence of scheme
   instances the hopping bounds are stated at.  A value of it is a setting,
   not a proof.
   The two axes share one number, not one execution: card_plain equates two
   cardinalities and nothing identifies the two message spaces, so the
   weights and the keys occur twice as unrelated objects, as random variables
   inside inputs and as values inside instance_sequence.
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

  (* The counting side of the run at k, at the modulus the two prime fields
     give there.  The sample spaces at distinct k are unrelated, as the
     scheme instances at distinct k already are. *)
  inputs : forall k, dsdp_random_inputs R (p_minus_2 k) (q_minus_2 k) }.

(* =================================================================          *)
(* Alice's query                                                              *)
(* =================================================================          *)

Section dsdp_query_records.
Context {R : realType}.

(* The condition on Alice's query weights at k under which her conditional
   entropy about the relay pair is exactly log m: her weight on Charlie's
   input is a nonzero residue below both prime factors, hence invertible
   modulo the composite modulus, which is what leaves the relay pair uniform
   on the fiber her leaked output cuts. *)
Record dsdp_honest_query (X : dsdp_setting R) (k : nat) := {
  U3_gt0 : forall t, (0 < U3 (inputs X k) t)%N ;
  U3_lt_minn : forall t,
    (U3 (inputs X k) t < minn (p_minus_2 X k).+2 (q_minus_2 X k).+2)%N }.

(* The choice of Alice's query weights at k under which the protocol output
   is Bob's input itself, the basis vector e_1: the leakage theorem is stated
   at this query, and it is what makes that theorem's zero conditional
   entropy a statement about a query rather than about an encryption. *)
Record dsdp_corrupted_query (X : dsdp_setting R) (k : nat) := {
  U2_eq1 : U2 (inputs X k) = (fun _ => 1) ;
  U3_eq0 : U3 (inputs X k) = (fun _ => 0) }.

End dsdp_query_records.

(* No value of dsdp_random_inputs satisfies both records at one k, since
   U3 = 0 falls outside the honest range.  That is why the two conditions are
   premises of two different results rather than fields of the setting: as a
   field, either one would make the other result vacuous. *)

(* =================================================================          *)
(* The laws of one setting at one security parameter                          *)
(* =================================================================          *)

Section dsdp_setting_laws.
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

(* The counting side of the run at k, the record the eleven input names
   below are read off. *)
Local Notation I := (inputs X k).
Local Notation P := (sample_fdist I).
Local Notation V1 := (V1 I).
Local Notation V2 := (V2 I).
Local Notation V3 := (V3 I).
Local Notation U1 := (U1 I).
Local Notation U2 := (U2 I).
Local Notation U3 := (U3 I).
Local Notation R2 := (R2 I).
Local Notation R3 := (R3 I).
Local Notation Dk_a := (Dk_a I).
Local Notation Dk_b := (Dk_b I).
Local Notation Dk_c := (Dk_c I).

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
  (V3_indep I).
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
rewrite /VarRV (inde_dist_of_RV2 V2_indep_V3) (pV2_unif I) (pV3_unif I).
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
    (V2_indep I).
  by rewrite /comp_RV /= in h *.
- have h := inde_RV_comp
    (fun w : rest10 => ((((w.1.1.1.1.1.1.1.1.1, w.1.1.1.1.1.1.1.2),
                          w.1.1.1.1.1.1.2), w.1.1.1.1.1.2),
                        w.1.1.1.1.1.1.1.1.2)) idfun
    (V3_indep I).
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
  idfun (V1_indep I).
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
  idfun (V1_indep I).
by rewrite /comp_RV /D3 /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* Alice's second mask is independent of Charlie's weighted input and of
   Charlie's input itself, the R3 field projected onto that pair.  R3 is the
   pad that hides V3 from Bob. *)
Lemma R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.2)) idfun (R3_indep I).
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
                        + w.1.1.1.1.2)) idfun (V3_indep I).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hu3 : P |= [% [% Dk_b, V2, D2], V3] _|_ U3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.1.2), w.1.1.1.1.1.1.1.2))
    idfun (U3_indep I).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hr3 : P |= [% [% Dk_b, V2, D2], [% V3, U3]] _|_ R3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.2), (w.1.1.1.1.1.1.1.2,
                                        w.1.1.1.1.2)))
    idfun (R3_indep I).
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
                      w.1.1.1.1.1.1.1.1.2)) idfun (R2_indep I).
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
                       w.1.1.1.1.1.1.1.1.2))) idfun (R2_indep I).
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
  by rewrite (pR2_unif I); congr fdist_uniform; exact: eq_irrelevance.
have r2_rest : P |= R2 _|_ [% VU2, [% VU3R, [% [% Dk_c, V3], V2]]].
  have h := inde_RV_comp
    (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                        (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                         ((w.2, w.1.1.1.1.1.1.1.2),
                          w.1.1.1.1.1.1.1.1.2)))) idfun (R2_indep I).
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
  (V2_indep I).
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
(* The hopping objects of one setting at one security parameter               *)
(* =================================================================          *)

(* Each declaration below names an object of the hopping axis at the k-th
   instance of the sequence X carries, so that a bound of dsdp_alice_hop_
   secrecy.v or dsdp_alice_trace_link.v can be stated over a setting without
   the instance's fifteen projections being written out at every use. *)
Section dsdp_hopping_views.
Local Unset Implicit Arguments.
Context {R : realType}.
Variable X : dsdp_setting R.
Variable k : nat.

Local Notation Inst := (sequence_instance (instance_sequence X) k).
Local Notation AHE := (inst_AHE Inst).
Local Notation Renc := (inst_renc Inst).
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

(* The scheme packaging at the k-th instance, and its coin index type. *)
Definition AHE_at : AHEncType := AHE.
Definition Renc_at : finType := Renc.

(* The five carriers the hopping bounds quantify predictors over, at the k-th
   instance. *)
Definition hop_tupleT_at : finType := alice_hop_tupleT AHE Renc.
Definition hop_jointT_at : finType := alice_hop_jointT AHE Renc.
Definition viewT_at : finType := alice_viewT AHE Renc.
Definition traceT_at : finType := alice_traceT AHE.
Definition trace_jointT_at : finType := trace_jointT AHE.

(* The corrupted-Alice sample space at the k-th instance, and the two honest
   relay inputs on it. *)
Definition hop_fdist_at : R.-fdist (alice_sampleT AHE Renc) :=
  alice_sample_fdist (R:=R) AHE card_renc.
Definition hop_V2_at : {RV hop_fdist_at -> plain AHE} :=
  sample_V2 (R:=R) (AHE:=AHE) card_renc.
Definition hop_V3_at : {RV hop_fdist_at -> plain AHE} :=
  sample_V3 (R:=R) (AHE:=AHE) card_renc.

(* The three conditioners of the hopping ladder at the k-th instance: its
   real endpoint, its all-zero endpoint, and Alice's whole view. *)
Definition AliceRealTuple_at : {RV hop_fdist_at -> hop_tupleT_at} :=
  alice_tuple_real (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_party
    v1 u1 u2 u3.
Definition AliceAllZeroTuple_at : {RV hop_fdist_at -> hop_tupleT_at} :=
  alice_tuple_all_zero (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_party
    v1 u1 u2 u3.
Definition AliceView_at : {RV hop_fdist_at -> viewT_at} :=
  AliceView (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_party
    v1 u1 u2 u3.

(* Alice's executed trace at the k-th instance, the conditioner the trace
   bounds read, and the output she leaks there. *)
Definition AliceTrace_at : {RV hop_fdist_at -> traceT_at} :=
  AliceTrace (R:=R) (AHE:=AHE) card_renc rand_of_renc
    v1 u1 u2 u3 dk_a dk_b dk_c rb2 rc2.
Definition Sout_at : {RV hop_fdist_at -> plain AHE} :=
  Sout (R:=R) (AHE:=AHE) card_renc v1 u1 u2 u3.

(* The two public keys the ladder prices its hops at, at the k-th instance. *)
Definition bob_pkey_at : pub_key AHE := bob_pkey pkey_of_party.
Definition charlie_pkey_at : pub_key AHE := charlie_pkey pkey_of_party.

(* The simulator's law at the k-th instance, at the hopping tuple and at the
   executed trace. *)
Definition alice_ideal_joint_at : R.-fdist hop_jointT_at :=
  alice_ideal_joint (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_party
    v1 u1 u2 u3.
(* Naming: the [trace] variant of alice_ideal_joint_at, the same simulator
   law read at the executed trace rather than at the hopping tuple. *)
Definition alice_trace_ideal_joint_at : R.-fdist trace_jointT_at :=
  alice_trace_ideal_joint (R:=R) card_renc rand_of_renc
    v1 u1 u2 u3 dk_a dk_b dk_c rc2.

(* The IND-CPA assumption type at the k-th instance, and the assumption the
   sequence itself makes there. *)
Definition indcpa_assumptionT_at : Type :=
  indcpa_epsilon_assumption (R:=R) (AHE:=AHE) card_renc rand_of_renc.
Definition assumption_at : indcpa_assumptionT_at :=
  sequence_assumption (instance_sequence X) k.

End dsdp_hopping_views.

(* =================================================================          *)
(* The counting views of one setting at one security parameter                *)
(* =================================================================          *)

(* The three views of the counting axis at the inputs X carries at k, each
   the axis definition of its own file applied to those eleven inputs. *)
Section dsdp_counting_views.
Local Unset Implicit Arguments.
Context {R : realType}.
Variable X : dsdp_setting R.
Variable k : nat.

Local Notation I := (inputs X k).
Local Notation V1 := (V1 I).
Local Notation V2 := (V2 I).
Local Notation V3 := (V3 I).
Local Notation U1 := (U1 I).
Local Notation U2 := (U2 I).
Local Notation U3 := (U3 I).
Local Notation R2 := (R2 I).
Local Notation R3 := (R3 I).
Local Notation Dk_a := (Dk_a I).
Local Notation Dk_b := (Dk_b I).
Local Notation Dk_c := (Dk_c I).

(* Bob's full real view at the inputs of X at k. *)
Definition BobView_at := BobView V2 V3 U2 U3 R2 R3 Dk_b.

(* Charlie's full real view at the inputs of X at k. *)
Definition CharlieView_at := CharlieView V2 V3 U2 U3 R2 R3 Dk_c.

(* Alice's full real view in the dot-product model at the inputs of X at k. *)
Definition AliceDotpView_at :=
  AliceDotpView V1 V2 V3 U1 U2 U3 R2 R3 Dk_a.

End dsdp_counting_views.

(* =================================================================          *)
(* The counting side is inhabited at every modulus                            *)
(* =================================================================          *)

(* The counting side at any modulus, with Alice's query weights held at three
   values of her choosing: the three plaintext inputs and the two masks are
   the five coordinates of a uniformly drawn row vector, and the three
   weights and the three private keys are constants of the sample space.
   Constant weights are what give the two query records values.  A weight
   drawn uniformly takes the value zero somewhere on the sample space, and
   the honest query asks for a weight invertible at every sample, so no
   setting whose weights are sampled satisfies either query record. *)
Section dsdp_inputs_uniform.
Local Open Scope vec_ext_scope.
Context {R : realType}.
Local Unset Implicit Arguments.

Local Notation ord5 j := (@Ordinal 5 j erefl).
Local Notation ord4 j := (@Ordinal 4 j erefl).
Local Notation msg a b := ('Z_(a.+2 * b.+2)).

(* The plaintext count at this modulus, in the form fdist_uniform takes its
   argument. *)
Definition uniform_card_msg (a b : nat) : #|msg a b| = (a.+2 * b.+2)%N :=
  card_Zp_pq a b.

Lemma uniform_card_sample (a b : nat) :
  #|'rV[msg a b]_5| = (((a.+2 * b.+2) ^ 5).-1).+1.
Proof. by rewrite card_mx mul1n (uniform_card_msg a b) prednK. Qed.

Lemma uniform_card_rest (a b : nat) :
  #|'rV[msg a b]_4| = (((a.+2 * b.+2) ^ 4).-1).+1.
Proof. by rewrite card_mx mul1n (uniform_card_msg a b) prednK. Qed.

Definition uniform_sampleT (a b : nat) : finType := 'rV[msg a b]_5.

Definition uniform_sample_fdist (a b : nat) : R.-fdist (uniform_sampleT a b) :=
  fdist_uniform (uniform_card_sample a b).

Local Notation P a b := (uniform_sample_fdist a b).

Definition uniform_coord (a b : nat) (i : 'I_5) : {RV (P a b) -> msg a b} :=
  fun v => v ``_ i.

Definition uniform_rest (a b : nat) (i : 'I_5) :
    {RV (P a b) -> 'rV[msg a b]_4} :=
  rV_drop i.

Lemma uniform_split (a b : nat) (i : 'I_5) :
  [/\ P a b |= uniform_rest a b i _|_ uniform_coord a b i,
      `p_ (uniform_rest a b i) = fdist_uniform (uniform_card_rest a b)
    & `p_ (uniform_coord a b i) = fdist_uniform (uniform_card_msg a b)].
Proof.
have bij_split : bijective (fun t => (uniform_rest a b i t,
                                      uniform_coord a b i t)).
  exact: (rV_split_bij (msg a b) i).
exact: (uniform_bij_indep (uniform_card_rest a b) (uniform_card_msg a b)
          bij_split).
Qed.

(* The rest-tuple seen from an input coordinate: the four remaining
   coordinates in their original order with the three weights and the three
   keys read off as constants. *)
Definition uniform_view_input (a b : nat) (w1 w2 w3 : msg a b)
    (w : 'rV[msg a b]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w1, w2, w3,
   w ``_ (ord4 2), w ``_ (ord4 3),
   @KeyOf Alice Dec (msg a b) 0, @KeyOf Bob Dec (msg a b) 0,
   @KeyOf Charlie Dec (msg a b) 0).

(* The same tuple seen from a mask coordinate, where the three weights sit
   after the three inputs rather than after two of them. *)
Definition uniform_view_mask (a b : nat) (w1 w2 w3 : msg a b)
    (w : 'rV[msg a b]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w ``_ (ord4 2), w1, w2, w3,
   w ``_ (ord4 3),
   @KeyOf Alice Dec (msg a b) 0, @KeyOf Bob Dec (msg a b) 0,
   @KeyOf Charlie Dec (msg a b) 0).

Definition uniform_V1 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 0).
Definition uniform_V2 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 1).
Definition uniform_V3 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 2).
Definition uniform_R2 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 3).
Definition uniform_R3 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 4).

Definition uniform_U1 (a b : nat) (w1 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w1.
Definition uniform_U2 (a b : nat) (w2 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w2.
Definition uniform_U3 (a b : nat) (w3 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w3.

Definition uniform_Dk_a (a b : nat) :
    {RV (P a b) -> (Alice.-key Dec (msg a b))} :=
  fun _ => @KeyOf Alice Dec _ 0.
Definition uniform_Dk_b (a b : nat) :
    {RV (P a b) -> (Bob.-key Dec (msg a b))} :=
  fun _ => @KeyOf Bob Dec _ 0.
Definition uniform_Dk_c (a b : nat) :
    {RV (P a b) -> (Charlie.-key Dec (msg a b))} :=
  fun _ => @KeyOf Charlie Dec _ 0.

Lemma uniform_V1_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V1 a b.
Proof.
have e0 : lift (ord5 0) (ord4 0) = ord5 1 by apply/val_inj.
have e1 : lift (ord5 0) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 0) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 0) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 0).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 0).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V2 a b.
Proof.
have e0 : lift (ord5 1) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 1) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 1) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 1) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 1).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 1).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V3 a b.
Proof.
have e0 : lift (ord5 2) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 2) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 2) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 2) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 2).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 2).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_R2 a b.
Proof.
have e0 : lift (ord5 3) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 3) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 3) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 3) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
     uniform_U2 a b w2, uniform_U3 a b w3, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_mask a b w1 w2 w3 `o uniform_rest a b (ord5 3).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 3).
exact: inde_RV_comp (uniform_view_mask a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_R3 a b.
Proof.
have e0 : lift (ord5 4) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 4) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 4) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 4) (ord4 3) = ord5 3 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
     uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_mask a b w1 w2 w3 `o uniform_rest a b (ord5 4).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 4).
exact: inde_RV_comp (uniform_view_mask a b w1 w2 w3) idfun ind.
Qed.

(* The three weights and the three keys are constants, and a constant is
   independent of everything.  Six of the eleven each-against-the-rest fields
   are therefore discharged without touching the sample space. *)
Lemma uniform_U1_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U1 a b w1.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U2 a b w2.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U3 a b w3.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_a_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_Dk_a a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_b_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_c a b]
  _|_ uniform_Dk_b a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_c_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b]
  _|_ uniform_Dk_c a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_pV1_unif (a b : nat) :
  `p_ (uniform_V1 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 0). Qed.

Lemma uniform_pV2_unif (a b : nat) :
  `p_ (uniform_V2 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 1). Qed.

Lemma uniform_pV3_unif (a b : nat) :
  `p_ (uniform_V3 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 2). Qed.

Lemma uniform_pR2_unif (a b : nat) :
  `p_ (uniform_R2 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 3). Qed.

Lemma uniform_pR3_unif (a b : nat) :
  `p_ (uniform_R3 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 4). Qed.

(* The counting side at any modulus with the query held fixed: five
   coordinates of the plaintext ring drawn uniformly for the three inputs and
   the two masks, the three weights and the three keys constant. *)
Definition uniform_inputs (a b : nat) (w1 w2 w3 : msg a b) :
    dsdp_random_inputs R a b := {|
  sampleT := uniform_sampleT a b ;
  sample_fdist := uniform_sample_fdist a b ;
  V1 := uniform_V1 a b ;
  V2 := uniform_V2 a b ;
  V3 := uniform_V3 a b ;
  U1 := uniform_U1 a b w1 ;
  U2 := uniform_U2 a b w2 ;
  U3 := uniform_U3 a b w3 ;
  R2 := uniform_R2 a b ;
  R3 := uniform_R3 a b ;
  Dk_a := uniform_Dk_a a b ;
  Dk_b := uniform_Dk_b a b ;
  Dk_c := uniform_Dk_c a b ;
  V1_indep := uniform_V1_indep a b w1 w2 w3 ;
  V2_indep := uniform_V2_indep a b w1 w2 w3 ;
  V3_indep := uniform_V3_indep a b w1 w2 w3 ;
  U1_indep := uniform_U1_indep a b w1 w2 w3 ;
  U2_indep := uniform_U2_indep a b w1 w2 w3 ;
  U3_indep := uniform_U3_indep a b w1 w2 w3 ;
  R2_indep := uniform_R2_indep a b w1 w2 w3 ;
  R3_indep := uniform_R3_indep a b w1 w2 w3 ;
  Dk_a_indep := uniform_Dk_a_indep a b w1 w2 w3 ;
  Dk_b_indep := uniform_Dk_b_indep a b w1 w2 w3 ;
  Dk_c_indep := uniform_Dk_c_indep a b w1 w2 w3 ;
  pV1_unif := uniform_pV1_unif a b ;
  pV2_unif := uniform_pV2_unif a b ;
  pV3_unif := uniform_pV3_unif a b ;
  pR2_unif := uniform_pR2_unif a b ;
  pR3_unif := uniform_pR3_unif a b |}.

End dsdp_inputs_uniform.

(* =================================================================          *)
(* Two inhabitants, one per query                                             *)
(* =================================================================          *)

(* The setting record is inhabited, at each of Alice's two queries.  On both
   values the hopping side is the idealized scheme of idealized_ahe.v under
   the cipher-constant assumption, whose assumed advantage is zero at every
   k, so every hopping bound stated over them is its unconditional
   1/#|plain| term alone; the counting side is uniform_inputs at the two
   query weight choices, on which every counting bound is exact at
   log (p k * q k).
   Every declaration carries the idealized_ stem of the value it builds,
   since the record's own projections hold the bare names, with idealized_pq_
   on the two that would otherwise collide with idealized_instance and
   idealized_instance_sequence of dsdp_instance_sequence.v; prime_minus2K and
   val_Zp_pq1 are general facts and keep their bare names. *)
Section dsdp_setting_witness.
Context {R : realType}.

(* Every k-indexed declaration below is meant to be applied to its security
   parameter, so the index stays explicit rather than being inferred from a
   later argument. *)
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

(* The unit residue of the composite modulus has natural number value one,
   the modulus being written as a double successor in both factors.  It is
   what lets the honest range be read off Alice's unit weight by
   computation. *)
Lemma val_Zp_pq1 (a b : nat) :
  nat_of_ord (1%R : 'Z_(a.+2 * b.+2)) = 1%N.
Proof.
have m_gt1 : (1 < a.+2 * b.+2)%N by rewrite (leq_trans (ltnSn 1)) // leq_pmulr.
by rewrite -[1%R]/(1%:R : 'Z_(a.+2 * b.+2)) (val_Zp_nat m_gt1) modn_small.
Qed.

(* The setting the two sides make together at Alice's honest query e_3: the
   composite-modulus idealized sequence on the hopping side, the uniform
   five-coordinate law with weights 0, 0, 1 on the counting side, and
   card_plain joining them.  It is named for its hopping side, after
   idealized_instance_sequence of dsdp_instance_sequence.v, which it repeats
   at a plaintext ring the counting side can also be carried on. *)
Definition idealized_setting : dsdp_setting R := {|
  instance_sequence := idealized_pq_sequence ;
  p_minus_2 := idealized_p_minus_2 ;
  q_minus_2 := idealized_q_minus_2 ;
  prime_p := idealized_prime_p ;
  prime_q := idealized_prime_q ;
  coprime_pq := idealized_coprime_pq ;
  card_plain := idealized_card_plain ;
  inputs := fun k =>
    uniform_inputs (idealized_p_minus_2 k) (idealized_q_minus_2 k) 0 0 1 |}.

(* Alice's honest query holds at every k on that value: her weight on
   Charlie's input is the unit residue, which is above zero and below both
   prime factors since each is written as a double successor. *)
Definition idealized_honest_query (k : nat) :
    dsdp_honest_query idealized_setting k.
Proof.
split=> t.
- by rewrite val_Zp_pq1.
- by rewrite val_Zp_pq1 leq_min.
Qed.

(* The same value at Alice's corrupted query e_1: weights 0, 1, 0.  The
   hopping side is unchanged, since the two axes share a cardinality and not
   an execution, so nothing on the hopping side reads Alice's counting
   weights.  The value exists so that the leakage result, which is stated
   under dsdp_corrupted_query, has an instance where its premise holds. *)
Definition corrupted_setting : dsdp_setting R := {|
  instance_sequence := idealized_pq_sequence ;
  p_minus_2 := idealized_p_minus_2 ;
  q_minus_2 := idealized_q_minus_2 ;
  prime_p := idealized_prime_p ;
  prime_q := idealized_prime_q ;
  coprime_pq := idealized_coprime_pq ;
  card_plain := idealized_card_plain ;
  inputs := fun k =>
    uniform_inputs (idealized_p_minus_2 k) (idealized_q_minus_2 k) 0 1 0 |}.

(* Alice's corrupted query holds at every k on that value, its two weights
   being the two constants the record asks for. *)
Definition corrupted_query (k : nat) :
    dsdp_corrupted_query corrupted_setting k.
Proof. by split. Qed.

End dsdp_setting_witness.
