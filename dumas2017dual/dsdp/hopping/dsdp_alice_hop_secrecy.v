From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.
Require Export indcpa_game.
Require Import dsdp_instance.
Require Import epshop.

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, hopping axis                               *)
(*                                                                            *)
(* Corrupted-Alice secrecy for the three-party DSDP protocol, proved in       *)
(* infotheo over an explicit product sample space. The sample space carries   *)
(* the two honest inputs, Alice's two mask plaintexts, the randomness of the  *)
(* two hop encryptions and the randomness of Alice's two combines; uniformity *)
(* and independence of the coordinates are theorems of the product            *)
(* construction rather than hypotheses.  The section runs over one instance   *)
(* of dsdp_instance.v, whose fields are the scheme, Alice's input, the three  *)
(* protocol weights, the three private keys and the two second-hop coins; the *)
(* one algebraic assumption, that Charlie's weight is a unit of the plaintext *)
(* ring, is the field inst_u3_unit.                                           *)
(*                                                                            *)
(* Three experiments run from Alice's real view to the view whose two         *)
(* ciphertext slots both encrypt zero, one slot replaced at each step.  This  *)
(* file builds the state each replacement is challenged at and proves that    *)
(* the law of that state is a product of the coin the challenge consumes and  *)
(* a part independent of it.  Those product laws are what let a replacement   *)
(* be read as one real-or-zero challenge at one key, so the gap it spans is   *)
(* an IND-CPA advantage and nothing more.                                     *)
(*                                                                            *)
(* The all-zero endpoint is bounded by the one-degree-of-freedom solution     *)
(* fiber of the DSDP linear constraint: all_zero_guess_V2_le_invm confines a  *)
(* predictor reading Alice's all-zero tuple to that fiber, and its bound is   *)
(* the one term of a DSDP guessing bound that rests on no computational       *)
(* assumption.  alice_simulator builds that all-zero tuple from the leaked    *)
(* output alone and alice_ideal is the joint law of the honest inputs beside  *)
(* it, so the ideal world a simulation statement is written against is the    *)
(* all-zero experiment.                                                       *)
(*                                                                            *)
(* The two entropy readings and the guessing bound at the all-zero endpoint   *)
(* descend from one fact, alice_V2_cond_Sout: the conditional law of Bob's    *)
(* input given the leaked output is uniform.  Neither is derived from the     *)
(* other, and they measure different things, an averaged conditional entropy  *)
(* against a bound on a probability.  Both entropy readings hold at their own *)
(* conditioner.  At Alice's executed trace the same quantity is zero, which   *)
(* centropy_V2_trace_eq0 of dsdp_alice_trace_link.v records.                  *)
(*                                                                            *)
(* ## Game vocabulary                                                         *)
(*                                                                            *)
(* The real-or-zero game layer and the reduction wiring live in               *)
(* computational_security/indcpa_game.v, whose header carries                 *)
(* the full role map.  The names this file plays those roles with are         *)
(*                                                                            *)
(* | role          | identifier                                             | *)
(* |---------------|--------------------------------------------------------| *)
(* | adversary     | indcpa_adversary                                       | *)
(* | challenger    | indcpa_challenger                                      | *)
(* | experiment    | indcpa_experiment                                      | *)
(* | advantage     | indcpa_epsilon                                         | *)
(* | distinguisher | distinguisher_of_predictor predict                     | *)
(*                                                                            *)
(* ## Terminology: law and distribution                                       *)
(*                                                                            *)
(* Both words name one object, the pushforward of the sample-space measure    *)
(* along a random variable: for X : Omega -> S on (Omega, F, P),              *)
(* L_X(B) = P(X^-1(B)) = P(X in B), that is L_X = X_*P.  Wikipedia,           *)
(* Random variable, section Measure-theoretic definition, records the         *)
(* synonymy:                                                                  *)
(*                                                                            *)
(*   > The measure p_X is called the '(probability) distribution of X' or     *)
(*   > the 'law of X'.                                                        *)
(*                                                                            *)
(* Both spellings appear below and denote that measure.  Its type is          *)
(* infotheo's R.-fdist, which probability/fdist.v documents as the type of    *)
(* distributions over a finType T.                                            *)
(*                                                                            *)
(* The word law names two further things in nearby code.  In the MathComp     *)
(* interfaces SemiGroup.law, Monoid.law, com_law, mul_law and add_law, a      *)
(* law is an associativity, identity, absorption or distributivity axiom.     *)
(* In the law of total probability and the weak law of large numbers, a       *)
(* law is a named theorem.  A distribution function F_X(r) = L_X(]-oo, r])    *)
(* represents L_X on the real line.                                           *)
(*                                                                            *)
(* ## The state variants                                                      *)
(*                                                                            *)
(* The tuples below flatten nested product types while preserving coordinate  *)
(* order.  The full sample is                                                 *)
(*                                                                            *)
(*   (V2, V3, R2, R3, EncCoins).                                              *)
(*                                                                            *)
(* V2 is Bob's input, and V3 is Charlie's input.                              *)
(* R2 and R3 are Alice's first and second mask plaintexts.                    *)
(* Section dsdp_alice_hop_secrecy reads those four plaintext coordinates as   *)
(* V2, V3, R2 and R3.  Their global names are sample_V2, sample_V3, sample_R2 *)
(* and sample_R3.                                                             *)
(* EncCoins is the record of the six coins the run draws.  RB1 and RC1 are    *)
(* the coins of the ciphertexts Alice receives, RA1 and RA2 the coins of her  *)
(* two combines, RB2 Bob's second-hop coin, and RC2 Charlie's re-encryption   *)
(* coin.                                                                      *)
(*                                                                            *)
(* Hop0State                                                                  *)
(*   (V2, V3, R2, R3, RA1, RA2, RC1, RB2, RC2)                                *)
(*   State for the Bob challenge.  The challenge supplies Bob's ciphertext,   *)
(*   while RC1 constructs Charlie's real ciphertext and RC2 his               *)
(*   re-encryption.                                                           *)
(*                                                                            *)
(* Hop1StatePre                                                               *)
(*   (V2, V3, R2, R3, RA1, RA2, RB1, RB2, RC2)                                *)
(*   Pre-encryption form of Hop1State.  hop1_state_of encrypts zero using     *)
(*   RB1 and stores the resulting Bob ciphertext.                             *)
(*                                                                            *)
(* Hop1State                                                                  *)
(*   (V2, V3, R2, R3, RA1, RA2, RC2, bob_zero_cipher)                         *)
(*   State for the Charlie challenge.  The challenge supplies Charlie's       *)
(*   ciphertext, while bob_zero_cipher supplies Bob's zero ciphertext.        *)
(*                                                                            *)
(* AliceSpectatorPre                                                          *)
(*   (R2, R3, EncCoins)                                                       *)
(*   The sample coordinates other than the two secret inputs.  Their joint    *)
(*   law is independent of (V2, V3) and is the law the simulator draws from.  *)
(*                                                                            *)
(* ```                                                                        *)
(* One protocol run and its hops                                              *)
(*                                                                            *)
(*             alice_sampleT == all honest inputs and random choices in one   *)
(*                              DSDP run                                      *)
(*        alice_sample_fdist == samples those values uniformly and            *)
(*                              independently                                 *)
(*      sample_V2, sample_V3 == Bob's and Charlie's honest inputs             *)
(*    bob_pkey, charlie_pkey == the two relay public keys selected from the   *)
(*                              party key table                               *)
(*      sample_R2, sample_R3 == the masks Alice adds to her two combines      *)
(*                  EncCoins == the six encryption coins of the run           *)
(*                  RB1, RC1 == the coins for the ciphertexts Alice receives  *)
(*                              from Bob and Charlie                          *)
(*                  RA1, RA2 == the encryption coins for Alice's two combines *)
(*                  RB2, RC2 == Bob's second-hop coin and Charlie's           *)
(*                              re-encryption coin                            *)
(*      charlie_reenc_cipher == Charlie's re-encryption of the aggregate      *)
(*                              under Alice's key, the slot no hop replaces   *)
(*                      Sout == the weighted output that Alice is allowed to  *)
(*                              learn                                         *)
(* bob_real_cipher, bob_zero_cipher == Bob's ciphertext slot carrying his     *)
(*                              input and carrying zero, under one coin       *)
(* charlie_real_cipher, charlie_zero_cipher == the same two slots at          *)
(*                              Charlie's key and coin                        *)
(*          alice_hop_tupleT == the core information used to study Alice's    *)
(*                              secrecy                                       *)
(*         alice_tuple_real == Alice's tuple as her protocol run produces it, *)
(*                              both ciphertext slots real                    *)
(*     alice_tuple_bob_zero == the same tuple with Bob's slot carrying zero   *)
(*     alice_tuple_all_zero == the tuple with both slots carrying zero        *)
(*                                                                            *)
(* The two ciphertext changes and the states they are challenged at           *)
(*                                                                            *)
(*    hop0_stateT, Hop0State == everything needed to rebuild Alice's value    *)
(*                              except Bob's challenge ciphertext             *)
(*    hop1_stateT, Hop1State == everything needed to rebuild Alice's value    *)
(*                              except Charlie's challenge ciphertext         *)
(*              Hop1StatePre == the hop-1 state before Bob's zero ciphertext  *)
(*                              is constructed                                *)
(*             hop1_state_of == constructs Bob's zero ciphertext and          *)
(*                              completes the hop-1 state                     *)
(*             hop0_assemble == builds the complete value given to D around   *)
(*                              Bob's challenge ciphertext                    *)
(*             hop1_assemble == builds the complete value given to D around   *)
(*                              Charlie's challenge ciphertext                *)
(*                                                                            *)
(* The all-zero endpoint and guessing                                         *)
(*                                                                            *)
(*        V1c, U1c, U2c, U3c == Alice's input and the three protocol weights  *)
(*                              as fixed random variables                     *)
(*      alice_spectator_preT == the secret-independent random choices used    *)
(*                              to construct the all-zero endpoint            *)
(*         AliceSpectatorPre == those random choices in one sampled run       *)
(*            AliceSpectator == the non-output fields of the all-zero hopping *)
(*                              tuple                                         *)
(*        alice_spectator_of == constructs those fields without the honest    *)
(*                              inputs                                        *)
(* alice_hop_tuple_of_spectator == combines the spectator and leaked output   *)
(*                              into the all-zero hopping tuple               *)
(* distinguisher_of_predictor predict ==                                      *)
(*                              accepts exactly when the predictor            *)
(*                              recovers Bob's input                          *)
(* all_zero_guess_V2_le_invm == a predictor reading Alice's all-zero tuple    *)
(*                              returns Bob's input at most as often as the   *)
(*                              inverse plaintext-space cardinality           *)
(*                                                                            *)
(* Simulation                                                                 *)
(*                                                                            *)
(*         alice_simulator s == constructs the all-zero view from the leaked  *)
(*                              output s, fresh masks, fresh coins, and two   *)
(*                              encryptions of zero                           *)
(*     alice_spectator_pre2T == the spectator choices reordered to separate   *)
(*                              the two encryption coins                      *)
(*        AliceSpectatorPre2 == those reordered choices in one sampled run    *)
(*   alice_spectator_regroup == performs that coordinate reordering           *)
(*      alice_spectator_prod == constructs the spectator from the reordered   *)
(*                              choices                                       *)
(* alice_spectator_of_hop_tuple == removes the leaked output from a hopping   *)
(*                              tuple                                         *)
(* alice_hop_tuple_of_spectatorK ==                                           *)
(*                              assembling the spectator with the leaked      *)
(*                              output loses neither                          *)
(*    centropy_V2_Sout_logm == the leaked output alone leaves Bob's input as  *)
(*                              uncertain as it was                           *)
(* centropy_V2_all_zero_logm == Alice's all-zero view leaves the same         *)
(*                              uncertainty, so the Shannon statement is      *)
(*                              non-degenerate at that endpoint               *)
(*               alice_ideal == samples the honest inputs and then simulates  *)
(*                              Alice's tuple from their leaked output        *)
(*                                                                            *)
(* Separate facts about encryption distributions                              *)
(*                                                                            *)
(*        enc_of_renc pk v r == maps an encryption-randomness index to the    *)
(*                              resulting ciphertext                          *)
(*     card_enc_img_gt0 pk v == at least one ciphertext encrypting v is       *)
(*                              reachable                                     *)
(* enc_fdist_uniform_img pk v == every reachable encryption of v has the same *)
(*                              probability                                   *)
(* enc_fdist_uniform_img_fiber == this uniformity follows when every          *)
(*                              reachable ciphertext has the same number of   *)
(*                              randomness indices                            *)
(* enc_fdist_uniform_img_inj == injective encryption randomness is a          *)
(*                              sufficient special case                       *)
(*    enc_fdist_uniform_imgE == each reachable ciphertext then has            *)
(*                              probability one divided by the number of      *)
(*                              reachable ciphertexts                         *)
(* ```                                                                        *)
(*                                                                            *)
(* Bob's and Charlie's inputs are sampled uniformly, so these results         *)
(* describe average-case secrecy over their inputs. Each hop uses one         *)
(* real-or-zero challenge at one fixed public key.                            *)
(* The guessing bound is nontrivial only while its complete right-hand side   *)
(* is below 1. The formal adversary has no running-time model.                *)
(* Computational efficiency remains an external assumption.                   *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_hop_secrecy.
Context {R : realType}.
Variable I : dsdp_instance.
(* The scheme, its coin space, the coin-space cardinality and the coin
   decoding.  All four are read off the instance through the coercion. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation card_renc := (scheme_card_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation pkey_of_party := (inst_pkey_of_party I).
(* Alice's input and the three protocol weights, with Charlie's weight
   invertible.  These are instance fields, under the names the DSDP protocol
   gives them. *)
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation u3_unit := (inst_u3_unit I).

Let u3_inj : injective (fun v : plain AHE => u3 * v) := mulrI u3_unit.

Let card_plain_gt0 : (0 < #|plain AHE|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.
Let card_plain : #|plain AHE| = #|plain AHE|.-1.+1.
Proof. by rewrite prednK. Qed.
Let card_plain_pair :
  #|((plain AHE * plain AHE)%type : finType)|
    = (#|plain AHE| * #|plain AHE|)%N.-1.+1.
Proof. by rewrite card_prod prednK // muln_gt0 card_plain_gt0. Qed.
Let card_renc_gt0 : (0 < #|Renc|)%N.
Proof. by rewrite card_renc. Qed.
Let card_renc_pair :
  #|((Renc * Renc)%type : finType)|
    = (#|Renc| * #|Renc|)%N.-1.+1.
Proof. by rewrite card_prod prednK // muln_gt0 card_renc_gt0. Qed.

(* The public key hop 0 challenges at, Bob's key read from the instance's key
   table.  Each hop challenges at one key, so the two advantage terms are
   attributed to separate keys. *)
Definition bob_pkey : pub_key AHE := pkey_of_party Bob.

(* The key hop 1 challenges at, the Charlie-key counterpart of bob_pkey.      *)
Definition charlie_pkey : pub_key AHE := pkey_of_party Charlie.

(* Alice's own key, the one Charlie re-encrypts the aggregate under.  No hop
   challenges at it, since Alice holds the matching private key. *)
Definition alice_pkey : pub_key AHE := pkey_of_party Alice.

Local Notation enc_fdist := (enc_fdist (R:=R) (S:=I)).
Local Notation indcpa_adversary := (indcpa_adversary (R:=R) I).
Local Notation indcpa_success_real := (indcpa_success_real (R:=R) (S:=I)).
Local Notation indcpa_success_zero := (indcpa_success_zero (R:=R) (S:=I)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation indcpa_fdist_acceptE := (indcpa_fdist_acceptE (R:=R) (S:=I)).
Local Notation predictor := (predictor I).

(* The sample space of the corrupted-Alice experiment: two honest inputs, two
   masks, and the run's six coins.  The programs draw those coins, so the
   instance pins none of them. *)
Definition alice_sampleT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * dsdp_enc_coins I)%type.

(* The uniform product distribution on the sample space. *)
Definition alice_sample_fdist : R.-fdist alice_sampleT :=
  ((fdist_uniform card_plain_pair) `x (fdist_uniform card_plain_pair))
    `x (dsdp_enc_coins_fdist I R).

(* Bob's honest input, the first plaintext coordinate of the sample.  Every
   bound in this file is stated about it. *)
Definition sample_V2 : {RV alice_sample_fdist -> plain AHE} :=
  fun t => t.1.1.1.
(* Charlie's honest input, the second plaintext coordinate of the sample.  It
   is the other unknown of the affine equation the leaked output reveals. *)
Definition sample_V3 : {RV alice_sample_fdist -> plain AHE} :=
  fun t => t.1.1.2.
(* Alice's mask on the first combine, the third plaintext coordinate of the
   sample. *)
Definition sample_R2 : {RV alice_sample_fdist -> plain AHE} :=
  fun t => t.1.2.1.
(* Alice's mask on the second combine, the fourth plaintext coordinate of the
   sample. *)
Definition sample_R3 : {RV alice_sample_fdist -> plain AHE} :=
  fun t => t.1.2.2.

(* The four plaintext coordinates under their protocol names, for the rest of
   this section. *)
Local Notation V2 := sample_V2.
Local Notation V3 := sample_V3.
Local Notation R2 := sample_R2.
Local Notation R3 := sample_R3.

(* The six coins the run draws, as one random variable. *)
Definition EncCoins : {RV alice_sample_fdist -> dsdp_enc_coins I} :=
  fun t => t.2.

(* The randomness of the ciphertext Alice receives from Bob, and the randomness
   the hop-0 challenger takes over. *)
Definition RB1 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_rb1 (EncCoins t).
(* The randomness of the ciphertext Alice receives from Charlie, and the
   randomness the hop-1 challenger takes over. *)
Definition RC1 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_rc1 (EncCoins t).
(* The randomness of Alice's first combine. *)
Definition RA1 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_ra1 (EncCoins t).
(* The randomness of Alice's second combine. *)
Definition RA2 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_ra2 (EncCoins t).
(* The randomness of Bob's encryption to Charlie. *)
Definition RB2 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_rb2 (EncCoins t).
(* The randomness of Charlie's re-encryption to Alice. *)
Definition RC2 : {RV alice_sample_fdist -> Renc} :=
  fun t => coin_rc2 (EncCoins t).

(* The protocol output Alice legitimately learns, the weighted scalar product
   of her weights with the two honest inputs. *)
Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry (dsdp_output v1 u1 u2 u3) `o [% V2, V3].

(* The leaked output written out as u1 * v1 + u2 * V2 + u3 * V3.  Alice learns
   one affine equation in the two secret inputs. *)
Lemma SoutE t : Sout t = u1 * v1 + u2 * V2 t + u3 * V3 t.
Proof. by []. Qed.

(* Bob's ciphertext slot of Alice's hopping tuple, carrying his real input.
   It is the encryption of V2 under Bob's key with Bob's own coin. *)
Definition bob_real_cipher : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc bob_pkey (V2 t) (rand_of_renc (RB1 t)).

(* The same slot carrying zero under the same coin.  Telling this slot from
   bob_real_cipher is the task the IND-CPA challenge at Bob's key sets. *)
Definition bob_zero_cipher : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc bob_pkey 0 (rand_of_renc (RB1 t)).

(* Charlie's ciphertext slot carrying his real input, the counterpart of
   bob_real_cipher at Charlie's key and coin. *)
Definition charlie_real_cipher : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc charlie_pkey (V3 t) (rand_of_renc (RC1 t)).

(* Charlie's slot carrying zero under the same coin. *)
Definition charlie_zero_cipher : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc charlie_pkey 0 (rand_of_renc (RC1 t)).

(* Charlie's re-encryption of the aggregate, as Alice receives it.  Its
   plaintext is the leaked output net of Alice's own term and masks, so no hop
   replaces it. *)
Definition charlie_reenc_cipher : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc alice_pkey (Sout t - u1 * v1 + R2 t + R3 t)
             (rand_of_renc (RC2 t)).

(* The type of Alice's hopping tuple: two masks, two combine randomnesses,
   the leaked output, two received ciphertexts, and Charlie's re-encryption. *)
Definition alice_hop_tupleT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * cipher AHE * cipher AHE * cipher AHE)%type.

(* Alice's hopping tuple with both ciphertext slots carrying their real
   plaintexts.  Her protocol run produces this tuple, and every bound of this
   file conditions on it. *)
Definition alice_tuple_real :
    {RV alice_sample_fdist -> alice_hop_tupleT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, bob_real_cipher, charlie_real_cipher,
     charlie_reenc_cipher].

(* The same tuple with Bob's slot carrying zero and Charlie's still real.  It
   is the zero side of the challenge at Bob's key and the real side at
   Charlie's. *)
Definition alice_tuple_bob_zero :
    {RV alice_sample_fdist -> alice_hop_tupleT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, bob_zero_cipher, charlie_real_cipher,
     charlie_reenc_cipher].

(* The tuple with both ciphertext slots carrying zero.  Here the leaked output
   is the only channel from the honest inputs into Alice's view. *)
Definition alice_tuple_all_zero :
    {RV alice_sample_fdist -> alice_hop_tupleT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, bob_zero_cipher, charlie_zero_cipher,
     charlie_reenc_cipher].

Let card_sample : #|alice_sampleT| = #|alice_sampleT|.-1.+1.
Proof. exact: fdist_card_prednK alice_sample_fdist. Qed.

(* The sample space carries the uniform distribution. *)
Lemma alice_sample_fdistE : alice_sample_fdist = fdist_uniform card_sample.
Proof.
apply/fdist_ext => -[[vv ms] c].
rewrite fdist_uniformE /alice_sample_fdist /dsdp_enc_coins_fdist.
rewrite !fdist_prodE !fdist_uniformE.
by rewrite -!invfM -!natrM /alice_sampleT !card_prod.
Qed.

(* The state bob_challenge_adversary holds at hop 0: the two inputs, Alice's
   masks, her combine coins, and the three coins no hop challenges.  RB1 is
   held by the challenger at this hop, which is why the state stops short of
   it. *)
Definition hop0_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * (Renc * Renc * Renc))%type.

(* The hop-0 state as a random variable on the sample space: everything
   bob_challenge_adversary holds before it queries the challenger. *)
Definition Hop0State : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1, t.1.2, (RA1 t, RA2 t), (RC1 t, RB2 t, RC2 t)).

Let card_hop0_state : #|hop0_stateT| = #|hop0_stateT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ Hop0State). Qed.

Let card_hop0_pair :
  #|((hop0_stateT * Renc)%type : finType)|
    = #|((hop0_stateT * Renc)%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% Hop0State, RB1]). Qed.

(* The hop-0 state and Bob's encryption randomness are jointly uniform on the
   product of their spaces.  So the challenger's randomness is uniform and
   independent of the reduction's data. *)
Lemma hop0_pair_uniformE :
  `p_ [% Hop0State, RB1]
    = (fdist_uniform card_hop0_state) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_state card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_stateT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2,
           {| coin_rb1 := p.2 ; coin_rc1 := p.1.2.1.1 ;
              coin_ra1 := p.1.1.2.1 ; coin_ra2 := p.1.1.2.2 ;
              coin_rb2 := p.1.2.1.2 ; coin_rc2 := p.1.2.2 |})).
  by move=> [[vv ms] [rb1 rc1 ra1 ra2 rb2 rc2]].
by move=> [[[[vv ms] [ra1 ra2]] [[rc1 rb2] rc2]] rb1].
Qed.

(* Bob's encryption randomness is uniform and independent of the hop-0 state,
   the freshness condition protocol_indcpa_fdistE consumes.  Bob draws that
   randomness independently of his own input and of the other parties'
   randomness. *)
Lemma hop0_state_prodE :
  `p_ [% Hop0State, RB1] = (`p_ Hop0State) `x (fdist_uniform card_renc).
Proof.
by rewrite -(fst_RV2 Hop0State RB1) !hop0_pair_uniformE fdist_prod1.
Qed.

(* The state charlie_challenge_adversary holds at hop 1: the two inputs, Alice's
   masks, her combine randomness, and Bob's already-zeroed ciphertext.  Bob's
   slot is fixed data at this hop, and Charlie's encryption randomness is what
   the challenger owns. *)
Definition hop1_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * Renc * cipher AHE)%type.

(* The hop-1 state as a random variable.  It is what
   charlie_challenge_adversary holds after Bob's slot is zeroed, before it
   queries Charlie's challenger. *)
Definition Hop1State : {RV alice_sample_fdist -> hop1_stateT} :=
  fun t => (t.1.1, t.1.2, (RA1 t, RA2 t), RC2 t, bob_zero_cipher t).

(* The hop-1 state with Bob's encryption randomness in place of the ciphertext
   it produces.  Uniformity holds at this layout, and hop1_state_of carries it
   to Hop1State. *)
Definition Hop1StatePre : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1, t.1.2, (RA1 t, RA2 t), (RB1 t, RB2 t, RC2 t)).

(* The map carrying Hop1StatePre to Hop1State, encrypting zero in the
   hop-0 slot. *)
Definition hop1_state_of (c : hop0_stateT) : hop1_stateT :=
  (c.1.1.1, c.1.1.2, c.1.2, c.2.2,
   enc bob_pkey 0 (rand_of_renc c.2.1.1)).

(* The hop-1 state before encryption and the hop-1 encryption randomness are
   jointly uniform. *)
Lemma hop1_state_pre_pair_uniformE :
  `p_ [% Hop1StatePre, RC1]
    = (fdist_uniform card_hop0_state) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_state card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_stateT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2,
           {| coin_rb1 := p.1.2.1.1 ; coin_rc1 := p.2 ;
              coin_ra1 := p.1.1.2.1 ; coin_ra2 := p.1.1.2.2 ;
              coin_rb2 := p.1.2.1.2 ; coin_rc2 := p.1.2.2 |})).
  by move=> [[vv ms] [rb1 rc1 ra1 ra2 rb2 rc2]].
by move=> [[[[vv ms] [ra1 ra2]] [[rb1 rb2] rc2]] rc1].
Qed.

(* The hop-1 encryption randomness is uniform. *)
Lemma rc1_uniformE : `p_ RC1 = fdist_uniform card_renc.
Proof.
by rewrite -(snd_RV2 Hop1StatePre RC1) hop1_state_pre_pair_uniformE
   fdist_prod2.
Qed.

(* A joint law that factors as the product of its marginals is the law of an
   independent pair. *)
Lemma inde_RV_of_prod (A B : finType)
    (X : {RV alice_sample_fdist -> A}) (Y : {RV alice_sample_fdist -> B}) :
  `p_ [% X, Y] = (`p_ X) `x (`p_ Y) -> alice_sample_fdist |= X _|_ Y.
Proof. by move=> H a b; rewrite -!dist_of_RVE H fdist_prodE. Qed.

(* Charlie's encryption randomness is uniform and independent of the hop-1
   state.  It is the freshness condition at the second hop, read off
   Hop1StatePre through hop1_state_of. *)
Lemma hop1_state_prodE :
  `p_ [% Hop1State, RC1] = (`p_ Hop1State) `x (fdist_uniform card_renc).
Proof.
have Hpre : alice_sample_fdist |= Hop1StatePre _|_ RC1.
  apply: inde_RV_of_prod.
  by rewrite hop1_state_pre_pair_uniformE -(fst_RV2 Hop1StatePre RC1)
             hop1_state_pre_pair_uniformE fdist_prod1 rc1_uniformE.
have Hstate : alice_sample_fdist |= Hop1State _|_ RC1.
  exact: (inde_RV_comp hop1_state_of idfun Hpre).
by rewrite (inde_dist_of_RV2 Hstate) rc1_uniformE.
Qed.

(* The hop-0 value the distinguisher is given: ch in Bob's slot, Charlie's
   real ciphertext and Charlie's re-encryption from the stored coins.
   Here bob_challenge_adversary rebuilds D's input. *)
Definition hop0_assemble (c : hop0_stateT) (ch : cipher AHE) :
    plain AHE * plain AHE * alice_hop_tupleT :=
  (* bob_challenge_adversary D is the procedure that adapts D to the
     encryption experiment, hop0_assemble is the function that procedure uses
     to rebuild D's input, and D is the Boolean test on the rebuilt input.
     Applying D to the assembled value gives Pr[D(...) = 1]. *)
  let: (vv, masks, ra, coins) := c in
  let s := dsdp_output v1 u1 u2 u3 vv.1 vv.2 in
  (vv.1, vv.2,
   (masks, ra, s, ch,
    enc charlie_pkey vv.2 (rand_of_renc coins.1.1),
    enc alice_pkey (s - u1 * v1 + masks.1 + masks.2)
      (rand_of_renc coins.2))).

(* The tested hop-1 joint value formed by retaining Bob's stored zero
   ciphertext and placing ch in Charlie's ciphertext slot. *)
Definition hop1_assemble (c : hop1_stateT) (ch : cipher AHE) :
    plain AHE * plain AHE * alice_hop_tupleT :=
  let: (vv, masks, ra, rc2, c2zero) := c in
  let s := dsdp_output v1 u1 u2 u3 vv.1 vv.2 in
  (vv.1, vv.2,
   (masks, ra, s, c2zero, ch,
    enc alice_pkey (s - u1 * v1 + masks.1 + masks.2) (rand_of_renc rc2))).

(* Alice's own input as a constant random variable. *)
Definition V1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ v1.
(* Alice's first protocol weight as a constant random variable. *)
Definition U1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u1.
(* Alice's second protocol weight as a constant random variable. *)
Definition U2c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u2.
(* Alice's third protocol weight as a constant random variable. *)
Definition U3c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u3.

(* The sample coordinates besides the two secret inputs: Alice's two masks and
   the six encryption coins of the run. *)
Definition alice_spectator_preT : finType :=
  ((plain AHE * plain AHE) * dsdp_enc_coins I)%type.

(* The spectator coordinates as a random variable: the part of the sample
   Alice's view reads besides the two secret inputs. *)
Definition AliceSpectatorPre :
    {RV alice_sample_fdist -> alice_spectator_preT} :=
  fun t => ((R2 t, R3 t), EncCoins t).

Let card_spectator_pre :
  #|alice_spectator_preT| = #|alice_spectator_preT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceSpectatorPre). Qed.

Let card_spectator_pre_pair :
  #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|
  = #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% AliceSpectatorPre, [% V2, V3]]). Qed.

(* The spectator coordinates and the secret input pair are jointly uniform.   *)
Lemma spectator_pre_pair_uniformE :
  `p_ [% AliceSpectatorPre, [% V2, V3]]
    = (fdist_uniform card_spectator_pre) `x (fdist_uniform card_plain_pair).
Proof.
rewrite -(fdist_uniform_prod card_spectator_pre card_plain_pair
            card_spectator_pre_pair) /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_spectator_pre_pair).
exists (fun p : alice_spectator_preT * (plain AHE * plain AHE) =>
          (p.2, p.1.1, p.1.2)).
  by move=> [[[v2 v3] [r2 r3]] c].
by move=> [[[r2 r3] c] [v2 v3]].
Qed.

(* The spectator coordinates are uniform. *)
Lemma spectator_pre_uniformE :
  `p_ AliceSpectatorPre = fdist_uniform card_spectator_pre.
Proof.
by rewrite -(fst_RV2 AliceSpectatorPre [% V2, V3]) spectator_pre_pair_uniformE
           fdist_prod1.
Qed.

(* The two secret inputs are jointly uniform. *)
Lemma alice_var_uniform : `p_ [% V2, V3] = fdist_uniform card_plain_pair.
Proof.
by rewrite -(snd_RV2 AliceSpectatorPre [% V2, V3]) spectator_pre_pair_uniformE
           fdist_prod2.
Qed.

(* The spectator coordinates are independent of the two secret inputs.  The
   all-zero view can therefore be produced from public data alone. *)
Lemma spectator_pre_indep :
  alice_sample_fdist |= AliceSpectatorPre _|_ [% V2, V3].
Proof.
apply: inde_RV_of_prod.
by rewrite spectator_pre_pair_uniformE spectator_pre_uniformE alice_var_uniform.
Qed.

(* Alice's input and the three protocol weights form one constant random
   variable. *)
Lemma alice_inputs_constE :
  [% V1c, U1c, U2c, U3c]
  = const_RV alice_sample_fdist (v1, u1, u2, u3).
Proof. by apply: boolp.funext => t; rewrite /V1c /U1c /U2c /U3c !const_RVE. Qed.

(* The protocol weights, the leaked output and the two secret inputs satisfy the
   DSDP linear constraint pointwise. *)
Lemma alice_constraint_holds (t : alice_sampleT) :
  dsdp_constraint_ring ([% V1c, U1c, U2c, U3c, Sout] t) ([% V2, V3] t).
Proof.
by rewrite /dsdp_constraint_ring /Sout /comp_RV /dsdp_output /V1c /U1c /U2c /U3c
           /= !const_RVE; apply/eqP; ring.
Qed.

(* Conditioned on the protocol weights and the leaked output, the secret input
   pair is uniform on the solution fiber.  Each pair on that fiber has mass
   1/#|plain AHE|. *)
Lemma alice_VarRV_cond_uniform (s v2 v3 : plain AHE) :
  `Pr[ [% V1c, U1c, U2c, U3c, Sout] = (v1, u1, u2, u3, s) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
  `Pr[ [% V2, V3] = (v2, v3)
     | [% V1c, U1c, U2c, U3c, Sout] = (v1, u1, u2, u3, s) ]
  = #|plain AHE|%:R^-1.
Proof.
apply: Pr_dsdp_sol_uniform_ring => //;
  last by rewrite alice_inputs_constE; exact: inde_const_RV.
  exact: alice_constraint_holds.
by rewrite alice_var_uniform; congr fdist_uniform; exact: eq_irrelevance.
Qed.

(* Conditioned on the leaked output alone, Bob's input is uniform on the
   plaintext space. *)
Lemma alice_V2_cond_Sout (a s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ V2 = a | Sout = s ] = #|plain AHE|%:R^-1.
Proof.
move=> Hs.
have [g _ Hg2] : bijective (fun v : plain AHE => u3 * v)
  by apply: inj_card_bij.
pose v3star := g (s - u1 * v1 - u2 * a).
have Hfib : (a, v3star) \in dsdp_fiber_ring u1 u2 u3 v1 s
  by rewrite inE /=; apply/eqP; rewrite /v3star Hg2; ring.
have Hnum : pfwd1 [% V2, Sout] (a, s)
          = pfwd1 [% [% V2, V3], Sout] ((a, v3star), s).
  apply: pfwd1_congr_preim => t; rewrite /= !xpair_eqE.
  case: (V2 t =P a) => [Hva|_] //=.
  suff -> : (Sout t == s) = (V3 t == v3star) by rewrite andbb.
  rewrite SoutE Hva.
  have -> : s = u1 * v1 + u2 * a + u3 * v3star
    by rewrite /v3star Hg2; ring.
  by rewrite (inj_eq (addrI _)) (inj_eq u3_inj).
have HcwN : `Pr[ [% V1c, U1c, U2c, U3c] = (v1, u1, u2, u3) ] != 0.
  by rewrite alice_inputs_constE pfwd1_const_RV eqxx oner_eq0.
have Hind : alice_sample_fdist
              |= [% V1c, U1c, U2c, U3c] _|_ [% [% V2, V3], Sout]
  by rewrite alice_inputs_constE; exact: inde_const_RV.
rewrite cpr_eqE Hnum -cpr_eqE -(cpr_eq_drop_indep (a, v3star) s HcwN Hind).
apply: alice_VarRV_cond_uniform => //.
by rewrite (pfwd1_RV2_compl Sout (fun=> (v1, u1, u2, u3)) s).
Qed.

(* Conditioned on the leaked output, Bob's input takes any given value with
   probability at most 1/#|plain AHE|. *)
Lemma alice_V2_cond_le (a s : plain AHE) :
  `Pr[ V2 = a | Sout = s ] <= #|plain AHE|%:R^-1.
Proof.
case: (eqVneq `Pr[ Sout = s ] 0) => [H0|Hn0].
  by rewrite cpr_eqE H0 invr0 mulr0 invr_ge0 ler0n.
by rewrite (alice_V2_cond_Sout a Hn0).
Qed.

(* Given the leaked output alone, Bob's input still carries log #|plain AHE|
   bits.  The leaked output cuts the sample space to a fiber on which Bob's
   input is uniform. *)
Lemma centropy_V2_Sout_logm :
  `H( V2 | Sout ) = log (#|plain AHE|%:R : R).
Proof.
rewrite centropy_RVE'.
transitivity (\sum_(s in plain AHE)
                `Pr[ Sout = s ] * log (#|plain AHE|%:R : R)); last first.
  by rewrite -big_distrl /= sum_pfwd1 mul1r.
apply: eq_bigr => s _.
have [->|Hs] := eqVneq `Pr[ Sout = s ] 0; first by rewrite !mul0r.
congr (_ * _); rewrite -[in RHS](cardsT (plain AHE)).
apply: centropy1_uniform_over_set => //.
- by move=> a _; rewrite cardsT; exact: alice_V2_cond_Sout.
- by move=> a; rewrite in_setT.
Qed.

(* Given the leaked output, the spectator coordinates and Bob's input are
   conditionally independent.  At the all-zero endpoint the leaked output is
   the single channel from V2 into Alice's view. *)
Lemma alice_spectator_cinde :
  alice_sample_fdist |= AliceSpectatorPre _|_ V2 | Sout.
Proof.
apply: cpr_prd_unit_RV; apply: weak_union.
apply/cinde_RV_unit.
exact: (inde_RV_comp idfun (fun p : plain AHE * plain AHE =>
          (p.1, uncurry (dsdp_output v1 u1 u2 u3) p))
        spectator_pre_indep).
Qed.

(* Alice's all-zero view assembled from the spectator coordinates and the
   leaked output.  Both ciphertext slots encrypt zero, and the re-encryption
   slot is built from the output, the two masks and Charlie's coin. *)
Definition alice_hop_tuple_of_spectator
    (p : alice_spectator_preT * plain AHE) : alice_hop_tupleT :=
  (p.1.1, (coin_ra1 p.1.2, coin_ra2 p.1.2), p.2,
   enc bob_pkey 0 (rand_of_renc (coin_rb1 p.1.2)),
   enc charlie_pkey 0 (rand_of_renc (coin_rc1 p.1.2)),
   enc alice_pkey (p.2 - u1 * v1 + p.1.1.1 + p.1.1.2)
     (rand_of_renc (coin_rc2 p.1.2))).

(* Alice's all-zero view is that assembly at the sampled coordinates. *)
Lemma alice_tuple_all_zeroE :
  alice_tuple_all_zero
  = alice_hop_tuple_of_spectator `o [% AliceSpectatorPre, Sout].
Proof. by []. Qed.

(* A predictor reading Alice's all-zero view matches Bob's input with
   probability at most 1/#|plain AHE|. *)
Lemma all_zero_guess_V2_le_invm (predict : predictor alice_hop_tupleT) :
  Pr alice_sample_fdist [set t | (predict `o alice_tuple_all_zero) t == V2 t]
    <= #|plain AHE|%:R^-1.
Proof.
by apply: (cinde_diagonal_bound
    (cinde_RV_comp (fun sp s => predict (alice_hop_tuple_of_spectator (sp, s)))
       alice_spectator_cinde)) => a c; exact: alice_V2_cond_le.
Qed.

(* The law of the spectator coordinates: uniform masks against the uniform
   coin law.  It is the randomness a simulator draws on its own. *)
Lemma alice_spectator_law :
  `p_ AliceSpectatorPre
  = (fdist_uniform card_plain_pair) `x (dsdp_enc_coins_fdist I R).
Proof.
rewrite spectator_pre_uniformE
        (fdist_uniform_prod card_plain_pair (card_dsdp_enc_coins I)
           card_spectator_pre).
by congr (_ `x _); rewrite /dsdp_enc_coins_fdist; congr fdist_uniform;
   apply: eq_irrelevance.
Qed.

(* The simulator law at one leaked output: uniform masks and uniform coins
   assembled into the all-zero view.  It reads only the output value, the
   weights and the three public keys. *)
Definition alice_simulator (s : plain AHE) :
    R.-fdist alice_hop_tupleT :=
  fdistmap (fun c : alice_spectator_preT =>
              alice_hop_tuple_of_spectator (c, s))
    ((fdist_uniform card_plain_pair) `x (dsdp_enc_coins_fdist I R)).

(* Given Alice's all-zero view, Bob's input still carries log #|plain AHE|
   bits.  Both ciphertext slots encrypt zero and the re-encryption slot reads
   the leaked output, which is the only channel from V2. *)
Lemma centropy_V2_all_zero_logm :
  `H( V2 | alice_tuple_all_zero ) = log (#|plain AHE|%:R : R).
Proof.
have cinde_assemble := cinde_RV_comp (fun sp s => alice_hop_tuple_of_spectator (sp, s))
                 alice_spectator_cinde.
rewrite -alice_tuple_all_zeroE in cinde_assemble.
have pair_selfK : cancel (fun v : alice_hop_tupleT => (v, v.1.1.1.2))
                          (fun p : alice_hop_tupleT * plain AHE => p.1) by [].
rewrite -(can_centropy_eq pair_selfK V2 alice_tuple_all_zero).
have -> : (fun v : alice_hop_tupleT => (v, v.1.1.1.2)) `o alice_tuple_all_zero
        = [% alice_tuple_all_zero, Sout] by [].
by rewrite (cinde_centropy_eq cinde_assemble) centropy_V2_Sout_logm.
Qed.

Section alice_hop_tuple_all_zero_mass.

Variable BT : finType.
Variable W : {RV alice_sample_fdist -> BT}.
Variable v : alice_hop_tupleT.
Variables (w : BT) (s : plain AHE).

(* On the event W = w, the leaked output equals s. *)
Hypothesis Sout_determinedE :
  forall t, W t = w -> Sout t = s.

(* On the event W = w, Alice's all-zero view is the simulator's assembly at
   the sampled spectator coordinates.  The conditioning event determines the
   leaked output, which is the one slot the assembly does not draw. *)
Lemma alice_hop_tuple_all_zero_pfwd1E :
  pfwd1 [% alice_tuple_all_zero, W] (v, w)
  = pfwd1 [% (fun c : alice_spectator_preT =>
                alice_hop_tuple_of_spectator (c, s)) `o AliceSpectatorPre, W]
      (v, w).
Proof.
(* The unfolding is spelled out: a [simpl] here would expand the finType
   structures under the six tuple slots. *)
apply: pfwd1_congr_preim => t.
rewrite /RV2 /comp_RV !xpair_eqE.
(* The mismatched branch is closed by the two implications rather than by
   rewriting andbF, whose match against a six-slot tuple equality is
   pathological. *)
case: (W t =P w) => [Ew|_]; last by apply/idP/idP => /andP[].
suff -> : alice_tuple_all_zero t
        = alice_hop_tuple_of_spectator (AliceSpectatorPre t, s) by [].
by rewrite -(Sout_determinedE Ew).
Qed.

End alice_hop_tuple_all_zero_mass.

(* Conditioned on the two secret inputs, Alice's all-zero view follows the
   simulator law fed the leaked output of those inputs. *)
Lemma dsdp_alice_hop_tuple_cond_sim (v : alice_hop_tupleT)
    (v2 v3 : plain AHE) :
  `Pr[ [% V2, V3] = (v2, v3) ] != 0 ->
  `Pr[ alice_tuple_all_zero = v | [% V2, V3] = (v2, v3) ]
    = alice_simulator (dsdp_output v1 u1 u2 u3 v2 v3) v.
Proof.
move=> Hvv.
have HW t : [% V2, V3] t = (v2, v3) ->
    Sout t = dsdp_output v1 u1 u2 u3 v2 v3.
  by rewrite /Sout /comp_RV => ->.
have assemble_indep : alice_sample_fdist
    |= ((fun c : alice_spectator_preT =>
           alice_hop_tuple_of_spectator (c, dsdp_output v1 u1 u2 u3 v2 v3))
        `o AliceSpectatorPre) _|_ [% V2, V3].
  exact: (inde_RV_comp _ idfun spectator_pre_indep).
rewrite cpr_eqE (alice_hop_tuple_all_zero_pfwd1E v HW) (assemble_indep v (v2, v3)).
rewrite mulfK // -dist_of_RVE /alice_simulator -alice_spectator_law.
by rewrite /dist_of_RV fdistmap_comp.
Qed.

(* The ideal-world joint law of the two secret inputs and a simulated view.
   The honest input law is bound to the simulator fed the leaked output. *)
Definition alice_ideal :
    R.-fdist (plain AHE * plain AHE * alice_hop_tupleT) :=
  vv <- `p_ [% V2, V3] ;
  fdistmap (fun v => (vv.1, vv.2, v))
    (alice_simulator (dsdp_output v1 u1 u2 u3 vv.1 vv.2)).

End dsdp_alice_hop_secrecy.

Section dsdp_alice_enc_uniform_img.
Context {R : realType}.
Variable S : indcpa_scheme.
Local Notation AHE := (scheme_AHE S).
Local Notation Renc := (scheme_renc S).
Local Notation card_renc := (scheme_card_renc S).
Local Notation rand_of_renc := (@scheme_rand_of_renc S).

(* The encryption of v under pk as a function of the randomness index. *)
Definition enc_of_renc (pk : pub_key AHE) (v : plain AHE) :
    Renc -> cipher AHE :=
  fun r => enc pk v (rand_of_renc r).

(* The reachable encryptions are nonempty, since the randomness-index type
   is. *)
Lemma card_enc_img_gt0 (pk : pub_key AHE) (v : plain AHE) :
  (0 < #|enc_of_renc pk v @: [set: Renc]|)%N.
Proof. by rewrite card_gt0 imset_eq0 -card_gt0 cardsT card_renc. Qed.

(* The property that the challenge law is uniform on the reachable
   encryptions of v under pk.  It is a property of the scheme's encryption map
   alone, and stands beside the hop correspondences. *)
Definition enc_fdist_uniform_img (pk : pub_key AHE) (v : plain AHE) : Prop :=
  enc_fdist (S:=S) pk v
  = fdist_uniform_supp R (card_enc_img_gt0 pk v).

(* Equal fiber cardinalities over the image suffice. *)
Lemma enc_fdist_uniform_img_fiber (pk : pub_key AHE) (v : plain AHE) :
  (forall c c', c \in enc_of_renc pk v @: [set: Renc] ->
                c' \in enc_of_renc pk v @: [set: Renc] ->
     #|[set r | enc_of_renc pk v r == c]|
     = #|[set r | enc_of_renc pk v r == c']|) ->
  enc_fdist_uniform_img pk v.
Proof.
exact: (fdistmap_uniform_supp_img card_renc (card_enc_img_gt0 pk v)).
Qed.

(* Injectivity of the composed encryption map suffices. *)
Lemma enc_fdist_uniform_img_inj (pk : pub_key AHE) (v : plain AHE) :
  injective (enc_of_renc pk v) -> enc_fdist_uniform_img pk v.
Proof.
move=> Hinj; apply: enc_fdist_uniform_img_fiber => c c'.
have fib1 w : w \in enc_of_renc pk v @: [set: Renc] ->
    #|[set r | enc_of_renc pk v r == w]| = 1%N.
  move=> /imsetP[r0 _ ->]; rewrite -(cards1 r0); apply: eq_card => r.
  by rewrite !inE (inj_eq Hinj).
by move=> /fib1 -> /fib1 ->.
Qed.

(* Under that property, each reachable ciphertext carries mass one over the
   number of reachable encryptions. *)
Lemma enc_fdist_uniform_imgE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist_uniform_img pk v ->
  forall c, c \in enc_of_renc pk v @: [set: Renc] ->
  enc_fdist (R:=R) (S:=S) pk v c
  = #|enc_of_renc pk v @: [set: Renc]|%:R^-1.
Proof. by move=> H c Hc; rewrite H fdist_uniform_supp_in. Qed.

End dsdp_alice_enc_uniform_img.
