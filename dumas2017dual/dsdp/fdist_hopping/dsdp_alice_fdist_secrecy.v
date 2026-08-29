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

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, fdist axis                                 *)
(*                                                                            *)
(* Corrupted-Alice secrecy for the three-party DSDP protocol, proved in       *)
(* infotheo over an explicit product sample space. The sample space carries   *)
(* the two honest inputs, Alice's two mask plaintexts, the randomness of the  *)
(* two hop encryptions and the randomness of Alice's two combines; uniformity *)
(* and independence of the coordinates are theorems of the product            *)
(* construction rather than hypotheses. The one algebraic assumption is       *)
(* [u3_unit]: Charlie's weight u3 is a unit of the plaintext ring.            *)
(*                                                                            *)
(* A one-parameter family of views interpolates from Alice's real view to the *)
(* view whose two ciphertext slots both encrypt zero. Each step of the        *)
(* interpolation is an equality between a distinguishing gap and the          *)
(* real-or-zero advantage of a reduction constructed here, and the all-zero   *)
(* endpoint is bounded by the one-degree-of-freedom solution fiber of the     *)
(* DSDP linear constraint. Every epsilon in this file is therefore the        *)
(* defined advantage of an explicit reduction.                                *)
(*                                                                            *)
(* Headline results: dsdp_alice_guess_fdist_V2_real_le bounds the probability *)
(* that a predictor reading Alice's real view returns Bob's input;            *)
(* dsdp_alice_unpredictability_fdist_ge is its negative-logarithm form;       *)
(* dsdp_alice_predictor_unpredictability_fdist_ge restates that bound through *)
(* the named quantity alice_predictor_unpredictability;                       *)
(* dsdp_alice_sim_advantage_fdist_le bounds the gap between the real joint    *)
(* law and the ideal-world joint law built from dsdp_alice_simulator;         *)
(* dsdp_alice_guess_fdist_view_le transfers the first bound to Alice's view.  *)
(*                                                                            *)
(* ## Game vocabulary                                                         *)
(*                                                                            *)
(* The real-or-zero game layer and the reduction wiring live in               *)
(* dumas2017dual/dsdp/fdist_hopping/indcpa_game.v, whose header carries       *)
(* the full role map.  The names this file plays those roles with are         *)
(*                                                                            *)
(* | role          | identifier                                             | *)
(* |---------------|--------------------------------------------------------| *)
(* | adversary     | indcpa_fdist_adversary                                 | *)
(* | challenger    | indcpa_challenger                                      | *)
(* | experiment    | indcpa_experiment                                      | *)
(* | advantage     | indcpa_fdist_epsilon                                   | *)
(* | distinguisher | guess_test predict                                     | *)
(* | reduction     | v2_challenge_adversary, v3_challenge_adversary         | *)
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
(*   (V2, V3, R2, R3, Rho2, Rho3, RA1, RA2).                                *)
(*                                                                            *)
(* V2 is Bob's input, and V3 is Charlie's input.                              *)
(* R2 and R3 are Alice's first and second mask plaintexts.                    *)
(* Rho2 and Rho3 are the randomnesses for the Bob and Charlie ciphertext      *)
(* slots.  RA1 and RA2 are the randomnesses for Alice's two ciphertext        *)
(* combinations.                                                             *)
(*                                                                            *)
(* Hop0State                                                                  *)
(*   (V2, V3, R2, R3, RA1, RA2, Rho3)                                       *)
(*   State for the Bob challenge.  The challenge supplies Bob's ciphertext,   *)
(*   while Rho3 constructs Charlie's real ciphertext.                         *)
(*                                                                            *)
(* Hop1StatePre                                                               *)
(*   (V2, V3, R2, R3, RA1, RA2, Rho2)                                       *)
(*   Pre-encryption form of Hop1State.  hop1_state_of encrypts zero using     *)
(*   Rho2 and stores the resulting Bob ciphertext.                            *)
(*                                                                            *)
(* Hop1State                                                                  *)
(*   (V2, V3, R2, R3, RA1, RA2, hop0_cipher 1)                               *)
(*   State for the Charlie challenge.  The challenge supplies Charlie's       *)
(*   ciphertext, while hop0_cipher 1 supplies Bob's zero ciphertext.          *)
(*                                                                            *)
(* AliceSpectatorPre                                                          *)
(*   (R2, R3, Rho2, Rho3, RA1, RA2)                                         *)
(*   Coordinates used to construct AliceSpectator.  Their joint law is        *)
(*   independent of (V2, V3).                                                 *)
(*                                                                            *)
(* AliceSpectator                                                             *)
(*   (R2, R3, RA1, RA2, hop0_cipher 2, hop1_cipher 2)                        *)
(*   Alice's all-zero hopping tuple without Sout.  Its law supplies the       *)
(*   remaining components of the simulator output.                            *)
(*                                                                            *)
(* AliceSpectatorPre2                                                         *)
(*   (R2, R3, RA1, RA2, Rho2, Rho3)                                         *)
(*   Reordered spectator coordinates.  Placing the encryption randomnesses    *)
(*   last exposes the product law used to derive the simulator distribution.  *)
(*                                                                            *)
(* ```                                                                        *)
(* One protocol run and its hops                                              *)
(*                                                                            *)
(*        dsdp_alice_sampleT == all honest inputs and random choices in one   *)
(*                              DSDP run                                      *)
(*        alice_sample_fdist == samples those values uniformly and            *)
(*                              independently                                 *)
(*                    V2, V3 == Bob's and Charlie's honest inputs             *)
(*                    R2, R3 == the masks Alice adds to her two combines      *)
(*                Rho2, Rho3 == the encryption coins for the ciphertexts      *)
(*                              Alice receives from Bob and Charlie           *)
(*                  RA1, RA2 == the encryption coins for Alice's two combines *)
(*                      Sout == the weighted output that Alice is allowed to  *)
(*                              learn                                         *)
(*             hop0_cipher i == Bob's ciphertext is real at hop 0 and         *)
(*                              encrypts zero afterwards                      *)
(*             hop1_cipher i == Charlie's ciphertext is real through hop 1    *)
(*                              and encrypts zero at hop 2                    *)
(*     dsdp_alice_hop_tupleT == the core information used to study Alice's    *)
(*                              secrecy                                       *)
(*          alice_hop_jointT == adds the honest inputs so a test can compare  *)
(*                              a prediction with the true input              *)
(*           AliceHopTuple i == Alice's core information in experiment i      *)
(*   alice_hop_joint_fdist i == the distribution given to a test at hop i     *)
(* alice_hop_game_success i D == the probability that D accepts at hop i      *)
(*   alice_hop_game_successE == expresses that probability as the event that  *)
(*                              D accepts the sampled joint value             *)
(*                                                                            *)
(* Reductions for the two ciphertext changes                                 *)
(*                                                                            *)
(*    hop0_stateT, Hop0State == everything needed to rebuild Alice's value    *)
(*                              except Bob's challenge ciphertext             *)
(*    hop1_stateT, Hop1State == everything needed to rebuild Alice's value    *)
(*                              except Charlie's challenge ciphertext         *)
(*              Hop1StatePre == the hop-1 state before Bob's zero ciphertext  *)
(*                              is constructed                                *)
(*             hop1_state_of == constructs Bob's zero ciphertext and          *)
(*                              completes the hop-1 state                     *)
(*             hop0_assemble == builds the complete value given to D around  *)
(*                              Bob's challenge ciphertext                    *)
(*             hop1_assemble == builds the complete value given to D around  *)
(*                              Charlie's challenge ciphertext                *)
(*  v2_challenge_adversary D == turns D on hops 0 and 1 into an adversary     *)
(*                              distinguishing Enc(pk_B, V2) from             *)
(*                              Enc(pk_B, 0)                                  *)
(*  v3_challenge_adversary D == turns D on hops 1 and 2 into an adversary     *)
(*                              distinguishing Enc(pk_C, V3) from             *)
(*                              Enc(pk_C, 0)                                  *)
(*                                                                            *)
(* The all-zero endpoint and guessing                                        *)
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
(*        guess_test predict == accepts exactly when the predictor            *)
(*                              recovers Bob's input                          *)
(* alice_predictor_unpredictability predict == the negative logarithm of      *)
(*                              the predictor's success probability           *)
(*             fdistmap_prod == applying separate functions to independent   *)
(*                              factors preserves their product form         *)
(*            fdistmap_prodr == changing only the second factor leaves the   *)
(*                              first factor unchanged                       *)
(*                                                                            *)
(* Simulation                                                                *)
(*                                                                            *)
(*    dsdp_alice_simulator s == constructs the all-zero view from the leaked *)
(*                              output s, fresh masks, fresh coins, and two   *)
(*                              encryptions of zero                          *)
(*     alice_spectator_pre2T == the spectator choices reordered to separate  *)
(*                              the two encryption coins                     *)
(*        AliceSpectatorPre2 == those reordered choices in one sampled run    *)
(*   alice_spectator_regroup == performs that coordinate reordering           *)
(*      alice_spectator_prod == constructs the spectator from the reordered  *)
(*                              choices                                       *)
(* alice_spectator_of_hop_tuple == removes the leaked output from a hopping   *)
(*                              tuple                                         *)
(*         alice_ideal_joint == samples the honest inputs and then simulates  *)
(*                              Alice's view from their leaked output         *)
(*                                                                            *)
(* Alice's complete view                                                     *)
(*                                                                            *)
(*   alice_view_of_hop_tuple == reconstructs Alice's complete view from the   *)
(*                              hopping tuple                                 *)
(*           AliceCombineBob == Alice's outgoing ciphertext under Bob's key  *)
(*       AliceCombineCharlie == Alice's outgoing ciphertext under Charlie's  *)
(*                              key                                           *)
(*            AliceRecvPlain == the plaintext Alice obtains in her final     *)
(*                              receive step                                  *)
(*                 AliceView == the hopping tuple and the values derived      *)
(*                              from it                                       *)
(*  alice_view_of_hop_tupleE == Alice's complete view is a deterministic     *)
(*                              function of the hopping tuple, so the bound   *)
(*                              transfers without another error term         *)
(*                                                                            *)
(* Public setup                                                              *)
(*                                                                            *)
(* dsdp_alice_simulator_pub pk_b pk_c s == the simulator with Bob's and       *)
(*                              Charlie's public keys given explicitly        *)
(* dsdp_alice_simulator_pubE == selecting those keys from the party key table *)
(*                              gives the original simulator                  *)
(*                                                                            *)
(* Separate facts about encryption distributions                             *)
(*                                                                            *)
(*        enc_of_renc pk v r == maps an encryption-randomness index to the    *)
(*                              resulting ciphertext                         *)
(*     card_enc_img_gt0 pk v == at least one ciphertext encrypting v is       *)
(*                              reachable                                     *)
(* enc_fdist_uniform_img pk v == every reachable encryption of v has the same *)
(*                              probability                                   *)
(* enc_fdist_uniform_img_fiber == this uniformity follows when every          *)
(*                              reachable ciphertext has the same number of   *)
(*                              randomness indices                           *)
(* enc_fdist_uniform_img_inj == injective encryption randomness is a          *)
(*                              sufficient special case                      *)
(*    enc_fdist_uniform_imgE == each reachable ciphertext then has            *)
(*                              probability one divided by the number of      *)
(*                              reachable ciphertexts                        *)
(* ```                                                                        *)
(*                                                                            *)
(* Bob's and Charlie's inputs are sampled uniformly, so these results         *)
(* describe average-case secrecy over their inputs. Each hop uses one         *)
(* real-or-zero challenge at one fixed public key. These advantages differ    *)
(* from the multi-query, party-indexed oracle advantage in indcpa_ror.v.      *)
(* The guessing bound is nontrivial only while its complete right-hand side   *)
(* is below 1. The formal adversary has no running-time model.                *)
(* Computational efficiency remains an external assumption.                  *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_fdist_secrecy.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variable pkey_of_party : party_id -> pub_key AHE.

(* Bob's public key. *)
Definition bob_pkey : pub_key AHE := pkey_of_party Bob.

(* Charlie's public key. *)
Definition charlie_pkey : pub_key AHE := pkey_of_party Charlie.
Variables (v1 u1 u2 u3 : plain AHE).
(* Naming: [u3_unit] reads "u3 is a unit", the subject_property hypothesis
   pattern. *)
Hypothesis u3_unit : u3 \is a GRing.unit.
Let u3_inj : injective (fun v : plain AHE => u3 * v) := mulrI u3_unit.

Let card_plain_gt0 : (0 < #|plain AHE|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.
Let card_plain : #|plain AHE| = #|plain AHE|.-1.+1.
Proof. by rewrite prednK. Qed.
Let card_plain_pair :
  #|((plain AHE * plain AHE)%type : finType)|
    = (#|plain AHE| * #|plain AHE|)%N.-1.+1.
Proof. by rewrite card_prod prednK // muln_gt0 card_plain_gt0. Qed.
Let card_renc_pair :
  #|((Renc * Renc)%type : finType)|
    = (index_renc.+1 * index_renc.+1)%N.-1.+1.
Proof. by rewrite card_prod card_renc. Qed.

Local Notation enc_fdist :=
  (enc_fdist (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation indcpa_fdist_adversary := (indcpa_fdist_adversary (R:=R) AHE).
Local Notation indcpa_fdist_success_real :=
  (indcpa_fdist_success_real (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation indcpa_fdist_success_zero :=
  (indcpa_fdist_success_zero (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation reduction_challenge_acceptE :=
  (reduction_challenge_acceptE (rand_of_renc := rand_of_renc)).
Local Notation reduction_challenge_successE :=
  (reduction_challenge_successE (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation predictor := (predictor AHE).

(* The sample space of the corrupted-Alice experiment: the two honest inputs,
   Alice's two mask plaintexts, the randomness of the two hop encryptions, and
   the randomness of Alice's two combines. *)
Definition dsdp_alice_sampleT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * (Renc * Renc))%type.

(* The uniform product distribution on the sample space. *)
Definition alice_sample_fdist : R.-fdist dsdp_alice_sampleT :=
  (((fdist_uniform card_plain_pair) `x (fdist_uniform card_plain_pair))
     `x (fdist_uniform card_renc_pair)) `x (fdist_uniform card_renc_pair).

(* Bob's honest input. *)
Definition V2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.1.
(* Charlie's honest input. *)
Definition V3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.2.
(* Alice's mask on the first combine. *)
Definition R2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.1.
(* Alice's mask on the second combine. *)
Definition R3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.2.
(* The randomness of the ciphertext Alice receives from Bob, and the randomness
   the hop-0 challenger takes over. *)
Definition Rho2 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.1.
(* The randomness of the ciphertext Alice receives from Charlie, and the
   randomness the hop-1 challenger takes over. *)
Definition Rho3 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.2.
(* The randomness of Alice's first combine. *)
Definition RA1 : {RV alice_sample_fdist -> Renc} := fun t => t.2.1.
(* The randomness of Alice's second combine. *)
Definition RA2 : {RV alice_sample_fdist -> Renc} := fun t => t.2.2.

(* The protocol output Alice legitimately learns, the weighted scalar product
   of her weights with the two honest inputs.
   Naming: [Sout] rather than [S], which shadows the successor of nat, after
   [dsdp_guess_fiber.v]. *)
Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry (dsdp_output v1 u1 u2 u3) `o [% V2, V3].

(* The leaked output written out as u1 * v1 + u2 * V2 + u3 * V3.  Alice
   legitimately learns one affine equation in the two secret inputs, and that
   equation is the leak the fiber term of the headline bound accounts for. *)
Lemma SoutE t : Sout t = u1 * v1 + u2 * V2 t + u3 * V3 t.
Proof. by []. Qed.

(* The Bob-key ciphertext slot of Alice's hopping tuple, encrypting Bob's
   input at index 0 and zero at every larger index. *)
Definition hop0_cipher (i : nat) : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc bob_pkey (if (0 < i)%N then 0 else V2 t)
               (rand_of_renc (Rho2 t)).

(* The Charlie-key ciphertext slot of Alice's hopping tuple, encrypting
   Charlie's input at indices 0 and 1 and zero at every larger index. *)
Definition hop1_cipher (i : nat) : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc charlie_pkey (if (1 < i)%N then 0 else V3 t)
               (rand_of_renc (Rho3 t)).

(* The type of Alice's hopping tuple: her two masks, her two combine
   randomnesses, the leaked output, and the two ciphertexts she receives. *)
Definition dsdp_alice_hop_tupleT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * cipher AHE * cipher AHE)%type.

(* The value a distinguisher is tested on: the two honest inputs together with
   Alice's hopping tuple.  Carrying the inputs beside the tuple lets a single
   sample hold both a predictor's guess, computed from the tuple, and the true
   input that guess is checked against.  That is what makes
   guess_test expressible as a Boolean test on one sample. *)
Definition alice_hop_jointT : finType :=
  (plain AHE * plain AHE * dsdp_alice_hop_tupleT)%type.

(* Alice's hopping tuple at hop i: her two masks, her two combine
   randomnesses, the leaked output, and the two ciphertext slots, where the
   first i slots hold encryptions of zero. Hop 0 is the real tuple, hop 2 is
   the all-zero endpoint. *)
Definition AliceHopTuple (i : nat) :
    {RV alice_sample_fdist -> dsdp_alice_hop_tupleT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, hop0_cipher i, hop1_cipher i].

(* The joint distribution of the two honest inputs and Alice's hopping tuple
   at hop i. *)
Definition alice_hop_joint_fdist (i : nat) : R.-fdist alice_hop_jointT :=
  `p_ [% V2, V3, AliceHopTuple i].

(* The probability that D returns true at hop i. *)
Definition alice_hop_game_success (i : nat)
    (D : alice_hop_jointT -> bool) : R :=
  Pr (fdistmap D (alice_hop_joint_fdist i)) [set true].

(* The pushforward form of the hop-i acceptance probability agrees with the
   event form, which is the shape the four reduction correspondences are stated
   in. *)
Lemma alice_hop_game_successE (i : nat) (D : alice_hop_jointT -> bool) :
  alice_hop_game_success i D
    = Pr (alice_hop_joint_fdist i) [set x | D x].
Proof. exact: Pr_fdistmap_bool. Qed.

(* Alice's real hopping tuple: the hop-0 rung, both ciphertext slots carrying
   their real plaintexts. *)
Definition AliceRealTuple :
    {RV alice_sample_fdist -> dsdp_alice_hop_tupleT} :=
  AliceHopTuple 0.

(* The joint law of the two honest inputs and Alice's real hopping tuple. *)
Definition alice_real_joint : R.-fdist alice_hop_jointT :=
  alice_hop_joint_fdist 0.

Let card_sample : #|dsdp_alice_sampleT| = #|dsdp_alice_sampleT|.-1.+1.
Proof. exact: fdist_card_prednK alice_sample_fdist. Qed.

(* The sample space carries the uniform distribution. *)
Lemma alice_sample_fdistE : alice_sample_fdist = fdist_uniform card_sample.
Proof.
apply/fdist_ext => -[[[vv ms] rho] ra].
rewrite fdist_uniformE /alice_sample_fdist !fdist_prodE !fdist_uniformE.
by rewrite -!invfM -!natrM /dsdp_alice_sampleT !card_prod.
Qed.

(* The state v2_challenge_adversary holds at hop 0: the two inputs, Alice's
   masks, her combine randomness, and Rho3.  Rho2 is held by the challenger at
   this hop, which is why the state stops short of it. *)
Definition hop0_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * Renc)%type.

(* The hop-0 state as a random variable on the sample space: everything
   v2_challenge_adversary holds before it queries the challenger. *)
Definition Hop0State : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.2).

Let card_hop0_state : #|hop0_stateT| = #|hop0_stateT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ Hop0State). Qed.

Let card_hop0_pair :
  #|((hop0_stateT * Renc)%type : finType)|
    = #|((hop0_stateT * Renc)%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% Hop0State, Rho2]). Qed.

(* The hop-0 state and Bob's encryption randomness are jointly uniform on the
   product of their spaces, so the randomness the challenger draws is uniform
   and independent of everything the reduction holds. *)
Lemma hop0_pair_uniformE :
  `p_ [% Hop0State, Rho2]
    = (fdist_uniform card_hop0_state) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_state card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_stateT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2, (p.2, p.1.2), p.1.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[[v2 v3] [r2 r3]] [ra1 ra2]] rho3] rho2].
Qed.

(* Bob's encryption randomness is uniform and independent of the hop-0 state.
   The freshness condition reduction_challenge_fdistE consumes, discharged here
   rather than assumed: Rho2 is a coordinate of the product sample space that
   the hop-0 state omits, so the pair is a re-indexing of the whole sample.
   Its protocol reading is that Bob draws the randomness of the ciphertext he
   sends independently of his own input and of the other parties' randomness,
   and that this randomness reaches Alice only through that ciphertext. *)
Lemma hop0_state_prodE :
  `p_ [% Hop0State, Rho2] = (`p_ Hop0State) `x (fdist_uniform card_renc).
Proof.
by rewrite -(fst_RV2 Hop0State Rho2) !hop0_pair_uniformE fdist_prod1.
Qed.

(* The state v3_challenge_adversary holds at hop 1: the two inputs, Alice's
   masks, her combine randomness, and Bob's already-zeroed ciphertext.  Bob's
   slot is fixed data at this hop, and Charlie's encryption randomness is what
   the challenger owns. *)
Definition hop1_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * cipher AHE)%type.

(* The hop-1 state as a random variable: what v3_challenge_adversary holds
   after Bob's slot has been zeroed and before it queries Charlie's
   challenger. *)
Definition Hop1State : {RV alice_sample_fdist -> hop1_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, hop0_cipher 1 t).

(* The hop-1 state with Bob's encryption randomness in place of the ciphertext
   it produces.  Uniformity is proved here, before that encryption happens.
   Hop1State is obtained by applying the fixed function hop1_state_of, and a
   fixed function of an independent pair leaves the independence in place. *)
Definition Hop1StatePre : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.1).

(* The map carrying Hop1StatePre to Hop1State, encrypting zero in the
   hop-0 slot. *)
Definition hop1_state_of (c : hop0_stateT) : hop1_stateT :=
  (c.1.1.1, c.1.1.2, c.1.2,
   enc bob_pkey 0 (rand_of_renc c.2)).

(* The hop-1 state before encryption and the hop-1 encryption randomness
   are jointly uniform. *)
Lemma hop1_state_pre_pair_uniformE :
  `p_ [% Hop1StatePre, Rho3]
    = (fdist_uniform card_hop0_state) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_state card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_stateT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2, (p.1.2, p.2), p.1.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[[v2 v3] [r2 r3]] [ra1 ra2]] rho2] rho3].
Qed.

(* The hop-1 encryption randomness is uniform. *)
Lemma rho3_uniformE : `p_ Rho3 = fdist_uniform card_renc.
Proof.
by rewrite -(snd_RV2 Hop1StatePre Rho3) hop1_state_pre_pair_uniformE fdist_prod2.
Qed.

(* A joint law that factors as the product of its marginals is the law of an
   independent pair. *)
Lemma inde_RV_of_prod (A B : finType)
    (X : {RV alice_sample_fdist -> A}) (Y : {RV alice_sample_fdist -> B}) :
  `p_ [% X, Y] = (`p_ X) `x (`p_ Y) -> alice_sample_fdist |= X _|_ Y.
Proof. by move=> H a b; rewrite -!dist_of_RVE H fdist_prodE. Qed.

(* Charlie's encryption randomness is uniform and independent of the hop-1
   state, the same freshness condition at the second hop.  Hop1State holds
   Bob's zeroed ciphertext where the hop-0 state held a coordinate, so the
   product is proved at the pre-encryption layout Hop1StatePre, where the pair
   is a re-indexing of the sample, and carried across by the fixed function
   hop1_state_of. *)
Lemma hop1_state_prodE :
  `p_ [% Hop1State, Rho3] = (`p_ Hop1State) `x (fdist_uniform card_renc).
Proof.
have Hpre : alice_sample_fdist |= Hop1StatePre _|_ Rho3.
  apply: inde_RV_of_prod.
  by rewrite hop1_state_pre_pair_uniformE -(fst_RV2 Hop1StatePre Rho3)
             hop1_state_pre_pair_uniformE fdist_prod1 rho3_uniformE.
have Hstate : alice_sample_fdist |= Hop1State _|_ Rho3.
  exact: (inde_RV_comp hop1_state_of idfun Hpre).
by rewrite (inde_dist_of_RV2 Hstate) rho3_uniformE.
Qed.

(* The tested hop-0 joint value formed by placing ch in Bob's ciphertext slot
   and constructing Charlie's ciphertext from the stored randomness. *)
(* If

      c = (V2, V3, R2, R3, RA1, RA2, Rho3),

   `hop0_assemble c ch` yields

      (V2, V3, R2, R3, RA1, RA2, Sout, ch, Enc(pk_Charlie, V3; Rho3))

   This can be used when calling D in the reduction:

      D (hop0_assemble c ch)

   Its result is then returned, which gives Pr[D(...) = 1].

   ----

   The relationship can be summarized as:

   v2_challenge_adversary D
      = the procedure that adapts D to the encryption experiment

   hop0_assemble
      = the function used by that procedure to rebuild D's input

   D
      = the final Boolean test on the rebuilt input
*)
Definition hop0_assemble (c : hop0_stateT) (ch : cipher AHE) :
    alice_hop_jointT :=
  let: (vv, masks, ra, rho3) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output v1 u1 u2 u3 vv.1 vv.2, ch,
    enc charlie_pkey vv.2 (rand_of_renc rho3))).

(* The tested hop-1 joint value formed by retaining Bob's stored zero
   ciphertext and placing ch in Charlie's ciphertext slot. *)
Definition hop1_assemble (c : hop1_stateT) (ch : cipher AHE) :
    alice_hop_jointT :=
  let: (vv, masks, ra, c2zero) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output v1 u1 u2 u3 vv.1 vv.2, c2zero, ch)).

(* A distinguisher D is a Boolean test on one sampled joint value.  This value
   contains V2 and V3 together with AliceHopTuple i.  Returning true means
   that D accepts the sampled value.  The acceptance probability at hop i is
   the probability, over x sampled from alice_hop_joint_fdist i, that D x is
   true:

     alice_hop_game_success i D
       = Pr (alice_hop_joint_fdist i) [set x | D x].

   ## v2_challenge_adversary

   v2_challenge_adversary D packages the following procedure:

     1. Sample (V2, V3, R2, R3, RA1, RA2, Rho3).
     2. Select V2 as the real challenge plaintext.  The experiment returns a
        challenge ciphertext ch encrypting either V2 or zero under Bob's key.
     3. Compute Sout, use ch as Bob's ciphertext, and use Rho3 to construct
        Charlie's ciphertext.
     4. Call D on the resulting joint value, shown flattened as

          (V2, V3, R2, R3, RA1, RA2, Sout, ch,
           enc charlie_pkey V3 (rand_of_renc Rho3)),

        and return its Boolean result.

   It is called a "reduction" because it converts a distinguishing problem
   into a security problem. The original problem is:

       Can D distinguish the protocol's hop-0 distribution from its hop-1
       distribution?

   The encryption-security problem is:

       Can an IND-CPA adversary distinguish an encryption of V2 from an
       encryption of zero under Bob's key?

   That advantage is indcpa_fdist_epsilon pk adv.

   The construction:

       D |--> v2_challenge_adversary(D)

   D accepts concrete (v_2,v_3,h) and returns a Boolean.
   The type does not require D to inspect only the challenged ciphertext.
   It may inspect every component of such a tuple. So A_i(D) wrap it
   to provide the assembled concrete values from the stateful experiment.

   turns any protocol distinguisher D into such an encryption adversary.
   The correspondence theorems prove

     alice_hop_game_success 0 D
       = indcpa_fdist_success_real
           bob_pkey (v2_challenge_adversary D),

   and

     alice_hop_game_success 1 D
       = indcpa_fdist_success_zero
           bob_pkey (v2_challenge_adversary D).

   Therefore, the protocol hop gap equals the real-or-zero advantage:

     `| alice_hop_game_success 0 D - alice_hop_game_success 1 D |
       = indcpa_fdist_epsilon
           bob_pkey (v2_challenge_adversary D).

   In other words, this procedure lets the real and zero experiments
   reproduce the change from hop 0 to hop 1.

      distinguishing protocol hops 0 and 1
              |
              | construct v2_challenge_adversary D
              v
      distinguishing Enc(pk_B, V2) and Enc(pk_B, 0)

   The second problem is the one the encryption-security property answers,
   and that is what bounds the first.
   Since D accepts a complete alice_hop_jointT value rather than an
   encryption challenge, v2_challenge_adversary D adapts D to the real-or-zero
   adversary interface.  It builds the joint value around the challenge
   ciphertext and calls D.  The correspondence theorems prove that D's gap
   between protocol hops 0 and 1 equals the real-or-zero advantage of the
   resulting encryption adversary.

   ## v3_challenge_adversary

   v3_challenge_adversary D packages the following procedure:

     1. Sample

          (V2, V3, R2, R3, RA1, RA2, hop0_cipher 1),

        where hop0_cipher 1 is Bob's encryption of zero.
     2. Select V3 as the real challenge plaintext.  The experiment returns a
        challenge ciphertext ch encrypting either V3 or zero under Charlie's
        key.
     3. Compute Sout and use ch as Charlie's ciphertext.
     4. Call D on the resulting joint value, shown flattened as

          (V2, V3, R2, R3, RA1, RA2, Sout, hop0_cipher 1, ch),

        and return its Boolean result.

   This procedure lets the real and zero experiments reproduce the change
   from hop 1 to hop 2.  The two correspondence theorems state

     alice_hop_game_success 1 D
       = indcpa_fdist_success_real
           charlie_pkey (v3_challenge_adversary D),

     alice_hop_game_success 2 D
       = indcpa_fdist_success_zero
           charlie_pkey (v3_challenge_adversary D).

   Therefore hop1_advantageE proves

     `| alice_hop_game_success 1 D - alice_hop_game_success 2 D |
       = indcpa_fdist_epsilon
           charlie_pkey (v3_challenge_adversary D).

   v2_challenge_adversary D and v3_challenge_adversary D are adversary
   records supplied to
   the real and zero experiments.  They are not themselves complete
   experiments. *)

(* The IND-CPA adversary built from D at Bob's key: it samples the hop-0 state,
   submits Bob's input V2 as the challenge plaintext, and answers with D run on
   the joint value assembled around the challenge ciphertext.  At the real bit
   it reproduces hop 0 and at the zero bit hop 1. *)
Definition v2_challenge_adversary (D : distinguisher alice_hop_jointT) :
    indcpa_fdist_adversary :=
  {| adv_state := hop0_stateT ;
     adv_choose := `p_ Hop0State ;
     adv_plain := fun c => c.1.1.1.1 ;
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.

(* The IND-CPA adversary built from D at Charlie's key: it samples the hop-1
   state, submits Charlie's input V3 as the challenge plaintext, and answers
   with D run on the joint value assembled around the challenge ciphertext.  At
   the real bit it reproduces hop 1 and at the zero bit hop 2. *)
Definition v3_challenge_adversary (D : distinguisher alice_hop_jointT) :
    indcpa_fdist_adversary :=
  {| adv_state := hop1_stateT ;
     adv_choose := `p_ Hop1State ;
     adv_plain := fun c => c.1.1.1.2 ;
     adv_decide := fun c ch => D (hop1_assemble c ch) |}.

(* D's acceptance probability on the real view, hop 0, equals the real-bit
   success probability of v2_challenge_adversary D against Bob's key. *)
Lemma hop0_real_challengeE (D : distinguisher alice_hop_jointT) :
  alice_hop_game_success 0 D
    = indcpa_fdist_success_real bob_pkey (v2_challenge_adversary D).
Proof.
rewrite alice_hop_game_successE.
rewrite (reduction_challenge_acceptE (pk := bob_pkey)
    (msg := fun c : hop0_stateT => c.1.1.1.1)
    (assemble := hop0_assemble) hop0_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite reduction_challenge_successE indcpa_fdist_success_realE.
Qed.

(* D's acceptance probability on the view whose Bob slot encrypts zero, hop 1,
   equals the zero-bit success probability of v2_challenge_adversary D against Bob's
   key. *)
Lemma hop0_zero_challengeE (D : distinguisher alice_hop_jointT) :
  alice_hop_game_success 1 D
    = indcpa_fdist_success_zero bob_pkey (v2_challenge_adversary D).
Proof.
rewrite alice_hop_game_successE.
rewrite (reduction_challenge_acceptE (pk := bob_pkey)
    (msg := fun _ : hop0_stateT => 0)
    (assemble := hop0_assemble) hop0_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite reduction_challenge_successE indcpa_fdist_success_zeroE.
Qed.

(* The gap D shows between hop 0 and hop 1 equals the advantage of
   v2_challenge_adversary D against Bob's key.  Zeroing Bob's slot costs exactly one
   IND-CPA advantage. *)
Lemma hop0_advantageE (D : distinguisher alice_hop_jointT) :
  `| alice_hop_game_success 0 D - alice_hop_game_success 1 D |
  = indcpa_fdist_epsilon bob_pkey (v2_challenge_adversary D).
Proof.
by rewrite /indcpa_fdist_epsilon hop0_real_challengeE hop0_zero_challengeE.
Qed.

(* D's acceptance probability at hop 1 equals the real-bit success probability
   of v3_challenge_adversary D against Charlie's key.  Hop 1 is the zero side for Bob's
   key and the real side for Charlie's, which is what chains the two hops. *)
Lemma hop1_real_challengeE (D : distinguisher alice_hop_jointT) :
  alice_hop_game_success 1 D
    = indcpa_fdist_success_real charlie_pkey (v3_challenge_adversary D).
Proof.
rewrite alice_hop_game_successE.
rewrite (reduction_challenge_acceptE (pk := charlie_pkey)
    (msg := fun c : hop1_stateT => c.1.1.1.2)
    (assemble := hop1_assemble) hop1_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite reduction_challenge_successE indcpa_fdist_success_realE.
Qed.

(* D's acceptance probability on the all-zero view, hop 2, equals the zero-bit
   success probability of v3_challenge_adversary D against Charlie's key. *)
Lemma hop1_zero_challengeE (D : distinguisher alice_hop_jointT) :
  alice_hop_game_success 2 D
    = indcpa_fdist_success_zero charlie_pkey (v3_challenge_adversary D).
Proof.
rewrite alice_hop_game_successE.
rewrite (reduction_challenge_acceptE (pk := charlie_pkey)
    (msg := fun _ : hop1_stateT => 0)
    (assemble := hop1_assemble) hop1_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite reduction_challenge_successE indcpa_fdist_success_zeroE.
Qed.

(* The gap D shows between hop 1 and hop 2 equals the advantage of
   v3_challenge_adversary D against Charlie's key.  Zeroing Charlie's slot costs
   exactly one IND-CPA advantage. *)
Lemma hop1_advantageE (D : distinguisher alice_hop_jointT) :
  `| alice_hop_game_success 1 D - alice_hop_game_success 2 D |
  = indcpa_fdist_epsilon charlie_pkey (v3_challenge_adversary D).
Proof.
by rewrite /indcpa_fdist_epsilon hop1_real_challengeE hop1_zero_challengeE.
Qed.

(* Alice's own input as a constant random variable. *)
Definition V1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ v1.
(* Alice's first protocol weight as a constant random variable. *)
Definition U1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u1.
(* Alice's second protocol weight as a constant random variable. *)
Definition U2c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u2.
(* Alice's third protocol weight as a constant random variable. *)
Definition U3c : {RV alice_sample_fdist -> plain AHE} := const_RV _ u3.

(* The sample coordinates the view reads besides the two secret inputs: the
   masks, the two encryption randomnesses, and Alice's combine randomness. *)
Definition alice_spectator_preT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * (Renc * Renc))%type.

(* The spectator coordinates as a random variable: the part of the sample
   Alice's view reads besides the two secret inputs. *)
Definition AliceSpectatorPre :
    {RV alice_sample_fdist -> alice_spectator_preT} :=
  fun t => (t.1.1.2, t.1.2, t.2).

Let card_spectator_pre :
  #|alice_spectator_preT| = #|alice_spectator_preT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceSpectatorPre). Qed.

Let card_spectator_pre_pair :
  #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|
  = #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% AliceSpectatorPre, [% V2, V3]]). Qed.

(* The spectator coordinates and the secret input pair are jointly uniform. *)
Lemma spectator_pre_pair_uniformE :
  `p_ [% AliceSpectatorPre, [% V2, V3]]
    = (fdist_uniform card_spectator_pre) `x (fdist_uniform card_plain_pair).
Proof.
rewrite -(fdist_uniform_prod card_spectator_pre card_plain_pair
            card_spectator_pre_pair) /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_spectator_pre_pair).
exists (fun p : alice_spectator_preT * (plain AHE * plain AHE) =>
          (p.2, p.1.1.1, p.1.1.2, p.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[r2 r3] [rho2 rho3]] [ra1 ra2]] [v2 v3]].
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

(* The spectator coordinates are independent of the two secret inputs, which is
   what lets the all-zero view be produced from public data alone. *)
Lemma spectator_pre_indep :
  alice_sample_fdist |= AliceSpectatorPre _|_ [% V2, V3].
Proof.
apply: inde_RV_of_prod.
by rewrite spectator_pre_pair_uniformE spectator_pre_uniformE alice_var_uniform.
Qed.

(* The four protocol weights form a constant random variable. *)
Lemma alice_inputs_constE :
  [% V1c, U1c, U2c, U3c]
  = const_RV alice_sample_fdist (v1, u1, u2, u3).
Proof. by apply: boolp.funext => t; rewrite /V1c /U1c /U2c /U3c !const_RVE. Qed.

(* The protocol weights, the leaked output and the two secret inputs satisfy the
   DSDP linear constraint pointwise. *)
Lemma alice_constraint_holds (t : dsdp_alice_sampleT) :
  dsdp_constraint_ring ([% V1c, U1c, U2c, U3c, Sout] t) ([% V2, V3] t).
Proof.
by rewrite /dsdp_constraint_ring /Sout /comp_RV /dsdp_output /V1c /U1c /U2c /U3c
           /= !const_RVE; apply/eqP; ring.
Qed.

(* Conditioned on the protocol weights and the leaked output, the secret input
   pair is uniform on the solution fiber, with mass 1/#|plain AHE|. *)
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

(* Everything Alice's all-zero view carries besides the leaked output. *)
Definition AliceSpectator :
    {RV alice_sample_fdist ->
       ((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE
        * cipher AHE)%type}
  := [% [% R2, R3], [% RA1, RA2], hop0_cipher 2, hop1_cipher 2].

(* The spectator rebuilt from the spectator coordinates, with both ciphertext
   slots encrypting zero.  It is a deterministic function of coordinates
   independent of the secrets. *)
Definition alice_spectator_of (c : alice_spectator_preT) :
    ((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE
     * cipher AHE)%type :=
  (c.1.1, c.2,
   enc bob_pkey 0 (rand_of_renc c.1.2.1),
   enc charlie_pkey 0 (rand_of_renc c.1.2.2)).

(* The spectator is independent of the two secret inputs. *)
Lemma alice_spectator_indep :
  alice_sample_fdist |= AliceSpectator _|_ [% V2, V3].
Proof.
have -> : AliceSpectator = alice_spectator_of `o AliceSpectatorPre.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
exact: (inde_RV_comp alice_spectator_of idfun spectator_pre_indep).
Qed.

(* Given the leaked output, the spectator and Bob's input are conditionally
   independent.  At the all-zero endpoint the leaked output is the single
   channel from V2 into Alice's view. *)
Lemma alice_spectator_cinde :
  alice_sample_fdist |= AliceSpectator _|_ V2 | Sout.
Proof.
apply: cpr_prd_unit_RV; apply: weak_union.
apply/cinde_RV_unit.
exact: (inde_RV_comp idfun (fun p : plain AHE * plain AHE =>
          (p.1, uncurry (dsdp_output v1 u1 u2 u3) p))
        alice_spectator_indep).
Qed.

(* Alice's all-zero view assembled from the spectator and the leaked output.
   Naming: the [_of_] connective names the source the conversion reads, after
   the repository's total-conversion family. *)
Definition alice_hop_tuple_of_spectator
    (p : (((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE * cipher AHE)
          * plain AHE)%type) : dsdp_alice_hop_tupleT :=
  (p.1.1.1.1, p.1.1.1.2, p.2, p.1.1.2, p.1.2).

(* A predictor reading Alice's all-zero view matches Bob's input with
   probability at most 1/#|plain AHE|.
   Naming: [guess] names the success probability being bounded, [all_zero] the
   view it reads, and [invm] the inverse plaintext-space cardinality bounding
   it. *)
Lemma guess_all_zero_le_invm (predict : predictor dsdp_alice_hop_tupleT) :
  Pr alice_sample_fdist [set t | (predict `o (AliceHopTuple 2)) t == V2 t]
    <= #|plain AHE|%:R^-1.
Proof.
by apply: (cinde_diagonal_bound
    (cinde_RV_comp (fun sp s => predict (alice_hop_tuple_of_spectator (sp, s)))
       alice_spectator_cinde)) => a c; exact: alice_V2_cond_le.
Qed.

(* The event that a predictor matches Bob's input is the acceptance event of
   the associated distinguisher on the joint law of the inputs and the view. *)
Lemma guess_event_jointE (predict : predictor dsdp_alice_hop_tupleT) (i : nat) :
  Pr alice_sample_fdist
     [set t | (predict `o AliceHopTuple i) t == V2 t]
  = Pr (`p_ [% V2, V3, AliceHopTuple i])
       [set x | guess_test predict x].
Proof.
by rewrite /dist_of_RV Pr_fdistmap_preim; apply: eq_bigl => t; rewrite !inE.
Qed.

(* A predictor reading Alice's real view returns Bob's input with probability at
   most the inverse plaintext-space cardinality plus the advantages of the two
   hop reductions.  The first term is the information-theoretic residue of the
   leaked output along the DSDP solution fiber, and the two advantages are the
   price of zeroing Bob's and Charlie's ciphertext slots.
   Naming: [fdist] marks the finite-distribution formulation, [V2_real] the
   input bounded and the hop-0 tuple it is bounded at. *)
Theorem dsdp_alice_guess_fdist_V2_real_le
    (predict : predictor dsdp_alice_hop_tupleT) :
  Pr alice_sample_fdist [set t | (predict `o AliceRealTuple) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon bob_pkey
           (v2_challenge_adversary (guess_test predict))
       + indcpa_fdist_epsilon charlie_pkey
           (v3_challenge_adversary (guess_test predict)).
Proof.
rewrite /AliceRealTuple guess_event_jointE -hop0_advantageE -hop1_advantageE.
rewrite -addrA -lerBlDl.
rewrite !alice_hop_game_successE.
apply: le_trans (lerB (lexx _) _) _; last first.
  exact: le_trans (ler_norm _) (ler_distD _ _ _).
by rewrite -guess_event_jointE; exact: guess_all_zero_le_invm.
Qed.

(* The IND-CPA advantage against Bob's key that one predictor buys: the
   predictor is scored by guess_test and that test is embedded in
   v2_challenge_adversary.  It is the price of the hop-0 ciphertext
   replacement, and it is assumption-conditional at Bob's key. *)
Definition bob_guess_epsilon (predict : predictor dsdp_alice_hop_tupleT) : R :=
  indcpa_fdist_epsilon bob_pkey
    (v2_challenge_adversary (guess_test predict)).

(* The Charlie-key counterpart of bob_guess_epsilon: the price of the hop-1
   ciphertext replacement, assumption-conditional at Charlie's key. *)
Definition charlie_guess_epsilon
    (predict : predictor dsdp_alice_hop_tupleT) : R :=
  indcpa_fdist_epsilon charlie_pkey
    (v3_challenge_adversary (guess_test predict)).

(* The negative logarithm of the probability that g recovers Bob's input
   from Alice's real hopping tuple.
   Naming: after [Hunp_leak_S] of the sdistr axis (dsdp_guess_fiber.v),
   with the fixed predictor explicit. *)
Definition alice_predictor_unpredictability
    (predict : predictor dsdp_alice_hop_tupleT) : R :=
  - log (Pr alice_sample_fdist
           [set t | (predict `o AliceRealTuple) t == V2 t]).

Local Notation "'`H_unp^{' g '}'" :=
  (alice_predictor_unpredictability g)
  (at level 0, g at level 200,
   format "'`H_unp^{' g '}'").

(* The negative logarithm of a predictor's success probability on Alice's real
   view is bounded below by the log of the plaintext-space cardinality minus a
   correction term in the two hop advantages.  When the two advantages are
   small the correction term is small, and what remains is the value the left
   side would take if Alice were guessing uniformly at random over the
   plaintext space.
   Naming: [fdist] marks the finite-distribution formulation, [ge] the
   direction of the bound. *)
Theorem dsdp_alice_unpredictability_fdist_ge
    (predict : predictor dsdp_alice_hop_tupleT)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (predict `o AliceRealTuple) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R
               * (bob_guess_epsilon predict + charlie_guess_epsilon predict))
  <= - log (Pr alice_sample_fdist
              [set t | (predict `o AliceRealTuple) t == V2 t]).
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R) by rewrite ltr0n card_plain_gt0.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R
                        * (bob_guess_epsilon predict
                           + charlie_guess_epsilon predict) :> R).
  apply: ltr_pwDl ltr01 (mulr_ge0 (ler0n _ _) _).
  by rewrite addr_ge0 // /bob_guess_epsilon /charlie_guess_epsilon
             /indcpa_fdist_epsilon normr_ge0.
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

(* The same bound stated through alice_predictor_unpredictability: the log of
   the plaintext-space cardinality minus the correction term in the two hop
   advantages lower-bounds the named unpredictability quantity.
   Naming: after [dsdp_alice_unpredictability_fdist_ge], whose right-hand
   side this theorem folds into the named quantity. *)
Theorem dsdp_alice_predictor_unpredictability_fdist_ge
    (predict : predictor dsdp_alice_hop_tupleT)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (predict `o AliceRealTuple) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R
               * (bob_guess_epsilon predict + charlie_guess_epsilon predict))
  <= `H_unp^{predict}.
Proof.
exact: dsdp_alice_unpredictability_fdist_ge.
Qed.

(* The pushforward of a product distribution along a pair of coordinate maps is
   the product of the pushforwards. *)
Lemma fdistmap_prod (A1 A2 B1 B2 : finType) (Q1 : R.-fdist A1)
    (Q2 : R.-fdist A2) (f1 : A1 -> B1) (f2 : A2 -> B2) :
  fdistmap (fun a : (A1 * A2)%type => (f1 a.1, f2 a.2)) (Q1 `x Q2)
  = (fdistmap f1 Q1) `x (fdistmap f2 Q2).
Proof.
apply/fdist_ext => -[b1 b2]; rewrite fdist_prodE !fdistmapE big_distrl /=.
rewrite (eq_bigr (fun i => \sum_(a in preim f2 (pred1 b2)) (Q1 i * Q2 a)));
  last by move=> i _; rewrite big_distrr.
rewrite pair_big /=; apply: eq_big => [[a1 a2]|[a1 a2] _] /=.
  by rewrite !inE /= xpair_eqE.
by rewrite fdist_prodE.
Qed.

(* The pushforward of a product distribution along a map acting only on the
   second coordinate keeps the first factor. *)
Lemma fdistmap_prodr (A1 A2 B2 : finType) (Q1 : R.-fdist A1)
    (Q2 : R.-fdist A2) (f2 : A2 -> B2) :
  fdistmap (fun a : (A1 * A2)%type => (a.1, f2 a.2)) (Q1 `x Q2)
  = Q1 `x (fdistmap f2 Q2).
Proof. by rewrite (fdistmap_prod Q1 Q2 idfun f2) fdistmap_id. Qed.

(* The law a simulator produces from a value of the leaked output: uniform
   masks, uniform combine randomness, that output, and an encryption of zero
   under each of the two other parties' keys.  It reads only the output value
   and the two public keys, so everything it produces is available without the
   secret inputs. *)
Definition dsdp_alice_simulator (s : plain AHE) :
    R.-fdist dsdp_alice_hop_tupleT :=
  ((((fdist_uniform card_plain_pair) `x (fdist_uniform card_renc_pair))
      `x (fdist1 s))
     `x (enc_fdist bob_pkey 0))
    `x (enc_fdist charlie_pkey 0).

(* The spectator coordinates with the two encryption randomnesses last. *)
Definition alice_spectator_pre2T : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * Renc * Renc)%type.

(* The spectator coordinates with the two encryption randomnesses last, the
   layout on which the spectator law factors as the simulator's product. *)
Definition AliceSpectatorPre2 :
    {RV alice_sample_fdist -> alice_spectator_pre2T} :=
  fun t => (t.1.1.2, t.2, t.1.2.1, t.1.2.2).

(* The reordering of the spectator coordinates that separates the two
   encryption randomnesses. *)
Definition alice_spectator_regroup (c : alice_spectator_preT) :
    alice_spectator_pre2T := (c.1.1, c.2, c.1.2.1, c.1.2.2).

Let card_masks_ra :
  #|(((plain AHE * plain AHE) * (Renc * Renc))%type : finType)|
  = #|(((plain AHE * plain AHE) * (Renc * Renc))%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% [% R2, R3], [% RA1, RA2]]). Qed.

Let card_masks_ra_rho :
  #|(((plain AHE * plain AHE) * (Renc * Renc) * Renc)%type : finType)|
  = #|(((plain AHE * plain AHE) * (Renc * Renc) * Renc)%type : finType)|.-1.+1.
Proof.
exact: fdist_card_prednK (`p_ [% [% [% R2, R3], [% RA1, RA2]], Rho2]).
Qed.

Let card_spectator_pre2 :
  #|alice_spectator_pre2T| = #|alice_spectator_pre2T|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceSpectatorPre2). Qed.

(* The reordered spectator coordinates are uniform. *)
Lemma spectator_pre2_uniformE :
  `p_ AliceSpectatorPre2 = fdist_uniform card_spectator_pre2.
Proof.
have -> : `p_ AliceSpectatorPre2
        = fdistmap alice_spectator_regroup (`p_ AliceSpectatorPre).
  by rewrite /dist_of_RV fdistmap_comp.
rewrite spectator_pre_uniformE.
apply: (fdistmap_bij_uniform card_spectator_pre card_spectator_pre2).
exists (fun d : alice_spectator_pre2T => (d.1.1.1, (d.1.2, d.2), d.1.1.2)).
  by move=> [[[r2 r3] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[r2 r3] [ra1 ra2]] rho2] rho3].
Qed.

(* The spectator rebuilt from the reordered spectator coordinates. *)
Definition alice_spectator_prod (c : alice_spectator_pre2T) :
    ((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE
     * cipher AHE)%type :=
  (c.1.1.1, c.1.1.2,
   enc bob_pkey 0 (rand_of_renc c.1.2),
   enc charlie_pkey 0 (rand_of_renc c.2)).

(* The spectator is the image of the reordered spectator coordinates under the
   zero-plaintext encryptions. *)
Lemma alice_spectator_prodE :
  AliceSpectator = alice_spectator_prod `o AliceSpectatorPre2.
Proof.
by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
Qed.

(* The law of the spectator is the product of the mask law, the combine
   randomness law and the two zero-plaintext encryption laws. *)
Lemma alice_spectator_law :
  `p_ AliceSpectator
  = ((((fdist_uniform card_plain_pair) `x (fdist_uniform card_renc_pair))
        `x (enc_fdist bob_pkey 0))
       `x (enc_fdist charlie_pkey 0)).
Proof.
have -> : `p_ AliceSpectator
        = fdistmap alice_spectator_prod (`p_ AliceSpectatorPre2).
  by rewrite alice_spectator_prodE /dist_of_RV fdistmap_comp.
rewrite spectator_pre2_uniformE
        (fdist_uniform_prod card_masks_ra_rho card_renc card_spectator_pre2)
        (fdist_uniform_prod card_masks_ra card_renc card_masks_ra_rho)
        (fdist_uniform_prod card_plain_pair card_renc_pair card_masks_ra).
rewrite /enc_fdist -!fdistmap_prodr -[X in _ = fdistmap _ (_ `x X)]fdistmap_id.
rewrite -fdistmap_prod fdistmap_comp; congr fdistmap.
by apply/boolp.funext => -[[[m ra] rho2] rho3].
Qed.

(* The spectator slots of a value of Alice's hopping tuple.
   Naming: the [_of_] connective names the source the projection reads, after
   the repository's total-conversion family. *)
Definition alice_spectator_of_hop_tuple (v : dsdp_alice_hop_tupleT) :
    ((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE
     * cipher AHE)%type :=
  (v.1.1.1.1, v.1.1.1.2, v.1.2, v.2).

Section alice_hop_tuple_all_zero_mass.

Variable BT : finType.
Variable W : {RV alice_sample_fdist -> BT}.
Variable v : dsdp_alice_hop_tupleT.
Variables (w : BT) (s : plain AHE).

(* On the event W = w, the leaked output equals s. *)
Hypothesis Sout_determinedE :
  forall t, W t = w -> Sout t = s.

(* On a conditioning event that determines the leaked output, the joint mass of
   Alice's all-zero view splits into the leaked-output indicator times the joint
   mass of the spectator. *)
Lemma alice_hop_tuple_all_zero_pfwd1E :
  pfwd1 [% (AliceHopTuple 2), W] (v, w)
  = (v.1.1.2 == s)%:R
    * pfwd1 [% AliceSpectator, W] (alice_spectator_of_hop_tuple v, w).
Proof.
case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_hop_tuple /=.
case: (eqVneq sv s) => [->|Hne]; last first.
  rewrite mul0r pfwd1E (_ : finset _ = set0) ?Pr_set0 //.
  apply/setP => t; rewrite !inE; apply/negbTE; apply: contra Hne.
  rewrite !xpair_eqE => /andP[/andP[/andP[/andP[_ Hsv] _] _] Hw].
  by rewrite -(eqP Hsv) (Sout_determinedE (eqP Hw)).
rewrite mul1r !pfwd1E; congr (Pr _ _).
apply/setP => t; rewrite !inE !xpair_eqE.
case: (W t =P w) => [Ew|_]; last by rewrite !andbF.
by rewrite (Sout_determinedE Ew) eqxx !andbT.
Qed.

End alice_hop_tuple_all_zero_mass.

(* Conditioned on the two secret inputs, Alice's all-zero view follows the
   simulator law fed the leaked output of those inputs.
   Naming: after [bob_view_cond_sim] of [du2002/spp_simulator.v], with the
   [dsdp_alice] prefix separating it from that near-namesake. *)
Lemma dsdp_alice_hop_tuple_cond_sim (v : dsdp_alice_hop_tupleT)
    (v2 v3 : plain AHE) :
  `Pr[ [% V2, V3] = (v2, v3) ] != 0 ->
  `Pr[ (AliceHopTuple 2) = v | [% V2, V3] = (v2, v3) ]
    = dsdp_alice_simulator (dsdp_output v1 u1 u2 u3 v2 v3) v.
Proof.
move=> Hvv.
have HW t : [% V2, V3] t = (v2, v3) ->
    Sout t = dsdp_output v1 u1 u2 u3 v2 v3.
  by rewrite /Sout /comp_RV => ->.
rewrite cpr_eqE (alice_hop_tuple_all_zero_pfwd1E v HW)
        (alice_spectator_indep _ _).
rewrite mulrA mulfK // -dist_of_RVE alice_spectator_law.
case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_hop_tuple /dsdp_alice_simulator
        !fdist_prodE fdist1E /=.
by ring.
Qed.

(* Conditioned on the leaked output, Alice's all-zero view follows the simulator
   law fed that output. *)
Corollary dsdp_alice_hop_tuple_cond_sim_S (v : dsdp_alice_hop_tupleT)
    (s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ (AliceHopTuple 2) = v | Sout = s ] = dsdp_alice_simulator s v.
Proof.
move=> Hs.
have Hind : alice_sample_fdist |= AliceSpectator _|_ Sout.
  exact: (inde_RV_comp idfun (uncurry (dsdp_output v1 u1 u2 u3))
            alice_spectator_indep).
rewrite cpr_eqE (alice_hop_tuple_all_zero_pfwd1E v (fun=> id)) (Hind _ _).
rewrite mulrA mulfK // -dist_of_RVE alice_spectator_law.
case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_hop_tuple /dsdp_alice_simulator
        !fdist_prodE fdist1E /=.
by ring.
Qed.

(* The ideal-world joint law of the two secret inputs and a simulated view: the
   honest input law bound to the simulator fed the leaked output. *)
Definition alice_ideal_joint :
    R.-fdist (plain AHE * plain AHE * dsdp_alice_hop_tupleT) :=
  vv <- `p_ [% V2, V3] ;
  fdistmap (fun v => (vv.1, vv.2, v))
    (dsdp_alice_simulator (dsdp_output v1 u1 u2 u3 vv.1 vv.2)).

(* The ideal-world joint law is the joint law of the two secret inputs and
   Alice's all-zero view.  The ideal world is therefore hop 2 itself, and the
   simulation gap is the two-hop distance. *)
Lemma alice_ideal_jointE :
  alice_ideal_joint = `p_ [% V2, V3, (AliceHopTuple 2)].
Proof.
apply/fdist_ext => -[[v2 v3] v].
rewrite fdistbindE (bigD1 (v2, v3)) //= big1 ?addr0; last first.
  move=> [w2 w3] Hne; rewrite [X in _ * X]fdistmapE big1 ?mulr0 // => a.
  by rewrite !inE /= xpair_eqE (negbTE Hne).
rewrite [X in _ * X]fdistmapE (big_pred1 v); last first.
  by move=> a; rewrite !inE /= xpair_eqE eqxx.
rewrite !dist_of_RVE [RHS]pfwd1_pairC /unstable.swap /=.
case: (eqVneq `Pr[ [% V2, V3] = (v2, v3) ] 0) => [H0|H0].
  by rewrite H0 mul0r pfwd1_domin_RV1.
by rewrite -[RHS]cpr_eqE_mul (dsdp_alice_hop_tuple_cond_sim v H0) mulrC.
Qed.

(* A distinguisher separates the real joint law of the two secret inputs and
   Alice's view from the ideal-world joint law by at most the sum of the
   advantages of the two hop reductions.  This is the simulation-based reading
   of the same two hops: the real world is hop 0, the ideal world is hop 2, and
   the distance between them is the sum of the two IND-CPA advantages.
   Naming: [sim_advantage] rather than [advantage_sim] because the statement
   bounds a distinguishing gap between two laws rather than instantiating a
   simulation-advantage predicate. *)
Theorem dsdp_alice_sim_advantage_fdist_le
    (D : distinguisher alice_hop_jointT) :
  `| Pr (`p_ [% V2, V3, AliceRealTuple]) [set x | D x]
     - Pr alice_ideal_joint [set x | D x] |
  <= indcpa_fdist_epsilon bob_pkey (v2_challenge_adversary D)
     + indcpa_fdist_epsilon charlie_pkey (v3_challenge_adversary D).
Proof.
rewrite /AliceRealTuple alice_ideal_jointE -hop0_advantageE -hop1_advantageE.
rewrite !alice_hop_game_successE.
exact: ler_distD.
Qed.

(* Alice's view rebuilt from a value of her hopping tuple: that
   value, Alice's two outgoing combines, and the plaintext of her final
   decrypt-on-receive.
   Naming: [_of_] after the repository's total-conversion family, paired with
   the [alice_view_of_hop_tupleE] rewrite lemma below. *)
Definition alice_view_of_hop_tuple (v : dsdp_alice_hop_tupleT) :
    dsdp_alice_hop_tupleT * cipher AHE * cipher AHE * plain AHE :=
  let c_bob := v.1.2 in
  let c_charlie := v.2 in
  let r2 := v.1.1.1.1.1 in
  let r3 := v.1.1.1.1.2 in
  let ra1 := v.1.1.1.2.1 in
  let ra2 := v.1.1.1.2.2 in
  let s := v.1.1.2 in
  let combine_bob :=
    Emul (Epow c_bob u2)
         (enc bob_pkey r2 (rand_of_renc ra1)) in
  let combine_charlie :=
    Emul (Epow c_charlie u3)
         (enc charlie_pkey r3 (rand_of_renc ra2)) in
  let recv_plain := s - u1 * v1 + r2 + r3 in
  (v, combine_bob, combine_charlie, recv_plain).

(* The carrier of Alice's full view: her hopping tuple, her two outgoing
   combines, and the plaintext of her final decrypt-on-receive. *)
Definition alice_viewT : finType :=
  (dsdp_alice_hop_tupleT * cipher AHE * cipher AHE * plain AHE)%type.

(* The IND-CPA adversary against Bob's key induced by a view predictor: it
   embeds the challenge in the ciphertext of Bob's input V2, rebuilds Alice's
   view around it, and guesses with the predictor. *)
Definition bob_view_adversary (predict : predictor alice_viewT) :
    indcpa_fdist_adversary :=
  v2_challenge_adversary (guess_test (predict \o alice_view_of_hop_tuple)).

(* The Charlie-key counterpart of bob_view_adversary. *)
Definition charlie_view_adversary (predict : predictor alice_viewT) :
    indcpa_fdist_adversary :=
  v3_challenge_adversary (guess_test (predict \o alice_view_of_hop_tuple)).

(* Alice's outgoing combine toward Bob's key, replaying her real protocol step:
   the ciphertext she received from Bob raised to her second weight, times an
   encryption of her first mask. *)
Definition AliceCombineBob : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc bob_pkey (V2 t) (rand_of_renc (Rho2 t))) u2)
    (enc bob_pkey (R2 t) (rand_of_renc (RA1 t))).

(* Alice's outgoing combine toward Charlie's key, the symmetric counterpart of
   AliceCombineBob: the ciphertext she received from Charlie raised to her
   third weight, times an encryption of her second mask. *)
Definition AliceCombineCharlie : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc charlie_pkey (V3 t) (rand_of_renc (Rho3 t))) u3)
    (enc charlie_pkey (R3 t) (rand_of_renc (RA2 t))).

(* The plaintext Alice recovers at her final decrypt-on-receive step: the two
   weighted inputs of the other parties plus her two masks.  Its value is
   determined by the hopping tuple through alice_view_of_hop_tuple.
   Naming: Owner-Verb-Noun, parallel to AliceCombineBob and
   AliceCombineCharlie; [Plain] is the AHE plaintext carrier. *)
Definition AliceRecvPlain : {RV alice_sample_fdist -> plain AHE} :=
  fun t => u2 * V2 t + u3 * V3 t + R2 t + R3 t.

(* Alice's four real observables: her hopping tuple, her two outgoing combines,
   and the plaintext of her final decrypt-on-receive. *)
Definition AliceView : {RV alice_sample_fdist -> alice_viewT} :=
  [% AliceRealTuple, AliceCombineBob, AliceCombineCharlie, AliceRecvPlain].

(* AliceView is alice_view_of_hop_tuple composed with AliceHopTuple 0.
   Her combine addressed to Bob's key, her combine addressed to Charlie's key,
   and the plaintext of her final decrypt-on-receive are each a deterministic
   function of the hopping tuple, so a bound on the tuple transfers to her
   whole view with no extra term.
   Naming: [E] marks the equation unfolding [AliceView] into
   [alice_view_of_hop_tuple] composed with [AliceHopTuple 0]. *)
Lemma alice_view_of_hop_tupleE :
  AliceView = alice_view_of_hop_tuple \o AliceRealTuple.
Proof.
apply/boolp.funext => t.
rewrite /AliceView /AliceRealTuple /alice_view_of_hop_tuple /AliceCombineBob
        /AliceCombineCharlie /AliceRecvPlain /=.
by congr (_, _, _, _); rewrite /Sout /comp_RV /dsdp_output /=; ring.
Qed.

(* A predictor reading Alice's view matches Bob's input with
   probability at most 1/#|plain AHE| plus the advantages of the two hop
   reductions.
   Naming: [dsdp_alice_guess_fdist] as in the hopping-tuple headline, with
   [view] naming the view read. *)
Corollary dsdp_alice_guess_fdist_view_le
    (predict : predictor alice_viewT) :
  Pr alice_sample_fdist [set t | (predict `o AliceView) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon bob_pkey (bob_view_adversary predict)
       + indcpa_fdist_epsilon charlie_pkey (charlie_view_adversary predict).
Proof.
by rewrite alice_view_of_hop_tupleE; exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

End dsdp_alice_fdist_secrecy.

Section dsdp_alice_simulator_pub_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.

(* The two uniform factors below reuse the card constants the main section
   discharges.  Those [_subproof] names are generated from the [Let] names
   [card_plain_pair] and [card_renc_pair] of Section dsdp_alice_fdist_secrecy,
   so renaming either [Let] breaks this section. *)

(* The simulated view law with its cryptographic setup passed as the two
   public keys it encrypts under. *)
Definition dsdp_alice_simulator_pub (pk_b pk_c : pub_key AHE)
    (s : plain AHE) : R.-fdist (dsdp_alice_hop_tupleT AHE Renc) :=
  ((((fdist_uniform (card_plain_pair_subproof AHE))
       `x (fdist_uniform (card_renc_pair_subproof card_renc)))
      `x (fdist1 s))
     `x (enc_fdist card_renc rand_of_renc pk_b 0))
    `x (enc_fdist card_renc rand_of_renc pk_c 0).

(* Instantiating the public keys as any party-indexed key table yields the
   existing simulator. *)
Lemma dsdp_alice_simulator_pubE (pkey_of_party : party_id -> pub_key AHE)
    (s : plain AHE) :
  dsdp_alice_simulator_pub (pkey_of_party Bob) (pkey_of_party Charlie) s
  = dsdp_alice_simulator card_renc rand_of_renc pkey_of_party s.
Proof. by []. Qed.

End dsdp_alice_simulator_pub_sec.

Section dsdp_alice_enc_uniform_img_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.

(* The encryption of v under pk as a function of the randomness index.
   Naming: the [_of_] connective names the source the map reads, after the
   repository's total-conversion family. *)
Definition enc_of_renc (pk : pub_key AHE) (v : plain AHE) :
    Renc -> cipher AHE :=
  fun r => enc pk v (rand_of_renc r).

(* The reachable encryptions are nonempty, since the randomness-index type
   is. *)
Lemma card_enc_img_gt0 (pk : pub_key AHE) (v : plain AHE) :
  (0 < #|enc_of_renc pk v @: [set: Renc]|)%N.
Proof. by rewrite card_gt0 imset_eq0 -card_gt0 cardsT card_renc. Qed.

(* The property that the challenge law is uniform on the reachable encryptions
   of v under pk.  It is a property of the scheme's encryption map, standing on
   its own beside the hop correspondences.
   Naming: [img] marks the image the uniformity ranges over, after
   [fdistmap_uniform_supp_img] of extra_proba.v. *)
Definition enc_fdist_uniform_img (pk : pub_key AHE) (v : plain AHE) : Prop :=
  enc_fdist card_renc rand_of_renc pk v
  = fdist_uniform_supp R (card_enc_img_gt0 pk v).

(* Equal fiber cardinalities over the image suffice.
   Naming: [_fiber] marks the sufficient condition the lemma consumes. *)
Lemma enc_fdist_uniform_img_fiber (pk : pub_key AHE) (v : plain AHE) :
  (forall c c', c \in enc_of_renc pk v @: [set: Renc] ->
                c' \in enc_of_renc pk v @: [set: Renc] ->
     #|[set r | enc_of_renc pk v r == c]|
     = #|[set r | enc_of_renc pk v r == c']|) ->
  enc_fdist_uniform_img pk v.
Proof.
exact: (fdistmap_uniform_supp_img card_renc (card_enc_img_gt0 pk v)).
Qed.

(* Injectivity of the composed encryption map suffices.
   Naming: [_inj] marks the sufficient condition the lemma consumes. *)
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

(* Under the named property, each reachable ciphertext carries mass one over
   the number of reachable encryptions.
   Naming: the [E] suffix marks the mass equation the property yields. *)
Lemma enc_fdist_uniform_imgE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist_uniform_img pk v ->
  forall c, c \in enc_of_renc pk v @: [set: Renc] ->
  enc_fdist (R:=R) card_renc rand_of_renc pk v c
  = #|enc_of_renc pk v @: [set: Renc]|%:R^-1.
Proof. by move=> H c Hc; rewrite H fdist_uniform_supp_in. Qed.

End dsdp_alice_enc_uniform_img_sec.
