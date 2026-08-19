From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

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
(* order.  The full sample is                                                  *)
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
(*   Pre-encryption form of Hop1State.  hop1_state_of encrypts zero using      *)
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
(*   Alice's all-zero hopping tuple without Sout.  Its law supplies the        *)
(*   remaining components of the simulator output.                            *)
(*                                                                            *)
(* AliceSpectatorPre2                                                         *)
(*   (R2, R3, RA1, RA2, Rho2, Rho3)                                         *)
(*   Reordered spectator coordinates.  Placing the encryption randomnesses    *)
(*   last exposes the product law used to derive the simulator distribution.  *)
(*                                                                            *)
(* ```                                                                        *)
(*        dsdp_alice_sampleT == the sample space: the two honest inputs,      *)
(*                              Alice's two masks, the two hop encryption     *)
(*                              randomnesses and Alice's two combine          *)
(*                              randomnesses                                  *)
(*        alice_sample_fdist == the uniform product distribution on that      *)
(*                              sample space                                  *)
(*                    V2, V3 == the honest inputs of Bob and of Charlie       *)
(*                    R2, R3 == Alice's two mask plaintexts                   *)
(*                Rho2, Rho3 == the randomness of the two hop encryptions     *)
(*                  RA1, RA2 == the randomness of Alice's two combines        *)
(*                      Sout == the protocol output Alice legitimately learns *)
(*             hop0_cipher i == the Bob-key ciphertext slot, encrypting V2    *)
(*                              for i = 0 and zero for larger i               *)
(*             hop1_cipher i == the Charlie-key ciphertext slot, encrypting   *)
(*                              V3 for i at most 1 and zero for larger i      *)
(*     dsdp_alice_hop_tupleT == the type of Alice's hopping tuple: masks,     *)
(*                              combine randomness, output and the two        *)
(*                              ciphertext slots                              *)
(*          alice_hop_jointT == the type of the two honest inputs paired with *)
(*                              Alice's hopping tuple                         *)
(*           AliceHopTuple i == Alice's hopping tuple with its first i        *)
(*                              ciphertext slots zeroed                       *)
(*   alice_hop_joint_fdist i == the joint distribution of the two honest      *)
(*                              inputs and Alice's hopping tuple at hop i     *)
(* alice_hop_game_success i D == the probability that a distinguisher D       *)
(*                              returns true at hop i                         *)
(*   alice_hop_game_successE == rewrites that probability over the joint      *)
(*                              distribution at hop i                         *)
(*            enc_fdist pk v == the law of an encryption of v under pk with   *)
(*                              uniform randomness                            *)
(*                x <- m ; f == a sampling step of an experiment, the bind    *)
(*                              of a distribution with a stochastic map       *)
(*                     ret a == the Dirac distribution at a                   *)
(*    indcpa_fdist_adversary == a single-query real-or-zero adversary: a      *)
(*                              state type adv_state, a law adv_choose over   *)
(*                              it, a challenge plaintext adv_plain read off  *)
(*                              the state, and a decision adv_decide on the   *)
(*                              state and the challenge ciphertext            *)
(* indcpa_fdist_success_real == the probability that the adversary accepts    *)
(*                              when the challenge encrypts its chosen        *)
(*                              plaintext                                     *)
(* indcpa_fdist_success_zero == the probability that the adversary accepts    *)
(*                              when the challenge encrypts zero              *)
(*      indcpa_fdist_epsilon == the absolute gap between those two            *)
(*                              probabilities                                 *)
(*        enc_slot_resampleE == the law of a state paired with a slot         *)
(*                              computed from the state and a coordinate      *)
(*                              disjoint from the state factors as a          *)
(*                              stochastic map resampling that coordinate     *)
(*    hop0_stateT, Hop0State == the adversary state of hop 0 and its random   *)
(*                              variable                                      *)
(*    hop1_stateT, Hop1State == the adversary state of hop 1 and its random   *)
(*                              variable                                      *)
(*              Hop1StatePre == the hop-1 state before the hop-0 slot is      *)
(*                              encrypted                                     *)
(*             hop1_state_of == the map carrying Hop1StatePre to Hop1State    *)
(*             hop0_assemble == the tested joint value reconstructed from a   *)
(*                              hop-0 reduction state and Bob's challenge     *)
(*                              ciphertext                                    *)
(*             hop1_assemble == the tested joint value reconstructed from a   *)
(*                              hop-1 reduction state and Charlie's challenge *)
(*                              ciphertext                                    *)
(*          hop0_reduction D == the reduction of a distinguisher D to Bob's   *)
(*                              key                                           *)
(*          hop1_reduction D == the reduction of a distinguisher D to         *)
(*                              Charlie's key                                 *)
(*       hop_challenge_fdist == the joint law obtained by sampling a          *)
(*                              reduction state and its challenge ciphertext  *)
(*                              before reconstructing the tested value        *)
(*      hop_challenge_fdistE == the law of a tested value assembled from a    *)
(*                              reduction state and independent uniform       *)
(*                              encryption randomness is that challenge law   *)
(*     hop_challenge_acceptE == equal joint laws give equal acceptance        *)
(*                              probabilities for every Boolean test          *)
(*    hop_challenge_successE == the challenge law tested by a distinguisher   *)
(*                              is the state law bound with the pushforward   *)
(*                              of that distinguisher along each challenge    *)
(*                              law                                           *)
(*        V1c, U1c, U2c, U3c == Alice's four protocol weights as constant     *)
(*                              random variables                              *)
(*      alice_spectator_preT == the sample coordinates Alice's hopping        *)
(*                              tuple reads besides the two inputs            *)
(*         AliceSpectatorPre == the random variable of those coordinates      *)
(*            AliceSpectator == everything Alice's all-zero view carries      *)
(*                              besides the output                            *)
(*        alice_spectator_of == the spectator rebuilt from the spectator      *)
(*                              coordinates                                   *)
(* alice_hop_tuple_of_spectator == Alice's all-zero view assembled from the   *)
(*                              spectator and the output                      *)
(*  distinguisher_of_guess g == the distinguisher accepting when the          *)
(*                              predictor g returns the first input of its    *)
(*                              argument                                      *)
(* alice_predictor_unpredictability g == the negative logarithm of the        *)
(*                              probability that the predictor g recovers     *)
(*                              Bob's input from Alice's real hopping tuple   *)
(*             fdistmap_prod == the pushforward of a product along a pair of  *)
(*                              coordinate maps is the product of the         *)
(*                              pushforwards                                  *)
(*            fdistmap_prodr == the pushforward of a product along a map      *)
(*                              acting only on the second coordinate keeps    *)
(*                              the first factor                              *)
(*    dsdp_alice_simulator s == the simulated view law at output value s:     *)
(*                              uniform masks, uniform combine randomness, s, *)
(*                              and an encryption of zero under each of the   *)
(*                              two other keys                                *)
(*     alice_spectator_pre2T == the spectator coordinates with the two        *)
(*                              encryption randomnesses last                  *)
(*        AliceSpectatorPre2 == the random variable of that layout            *)
(*   alice_spectator_regroup == the reordering of the spectator coordinates   *)
(*                              onto that layout                              *)
(*      alice_spectator_prod == the spectator rebuilt from the reordered      *)
(*                              spectator coordinates                         *)
(* alice_spectator_of_hop_tuple == the spectator slots of a value of Alice's  *)
(*                              view                                          *)
(*         alice_ideal_joint == the ideal-world joint law of the two inputs   *)
(*                              and a simulated view                          *)
(*   alice_view_of_hop_tuple == Alice's view rebuilt from a value             *)
(*                              of the hopping tuple                          *)
(*           AliceCombineBob == Alice's outgoing combine addressed to Bob's   *)
(*                              key                                           *)
(*       AliceCombineCharlie == Alice's outgoing combine addressed to         *)
(*                              Charlie's key                                 *)
(*            AliceRecvPlain == the plaintext of Alice's final                *)
(*                              decrypt-on-receive                            *)
(*                 AliceView == Alice's four real observables: the hopping    *)
(*                              tuple, the two combines and that plaintext    *)
(*  alice_view_of_hop_tupleE == those four observables assemble into the      *)
(*                              reconstruction of Alice's view from the       *)
(*                              hopping tuple                                 *)
(* dsdp_alice_simulator_pub pk_b pk_c s ==                                    *)
(*                              the simulated view law with its setup passed  *)
(*                              as the two public keys it encrypts under      *)
(* dsdp_alice_simulator_pubE == any party-indexed key table instantiates the  *)
(*                              public-key simulator to dsdp_alice_simulator  *)
(*        enc_of_renc pk v r == the encryption of v under pk at coin index r  *)
(*     card_enc_img_gt0 pk v == the reachable encryptions of v under pk are   *)
(*                              nonempty                                      *)
(* enc_fdist_uniform_img pk v ==                                              *)
(*                              the challenge law is uniform over the         *)
(*                              reachable encryptions of v under pk           *)
(* enc_fdist_uniform_img_fiber ==                                             *)
(*                              equal fiber cardinalities over the image      *)
(*                              establish that property                       *)
(* enc_fdist_uniform_img_inj == injectivity of the coin-index encryption map  *)
(*                              establishes that property                     *)
(*    enc_fdist_uniform_imgE == under that property each reachable            *)
(*                              ciphertext carries mass one over the number   *)
(*                              of reachable encryptions                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Scope. The statements are average-case over the honest inputs V2 and V3,   *)
(* which are sampled uniformly inside the experiment. Each per-hop epsilon is *)
(* a single-query advantage at a fixed key, a number related to but distinct  *)
(* from the multi-query party-indexed oracle advantage of indcpa_ror.v. A     *)
(* bound here is informative to the extent that its epsilons are small, and   *)
(* holds vacuously once they exceed 1. The efficiency reading of the          *)
(* reductions stays on paper: the adversary is a plain function record, and   *)
(* complexity is argued outside the formalization.                            *)
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
(* The randomness of the encryption Alice receives from Bob. *)
Definition Rho2 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.1.
(* The randomness of the encryption Alice receives from Charlie. *)
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

(* The output written out at the protocol's weights. *)
Lemma SoutE t : Sout t = u1 * v1 + u2 * V2 t + u3 * V3 t.
Proof. by []. Qed.

(* The Bob-key ciphertext slot of Alice's hopping tuple, encrypting Bob's
   input at index 0 and zero at every larger index. *)
Definition hop0_cipher (i : nat) : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc (pkey_of_party Bob) (if (0 < i)%N then 0 else V2 t)
               (rand_of_renc (Rho2 t)).

(* The Charlie-key ciphertext slot of Alice's hopping tuple, encrypting
   Charlie's input at indices 0 and 1 and zero at every larger index. *)
Definition hop1_cipher (i : nat) : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => enc (pkey_of_party Charlie) (if (1 < i)%N then 0 else V3 t)
               (rand_of_renc (Rho3 t)).

(* The type of Alice's hopping tuple: her two masks, her two combine
   randomnesses, the leaked output, and the two ciphertexts she receives. *)
Definition dsdp_alice_hop_tupleT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * cipher AHE * cipher AHE)%type.

(* The type of the two honest inputs paired with Alice's hopping tuple. *)
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

(* The acceptance probability at hop i is the probability that D returns true
   under the joint distribution at hop i. *)
Lemma alice_hop_game_successE (i : nat) (D : alice_hop_jointT -> bool) :
  alice_hop_game_success i D
    = Pr (alice_hop_joint_fdist i) [set x | D x].
Proof. exact: Pr_fdistmap_bool. Qed.

(* The law of an encryption of a plaintext under a public key, with uniform
   encryption randomness. *)
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  fdistmap (fun r => enc pk v (rand_of_renc r)) (fdist_uniform card_renc).

(* A sampling step of an experiment, the bind of a distribution with a
   stochastic map. *)
Local Notation "x '<-' m ';' f" := (m >>= (fun x => f))
  (at level 100, right associativity,
   format "'[v' x  '<-'  m ;  '//' f ']'") : fdist_scope.

(* The outcome of an experiment that samples nothing further, the Dirac
   distribution at a value. *)
Local Notation "'ret' a" := (fdist1 a) (at level 0) : fdist_scope.

(* A single-query real-or-zero adversary: a state type, a law over it, a
   challenge plaintext read off the state, and a decision taken on the
   state and the challenge ciphertext. *)
Record indcpa_fdist_adversary := {
  adv_state : finType ;
  adv_choose : R.-fdist adv_state ;
  adv_plain : adv_state -> plain AHE ;
  adv_decide : adv_state -> cipher AHE -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

(* The probability that the adversary accepts when the challenge encrypts the
   plaintext it chose.
   Naming: [_success_real] after [oracle_encrypt_real] and
   [guess_sdistr_success_real]; [Pr_] is reserved for the lemma family. *)
Definition indcpa_fdist_success_real (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (c  <- adv_choose adv ;
      ch <- enc_fdist pk (adv_plain adv c) ;
      ret (adv_decide adv c ch))
     [set true].

(* The real success probability as a bind of the state law with the
   pushforward of the decision along the challenge law. *)
Lemma indcpa_fdist_success_realE (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) :
  indcpa_fdist_success_real pk adv
  = Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                       (enc_fdist pk (adv_plain adv c))))
       [set true].
Proof. by []. Qed.

(* The probability that the adversary accepts when the challenge encrypts
   zero.
   Naming: [_success_zero] after [oracle_encrypt_zero]; [Pr_] is reserved for
   the lemma family. *)
Definition indcpa_fdist_success_zero (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (c  <- adv_choose adv ;
      ch <- enc_fdist pk 0 ;
      ret (adv_decide adv c ch))
     [set true].

(* The zero success probability as a bind of the state law with the
   pushforward of the decision along the challenge law. *)
Lemma indcpa_fdist_success_zeroE (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) :
  indcpa_fdist_success_zero pk adv
  = Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                       (enc_fdist pk 0)))
       [set true].
Proof. by []. Qed.

(* The real-or-zero advantage of an adversary at a public key: the absolute
   gap between its two success probabilities. *)
(* This is the assumption of reduction to computationally hard problem. *)
(* To make the epsilon small,
   NEED to assume the adversary cannot get the private key,
   when every time this definition is used.
*)
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.

Section enc_slot_resample.

Variable stateT : finType.
Variable Q : R.-fdist stateT.
Variables
  (State : {RV alice_sample_fdist -> stateT})
  (Rho : {RV alice_sample_fdist -> Renc}).
Variable k : stateT -> Renc -> cipher AHE.

(* The state and selected coordinate have the product of Q and the uniform
   coordinate law. *)
Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = Q `x (fdist_uniform card_renc).

(* The law of a state paired with a slot computed from the state and a
   coordinate disjoint from the state is the law of the state with the
   stochastic map that resamples the coordinate. *)
Lemma enc_slot_resampleE :
  `p_ [% State, (fun t => k (State t) (Rho t))
        : {RV alice_sample_fdist -> cipher AHE}]
  = Q `X (fun a => fdistmap (k a) (fdist_uniform card_renc)).
Proof.
have HL : `p_ [% State, (fun t => k (State t) (Rho t))
                : {RV alice_sample_fdist -> cipher AHE}]
        = fdistmap (fun p : (stateT * Renc)%type => (p.1, k p.1 p.2))
                   (`p_ [% State, Rho]).
  by rewrite /dist_of_RV fdistmap_comp.
rewrite HL state_rho_prodE [in RHS]fdist_prod_bindE fdist_prod_bindE
        fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => a.
rewrite !fdistmap_comp.
congr fdistmap; exact/boolp.funext.
Qed.

End enc_slot_resample.

Let card_sample : #|dsdp_alice_sampleT| = #|dsdp_alice_sampleT|.-1.+1.
Proof. exact: fdist_card_prednK alice_sample_fdist. Qed.

(* The sample space carries the uniform distribution. *)
Lemma alice_sample_fdistE : alice_sample_fdist = fdist_uniform card_sample.
Proof.
apply/fdist_ext => -[[[vv ms] rho] ra].
rewrite fdist_uniformE /alice_sample_fdist !fdist_prodE !fdist_uniformE.
by rewrite -!invfM -!natrM /dsdp_alice_sampleT !card_prod.
Qed.

(* The adversary state of hop 0: the inputs, the masks, Alice's combine
   randomness, and the randomness of the hop-1 encryption. *)
Definition hop0_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * Renc)%type.

(* The random variable of the hop-0 adversary state. *)
Definition Hop0State : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.2).

Let card_hop0_state : #|hop0_stateT| = #|hop0_stateT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ Hop0State). Qed.

Let card_hop0_pair :
  #|((hop0_stateT * Renc)%type : finType)|
    = #|((hop0_stateT * Renc)%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ [% Hop0State, Rho2]). Qed.

(* The hop-0 state and the hop-0 encryption randomness are jointly
   uniform. *)
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

(* The hop-0 encryption randomness is uniform and independent of the hop-0
   state. *)
Lemma hop0_state_prodE :
  `p_ [% Hop0State, Rho2] = (`p_ Hop0State) `x (fdist_uniform card_renc).
Proof.
by rewrite -(fst_RV2 Hop0State Rho2) !hop0_pair_uniformE fdist_prod1.
Qed.

(* The adversary state of hop 1: the inputs, the masks, Alice's combine
   randomness, and the hop-0 ciphertext of zero. *)
Definition hop1_stateT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * cipher AHE)%type.

(* The random variable of the hop-1 adversary state. *)
Definition Hop1State : {RV alice_sample_fdist -> hop1_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, hop0_cipher 1 t).

(* The hop-1 adversary state with the randomness of the hop-0 encryption in
   place of the ciphertext it produces. *)
Definition Hop1StatePre : {RV alice_sample_fdist -> hop0_stateT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.1).

(* The map carrying Hop1StatePre to Hop1State, encrypting zero in the
   hop-0 slot. *)
Definition hop1_state_of (c : hop0_stateT) : hop1_stateT :=
  (c.1.1.1, c.1.1.2, c.1.2,
   enc (pkey_of_party Bob) 0 (rand_of_renc c.2)).

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

(* The hop-1 encryption randomness is uniform and independent of the hop-1
   state. *)
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
Definition hop0_assemble (c : hop0_stateT) (ch : cipher AHE) :
    alice_hop_jointT :=
  let: (vv, masks, ra, rho3) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output v1 u1 u2 u3 vv.1 vv.2, ch,
    enc (pkey_of_party Charlie) vv.2 (rand_of_renc rho3))).

(* The tested hop-1 joint value formed by retaining Bob's stored zero
   ciphertext and placing ch in Charlie's ciphertext slot. *)
Definition hop1_assemble (c : hop1_stateT) (ch : cipher AHE) :
    alice_hop_jointT :=
  let: (vv, masks, ra, c2zero) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output v1 u1 u2 u3 vv.1 vv.2, c2zero, ch)).

(* The adversary that challenges Bob's key on the first input and runs the
   distinguisher on the view rebuilt around the challenge. *)
Definition hop0_reduction (D : alice_hop_jointT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_state := hop0_stateT ;
     adv_choose := `p_ Hop0State ;
     adv_plain := fun c => c.1.1.1.1 ;
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.

(* The adversary that challenges Charlie's key on the second input and runs
   the distinguisher on the view rebuilt around the challenge. *)
Definition hop1_reduction (D : alice_hop_jointT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_state := hop1_stateT ;
     adv_choose := `p_ Hop1State ;
     adv_plain := fun c => c.1.1.1.2 ;
     adv_decide := fun c ch => D (hop1_assemble c ch) |}.

Section hop_challenge.

Variable stateT : finType.
Variables
  (State : {RV alice_sample_fdist -> stateT})
  (Rho : {RV alice_sample_fdist -> Renc}).
Variable pk : pub_key AHE.
Variable msg : stateT -> plain AHE.

(* [assemble c ch] reconstructs the complete joint value tested by a
   distinguisher from reduction state c and challenge ciphertext ch. *)
Variable assemble : stateT -> cipher AHE -> alice_hop_jointT.

Variable X : {RV alice_sample_fdist -> alice_hop_jointT}.

Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = (`p_ State) `x (fdist_uniform card_renc).

Hypothesis X_assembleE : forall t,
  X t = assemble (State t) (enc pk (msg (State t)) (rand_of_renc (Rho t))).

(* The joint law obtained by sampling a reduction state and its challenge
   ciphertext before reconstructing the tested value. *)
Definition hop_challenge_fdist : R.-fdist alice_hop_jointT :=
  c  <- `p_ State ;
  ch <- enc_fdist pk (msg c) ;
  ret (assemble c ch).

(* The protocol-game law from one complete protocol sample equals the
   reduction-game law obtained by separately sampling the reduction state and
   fresh uniform encryption randomness, then applying the same deterministic
   encryption and assembly functions. *)
Lemma hop_challenge_fdistE : `p_ X = hop_challenge_fdist.
Proof.
have -> : `p_ X
        = fdistmap (fun q : stateT * cipher AHE => assemble q.1 q.2)
            (`p_ [% State,
                  (fun t => enc pk (msg (State t)) (rand_of_renc (Rho t)))
                    : {RV alice_sample_fdist -> cipher AHE}]).
  by rewrite /dist_of_RV fdistmap_comp; congr fdistmap; exact/boolp.funext.
rewrite (enc_slot_resampleE (fun c r => enc pk (msg c) (rand_of_renc r))
           state_rho_prodE) fdist_prod_bindE fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (msg c))) fdistmap_comp.
Qed.

(* Equal joint laws give equal acceptance probabilities for every Boolean
   test. *)
Corollary hop_challenge_acceptE (D : alice_hop_jointT -> bool) :
  Pr (`p_ X) [set x | D x]
  = Pr hop_challenge_fdist [set x | D x].
Proof. by rewrite hop_challenge_fdistE. Qed.

(* The challenge law tested by D is the state law bound with the pushforward
   of D along each challenge law. *)
Lemma hop_challenge_successE (D : alice_hop_jointT -> bool) :
  Pr hop_challenge_fdist [set x | D x]
  = Pr (`p_ State >>= (fun c => fdistmap (fun ch => D (assemble c ch))
                                  (enc_fdist pk (msg c)))) [set true].
Proof.
rewrite -Pr_fdistmap_bool /hop_challenge_fdist fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (msg c))) fdistmap_comp.
Qed.

End hop_challenge.

(* The distinguisher on the real view is the hop-0 reduction facing an
   encryption of the first input. *)
Lemma hop0_real_challengeE (D : alice_hop_jointT -> bool) :
  alice_hop_game_success 0 D
    = indcpa_fdist_success_real (pkey_of_party Bob) (hop0_reduction D).
Proof.
rewrite alice_hop_game_successE.
rewrite (hop_challenge_acceptE (pk := pkey_of_party Bob)
    (msg := fun c : hop0_stateT => c.1.1.1.1)
    (assemble := hop0_assemble) hop0_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite hop_challenge_successE indcpa_fdist_success_realE.
Qed.

(* The distinguisher on the view with a zeroed hop-0 slot is the hop-0
   reduction facing an encryption of zero. *)
Lemma hop0_zero_challengeE (D : alice_hop_jointT -> bool) :
  alice_hop_game_success 1 D
    = indcpa_fdist_success_zero (pkey_of_party Bob) (hop0_reduction D).
Proof.
rewrite alice_hop_game_successE.
rewrite (hop_challenge_acceptE (pk := pkey_of_party Bob)
    (msg := fun _ : hop0_stateT => 0)
    (assemble := hop0_assemble) hop0_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite hop_challenge_successE indcpa_fdist_success_zeroE.
Qed.

(* Zeroing the hop-0 slot of the view moves the distinguishing probability by
   the advantage of the hop-0 reduction against Bob's key. *)
Lemma hop0_advantageE (D : alice_hop_jointT -> bool) :
  `| alice_hop_game_success 0 D - alice_hop_game_success 1 D |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D).
Proof.
by rewrite /indcpa_fdist_epsilon hop0_real_challengeE hop0_zero_challengeE.
Qed.

(* The distinguisher on the view with a zeroed hop-0 slot is the hop-1
   reduction facing an encryption of the second input. *)
Lemma hop1_real_challengeE (D : alice_hop_jointT -> bool) :
  alice_hop_game_success 1 D
    = indcpa_fdist_success_real (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite alice_hop_game_successE.
rewrite (hop_challenge_acceptE (pk := pkey_of_party Charlie)
    (msg := fun c : hop1_stateT => c.1.1.1.2)
    (assemble := hop1_assemble) hop1_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite hop_challenge_successE indcpa_fdist_success_realE.
Qed.

(* The distinguisher on the all-zero view is the hop-1 reduction facing an
   encryption of zero. *)
Lemma hop1_zero_challengeE (D : alice_hop_jointT -> bool) :
  alice_hop_game_success 2 D
    = indcpa_fdist_success_zero (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite alice_hop_game_successE.
rewrite (hop_challenge_acceptE (pk := pkey_of_party Charlie)
    (msg := fun _ : hop1_stateT => 0)
    (assemble := hop1_assemble) hop1_state_prodE); last first.
  by move=> -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by rewrite hop_challenge_successE indcpa_fdist_success_zeroE.
Qed.

(* Zeroing the hop-1 slot of the view moves the distinguishing probability by
   the advantage of the hop-1 reduction against Charlie's key. *)
Lemma hop1_advantageE (D : alice_hop_jointT -> bool) :
  `| alice_hop_game_success 1 D - alice_hop_game_success 2 D |
  = indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
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

(* The random variable of the spectator coordinates. *)
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

(* The spectator coordinates are independent of the two secret inputs. *)
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
           /= !const_RVE; ring.
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
  rewrite !pfwd1E; congr (Pr _ _).
  apply/setP => t; rewrite !inE /= !xpair_eqE.
  case: (V2 t =P a) => [Hva|_] //=.
  suff -> : (Sout t == s) = (V3 t == v3star) by rewrite andbb.
  rewrite /Sout /comp_RV /dsdp_output /= Hva.
  have -> : s = u1 * v1 + u2 * a + u3 * v3star
    by rewrite /v3star Hg2; ring.
  by rewrite (inj_eq (addrI _)) (inj_eq u3_inj).
have Hcond_eq : pfwd1 [% V1c, U1c, U2c, U3c, Sout] (v1, u1, u2, u3, s)
              = `Pr[ Sout = s ]
  := pfwd1_RV2_compl Sout (fun=> (v1, u1, u2, u3)) s.
have HcwN : `Pr[ [% V1c, U1c, U2c, U3c] = (v1, u1, u2, u3) ] != 0.
  by apply: contra_neq Hs => /(pfwd1_domin_RV2 Sout s); rewrite -Hcond_eq.
have Hind : alice_sample_fdist
              |= [% V1c, U1c, U2c, U3c] _|_ [% [% V2, V3], Sout]
  by rewrite alice_inputs_constE; exact: inde_const_RV.
rewrite cpr_eqE Hnum -cpr_eqE -(cpr_eq_drop_indep (a, v3star) s HcwN Hind).
by apply: alice_VarRV_cond_uniform; rewrite ?Hcond_eq.
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

(* The spectator rebuilt from the spectator coordinates. *)
Definition alice_spectator_of (c : alice_spectator_preT) :
    ((plain AHE * plain AHE) * (Renc * Renc) * cipher AHE
     * cipher AHE)%type :=
  (c.1.1, c.2,
   enc (pkey_of_party Bob) 0 (rand_of_renc c.1.2.1),
   enc (pkey_of_party Charlie) 0 (rand_of_renc c.1.2.2)).

(* The spectator is independent of the two secret inputs. *)
Lemma alice_spectator_indep :
  alice_sample_fdist |= AliceSpectator _|_ [% V2, V3].
Proof.
have -> : AliceSpectator = alice_spectator_of `o AliceSpectatorPre.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
exact: (inde_RV_comp alice_spectator_of idfun spectator_pre_indep).
Qed.

(* The spectator is conditionally independent of Bob's input given the leaked
   output. *)
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
Lemma guess_all_zero_le_invm (g : dsdp_alice_hop_tupleT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o (AliceHopTuple 2)) t == V2 t]
    <= #|plain AHE|%:R^-1.
Proof.
by apply: (cinde_diagonal_bound
    (cinde_RV_comp (fun sp s => g (alice_hop_tuple_of_spectator (sp, s)))
       alice_spectator_cinde)) => a c; exact: alice_V2_cond_le.
Qed.

(* The distinguisher that accepts when a predictor reading the view slot of its
   input returns the first input. *)
Definition distinguisher_of_guess (g : dsdp_alice_hop_tupleT -> plain AHE) :
    plain AHE * plain AHE * dsdp_alice_hop_tupleT -> bool :=
  fun x => g x.2 == x.1.1.

(* The event that a predictor matches Bob's input is the acceptance event of
   the associated distinguisher on the joint law of the inputs and the view. *)
Lemma guess_event_jointE (g : dsdp_alice_hop_tupleT -> plain AHE) (i : nat) :
  Pr alice_sample_fdist
     [set t | (g `o AliceHopTuple i) t == V2 t]
  = Pr (`p_ [% V2, V3, AliceHopTuple i])
       [set x | distinguisher_of_guess g x].
Proof.
by rewrite /dist_of_RV Pr_fdistmap_preim; apply: eq_bigl => t; rewrite !inE.
Qed.

(* A predictor reading Alice's real view matches Bob's input with probability at
   most 1/#|plain AHE| plus the advantages of the two hop reductions.
   Naming: [dsdp_alice_guess] after [dsdp_alice_guess_V2_real_le] of the
   SSProve axis, with the axis token [fdist] after [guess]. *)
Theorem dsdp_alice_guess_fdist_V2_real_le
    (g : dsdp_alice_hop_tupleT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o (AliceHopTuple 0)) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess g)).
Proof.
rewrite guess_event_jointE -hop0_advantageE -hop1_advantageE -addrA -lerBlDl.
rewrite !alice_hop_game_successE.
apply: le_trans (lerB (lexx _) _) _; last first.
  exact: le_trans (ler_norm _) (ler_distD _ _ _).
by rewrite -guess_event_jointE; exact: guess_all_zero_le_invm.
Qed.

(* The advantage against Bob's key of the hop-0 reduction of the distinguisher
   associated with a predictor. *)
Let eps0 (g : dsdp_alice_hop_tupleT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_party Bob)
    (hop0_reduction (distinguisher_of_guess g)).

(* The advantage against Charlie's key of the hop-1 reduction of the
   distinguisher associated with a predictor. *)
Let eps1 (g : dsdp_alice_hop_tupleT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_party Charlie)
    (hop1_reduction (distinguisher_of_guess g)).

(* The negative logarithm of the probability that g recovers Bob's input
   from Alice's real hopping tuple.
   Naming: after [Hunp_leak_S] of the sdistr axis (dsdp_guess_fiber.v),
   with the fixed predictor explicit. *)
Definition alice_predictor_unpredictability
    (g : dsdp_alice_hop_tupleT -> plain AHE) : R :=
  - log (Pr alice_sample_fdist
           [set t | (g `o (AliceHopTuple 0)) t == V2 t]).

Local Notation "'`H_unp^{' g '}'" :=
  (alice_predictor_unpredictability g)
  (at level 0, g at level 200,
   format "'`H_unp^{' g '}'").

(* The negative logarithm of the success probability of a predictor reading
   Alice's real view is at least log #|plain AHE| minus the logarithm of one
   plus #|plain AHE| times the sum of the two hop advantages.
   Naming: after [dsdp_alice_unpredictability_entropy_ge] of the SSProve axis,
   with the axis token [fdist] in place of [entropy]. *)
Theorem dsdp_alice_unpredictability_fdist_ge
    (g : dsdp_alice_hop_tupleT -> plain AHE)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (g `o (AliceHopTuple 0)) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
  <= - log (Pr alice_sample_fdist
              [set t | (g `o (AliceHopTuple 0)) t == V2 t]).
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R) by rewrite ltr0n card_plain_gt0.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R * (eps0 g + eps1 g) :> R).
  apply: ltr_pwDl ltr01 (mulr_ge0 (ler0n _ _) _).
  by rewrite addr_ge0 // /eps0 /eps1 /indcpa_fdist_epsilon normr_ge0.
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

(* The predictor-specific unpredictability of Bob's input is at least the
   negative-logarithm form of the two-hop guessing bound.
   Naming: after [dsdp_alice_unpredictability_fdist_ge], whose right-hand
   side this theorem folds into the named quantity. *)
Theorem dsdp_alice_predictor_unpredictability_fdist_ge
    (g : dsdp_alice_hop_tupleT -> plain AHE)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (g `o (AliceHopTuple 0)) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
  <= `H_unp^{g}.
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
   under each of the two other parties' keys. *)
Definition dsdp_alice_simulator (s : plain AHE) :
    R.-fdist dsdp_alice_hop_tupleT :=
  ((((fdist_uniform card_plain_pair) `x (fdist_uniform card_renc_pair))
      `x (fdist1 s))
     `x (enc_fdist (pkey_of_party Bob) 0))
    `x (enc_fdist (pkey_of_party Charlie) 0).

(* The spectator coordinates with the two encryption randomnesses last. *)
Definition alice_spectator_pre2T : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * Renc * Renc)%type.

(* The random variable of the reordered spectator coordinates. *)
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
   enc (pkey_of_party Bob) 0 (rand_of_renc c.1.2),
   enc (pkey_of_party Charlie) 0 (rand_of_renc c.2)).

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
        `x (enc_fdist (pkey_of_party Bob) 0))
       `x (enc_fdist (pkey_of_party Charlie) 0)).
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
Hypothesis W_determines_Sout :
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
  by rewrite -(eqP Hsv) (W_determines_Sout (eqP Hw)).
rewrite mul1r !pfwd1E; congr (Pr _ _).
apply/setP => t; rewrite !inE !xpair_eqE.
case: (W t =P w) => [Ew|_]; last by rewrite !andbF.
by rewrite (W_determines_Sout Ew) eqxx !andbT.
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
  `p_ [% V2, V3] >>= (fun vv =>
     fdistmap (fun v => (vv.1, vv.2, v))
       (dsdp_alice_simulator (dsdp_output v1 u1 u2 u3 vv.1 vv.2))).

(* The ideal-world joint law is the joint law of the two secret inputs and
   Alice's all-zero view. *)
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
   advantages of the two hop reductions.
   Naming: [sim_advantage] rather than [advantage_sim] because the statement
   bounds a distinguishing gap between two laws instead of instantiating the
   [advantage_sim_le] predicate of [smc/ssprove_ext_simulator.v]. *)
Theorem dsdp_alice_sim_advantage_fdist_le
    (D : plain AHE * plain AHE * dsdp_alice_hop_tupleT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceHopTuple 0]) [set x | D x]
     - Pr (fdistmap D alice_ideal_joint) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D)
     + indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite Pr_fdistmap_bool alice_ideal_jointE -hop0_advantageE -hop1_advantageE.
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
         (enc (pkey_of_party Bob) r2 (rand_of_renc ra1)) in
  let combine_charlie :=
    Emul (Epow c_charlie u3)
         (enc (pkey_of_party Charlie) r3 (rand_of_renc ra2)) in
  let recv_plain := s - u1 * v1 + r2 + r3 in
  (v, combine_bob, combine_charlie, recv_plain).

(* Alice's outgoing combine toward Bob's key, replaying her real protocol step:
   the ciphertext she received from Bob raised to her second weight, times an
   encryption of her first mask.  Used by alice_view_of_hop_tupleE. *)
Definition AliceCombineBob : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc (pkey_of_party Bob) (V2 t) (rand_of_renc (Rho2 t))) u2)
    (enc (pkey_of_party Bob) (R2 t) (rand_of_renc (RA1 t))).

(* Alice's outgoing combine toward Charlie's key, the symmetric counterpart of
   AliceCombineBob: the ciphertext she received from Charlie raised to her
   third weight, times an encryption of her second mask.  Used by
   alice_view_of_hop_tupleE. *)
Definition AliceCombineCharlie : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc (pkey_of_party Charlie) (V3 t) (rand_of_renc (Rho3 t))) u3)
    (enc (pkey_of_party Charlie) (R3 t) (rand_of_renc (RA2 t))).

(* The plaintext Alice recovers at her final decrypt-on-receive step: the two
   weighted inputs of the other parties plus her two masks.  The last of the
   four observables alice_view_of_hop_tupleE assembles.
   Naming: Owner-Verb-Noun, parallel to AliceCombineBob and
   AliceCombineCharlie; [Plain] is the AHE plaintext carrier. *)
Definition AliceRecvPlain : {RV alice_sample_fdist -> plain AHE} :=
  fun t => u2 * V2 t + u3 * V3 t + R2 t + R3 t.

(* Alice's four real observables: her hopping tuple, her two outgoing combines,
   and the plaintext of her final decrypt-on-receive. *)
Definition AliceView :
    {RV alice_sample_fdist ->
       (dsdp_alice_hop_tupleT * cipher AHE * cipher AHE * plain AHE)%type} :=
  [% (AliceHopTuple 0), AliceCombineBob, AliceCombineCharlie, AliceRecvPlain].

(* Alice's four real observables assemble into the reconstruction of her view
   from her hopping tuple.
   Naming: [E] marks the equation unfolding [AliceView] into
   [alice_view_of_hop_tuple] composed with [AliceHopTuple 0]. *)
Lemma alice_view_of_hop_tupleE :
  AliceView = alice_view_of_hop_tuple \o (AliceHopTuple 0).
Proof.
apply/boolp.funext => t.
rewrite /AliceView /alice_view_of_hop_tuple /AliceCombineBob
        /AliceCombineCharlie /AliceRecvPlain /=.
by congr (_, _, _, _); rewrite /Sout /comp_RV /dsdp_output /=; ring.
Qed.

(* A predictor reading Alice's view matches Bob's input with
   probability at most 1/#|plain AHE| plus the advantages of the two hop
   reductions.
   Naming: [dsdp_alice_guess_fdist] as in the hopping-tuple headline, with
   [view] naming the view read. *)
Corollary dsdp_alice_guess_fdist_view_le
    (g' : dsdp_alice_hop_tupleT * cipher AHE * cipher AHE * plain AHE
          -> plain AHE) :
  Pr alice_sample_fdist [set t | (g' `o AliceView) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction
              (distinguisher_of_guess (g' \o alice_view_of_hop_tuple)))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction
              (distinguisher_of_guess (g' \o alice_view_of_hop_tuple))).
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

(* The encryption of v under pk as a function of the coin index.
   Naming: the [_of_] connective names the source the map reads, after the
   repository's total-conversion family. *)
Definition enc_of_renc (pk : pub_key AHE) (v : plain AHE) :
    Renc -> cipher AHE :=
  fun r => enc pk v (rand_of_renc r).

(* The reachable encryptions are nonempty, since the coin-index type is. *)
Lemma card_enc_img_gt0 (pk : pub_key AHE) (v : plain AHE) :
  (0 < #|enc_of_renc pk v @: [set: Renc]|)%N.
Proof. by rewrite card_gt0 imset_eq0 -card_gt0 cardsT card_renc. Qed.

(* The named property: the challenge law is uniform over the reachable
   encryptions of v under pk.  It is a property of the scheme map, consumed
   only by its own specialization below, never by a hop theorem.
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
