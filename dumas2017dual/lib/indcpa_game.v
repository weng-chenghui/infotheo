From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba.
Require Import homomorphic_encryption.
Require Import extra_proba.

(**md**************************************************************************)
(* # IND-CPA game vocabulary                                                  *)
(*                                                                            *)
(* The real-or-zero IND-CPA game over infotheo distributions, together        *)
(* with the reduction plumbing that carries a protocol distinguishing gap     *)
(* to the advantage of that game.  An adversary is a record: a finite         *)
(* state type, a law over that type, a challenge plaintext read off the       *)
(* state, and a Boolean decision on the state and the challenge               *)
(* ciphertext.  The challenger is indexed by the hidden bit and answers       *)
(* with an encryption of the chosen plaintext at true and of zero at          *)
(* false.  The advantage is the absolute gap between the two acceptance       *)
(* probabilities.                                                             *)
(*                                                                            *)
(* ## Role map                                                                *)
(*                                                                            *)
(* | role          | identifier                                             | *)
(* |---------------|--------------------------------------------------------| *)
(* | adversary     | indcpa_fdist_adversary                                 | *)
(* | challenger    | indcpa_challenger                                      | *)
(* | experiment    | indcpa_experiment                                      | *)
(* | advantage     | indcpa_fdist_epsilon                                   | *)
(* | distinguisher | distinguisher                                          | *)
(* | reduction     | reduction_challenge_fdist                              | *)
(*                                                                            *)
(* A distinguisher here is a plain Boolean function, the counterpart of       *)
(* the finfun tester of smc/security_models/statdist.v.  A concrete           *)
(* reduction is built by the protocol file that instantiates this one:        *)
(* hop0_reduction and hop1_reduction of                                       *)
(* dumas2017dual/dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v package a      *)
(* distinguisher as an indcpa_fdist_adversary, and                            *)
(* reduction_challenge_fdist is the law their challenge induces.              *)
(*                                                                            *)
(* Each indcpa_fdist_epsilon is a single-query advantage at a fixed           *)
(* public key, and a bound stated through it holds vacuously once that        *)
(* advantage reaches 1.                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*            enc_fdist pk v == the law of an encryption of v under pk with   *)
(*                              uniform randomness                            *)
(*                x <- m ; f == a sampling step of an experiment, the bind    *)
(*                              of a distribution with a stochastic map       *)
(*                     ret a == the Dirac distribution at a                   *)
(*           distinguisher B == the type of Boolean tests on the value a game *)
(*                              hands the adversary                           *)
(*    indcpa_fdist_adversary == a single-query real-or-zero adversary: a      *)
(*                              state type adv_state, a law adv_choose over   *)
(*                              it, a challenge plaintext adv_plain read off  *)
(*                              the state, and a decision adv_decide on the   *)
(*                              state and the challenge ciphertext            *)
(*  indcpa_challenger b pk v == the challenge law at hidden bit b: the        *)
(*                              encryption law of v at true and of zero at    *)
(*                              false                                         *)
(*   indcpa_challenger_realE == the challenge law at hidden bit true is the   *)
(*                              encryption law of the plaintext               *)
(*   indcpa_challenger_zeroE == the challenge law at hidden bit false is the  *)
(*                              encryption law of zero                        *)
(* indcpa_experiment b pk adv == the law of the adversary's decision at       *)
(*                              hidden bit b: its state law bound with the    *)
(*                              challenge law at that bit, then with its      *)
(*                              decision                                      *)
(*     indcpa_fdist_accept b == the probability that the adversary accepts at *)
(*                              hidden bit b                                  *)
(* indcpa_fdist_success_real == the probability that the adversary accepts    *)
(*                              when the challenge encrypts its chosen        *)
(*                              plaintext                                     *)
(* indcpa_fdist_success_zero == the probability that the adversary accepts    *)
(*                              when the challenge encrypts zero              *)
(* indcpa_fdist_success_realE == the real acceptance probability as the state *)
(*                              law bound with the pushforward of the         *)
(*                              decision along the challenge law              *)
(* indcpa_fdist_success_zeroE == the zero acceptance probability in that same *)
(*                              bind form                                     *)
(*      indcpa_fdist_epsilon == the absolute gap between those two            *)
(*                              probabilities                                 *)
(*        enc_slot_resampleE == the law of a state paired with a slot         *)
(*                              computed from the state and a coordinate      *)
(*                              disjoint from the state factors as a          *)
(*                              stochastic map resampling that coordinate     *)
(* reduction_challenge_fdist == the joint law obtained by sampling a          *)
(*                              reduction state and its challenge ciphertext  *)
(*                              before reconstructing the tested value        *)
(* reduction_challenge_fdistE == the law of a tested value assembled from a   *)
(*                              reduction state and independent uniform       *)
(*                              encryption randomness is that challenge law   *)
(* reduction_challenge_acceptE == equal joint laws give equal acceptance      *)
(*                              probabilities for every Boolean test          *)
(* reduction_challenge_successE == the challenge law tested by a              *)
(*                              distinguisher is the state law bound with the *)
(*                              pushforward of that distinguisher along each  *)
(*                              challenge law                                 *)
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

(* A sampling step of an experiment, the bind of a distribution with a
   stochastic map. *)
Notation "x '<-' m ';' f" := (m >>= (fun x => f))
  (at level 100, right associativity,
   format "'[v' x  '<-'  m ;  '//' f ']'") : fdist_scope.

(* The outcome of an experiment that samples nothing further, the Dirac
   distribution at a value. *)
Notation "'ret' a" := (fdist1 a) (at level 0) : fdist_scope.

Section indcpa_game.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.

(* The law of an encryption of a plaintext under a public key, with uniform
   encryption randomness. *)
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  fdistmap (fun r => enc pk v (rand_of_renc r)) (fdist_uniform card_renc).

(* A distinguisher on a finite type is a Boolean function on it.
   This is the plain-function counterpart of [tester] in
   smc/security_models/statdist.v, which is a finfun. *)
Definition distinguisher (joint : finType) : Type := joint -> bool.

(* A single-query real-or-zero adversary has a finite state type, a law over
   that state, a challenge plaintext read from the state, and a Boolean
   decision based on the state and the challenge ciphertext. *)
Record indcpa_fdist_adversary := {
  adv_state : finType ;
  adv_choose : R.-fdist adv_state ;
  adv_plain : adv_state -> plain AHE ;
  adv_decide : adv_state -> cipher AHE -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

(* The challenge law at hidden bit b: the encryption law of v at true and of
   zero at false. *)
Definition indcpa_challenger (b : bool) (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  enc_fdist pk (if b then v else 0).

(* The challenge law at hidden bit true is the encryption law of the
   plaintext. *)
Lemma indcpa_challenger_realE pk v :
  indcpa_challenger true pk v = enc_fdist pk v.
Proof. by []. Qed.

(* The challenge law at hidden bit false is the encryption law of zero. *)
Lemma indcpa_challenger_zeroE pk v :
  indcpa_challenger false pk v = enc_fdist pk 0.
Proof. by []. Qed.

(* The law of the adversary's decision at hidden bit b: its state law bound
   with the challenge law at that bit, then with its decision. *)
Definition indcpa_experiment (b : bool) (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R.-fdist bool :=
  c  <- adv_choose adv ;
  ch <- indcpa_challenger b pk (adv_plain adv c) ;
  ret (adv_decide adv c ch).

(* The probability that the adversary accepts at hidden bit b. *)
Definition indcpa_fdist_accept (b : bool) (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (indcpa_experiment b pk adv) [set true].

(* The probability that the adversary accepts when the challenge encrypts the
   plaintext it chose.
   Naming: [_success_real] after [oracle_encrypt_real] and
   [guess_sdistr_success_real]; [Pr_] is reserved for the lemma family. *)
Definition indcpa_fdist_success_real := indcpa_fdist_accept true.

(* The real success probability as a bind of the state law with the
   pushforward of the decision along the challenge law. *)
Lemma indcpa_fdist_success_realE (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) :
  indcpa_fdist_success_real pk adv
  = Pr (c <- adv_choose adv ;
        fdistmap (adv_decide adv c) (enc_fdist pk (adv_plain adv c)))
       [set true].
Proof. by []. Qed.

(* The probability that the adversary accepts when the challenge encrypts
   zero.
   Naming: [_success_zero] after [oracle_encrypt_zero]; [Pr_] is reserved for
   the lemma family. *)
Definition indcpa_fdist_success_zero := indcpa_fdist_accept false.

(* The zero success probability as a bind of the state law with the
   pushforward of the decision along the challenge law. *)
Lemma indcpa_fdist_success_zeroE (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) :
  indcpa_fdist_success_zero pk adv
  = Pr (c <- adv_choose adv ;
        fdistmap (adv_decide adv c) (enc_fdist pk 0))
       [set true].
Proof. by []. Qed.

(* The real-or-zero advantage of an adversary at a public key: the absolute
   gap between its two success probabilities. *)
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.

Section enc_slot_resample.

Variables (sampleT stateT : finType).
Variable P : R.-fdist sampleT.
Variable Q : R.-fdist stateT.
Variables (State : {RV P -> stateT}) (Rho : {RV P -> Renc}).
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
        : {RV P -> cipher AHE}]
  = Q `X (fun a => fdistmap (k a) (fdist_uniform card_renc)).
Proof.
have HL : `p_ [% State, (fun t => k (State t) (Rho t))
                : {RV P -> cipher AHE}]
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

Section reduction_challenge.

Variables (sampleT stateT joint : finType).
Variable P : R.-fdist sampleT.
Variables (State : {RV P -> stateT}) (Rho : {RV P -> Renc}).
Variable pk : pub_key AHE.
Variable msg : stateT -> plain AHE.

(* [assemble c ch] reconstructs the complete joint value tested by a
   distinguisher from reduction state c and challenge ciphertext ch. *)
Variable assemble : stateT -> cipher AHE -> joint.

Variable X : {RV P -> joint}.

Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = (`p_ State) `x (fdist_uniform card_renc).

Hypothesis X_assembleE : forall t,
  X t = assemble (State t) (enc pk (msg (State t)) (rand_of_renc (Rho t))).

(* The joint law obtained by sampling a reduction state and its challenge
   ciphertext before reconstructing the tested value. *)
Definition reduction_challenge_fdist : R.-fdist joint :=
  c  <- `p_ State ;
  ch <- enc_fdist pk (msg c) ;
  ret (assemble c ch).

(* The protocol-game law from one complete protocol sample equals the
   reduction-game law obtained by separately sampling the reduction state and
   fresh uniform encryption randomness, then applying the same deterministic
   encryption and assembly functions. *)
Lemma reduction_challenge_fdistE : `p_ X = reduction_challenge_fdist.
Proof.
have -> : `p_ X
        = fdistmap (fun q : stateT * cipher AHE => assemble q.1 q.2)
            (`p_ [% State,
                  (fun t => enc pk (msg (State t)) (rand_of_renc (Rho t)))
                    : {RV P -> cipher AHE}]).
  by rewrite /dist_of_RV fdistmap_comp; congr fdistmap; exact/boolp.funext.
rewrite (enc_slot_resampleE (fun c r => enc pk (msg c) (rand_of_renc r))
           state_rho_prodE) fdist_prod_bindE fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (msg c))) fdistmap_comp.
Qed.

(* Equal joint laws give equal acceptance probabilities for every Boolean
   test. *)
Corollary reduction_challenge_acceptE (D : distinguisher joint) :
  Pr (`p_ X) [set x | D x]
  = Pr reduction_challenge_fdist [set x | D x].
Proof. by rewrite reduction_challenge_fdistE. Qed.

(* The challenge law tested by D is the state law bound with the pushforward
   of D along each challenge law. *)
Lemma reduction_challenge_successE (D : distinguisher joint) :
  Pr reduction_challenge_fdist [set x | D x]
  = Pr (c <- `p_ State ;
        fdistmap (fun ch => D (assemble c ch)) (enc_fdist pk (msg c)))
       [set true].
Proof.
rewrite -Pr_fdistmap_bool /reduction_challenge_fdist fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (msg c))) fdistmap_comp.
Qed.

End reduction_challenge.

End indcpa_game.
