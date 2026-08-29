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
(* v2_challenge_adversary and v3_challenge_adversary of                       *)
(* dumas2017dual/dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v package a      *)
(* distinguisher as an indcpa_fdist_adversary, and                            *)
(* reduction_challenge_fdist is the law their challenge induces.              *)
(*                                                                            *)
(* The reduction lemmas take one condition on the protocol they are applied   *)
(* to: the encryption randomness of the challenged slot is uniform and        *)
(* independent of the state the reduction keeps.  That is freshness, not      *)
(* secrecy.  The state may hold the secrets themselves, and whether a         *)
(* ciphertext hides its plaintext is charged for by indcpa_fdist_epsilon      *)
(* alone.  What the condition forbids is randomness reuse across a            *)
(* protocol's messages.                                                       *)
(*                                                                            *)
(* Each indcpa_fdist_epsilon is a single-query advantage at a fixed           *)
(* public key, and a bound stated through it holds vacuously once that        *)
(* advantage reaches 1.  The advantage quantifies over adversaries holding    *)
(* the public key alone: an adversary holding the matching private key        *)
(* decrypts the challenge and reaches advantage 1.                            *)
(*                                                                            *)
(* ```                                                                        *)
(*            enc_fdist pk v == the distribution obtained by encrypting v     *)
(*                               under pk with fresh uniform randomness       *)
(*                x <- m ; f == samples x from m and continues with f x       *)
(*                      ret a == returns a without sampling anything else     *)
(*            distinguisher B == a Boolean test on the game output, where     *)
(*                               true means that the test accepts             *)
(*              predictor obs == a guessing strategy: a map from an           *)
(*                               observation to a claimed plaintext           *)
(*         guess_test predict == the test accepting when the predictor,       *)
(*                               reading the observation slot, returns the    *)
(*                               first input slot                             *)
(*  fdist_uniform_irrelevance == fdist_uniform does not depend on which       *)
(*                               cardinality proof it is given                *)
(*     indcpa_fdist_adversary == packages the state sampled before the        *)
(*                               challenge, the plaintext selected from that  *)
(*                               state, and the decision made from the state  *)
(*                               and challenge ciphertext                     *)
(*   indcpa_challenger b pk v == encrypts v when b is true and zero when b    *)
(*                               is false, using fresh uniform randomness     *)
(*  indcpa_experiment b pk adv == samples the adversary state, gives it the   *)
(*                               challenge selected by b, and returns its     *)
(*                               Boolean decision                             *)
(*      indcpa_fdist_accept b == the probability that this decision is true   *)
(*                               at hidden bit b                              *)
(*  indcpa_fdist_success_real == the acceptance probability when the          *)
(*                               challenge encrypts the selected plaintext    *)
(*  indcpa_fdist_success_zero == the acceptance probability when the          *)
(*                               challenge encrypts zero                      *)
(*  indcpa_fdist_success_realE == computes real acceptance by sampling the    *)
(*                               state, encrypting its selected plaintext,    *)
(*                               and applying the decision                    *)
(*  indcpa_fdist_success_zeroE == computes zero acceptance in the same way,   *)
(*                               with zero as the encrypted plaintext         *)
(*       indcpa_fdist_epsilon == the absolute difference between the real     *)
(*                               and zero acceptance probabilities            *)
(*         enc_slot_resampleE == fresh encryption randomness independent of   *)
(*                               the state may be sampled after the state     *)
(*                               without changing the joint distribution      *)
(*  reduction_challenge_fdist == samples a reduction state and challenge      *)
(*                               ciphertext, then builds the complete value   *)
(*                               given to the distinguisher                   *)
(*  reduction_challenge_fdistE == the protocol value and the value built      *)
(*                               around the challenge have the same           *)
(*                               distribution when the challenge randomness   *)
(*                               is fresh                                     *)
(*  reduction_challenge_acceptE == a distinguisher has the same acceptance    *)
(*                               probability on those two distributions       *)
(*  reduction_challenge_successE == the distinguisher's acceptance            *)
(*                               probability on the complete value built      *)
(*                               around a challenge is computed by sampling   *)
(*                               the state and challenge, then running the    *)
(*                               distinguisher                                *)
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

(* fdist_uniform does not depend on which cardinality proof it is given.
   States once what four proof sites re-derived inline as
   [congr fdist_uniform; exact: eq_irrelevance], and lets a cloned context
   state a uniformity hypothesis with its own locally built proof term
   instead of importing the machine-generated [_subproof] constant of the
   section it clones. *)
Lemma fdist_uniform_irrelevance {R : realType} (A : finType) (n : nat)
    (e e' : #|A| = n.+1) :
  fdist_uniform e = fdist_uniform e' :> R.-fdist A.
Proof. by congr fdist_uniform; exact: eq_irrelevance. Qed.

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

(* The law of an encryption of v under pk when the encryption randomness is
   drawn uniformly.  This is the only randomness the challenger uses, so an
   IND-CPA challenge is a sample from enc_fdist pk v at the real bit and from
   enc_fdist pk 0 at the zero bit. *)
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  fdistmap (fun r => enc pk v (rand_of_renc r)) (fdist_uniform card_renc).

(* A Boolean test on the value a game hands the adversary.  In a game hop the
   same test is run on two consecutive games, and the gap between its two
   acceptance probabilities is the cost of that hop.
   The statistical-distance axis writes the same notion as the finfun [tester]
   of smc/security_models/statdist.v, where finiteness is what lets
   [class_adv] maximize over testers and recover [statdist].  A plain function
   is enough here because every bound below is stated for one fixed
   distinguisher, so an epsilon in this development is a per-distinguisher
   advantage rather than a supremum. *)
Definition distinguisher (joint : finType) : Type := joint -> bool.

(* A guessing strategy on an observation: a map from the observed value to a
   claimed plaintext.  The counterpart of [distinguisher] for guessing games:
   every guessing bound below quantifies over one predictor at a fixed
   observation. *)
Definition predictor (obs : finType) : Type := obs -> plain AHE.

(* The test that accepts when a predictor, reading the observation slot,
   returns the first input slot.  A predictor is scored by an equality event
   while a hop speaks only about how often a Boolean test accepts; wrapping
   the predictor this way makes the two the same number: the probability
   that the predictor succeeds at hop i is the probability that this test
   accepts at hop i. *)
Definition guess_test {obs : finType} (predict : obs -> plain AHE) :
    distinguisher (plain AHE * plain AHE * obs)%type :=
  fun x => predict x.2 == x.1.1.

(* A single-query real-or-zero adversary.  [adv_state] is everything the
   adversary holds before the challenge, [adv_choose] is its law, [adv_plain]
   is the challenge plaintext read off that state, and [adv_decide] is the
   verdict on the state together with the one challenge ciphertext.  The record
   grants the public key alone and one challenge, which is the attack model
   every epsilon in the DSDP files is measured in. *)
Record indcpa_fdist_adversary := {
  adv_state : finType ;
  adv_choose : R.-fdist adv_state ;
  adv_plain : adv_state -> plain AHE ;
  adv_decide : adv_state -> cipher AHE -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

(* The challenge law at hidden bit b: enc_fdist pk v at true and enc_fdist pk 0
   at false.  This is the real-or-zero form of IND-CPA, and zero is the
   plaintext the DSDP simulator encrypts, so the hidden bit separates Alice's
   real view from her simulated one. *)
Definition indcpa_challenger (b : bool) (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  enc_fdist pk (if b then v else 0).

(* The law of the adversary's verdict at hidden bit b: sample its state, sample
   the challenge at b, then apply its decision.  The bit b stays hidden from
   the adversary, and the two instances b = true and b = false are the pair of
   experiments whose acceptance gap is the advantage. *)
Definition indcpa_experiment (b : bool) (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R.-fdist bool :=
  c  <- adv_choose adv ;
  ch <- indcpa_challenger b pk (adv_plain adv c) ;
  ret (adv_decide adv c ch).

(* The probability that the adversary's verdict is true at hidden bit b. *)
Definition indcpa_fdist_accept (b : bool) (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (indcpa_experiment b pk adv) [set true].

(* The probability that the adversary accepts when the challenge encrypts the
   plaintext it chose.
   Naming: [_success_real] after [oracle_encrypt_real] and
   [guess_sdistr_success_real]; [Pr_] is reserved for the lemma family. *)
Definition indcpa_fdist_success_real := indcpa_fdist_accept true.

(* The real success probability, unfolded as: draw the adversary state, encrypt
   the plaintext that state chose under fresh uniform randomness, and test the
   result.  A protocol hop whose challenged slot still carries the real
   plaintext has its acceptance probability in exactly this form, which is how
   hop0_real_challengeE and hop1_real_challengeE close. *)
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

(* The zero success probability in that same unfolded form, with the plaintext
   replaced by zero.  The neighbouring hop, the one whose challenged slot
   already encrypts zero, has its acceptance probability in exactly this form.
   The two lemmas together put two neighbouring hops on the two branches of a
   single IND-CPA experiment. *)
Lemma indcpa_fdist_success_zeroE (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) :
  indcpa_fdist_success_zero pk adv
  = Pr (c <- adv_choose adv ;
        fdistmap (adv_decide adv c) (enc_fdist pk 0))
       [set true].
Proof. by []. Qed.

(* The advantage of adv against pk: the absolute gap between its real and zero
   success probabilities.  Every DSDP hop is priced by one such advantage, at a
   fixed key and a single query. *)
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.

Section enc_slot_resample.

Variables (sampleT stateT : finType).
Variable P : R.-fdist sampleT.
Variable Q : R.-fdist stateT.
Variables (State : {RV P -> stateT}) (Rho : {RV P -> Renc}).
Variable k : stateT -> Renc -> cipher AHE.

(* Rho is uniform on its coordinate and independent of State, and Q is State's
   own law: the pair can be produced by drawing State from Q and then drawing
   Rho without consulting it.
   As a condition on a protocol this is freshness, not secrecy: the party that
   produces the ciphertext draws its encryption randomness uniformly, and
   independently of its own input and of every other party's randomness.  The
   state is free to hold the secrets themselves, and whether a ciphertext hides
   its plaintext is charged for separately, by indcpa_fdist_epsilon.
   What the condition forbids is randomness reuse.  A protocol that let the same
   coordinate reach the adversary by any route other than the ciphertext built
   from it would break the product, and no reduction could then rebuild the
   adversary's view around a challenge ciphertext. *)
Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = Q `x (fdist_uniform card_renc).

(* A state paired with a slot built from the state and a coordinate the state
   omits has the law of the state extended by resampling that coordinate.  The
   omitted coordinate is the encryption randomness, so one protocol sample can
   be re-read as sampling the reduction state first and drawing fresh uniform
   randomness afterwards, which is the order the challenger works in. *)
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

(* The freshness condition at the reduction's own state: the encryption
   randomness is uniform and independent of everything the reduction holds
   before it queries the challenger. *)
Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = (`p_ State) `x (fdist_uniform card_renc).

(* Rho enters the tested value at one place only, the ciphertext of the
   plaintext that State selects.  Everything else X reads is a function of
   State, so a reduction that gives Rho to the challenger can still rebuild X
   around the challenge ciphertext it gets back.  The two hypotheses divide the
   work: state_rho_prodE makes Rho fresh, and this one confines where it
   enters. *)
Hypothesis X_assembleE : forall t,
  X t = assemble (State t) (enc pk (msg (State t)) (rand_of_renc (Rho t))).

(* The law of the value a distinguisher is handed inside the IND-CPA
   experiment: sample the reduction state, sample the challenge ciphertext for
   the plaintext that state selects, then assemble the tested value from the
   two. *)
Definition reduction_challenge_fdist : R.-fdist joint :=
  c  <- `p_ State ;
  ch <- enc_fdist pk (msg c) ;
  ret (assemble c ch).

(* The protocol-game law from one complete protocol sample equals the
   reduction-game law obtained by separately sampling the reduction state and
   fresh uniform encryption randomness, then applying the same deterministic
   encryption and assembly functions.  The reduction therefore reproduces the
   protocol hop for the distinguisher with no error term. *)
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

(* A distinguisher accepts the protocol sample with the same probability as it
   accepts the value assembled inside the IND-CPA experiment.  The reduction is
   tight: the hop gap it hands to the challenger is the gap the distinguisher
   had. *)
Corollary reduction_challenge_acceptE (D : distinguisher joint) :
  Pr (`p_ X) [set x | D x]
  = Pr reduction_challenge_fdist [set x | D x].
Proof. by rewrite reduction_challenge_fdistE. Qed.

(* The acceptance probability under reduction_challenge_fdist, unfolded as the
   state law bound with the pushforward of D along each challenge law.  Read
   together with indcpa_fdist_success_realE and indcpa_fdist_success_zeroE it
   identifies a hop success probability with an IND-CPA success probability. *)
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

Arguments predictor : clear implicits.
