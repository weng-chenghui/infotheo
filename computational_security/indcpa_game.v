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
(* | adversary     | indcpa_adversary                                       | *)
(* | challenger    | indcpa_challenger                                      | *)
(* | experiment    | indcpa_experiment                                      | *)
(* | advantage     | indcpa_epsilon                                         | *)
(* | distinguisher | distinguisher                                          | *)
(* | reduction     | bob_challenge_adversary, charlie_challenge_adversary   | *)
(* | assumption    | indcpa_epsilon_assumption                              | *)
(* | asymptotics   | negligible_fun of negligible.v                         | *)
(* | inhabitant    | cipher_constant_assumption                             | *)
(*                                                                            *)
(* A distinguisher here is a plain Boolean function, the counterpart of       *)
(* the finfun tester of smc/security_models/statdist.v.  A concrete           *)
(* reduction is built by the protocol file that instantiates this one:        *)
(* bob_challenge_adversary and charlie_challenge_adversary of                 *)
(* dumas2017dual/dsdp/hopping/dsdp_alice_hop_secrecy.v package a              *)
(* distinguisher as an indcpa_adversary, and                                  *)
(* indcpa_fdist is the law their challenge induces.                           *)
(*                                                                            *)
(* The reduction lemmas take one condition on the protocol they are applied   *)
(* to: the encryption randomness of the challenged slot is uniform and        *)
(* independent of the state the reduction keeps.  That is freshness, not      *)
(* secrecy.  The state may hold the secrets themselves, and whether a         *)
(* ciphertext hides its plaintext is charged for by indcpa_epsilon            *)
(* alone.  What the condition forbids is randomness reuse across a            *)
(* protocol's messages.                                                       *)
(*                                                                            *)
(* Each indcpa_epsilon is a single-query advantage at a fixed                 *)
(* public key, and a bound stated through it holds vacuously once that        *)
(* advantage reaches 1.  The advantage quantifies over adversaries holding    *)
(* the public key alone: when #|plain AHE| > 1, an adversary holding the      *)
(* matching private key and submitting a nonzero challenge plaintext          *)
(* decrypts the challenge and reaches advantage 1.                            *)
(*                                                                            *)
(* Each epsilon above is measured at one fixed instance.  The asymptotic      *)
(* reading of a computational assumption lives in                             *)
(* computational_security/negligible.v, whose negligible_fun and closure      *)
(* lemmas say what a family of such instances, indexed by a security          *)
(* parameter, must satisfy for a bound of this shape to vanish faster than    *)
(* every inverse polynomial.  indcpa_epsilon_assumption is the other half,    *)
(* the adversary class a bound may be restricted to; its classifier is        *)
(* extensional, so it says which adversaries a bound covers while running     *)
(* time stays a property of a syntax it does not read.                        *)
(*                                                                            *)
(* scheme_card_renc is carried as a field to pin one proof of the coin type's *)
(* nonemptiness: a second proof of the same equation is propositionally equal *)
(* to it and not convertible with it, so bounds stated at the two would       *)
(* compose only through a rewrite.                                            *)
(*                                                                            *)
(* A class may be empty, and a bound conditional on an empty class holds      *)
(* vacuously.  A classifier admitting every adversary is instead forced to    *)
(* assume epsilon at least 1, once the scheme is correct and the plaintext    *)
(* space has more than one element.  SSProve sits at the same boundary:       *)
(* Haselwarter et al., ACM TOPLAS 45(3) Article 15, 2023, section 2.3 reads   *)
(* the polynomial-time hypothesis off a concrete bound, outside every         *)
(* mechanized statement, and its Coq development defines no cost notion, its  *)
(* source at theories/Crypt/examples/PRFMAC.v:6-8 of commit c6d7d4bc leaving  *)
(* Claim 10.3 (p. 186) unformalised because its argument depends on the       *)
(* adversary only having polynomial time and how to formulate that is         *)
(* unclear.  FCF states its efficiency predicate admissible_oc, in            *)
(* WC_PolyTime.v, over families of OracleComp terms, so there the classified  *)
(* object is a program rather than a function.                                *)
(*                                                                            *)
(* A protocol whose sample is laid out differently reaches the reduction      *)
(* section by proving its own tested value equal to protocol_RV, which is     *)
(* where the confinement of the encryption randomness is checked.             *)
(*                                                                            *)
(* ```                                                                        *)
(*              indcpa_scheme == an encryption scheme, a finite coin space,   *)
(*                               its nonemptiness, and the map from a coin    *)
(*                               index to the randomness encryption consumes  *)
(* indcpa_epsilon_assumption == a Boolean adversary class, one epsilon, and   *)
(*                               the assumption that every classified         *)
(*                               adversary stays below that epsilon at every  *)
(*                               key built from a private key                 *)
(*       indcpa_admissible A == the class of A, as a Boolean test on          *)
(*                               adversaries                                  *)
(* indcpa_assumption_epsilon A == the advantage A assumes for its class       *)
(* indcpa_admissible_epsilon_le == the class-conditional bound A assumes      *)
(* adv_decide_cipher_constant adv ==                                          *)
(*                               decides whether the adversary's verdict      *)
(*                               ignores the challenge ciphertext             *)
(* indcpa_epsilon_cipher_constant_eq0 ==                                      *)
(*                               an adversary whose verdict ignores the       *)
(*                               ciphertext has advantage zero                *)
(* cipher_constant_assumption == that class with epsilon zero, an assumption  *)
(*                               whose bound is proved rather than assumed    *)
(*            fdistbind_cst == a distribution bound to a continuation that    *)
(*                               ignores its sample is the Dirac law there    *)
(*            enc_fdist pk v == the distribution obtained by encrypting v     *)
(*                               under pk with fresh uniform randomness       *)
(*                x <- m ; f == samples x from m and continues with f x       *)
(*                      ret a == returns a without sampling anything else     *)
(*            distinguisher B == a Boolean test on the game output, where     *)
(*                               true means that the test accepts             *)
(*                 accept D G == the probability that D accepts a value       *)
(*                               sampled from G, at any finite carrier        *)
(*                    acceptE == expresses that probability as the event that *)
(*                               the sampled value is accepted                *)
(*                accept_ge0 == that probability is nonnegative               *)
(*      predictor observation == a guessing strategy: a map from an           *)
(*                               observation to a claimed plaintext           *)
(* distinguisher_of_predictor predict ==                                      *)
(*                               the test accepting when the predictor,       *)
(*                               reading the observation slot, returns the    *)
(*                               first input slot                             *)
(*           indcpa_adversary == packages the state sampled before the        *)
(*                               challenge, the plaintext selected from that  *)
(*                               state, and the decision made from the state  *)
(*                               and challenge ciphertext                     *)
(*   indcpa_challenger b pk v == encrypts v when b is true and zero when b    *)
(*                               is false, using fresh uniform randomness     *)
(*  indcpa_experiment b pk adv == samples the adversary state, gives it the   *)
(*                               challenge selected by b, and returns its     *)
(*                               Boolean decision                             *)
(*            indcpa_accept b == the probability that this decision is true   *)
(*                               at hidden bit b                              *)
(*        indcpa_success_real == the acceptance probability when the          *)
(*                               challenge encrypts the selected plaintext    *)
(*        indcpa_success_zero == the acceptance probability when the          *)
(*                               challenge encrypts zero                      *)
(*        indcpa_success_realE == computes real acceptance by sampling the    *)
(*                               state, encrypting its selected plaintext,    *)
(*                               and applying the decision                    *)
(*        indcpa_success_zeroE == computes zero acceptance in the same way,   *)
(*                               with zero as the encrypted plaintext         *)
(*             indcpa_epsilon == the absolute difference between the real     *)
(*                               and zero acceptance probabilities            *)
(*         enc_slot_resampleE == fresh encryption randomness independent of   *)
(*                               the state may be sampled after the state     *)
(*                               without changing the joint distribution      *)
(*                protocol_RV == the value a distinguisher is tested on in    *)
(*                               one protocol run, with the challenged slot   *)
(*                               holding the ciphertext the protocol's own    *)
(*                               randomness produced                          *)
(*               indcpa_fdist == the law of that same value inside the        *)
(*                               IND-CPA experiment: sample the reduction     *)
(*                               state, take the challenge ciphertext from    *)
(*                               the challenger, then assemble                *)
(*     protocol_indcpa_fdistE == the protocol law and the IND-CPA law of      *)
(*                               that value agree, so the reduction           *)
(*                               reproduces the hop with no error term        *)
(*       indcpa_fdist_acceptE == acceptance under the IND-CPA law is          *)
(*                               computed by sampling the state and the       *)
(*                               challenge, then running the distinguisher    *)
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

(* The four data every epsilon of this file is measured at, packed as one
   value: an additively homomorphic scheme, the finite type indexing its
   encryption coins, the nonemptiness that type needs to carry a uniform law,
   and the map from a coin index to the randomness encryption consumes.  One
   value rather than four arguments, so an assumption is made about a scheme
   and a sequence of schemes is a function nat -> indcpa_scheme. *)
Record indcpa_scheme := {
  (* the additively homomorphic encryption scheme *)
  scheme_AHE          : AHEncType ;
  (* the finite type indexing the coins, rand being a bare Type *)
  scheme_renc         : finType ;
  (* nonemptiness, one pinned proof, in the form fdist_uniform takes *)
  scheme_card_renc    : #|scheme_renc| = #|scheme_renc|.-1.+1 ;
  (* the randomness a coin index stands for *)
  scheme_rand_of_renc : scheme_renc -> rand scheme_AHE }.

Section indcpa_game.
Context {R : realType}.
Variable S : indcpa_scheme.
Local Notation AHE := (scheme_AHE S).
Local Notation Renc := (scheme_renc S).
Local Notation card_renc := (scheme_card_renc S).
Local Notation rand_of_renc := (@scheme_rand_of_renc S).

(* The law of an encryption of v under pk when the encryption randomness is
   drawn uniformly.  This is the only randomness the challenger uses, so an
   IND-CPA challenge is a sample from enc_fdist pk v at the real bit and from
   enc_fdist pk 0 at the zero bit. *)
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist (cipher AHE) :=
  fdistmap (fun r => enc pk v (rand_of_renc r)) (fdist_uniform card_renc).

(* A Boolean test on the value a game hands the adversary, run on both games
   of a hop so that the gap between its two acceptance probabilities is the
   cost of that hop.  Every bound below fixes one distinguisher, so an epsilon
   here is a per-distinguisher advantage rather than a supremum over tests. *)
Definition distinguisher (T : finType) : Type := T -> bool.

(* The probability that D accepts a value sampled from G.  This number is what
   a game of a hopping argument is, and the carrier is a parameter, so a
   protocol trace and a tuple of protocol values are games of the same kind. *)
Definition accept (T : finType) (D : T -> bool) (G : R.-fdist T) : R :=
  Pr (fdistmap D G) [set true].

(* The pushforward form of that acceptance probability agrees with the event
   form, which is the shape a reduction correspondence is stated in. *)
Lemma acceptE (T : finType) (D : T -> bool) (G : R.-fdist T) :
  accept D G = Pr G [set x | D x].
Proof. exact: Pr_fdistmap_bool. Qed.

(* That probability is nonnegative.  A hop to the zero game reads the game it
   leaves as a distance from zero, and that reading bounds the game itself
   only because the game is nonnegative. *)
Lemma accept_ge0 (T : finType) (D : T -> bool) (G : R.-fdist T) :
  0 <= accept D G.
Proof. exact: Pr_ge0. Qed.

(* A guessing strategy on an observation: a map from the observed value to a
   claimed plaintext.  The counterpart of [distinguisher] for guessing games:
   every guessing bound below quantifies over one predictor at a fixed
   observation. *)
Definition predictor (observation : finType) : Type := observation -> plain AHE.

(* The test that accepts when a predictor, reading the observation slot,
   returns the first input slot.  Wrapping the predictor this way makes its
   success probability at a hop the acceptance probability of a test. *)
Definition distinguisher_of_predictor {observation : finType}
    (predict : predictor observation) :
    distinguisher (plain AHE * plain AHE * observation)%type :=
  fun x => predict x.2 == x.1.1.

(* A single-query real-or-zero adversary: a state drawn before the challenge,
   a challenge plaintext read off that state, and a verdict on the state and
   the one challenge ciphertext.  It holds the public key alone and asks one
   challenge, which is the attack model every epsilon of the DSDP files is
   measured in. *)
Record indcpa_adversary := {
  (* everything the adversary holds before the challenge *)
  adv_state : finType ;
  (* the law that state is drawn from *)
  adv_choose : R.-fdist adv_state ;
  (* the challenge plaintext read off the state *)
  adv_plain : adv_state -> plain AHE ;
  (* the verdict on the state and the challenge ciphertext *)
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
    (adv : indcpa_adversary) : R.-fdist bool :=
  c  <- adv_choose adv ;
  ch <- indcpa_challenger b pk (adv_plain adv c) ;
  ret (adv_decide adv c ch).

(* The probability that the adversary's verdict is true at hidden bit b. *)
Definition indcpa_accept (b : bool) (pk : pub_key AHE)
    (adv : indcpa_adversary) : R :=
  Pr (indcpa_experiment b pk adv) [set true].

(* The probability that the adversary accepts when the challenge encrypts the
   plaintext it chose. *)
Definition indcpa_success_real := indcpa_accept true.

(* The real success probability unfolded: draw the adversary state, encrypt
   the plaintext that state chose under fresh uniform randomness, and test the
   result.  A hop whose challenged slot still carries the real plaintext has
   its acceptance probability in this form. *)
Lemma indcpa_success_realE (pk : pub_key AHE)
    (adv : indcpa_adversary) :
  indcpa_success_real pk adv
  = Pr (c <- adv_choose adv ;
        fdistmap (adv_decide adv c) (enc_fdist pk (adv_plain adv c)))
       [set true].
Proof. by []. Qed.

(* The probability that the adversary accepts when the challenge encrypts
   zero. *)
Definition indcpa_success_zero := indcpa_accept false.

(* The zero success probability in that same unfolded form, with zero in place
   of the chosen plaintext.  With indcpa_success_realE it puts two neighbouring
   hops on the two branches of one IND-CPA experiment. *)
Lemma indcpa_success_zeroE (pk : pub_key AHE)
    (adv : indcpa_adversary) :
  indcpa_success_zero pk adv
  = Pr (c <- adv_choose adv ;
        fdistmap (adv_decide adv c) (enc_fdist pk 0))
       [set true].
Proof. by []. Qed.

(* The advantage of adv against pk: the absolute gap between its real and zero
   success probabilities.  Every DSDP hop costs one such advantage, at a fixed
   key and a single query. *)
Definition indcpa_epsilon (pk : pub_key AHE)
    (adv : indcpa_adversary) : R :=
  `| indcpa_success_real pk adv - indcpa_success_zero pk adv |.

(* A Boolean class of adversaries, one epsilon, and the assumption that every
   adversary of the class stays below that epsilon at every public key built
   from a private key.  The classifier is extensional, so it reads an
   adversary as a function and running time stays a property of a syntax it
   does not see. *)
Record indcpa_epsilon_assumption := {
  (* the class of adversaries the assumption speaks about *)
  indcpa_admissible : indcpa_adversary -> bool ;
  (* the advantage assumed of every adversary of that class *)
  indcpa_assumption_epsilon : R ;
  (* at every key of a private key, a classified adversary stays below it *)
  indcpa_admissible_epsilon_le : forall (dk : priv_key AHE) adv,
    indcpa_admissible adv ->
    indcpa_epsilon (pub_of_priv dk) adv
      <= indcpa_assumption_epsilon }.

(* A distribution bound to a continuation that ignores what it sampled is the
   Dirac law at that constant value. *)
Lemma fdistbind_cst (A B : finType) (D : R.-fdist A) (f : A -> B) (b : B) :
  (forall a, f a = b) -> (a <- D ; ret (f a)) = fdist1 b.
Proof.
move=> Hf; apply/fdist_ext => x; rewrite fdistbindE.
under eq_bigr do rewrite Hf.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(* The class of adversaries whose verdict ignores the challenge ciphertext,
   decided over every state and every pair of ciphertexts by finite
   quantification.  It is a classifier that computes rather than a placeholder
   Boolean. *)
Definition adv_decide_cipher_constant (adv : indcpa_adversary) : bool :=
  [forall c, [forall ch1, [forall ch2,
     adv_decide adv c ch1 == adv_decide adv c ch2]]].

(* An adversary whose verdict ignores the challenge ciphertext has advantage
   exactly zero.  The real and the zero experiment hand its decision the same
   law, so the two acceptance probabilities are one number. *)
Lemma indcpa_epsilon_cipher_constant_eq0 (pk : pub_key AHE)
    (adv : indcpa_adversary) :
  adv_decide_cipher_constant adv -> indcpa_epsilon pk adv = 0.
Proof.
move=> /forallP Hc.
have /card_gt0P[r0 _] : (0 < #|Renc|)%N by rewrite card_renc.
have Hexp : indcpa_experiment true pk adv = indcpa_experiment false pk adv.
  congr (_ >>= _); apply/boolp.funext => c.
  have Hcst (D : R.-fdist (cipher AHE)) :
      (ch <- D ; ret (adv_decide adv c ch))
      = fdist1 (adv_decide adv c (enc pk 0 (rand_of_renc r0))).
    apply: fdistbind_cst => ch; apply/eqP.
    by move: (Hc c) => /forallP/(_ ch)/forallP/(_ (enc pk 0 (rand_of_renc r0))).
  by rewrite !Hcst.
by rewrite /indcpa_epsilon /indcpa_success_real
           /indcpa_success_zero /indcpa_accept Hexp subrr normr0.
Qed.

(* The class-conditional bound the instance below carries, discharged by
   the lemma. *)
Let cipher_constant_epsilon_le (dk : priv_key AHE)
    (adv : indcpa_adversary) :
  adv_decide_cipher_constant adv ->
  indcpa_epsilon (pub_of_priv dk) adv <= 0.
Proof. by move=> H; rewrite (indcpa_epsilon_cipher_constant_eq0 _ H). Qed.

(* The cipher-ignoring class with epsilon zero, an assumption whose bound is
   proved by the lemma above rather than assumed.  The class it admits is
   small, so the bounds conditional on it are weak, and it settles that the
   record type has an inhabitant with content. *)
Definition cipher_constant_assumption : indcpa_epsilon_assumption :=
  {| indcpa_admissible := adv_decide_cipher_constant ;
     indcpa_assumption_epsilon := 0 ;
     indcpa_admissible_epsilon_le := cipher_constant_epsilon_le |}.

Section enc_slot_resample.

Variables (sampleT stateT : finType).
Variable P : R.-fdist sampleT.
Variable Q : R.-fdist stateT.
Variables (State : {RV P -> stateT}) (Rho : {RV P -> Renc}).
Variable enc_slot : stateT -> Renc -> cipher AHE.

(* Rho is uniform on its coordinate and independent of State, and Q is State's
   own law: the pair can be produced by drawing State from Q and then drawing
   Rho without consulting it.
   As a condition on a protocol this is freshness, not secrecy: the party that
   produces the ciphertext draws its encryption randomness uniformly, and
   independently of its own input and of every other party's randomness.  The
   state is free to hold the secrets themselves, and whether a ciphertext hides
   its plaintext is charged for separately, by indcpa_epsilon.
   What the condition forbids is randomness reuse.  A protocol that let the same
   coordinate reach the adversary by any route other than the ciphertext built
   from it would break the product, and no reduction could then rebuild the
   adversary's view around a challenge ciphertext. *)
Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = Q `x (fdist_uniform card_renc).

(* A state paired with a slot built from the state and a coordinate the state
   omits has the law of the state extended by resampling that coordinate.  The
   omitted coordinate is the encryption randomness, so one protocol sample is
   also a sample of the reduction state followed by fresh uniform randomness,
   the order the challenger works in. *)
Lemma enc_slot_resampleE :
  `p_ [% State, (fun t => enc_slot (State t) (Rho t))
        : {RV P -> cipher AHE}]
  = Q `X (fun a => fdistmap (enc_slot a) (fdist_uniform card_renc)).
Proof.
have HL : `p_ [% State, (fun t => enc_slot (State t) (Rho t))
                : {RV P -> cipher AHE}]
        = fdistmap (fun p : (stateT * Renc)%type => (p.1, enc_slot p.1 p.2))
                   (`p_ [% State, Rho]).
  by rewrite /dist_of_RV fdistmap_comp.
rewrite HL state_rho_prodE [in RHS]fdist_prod_bindE fdist_prod_bindE
        fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => a.
rewrite !fdistmap_comp.
congr fdistmap; exact/boolp.funext.
Qed.

End enc_slot_resample.

Section protocol_indcpa.

Variables (sampleT stateT : finType).
(* The carrier a distinguisher reads, as in distinguisher and accept above. *)
Variable T : finType.
Variable P : R.-fdist sampleT.
Variables (State : {RV P -> stateT}) (Rho : {RV P -> Renc}).
Variable pk : pub_key AHE.

(* The plaintext the reduction submits to the challenger, read off its own
   state.  It plays the role of the adv_plain field of indcpa_adversary. *)
Variable challenge_plain : stateT -> plain AHE.

(* [assemble c ch] reconstructs the complete value a distinguisher is tested
   on from reduction state c and challenge ciphertext ch. *)
Variable assemble : stateT -> cipher AHE -> T.

(* The value a distinguisher is tested on in a protocol run: Rho enters it at
   one place, the ciphertext of the plaintext that State selects, and
   everything else is a function of State.  That confinement is what lets a
   reduction hand Rho to the challenger and rebuild the tested value around
   the challenge ciphertext it gets back. *)
Definition protocol_RV : {RV P -> T} :=
  fun t => assemble (State t)
             (enc pk (challenge_plain (State t)) (rand_of_renc (Rho t))).

(* The freshness condition at the reduction's own state: the encryption
   randomness is uniform and independent of everything the reduction holds
   before it queries the challenger.  Confinement says where Rho enters, and
   this says that the coordinate the challenger takes over is a fresh one. *)
Hypothesis state_rho_prodE :
  `p_ [% State, Rho] = (`p_ State) `x (fdist_uniform card_renc).

(* The law of the value a distinguisher is handed inside the IND-CPA
   experiment: sample the reduction state, sample the challenge ciphertext for
   the plaintext that state selects, then assemble the tested value from the
   two. *)
Definition indcpa_fdist : R.-fdist T :=
  c  <- `p_ State ;
  ch <- enc_fdist pk (challenge_plain c) ;
  ret (assemble c ch).

(* The law read off one protocol sample equals the law of the IND-CPA
   experiment on the same value.  The two sides differ only in who owns the
   challenged coordinate, the protocol's Rho on the left and the challenger on
   the right, so the reduction reproduces the hop with no error term. *)
Lemma protocol_indcpa_fdistE : `p_ protocol_RV = indcpa_fdist.
Proof.
have -> : `p_ protocol_RV
        = fdistmap (fun q : stateT * cipher AHE => assemble q.1 q.2)
           (`p_ [% State,
                (fun t => enc pk (challenge_plain (State t))
                            (rand_of_renc (Rho t)))
                  : {RV P -> cipher AHE}]).
  by rewrite fdistmap_comp.
rewrite (enc_slot_resampleE
           (fun c r => enc pk (challenge_plain c) (rand_of_renc r))
           state_rho_prodE) fdist_prod_bindE fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (challenge_plain c)))
           fdistmap_comp.
Qed.

(* Acceptance under indcpa_fdist, unfolded as the state law bound with the
   pushforward of D along each challenge law.  With indcpa_success_realE and
   indcpa_success_zeroE it identifies a hop success probability with an
   IND-CPA success probability. *)
Lemma indcpa_fdist_acceptE (D : distinguisher T) :
  Pr indcpa_fdist [set x | D x]
  = Pr (c <- `p_ State ;
        fdistmap (fun ch => D (assemble c ch))
                 (enc_fdist pk (challenge_plain c)))
       [set true].
Proof.
rewrite -Pr_fdistmap_bool /indcpa_fdist fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite -/(fdistmap (assemble c) (enc_fdist pk (challenge_plain c)))
           fdistmap_comp.
Qed.

End protocol_indcpa.

End indcpa_game.

Arguments predictor : clear implicits.
