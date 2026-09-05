From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption residuosity_game.
Require Import benaloh_enc benaloh_ahe.
Require Import negligible indcpa_game epshop.

(**md**************************************************************************)
(* # Benaloh as an IND-CPA scheme                                             *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v quantifies over an AHEncType, a finite   *)
(* coin-index type, a proof that its cardinality is a successor, and a map    *)
(* from coin indices to the scheme's randomness.  This file supplies all four *)
(* at the Benaloh packaging of benaloh_ahe.v, packs them as the indcpa_scheme *)
(* value benaloh_indcpa_scheme, derives the IND-CPA assumption of Benaloh at  *)
(* that packaging from r-th residuosity, and indexes the whole scheme by a    *)
(* security parameter.  No protocol enters: the file is the scheme side of    *)
(* every computational bound the DSDP files read off at Benaloh, and          *)
(* dsdp_instance_sequence.v is where those bounds are read off.               *)
(*                                                                            *)
(* At this scheme the coin index type is the scheme's own randomness, the     *)
(* finite unit group of Z/nZ, and the coin map is the identity.  The          *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* ## How the scheme and the game are connected                               *)
(*                                                                            *)
(* Benaloh_AHEnc packs the Benaloh scheme as one structure.  It holds the     *)
(* encryption function enc, the decryption function dec, the map from a       *)
(* private key to its public key, and the homomorphic operations.  The DSDP   *)
(* protocol runs on this structure.                                           *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v is written for any such structure.  Its  *)
(* challenger encrypts with the structure's own enc, and draws the coin       *)
(* uniformly from the coin type.  At Benaloh the coin type is the unit        *)
(* group of Z/nZ and the coin map is the identity.  So the challenger draws   *)
(* a uniform unit u and returns y^m * u^r mod n.  That is the Benaloh         *)
(* encryption of benaloh_enc.v.  enc_fdist_benalohE states this; both sides   *)
(* unfold to the same term, so its proof is by [].                            *)
(*                                                                            *)
(* The IND-CPA assumption is a record indexed by that structure.  Its bound   *)
(* is on indcpa_epsilon, which unfolds through the challenger to the same     *)
(* enc.  So the bound this file carries is a bound on the real Benaloh        *)
(* encryption and nothing else.  benaloh_indcpa_epsilon_le writes that        *)
(* bound out in full.                                                         *)
(*                                                                            *)
(* The assumption is derived rather than taken.  benaloh_indcpa_assumption    *)
(* below is built from an r-th residuosity assumption at modulus n, the       *)
(* record of residuosity_game.v holding an extensional Boolean class of       *)
(* distinguishers, one epsilon, and the promise that every classified         *)
(* distinguisher tells an r-th residue of Z/nZ from a uniform unit with       *)
(* advantage at most that epsilon.  The IND-CPA class the derived record      *)
(* carries is the adversaries whose two residuosity reductions that class     *)
(* admits, and its epsilon is twice the residuosity epsilon: one residuosity  *)
(* call carries the real arm of the experiment from the residue law to the    *)
(* unit law, where the generator power the adversary chose cancels, and a     *)
(* second call carries the zero arm back.  Both terms are                     *)
(* assumption-conditional, so the whole derived bound is computational.       *)
(*                                                                            *)
(* The reduction below is written in the epsHop language of                   *)
(* computational_security/epshop.v.  Its objects are the four acceptance      *)
(* probabilities the hybrid passes through, and its loss is the two-term      *)
(* list whose entries are labelled residuosity_y and residuosity_0, each      *)
(* carrying the r-th residuosity epsilon its call assumes.  The bound of      *)
(* benaloh_residuosity_epsilon_le is loss_eval of that list and its two       *)
(* hypotheses are the two class memberships the chain is built at, so the     *)
(* bound is read off the chain rather than reassembled from a triangle        *)
(* inequality of its own.  The chain differs from the Paillier chain of       *)
(* paillier_indcpa_scheme.v in one place: its middle equality takes no order  *)
(* premise on the generator, the multiplier val y ^+ m being a unit whatever  *)
(* y and m are.                                                               *)
(*                                                                            *)
(* The reduction reads two number-theoretic facts, 1 < n and 1 < r.  It       *)
(* multiplies by val y ^+ m, the value of a group power and hence a unit by   *)
(* its type, so the order condition y ^+ r = 1 the key records carry stays    *)
(* unused, as do primality of the factors of n and the structure of the unit  *)
(* group of Z/nZ.  The key is any private key record, quantified universally, *)
(* rather than a sample from a key generation law, and BenalohPrivKey has no  *)
(* inhabitant in the development, asking in addition for r %| phi(n) and for  *)
(* the injectivity of m |-> y ^+ ((phi(n) %/ r) * m).  Every bound below is   *)
(* therefore stated at private keys the development never constructs.         *)
(* trivial_pub_key of benaloh_ahe.v inhabits the public key record instead,   *)
(* at the degenerate generator y = 1.  The homomorphic operations are read    *)
(* only by the protocol, never by the game.                                   *)
(*                                                                            *)
(* Along a sequence of parameters every datum above becomes a function of     *)
(* the security parameter k, and two hypotheses give the sequence its         *)
(* asymptotic content: the block sizes outgrow every polynomial, and the      *)
(* assumed residuosity advantages fall below every inverse polynomial.  It    *)
(* is the block size r, the plaintext space Z/rZ, that must grow, and not     *)
(* the modulus n, which sizes the ciphertext space.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*              Benaloh_AHEnc == the Benaloh AHEncType at modulus n and       *)
(*                               block size r                                 *)
(*               renc_benaloh == the coin index type of this instantiation,   *)
(*                               the unit group of Z/nZ                       *)
(*       rand_of_renc_benaloh == the coin map, the identity                   *)
(*          card_renc_benaloh == the successor form of that cardinality, in   *)
(*                               one pinned proof term                        *)
(*      benaloh_indcpa_scheme == the four data above as one indcpa_scheme     *)
(*                               value, at modulus n and block size r         *)
(*         enc_fdist_benalohE == the IND-CPA challenger at this packaging     *)
(*                               encrypts with benaloh_enc under uniform      *)
(*                               unit-group randomness                        *)
(* benaloh_residuosity_assumption ==                                          *)
(*                            r-th residuosity at modulus n, the assumption   *)
(*                            every bound below is derived from               *)
(* benaloh_residuosity_epsilon ==                                             *)
(*                            the advantage that record assumes, the          *)
(*                            currency the Benaloh bounds are stated in       *)
(*   residuosity_of_adversary == the adversary read as a distinguisher        *)
(*                               multiplying its challenge by the generator   *)
(*                               power its plaintext names                    *)
(* residuosity_of_adversary_zero ==                                           *)
(*                            the same adversary passing its challenge        *)
(*                            through unchanged                               *)
(*   real_accept_residuosityE == the real arm of the experiment is the first  *)
(*                               reduction under the residue law              *)
(*   zero_accept_residuosityE == the zero arm is the second reduction under   *)
(*                               the residue law                              *)
(*   unit_accept_residuosityE == under the unit law the two reductions accept *)
(*                               with the same probability                    *)
(*              residuosity_y == the label of the hop that carries the real   *)
(*                               arm to the unit law                          *)
(*              residuosity_0 == the label of the hop that carries the zero   *)
(*                               arm back                                     *)
(*        benaloh_chain Hy H0 == the reduction as a chain of two hops         *)
(*                               around one equality, at the two class        *)
(*                               memberships it spends                        *)
(*        benaloh_chain_lossE == the loss of that chain totals twice the      *)
(*                               residuosity epsilon                          *)
(* benaloh_residuosity_epsilon_le ==                                          *)
(*                            an adversary whose two reductions are both      *)
(*                            classified has IND-CPA advantage at most twice  *)
(*                            the residuosity epsilon                         *)
(* benaloh_residuosity_admissible ==                                          *)
(*                            the IND-CPA class of the derived assumption,    *)
(*                            the adversaries whose two reductions the        *)
(*                            residuosity class admits                        *)
(* benaloh_residuosity_admissible_epsilon_le ==                               *)
(*                            that bound under the Boolean class              *)
(*  benaloh_indcpa_assumption == the IND-CPA assumption of Benaloh, derived   *)
(*                               from r-th residuosity at twice its epsilon   *)
(* benaloh_residuosity_admissible_cipher_constant ==                          *)
(*                            at the zero-epsilon residuosity assumption the  *)
(*                            derived class admits every ciphertext-ignoring  *)
(*                            adversary                                       *)
(*  benaloh_indcpa_epsilon_le == that bound with the Benaloh experiment       *)
(*                               written out: acceptance of an encryption of  *)
(*                               the chosen plaintext and of zero differ by   *)
(*                               at most twice the residuosity epsilon        *)
(*                        f_r == the inverse block-size sequence 1/(r k)      *)
(*             f_size_benaloh == the inverse plaintext-cardinality sequence   *)
(*                               at Benaloh                                   *)
(*      f_residuosity_benaloh == the assumed residuosity-advantage sequence   *)
(*              f_adv_benaloh == the derived advantage sequence, twice        *)
(*                               f_residuosity_benaloh                        *)
(*            f_bound_benaloh == f_r plus twice f_adv_benaloh                 *)
(* f_size_benaloh_negligible ==                                               *)
(*                              superpolynomial growth of r k makes           *)
(*                              f_size_benaloh negligible                     *)
(*   f_adv_benaloh_negligible == f_adv_benaloh is negligible when             *)
(*                               f_residuosity_benaloh is                     *)
(* f_bound_benaloh_negligible == f_bound_benaloh is negligible when f_r and   *)
(*                               f_residuosity_benaloh are                    *)
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

Section benaloh_indcpa_scheme.
Context {R : realType}.
Variables n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* The Benaloh AHEncType at modulus n and block size r: the encryption and
   decryption pair of benaloh_ahe.v together with the additively homomorphic
   structure the DSDP protocol runs on.  The homomorphic mixin is built at
   r > 1, which is why r_gt1 enters the packaging.  The modulus condition
   n > 1 is the standing requirement on the key space, weaker than the
   composite modulus the scheme's security rests on and consumed by neither
   the packaging nor the bound below. *)
Definition Benaloh_AHEnc : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r) (@Benaloh_isEncDec n r)
      (@Benaloh_isAHEnc n r r_gt1)).

Local Notation AHE := Benaloh_AHEnc.

(* The coin index type of this instantiation: the scheme's own randomness
   carrier, the unit group of Z/nZ.  The abstract development draws
   encryption randomness from a finite type and maps it into rand, because
   the generic rand of he_types.v is a bare Type and carries no distribution;
   at a concrete scheme the two coincide.
   Naming: [renc] is the coin-index token of the abstract development, with
   the scheme named after it. *)
Definition renc_benaloh : finType := {unit 'Z_n}.

(* The coin map of this instantiation is the identity: the coin index type
   above is definitionally the scheme's randomness, so a coin is already the
   randomness the encryption consumes. *)
Definition rand_of_renc_benaloh : renc_benaloh -> rand AHE := idfun.

(* The coin space is nonempty, written in the successor form the uniform
   distribution of the abstract development takes.
   Every statement below is instantiated at this one proof term.  A second
   proof of the same equation is propositionally equal to this one and not
   convertible with it, so bounds stated at the two would compose only
   through a rewrite. *)
Lemma card_renc_benaloh : #|renc_benaloh| = #|renc_benaloh|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The Benaloh scheme as one value of the scheme record the IND-CPA game is
   quantified over: the packaging at modulus n and block size r, its coin
   index type, the pinned cardinality above, and the identity coin map.  The
   DSDP files instantiate the game at this value, so every bound they read
   off at Benaloh is a bound at the scheme record built here and at no other
   proof of the coin-space cardinality. *)
Definition benaloh_indcpa_scheme : indcpa_scheme :=
  {| scheme_AHE := AHE ; scheme_renc := renc_benaloh ;
     scheme_card_renc := card_renc_benaloh ;
     scheme_rand_of_renc := rand_of_renc_benaloh |}.

(* The IND-CPA challenger at this packaging is the Benaloh encryption of
   benaloh_enc.v under uniform unit-group randomness.  The game's enc is the
   packaging's enc and the coin map is the identity, so the two laws are one
   term.  This is the point where the game of indcpa_game.v and the scheme
   of benaloh_ahe.v meet: every advantage measured below is measured against
   this law, and so against c = y^m * u^r mod n with u uniform in the unit
   group. *)
Lemma enc_fdist_benalohE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) card_renc_benaloh rand_of_renc_benaloh pk v
  = fdistmap (benaloh_enc (pub_gen pk) v) (fdist_uniform card_renc_benaloh).
Proof. by []. Qed.

(* The two challenge laws of the residuosity game at this scheme's ring: a
   uniform unit of Z/nZ read as a ring element, and its r-th power.  The
   second is the law of a Benaloh encryption of zero, the first the law the
   reduction moves that encryption to. *)
Local Notation unit_fdist := (unit_fdist (R:=R) 'Z_n card_renc_benaloh).
Local Notation residue_fdist :=
  (residue_fdist (R:=R) 'Z_n r card_renc_benaloh).

(* The r-th residuosity assumption at modulus n, Benaloh 1994's higher
   residuosity assumption: an extensional Boolean class of residuosity
   distinguishers, one epsilon, and the promise that every classified
   distinguisher tells an r-th residue of Z/nZ from a uniform unit with
   advantage at most that epsilon.  A record of this type is the only
   computational premise every bound below takes, and its epsilon is the
   advantage the assumption assumes rather than a quantity proved of any
   distinguisher. *)
Definition benaloh_residuosity_assumption : Type :=
  residuosity_assumption (R:=R) 'Z_n r card_renc_benaloh.

(* The advantage an r-th residuosity record assumes of the distinguishers its
   class admits.  It is the currency every Benaloh IND-CPA bound of this file
   is stated in: an IND-CPA epsilon at one key is twice it, one call per hop
   of the reduction below, and a trace bound that replaces a ciphertext at
   two keys spends it four times.
   Naming: [benaloh_residuosity] names the game the epsilon belongs to,
   distinguishing it from the IND-CPA epsilon derived from it. *)
Definition benaloh_residuosity_epsilon (A : benaloh_residuosity_assumption)
    : R := residuosity_assumption_epsilon A.

(* The first reduction: an IND-CPA adversary read as a residuosity
   distinguisher that multiplies its challenge by y ^+ m, the generator power
   its own plaintext names.  Under the residue law that multiplier turns the
   challenge into an encryption of m, and under the unit law it erases m. *)
Definition residuosity_of_adversary (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) AHE) :
    residuosity_distinguisher (R:=R) 'Z_n :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c (val y ^+ (adv_plain c) * x) |}.

(* The second reduction: the same adversary with its challenge passed through
   unchanged.  Under the residue law the challenge is already an encryption of
   zero, so this distinguisher runs the zero arm of the IND-CPA experiment. *)
Definition residuosity_of_adversary_zero
    (adv : indcpa_adversary (R:=R) AHE) :
    residuosity_distinguisher (R:=R) 'Z_n :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c x |}.

(* The real arm of the IND-CPA experiment is the first reduction run against
   the residue law: an encryption of m under generator y is y ^+ m times the
   r-th power of a uniform unit.  Both sides are one term once the two
   pushforwards are composed, so the reduction pays nothing here. *)
Lemma real_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) AHE) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (benaloh_enc y (adv_plain c))
           (fdist_uniform card_renc_benaloh))) [set true]
  = residuosity_accept (residuosity_of_adversary y adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _).
by congr (_ >>= _); apply/funext => c; rewrite !fdistmap_comp.
Qed.

(* The zero arm is the second reduction run against the residue law: at
   plaintext zero the generator power is 1 and an encryption is the r-th power
   of a uniform unit and nothing else.  The plaintext is written
   (0 : plain AHE) because the ring 'Z_n the generator lives in fixes the
   modulus and leaves the plaintext block size r to the annotation. *)
Lemma zero_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) AHE) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (benaloh_enc y (0 : plain AHE))
           (fdist_uniform card_renc_benaloh))) [set true]
  = residuosity_accept (residuosity_of_adversary_zero adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _).
congr (_ >>= _); apply/funext => c; rewrite !fdistmap_comp.
by congr (fdistmap _ _); apply/funext => u; rewrite /benaloh_enc expr0 /= mul1r.
Qed.

(* Under the unit law the two reductions accept with the same probability.
   This is the hop of the hybrid that costs nothing: it is the key fact of
   residuosity_game.v, multiplication by a unit fixes the uniform law, applied
   state by state at the multiplier val y ^+ (adv_plain c).  That multiplier
   is the value of the group power (y ^+ m)%g, hence a unit whatever y and m
   are, which is why the reduction never reads the generator's order. *)
Lemma unit_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) AHE) :
  residuosity_accept (residuosity_of_adversary y adv) unit_fdist
  = residuosity_accept (residuosity_of_adversary_zero adv) unit_fdist.
Proof.
(* Both sides draw the state c the same way; compare the inner laws at each
   fixed c, with the ring power rewritten as a group power. *)
rewrite !residuosity_acceptE /=; congr (Pr _ _); congr (_ >>= _).
apply/funext => c; rewrite -FinRing.val_unitX.
(* The key fact at this state's multiplier.  This step is not a pointwise
   probability computation in the ring: it treats multiplication by the fixed
   unit y ^+ (adv_plain c) as a permutation of the unit group.  fdistmap_comp
   and fdistmap_bij_uniform prove that this permutation leaves the uniform law
   unchanged, the result is pushed back to the ring along val, and so the two
   acceptance probabilities are equal. *)
exact: (unit_fdistmap_translateE 'Z_n card_renc_benaloh (adv_decide c)
          (y ^+ (adv_plain c))%g).
Qed.

(* The acceptance probability of a residuosity distinguisher, under the short
   name the chain below reads at. *)
Local Notation accept := (residuosity_accept (R:=R)).

(* The label of the first hop, whose residuosity call is made through the
   reduction that multiplies its challenge by the generator power the
   adversary's plaintext names.  A label names the reduction the hop invokes,
   so the loss of a finished chain records which distinguisher each of its
   terms was assumed of, alongside their numeric total.
   Naming: [residuosity] is the assumption invoked and [y] the generator that
   reduction multiplies the challenge by. *)
Definition residuosity_y : nat := 0%N.

(* The label of the second hop, whose residuosity call is made through the
   reduction that hands its challenge to the adversary unchanged.
   Naming: [0] is the plaintext that reduction encrypts, the zero arm of the
   IND-CPA experiment. *)
Definition residuosity_0 : nat := 1%N.

Local Open Scope epshop_scope.

(* The reduction as a chain of hops over acceptance probabilities.  It starts
   at the real arm, which is the multiplying reduction accepting under the
   residue law; one residuosity call moves that reduction to the unit law,
   where the generator power cancels; the middle equality replaces the
   multiplying reduction by the plain one at no cost; and a second call moves
   the plain reduction back to the residue law, where its acceptance is the
   zero arm.  Each call logs its own labelled term, so what the chain carries
   is the list of the two assumptions the derived bound rests on.  Those two
   assumptions are parameters of the chain, so a chain that exists has already
   spent them and leaves nothing to discharge. *)
Definition benaloh_chain (A : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) AHE)
    (Hy : residuosity_admissible A (residuosity_of_adversary (priv_gen dk) adv))
    (H0 : residuosity_admissible A (residuosity_of_adversary_zero adv))
    : chain nat R :=
  let D_y := residuosity_of_adversary (priv_gen dk) adv in
  let D_0 := residuosity_of_adversary_zero adv in
  let eps_residuosity := benaloh_residuosity_epsilon A in
  (* the real arm *)
  \epsilon{ start (accept D_y residue_fdist) ;
            (* the first residuosity call, through D_y *)
            hop residuosity_y eps_residuosity to (accept D_y unit_fdist)
              by residuosity_admissible_epsilon_le _ _ Hy ;
            (* the free step: under the unit law the multiplier erases the
               plaintext, Katz and Lindell 2015 Lemma 11.15 *)
            same to (accept D_0 unit_fdist)
              by unit_accept_residuosityE (priv_gen dk) adv ;
            (* the second residuosity call, through D_0 run backwards, and
               the zero arm *)
            hop residuosity_0 eps_residuosity to (accept D_0 residue_fdist)
              by residuosity_admissible_epsilon_leC _ _ H0 }.

(* The chain totals two residuosity calls: each hop logs one term at the
   assumed epsilon and the middle equality logs nothing.  This is where the
   factor two in every Benaloh IND-CPA bound of this file comes from. *)
Lemma benaloh_chain_lossE (A : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) AHE)
    (Hy : residuosity_admissible A (residuosity_of_adversary (priv_gen dk) adv))
    (H0 : residuosity_admissible A (residuosity_of_adversary_zero adv)) :
  loss_eval (chain_loss (benaloh_chain Hy H0))
  = 2 * benaloh_residuosity_epsilon A.
Proof.
rewrite /loss_eval /benaloh_chain /= big_cons big_cons big_nil addr0.
by rewrite mulr_natl mulr2n.
Qed.

(* The reduction and its loss.  At every private key, an adversary whose two
   residuosity reductions the residuosity class admits has IND-CPA advantage
   at most twice the assumed residuosity epsilon: one residuosity call carries
   the real arm from the residue law to the unit law, the middle equality
   above logs nothing, and a second call carries the zero arm back.  Both
   terms are assumption-conditional, so the whole bound is computational. *)
Lemma benaloh_residuosity_epsilon_le (A : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) AHE) :
  residuosity_admissible A (residuosity_of_adversary (priv_gen dk) adv) ->
  residuosity_admissible A (residuosity_of_adversary_zero adv) ->
  indcpa_epsilon (R:=R) card_renc_benaloh rand_of_renc_benaloh
    (pub_of_priv dk) adv
  <= 2 * benaloh_residuosity_epsilon A.
Proof.
move=> Hy H0.
rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE.
rewrite !enc_fdist_benalohE /= real_accept_residuosityE.
rewrite zero_accept_residuosityE -(benaloh_chain_lossE Hy H0).
exact: chain_sound (benaloh_chain Hy H0).
Qed.

(* The IND-CPA class the derived assumption carries: the adversaries whose two
   residuosity reductions the residuosity class admits.  The first quantifier
   runs over the whole unit group of Z/nZ because the multiplier is the key's
   generator and the class is fixed before any key is, and that group is a
   finite type, so the quantifier is a Boolean test. *)
Definition benaloh_residuosity_admissible (A : benaloh_residuosity_assumption)
    (adv : indcpa_adversary (R:=R) AHE) : bool :=
  [forall y : ring_units 'Z_n,
     residuosity_admissible A (residuosity_of_adversary y adv)]
  && residuosity_admissible A (residuosity_of_adversary_zero adv).

(* The same bound under that Boolean class, the shape the third field of an
   IND-CPA assumption record takes.
   Naming: extends [benaloh_residuosity_epsilon_le] with the [admissible]
   variant token before [le], after alice_trace_guess_V2_admissible_le. *)
Lemma benaloh_residuosity_admissible_epsilon_le
    (A : benaloh_residuosity_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) AHE) :
  benaloh_residuosity_admissible A adv ->
  indcpa_epsilon (R:=R) card_renc_benaloh rand_of_renc_benaloh
    (pub_of_priv dk) adv
  <= 2 * benaloh_residuosity_epsilon A.
Proof.
by case/andP => /forallP Hy H0; apply: benaloh_residuosity_epsilon_le (Hy _) H0.
Qed.

(* The IND-CPA assumption of Benaloh, derived rather than assumed: the class
   above, twice the residuosity epsilon, and the lemma above as the record's
   proof field.  Every computational bound the DSDP files read off at Benaloh
   passes through this record, so each of those bounds is stated in r-th
   residuosity currency at two residuosity calls per key. *)
Definition benaloh_indcpa_assumption (A : benaloh_residuosity_assumption) :
    indcpa_epsilon_assumption (R:=R) card_renc_benaloh
      rand_of_renc_benaloh :=
  {| indcpa_admissible := benaloh_residuosity_admissible A ;
     indcpa_assumption_epsilon := 2 * benaloh_residuosity_epsilon A ;
     indcpa_admissible_epsilon_le :=
       @benaloh_residuosity_admissible_epsilon_le A |}.

(* At the zero-epsilon residuosity assumption of residuosity_game.v the
   derived class admits every adversary whose verdict ignores the ciphertext:
   both reductions hand such an adversary a challenge it never reads.  The
   derived class therefore has an inhabitant at a record that exists, so a
   statement restricted to it is not empty for want of an adversary to read it
   at.  It does not show that the class is inhabited at a useful epsilon.
   Naming: [benaloh_residuosity_admissible] is the class the conclusion
   asserts and [cipher_constant] the premise's class, the token
   adv_decide_cipher_constant of indcpa_game.v carries. *)
Lemma benaloh_residuosity_admissible_cipher_constant
    (adv : indcpa_adversary (R:=R) AHE) :
  adv_decide_cipher_constant adv ->
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_n r card_renc_benaloh) adv.
Proof.
move=> /forallP Hc; apply/andP; split; last first.
  by apply/forallP => c; apply/forallP => x; apply/forallP => z;
     move: (Hc c) => /forallP/(_ x)/forallP/(_ z).
apply/forallP => y; apply/forallP => c; apply/forallP => x; apply/forallP => z.
by move: (Hc c) => /forallP/(_ (val y ^+ adv_plain c * x))
                   /forallP/(_ (val y ^+ adv_plain c * z)).
Qed.

(* What the derived assumption says of Benaloh, with the experiment written
   out.  For every private key and every adversary the residuosity class
   admits, the probability that the adversary accepts an encryption of its
   chosen plaintext under the key's generator and the probability that it
   accepts an encryption of zero differ by at most twice the residuosity
   epsilon.  The key ranges over every BenalohPrivKey record, so the bound is
   universal over keys rather than averaged over a key-generation law, and the
   adversary holds the public key alone. *)
Lemma benaloh_indcpa_epsilon_le (A : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) AHE) :
  benaloh_residuosity_admissible A adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_benaloh))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (0 : plain AHE))
              (fdist_uniform card_renc_benaloh))) [set true] |
  <= 2 * benaloh_residuosity_epsilon A.
Proof.
move=> Hadm; have := benaloh_residuosity_admissible_epsilon_le dk Hadm.
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
           !enc_fdist_benalohE.
Qed.

End benaloh_indcpa_scheme.

Section benaloh_indcpa_scheme_sequence.
Context {R : realType}.
Variables n r : nat -> nat.
Hypothesis n_gt1 : forall k, (1 < n k)%N.
Hypothesis r_gt1 : forall k, (1 < r k)%N.

(* The Benaloh IND-CPA scheme at parameter k is the fixed scheme above taken
   at n k and r k: the packaging Benaloh_AHEnc (n k) (r_gt1 k), the coin type
   renc_benaloh (n k), the pinned cardinality card_renc_benaloh (n k), and
   the coin map rand_of_renc_benaloh (r_gt1 k), which is
   benaloh_indcpa_scheme (n k) (r_gt1 k).  A sequence of r-th residuosity
   assumptions, at the modulus n k and the exponent r k, is the only
   computational premise the sequence takes: the IND-CPA assumption at k is
   derived from it by benaloh_indcpa_assumption. *)
Variable D : forall k, benaloh_residuosity_assumption (R:=R) (n k) (r k).

(* The inverse block-size sequence 1/(r k), the form a growth condition on
   the block sizes is stated in. *)
Definition f_r k : R := ((r k)%:R : R)^-1.

(* The inverse plaintext-cardinality sequence at Benaloh: the
   information-theoretic summand of every guessing bound read off along the
   sequence. *)
Definition f_size_benaloh k : R :=
  (#|plain (Benaloh_AHEnc (n k) (r_gt1 k))|%:R : R)^-1.

(* The assumed residuosity-advantage sequence: the epsilon D k assumes at each
   k, the currency every computational bound along the sequence is stated
   in. *)
Definition f_residuosity_benaloh k : R := benaloh_residuosity_epsilon (D k).

(* The derived IND-CPA advantage sequence: twice the residuosity advantage at
   k, the two residuosity calls the reduction spends at one key. *)
Definition f_adv_benaloh k : R :=
  indcpa_assumption_epsilon (benaloh_indcpa_assumption (r_gt1 k) (D k)).

(* The bound sequence 1/(r k) + 2 * eps k: the shape of the class-conditional
   guessing bound at each k, before any protocol is named. *)
Definition f_bound_benaloh k : R := f_r k + 2 * f_adv_benaloh k.

(* The block sizes outgrow every polynomial in k.  At Benaloh the block size
   is the plaintext cardinality, so this is the growth of the plaintext
   space, and negligible is the asymptotic acceptance criterion for the
   guessing residue an inverse plaintext cardinality concedes. *)
Hypothesis f_r_negligible : negligible_fun f_r.

(* The advantage the residuosity assumption sequence assumes is negligible:
   the asymptotic reading of r-th residuosity along the sequence, and the only
   computational hypothesis the sequence makes. *)
Hypothesis f_residuosity_benaloh_negligible :
  negligible_fun f_residuosity_benaloh.

(* The derived IND-CPA advantage is negligible, twice a negligible family
   being negligible.  What a sequence of IND-CPA assumptions had to take as a
   hypothesis is here a consequence of the residuosity hypothesis, at the
   cost of the factor two the reduction spends. *)
Lemma f_adv_benaloh_negligible : negligible_fun f_adv_benaloh.
Proof. exact: negligible_fun_double f_residuosity_benaloh_negligible. Qed.

(* The inverse plaintext cardinality along the sequence is negligible: the
   plaintext space at k is Z/(r k)Z, so block-size growth is plaintext
   growth.  This is the scheme-side summand of every guessing bound of the
   shape 1/#|plain| + 2 * eps read off along the sequence. *)
Lemma f_size_benaloh_negligible : negligible_fun f_size_benaloh.
Proof.
rewrite /f_size_benaloh.
under eq_fun => k do rewrite card_ord (Zp_cast (r_gt1 k)).
exact: f_r_negligible.
Qed.

(* The bound sequence is negligible.  This is the whole asymptotic content of
   the Benaloh IND-CPA scheme sequence, stated before any protocol is named:
   a bound of this shape at each k, whatever protocol produced it, vanishes
   in the security parameter. *)
Lemma f_bound_benaloh_negligible : negligible_fun f_bound_benaloh.
Proof.
exact: negligible_fun_predictor_bound f_r_negligible
         f_adv_benaloh_negligible.
Qed.

End benaloh_indcpa_scheme_sequence.
