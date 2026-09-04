From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption residuosity_game.
Require Import paillier_enc paillier_ahe paillier_fdist_instance.
Require Import indcpa_game.

(**md**************************************************************************)
(* # Paillier as an IND-CPA scheme                                            *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v quantifies over an AHEncType, a finite   *)
(* coin-index type, a proof that its cardinality is a successor, and a map    *)
(* from coin indices to the scheme's randomness.  This file supplies all      *)
(* four at the Paillier packaging of paillier_fdist_instance.v, packs them    *)
(* as the indcpa_scheme value paillier_indcpa_scheme, derives the IND-CPA     *)
(* assumption of Paillier at that packaging from decisional composite         *)
(* residuosity, and indexes the whole scheme by a security parameter.  No     *)
(* protocol enters: the file is the scheme side of every computational bound  *)
(* the DSDP files read off at Paillier, and dsdp_instance_sequence.v is where *)
(* those bounds are read off.                                                 *)
(*                                                                            *)
(* At this scheme the coin index type is the scheme's own randomness, the     *)
(* finite unit group of Z/(pq)^2 Z, and the coin map is the identity.  The    *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* ## How the scheme and the game are connected                               *)
(*                                                                            *)
(* Paillier_AHEnc packs the Paillier scheme as one structure.  It holds the   *)
(* encryption function enc, the decryption function dec, the map from a       *)
(* private key to its public key, and the homomorphic operations.  The DSDP   *)
(* protocol runs on this structure.                                           *)
(*                                                                            *)
(* The IND-CPA game of indcpa_game.v is written for any such structure.  Its  *)
(* challenger encrypts with the structure's own enc, and draws the coin       *)
(* uniformly from the coin type.  At Paillier the coin type is the unit       *)
(* group of Z/(pq)^2 Z and the coin map is the identity.  So the challenger   *)
(* draws a uniform unit u and returns g^m * u^n mod (pq)^2.  That is the      *)
(* Paillier encryption of paillier_enc.v.  enc_fdist_paillierE states this;   *)
(* both sides unfold to the same term, so its proof is by [].                 *)
(*                                                                            *)
(* The IND-CPA assumption is a record indexed by that structure.  Its bound   *)
(* is on indcpa_epsilon, which unfolds through the challenger to the same     *)
(* enc.  So a bound stated through indcpa_epsilon is a bound on the real      *)
(* Paillier encryption and nothing else.  paillier_indcpa_epsilon_le writes   *)
(* that bound out in full.                                                    *)
(*                                                                            *)
(* ## Where the IND-CPA assumption comes from                                 *)
(*                                                                            *)
(* The IND-CPA assumption of Paillier is derived here from a decisional       *)
(* composite residuosity record at modulus p q: the residuosity assumption    *)
(* of residuosity_game.v read at the ring Z/(pq)^2 Z and the exponent p q,    *)
(* which is Paillier 1999 Conjecture 1.  The class it covers is the class of  *)
(* IND-CPA adversaries whose two residuosity reductions the residuosity       *)
(* class admits: the reduction that multiplies the challenge by the           *)
(* generator raised to the adversary's plaintext, and the one that hands the  *)
(* challenge over unchanged.                                                  *)
(*                                                                            *)
(* The price is 2 eps_DCR at each key, one DCR call per hop of a two-step     *)
(* hybrid: the first hop moves the real experiment from the residue           *)
(* challenge to the unit challenge, the second moves the zero experiment      *)
(* back.  Between them the multiplier erases the plaintext, so the middle     *)
(* step is an identity and costs nothing.                                     *)
(*                                                                            *)
(* The one number-theoretic input is g ^+ (p q) = 1, the order condition the  *)
(* private key record already carries.  The statement proved here is          *)
(* therefore Katz and Lindell 2015, Theorem 13.13, generalized to any         *)
(* generator whose order divides the modulus, and primality of p and q is     *)
(* unused.  The key is any private key record, quantified universally,        *)
(* rather than a sample from a key generation law, and PaillierPrivKey has    *)
(* no inhabitant in this development, so every bound below holds at private   *)
(* keys the development never constructs.  The homomorphic operations are     *)
(* never read by the game; only the protocol uses them.                       *)
(*                                                                            *)
(* Along a sequence of moduli every datum above becomes a function of the     *)
(* security parameter k, and two hypotheses give the sequence its asymptotic  *)
(* content: the moduli outgrow every polynomial, and the assumed residuosity  *)
(* advantages fall below every inverse polynomial.                            *)
(*                                                                            *)
(* ```                                                                        *)
(*                    pq_gt1 == the modulus bound the packaging is taken at   *)
(*             renc_paillier == the coin index type of this instantiation,    *)
(*                              the unit group of Z/(pq)^2 Z                  *)
(*     rand_of_renc_paillier == the coin map, the identity                    *)
(*        card_renc_paillier == the successor form of that cardinality, in    *)
(*                              one pinned proof term                         *)
(*    paillier_indcpa_scheme == the four data above as one indcpa_scheme      *)
(*                              value, at modulus p q                         *)
(*       enc_fdist_paillierE == the IND-CPA challenger at this packaging      *)
(*                              encrypts with paillier_enc under uniform      *)
(*                              unit-group randomness                         *)
(*            dcr_assumption == decisional composite residuosity at           *)
(*                              modulus p q                                   *)
(*             dcr_epsilon A == the advantage that record assumes, the        *)
(*                              currency the Paillier bounds are priced in    *)
(*    dcr_of_adversary g adv == the residuosity distinguisher that hands      *)
(*                              adv the challenge multiplied by g raised      *)
(*                              to adv's plaintext                            *)
(* dcr_of_adversary_zero adv == the residuosity distinguisher that hands      *)
(*                              adv the challenge unchanged                   *)
(*          real_accept_dcrE == the real experiment is the first              *)
(*                              distinguisher at the residue challenge        *)
(*          zero_accept_dcrE == the zero experiment is the second             *)
(*                              distinguisher at the residue challenge        *)
(*          unit_accept_dcrE == at the unit challenge the two                 *)
(*                              distinguishers accept equally                 *)
(*   paillier_dcr_epsilon_le == the IND-CPA advantage of an adversary whose   *)
(*                              two reductions are classified is at most      *)
(*                              twice the residuosity epsilon                 *)
(*   paillier_dcr_admissible == the IND-CPA class the residuosity class       *)
(*                              induces: both reductions classified           *)
(* paillier_dcr_admissible_epsilon_le ==                                      *)
(*                              that bound under the induced class            *)
(* paillier_indcpa_assumption == the derived IND-CPA assumption of Paillier   *)
(*                              at this modulus, at epsilon 2 eps_DCR         *)
(* paillier_dcr_admissible_cipher_constant ==                                 *)
(*                              at the zero-epsilon residuosity witness the   *)
(*                              induced class admits every                    *)
(*                              ciphertext-ignoring adversary                 *)
(* paillier_indcpa_epsilon_le ==                                              *)
(*                              the derived bound with the Paillier           *)
(*                              experiment written out: acceptance of an      *)
(*                              encryption of the chosen plaintext and of     *)
(*                              zero differ by at most 2 eps_DCR              *)
(*                      f_pq == the inverse modulus sequence 1/(p k * q k)    *)
(*           f_size_paillier == the inverse plaintext-cardinality sequence    *)
(*                              at Paillier                                   *)
(*            f_dcr_paillier == the assumed residuosity-advantage sequence    *)
(*            f_adv_paillier == the derived IND-CPA advantage sequence,       *)
(*                              twice f_dcr_paillier                          *)
(*          f_bound_paillier == f_pq plus twice f_adv_paillier                *)
(* f_size_paillier_negligible ==                                              *)
(*                             superpolynomial growth of p k * q k makes      *)
(*                             f_size_paillier negligible                     *)
(* f_adv_paillier_negligible ==                                               *)
(*                             f_adv_paillier is negligible when              *)
(*                             f_dcr_paillier is                              *)
(* f_bound_paillier_negligible ==                                             *)
(*                             f_bound_paillier is negligible when f_pq       *)
(*                             and f_dcr_paillier are                         *)
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

Section paillier_indcpa_scheme.
Context {R : realType}.
Variables p q : nat.
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.

(* The modulus bound the Paillier packaging is taken at.  It is a Lemma
   rather than a section Let because the exported statements below mention
   the scheme, hence this proof term; a downstream file restating that bound
   at its own proof of the same inequality needs a name to write. *)
Lemma pq_gt1 : (1 < p * q)%N.
Proof. by rewrite (leq_trans p_gt1) // leq_pmulr // (ltnW q_gt1). Qed.

Local Notation AHE := (Paillier_AHEnc pq_gt1).

(* The coin index type of this instantiation: the scheme's own randomness
   carrier, the unit group of Z/(pq)^2 Z.  The abstract development draws
   encryption randomness from a finite type and maps it into rand, because
   the generic rand of he_types.v is a bare Type and carries no distribution;
   at a concrete scheme the two coincide.
   Naming: [renc] is the coin-index token of the abstract development, with
   the scheme named after it. *)
Definition renc_paillier : finType := {unit 'Z_((p * q) * (p * q))}.

(* The coin map of this instantiation is the identity: the coin index type
   above is definitionally the scheme's randomness, so a coin is already the
   randomness the encryption consumes. *)
Definition rand_of_renc_paillier : renc_paillier -> rand AHE := idfun.

(* The coin space is nonempty, written in the successor form the uniform
   distribution of the abstract development takes.
   Every statement below is instantiated at this one proof term.  A second
   proof of the same equation is propositionally equal to this one and not
   convertible with it, so bounds stated at the two would compose only
   through a rewrite. *)
Lemma card_renc_paillier : #|renc_paillier| = #|renc_paillier|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The Paillier scheme as one value of the scheme record the IND-CPA game is
   quantified over: the packaging at modulus p q, its coin index type, the
   pinned cardinality above, and the identity coin map.  The DSDP files
   instantiate the game at this value, so every bound they read off at
   Paillier is a bound at the scheme record built here and at no other
   proof of the coin-space cardinality. *)
Definition paillier_indcpa_scheme : indcpa_scheme :=
  {| scheme_AHE := AHE ; scheme_renc := renc_paillier ;
     scheme_card_renc := card_renc_paillier ;
     scheme_rand_of_renc := rand_of_renc_paillier |}.

(* The IND-CPA challenger at this packaging is the Paillier encryption of
   paillier_enc.v under uniform unit-group randomness.  The game's enc is
   the packaging's enc and the coin map is the identity, so the two laws are
   one term.  This is the point where the game of indcpa_game.v and the
   scheme of paillier_ahe.v meet: every advantage measured below is measured
   against this law, and so against c = g^m * u^n mod (pq)^2 with u
   uniform in the unit group. *)
Lemma enc_fdist_paillierE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) card_renc_paillier rand_of_renc_paillier pk v
  = fdistmap (paillier_enc (pub_gen pk) v) (fdist_uniform card_renc_paillier).
Proof. by []. Qed.

(* The two challenge laws of the residuosity problem at this scheme's ring
   and exponent: a uniform unit of Z/(pq)^2 Z, and the (p q)-th power of a
   uniform unit, which is the law of a Paillier encryption of zero. *)
Local Notation unit_fdist :=
  (unit_fdist (R:=R) 'Z_((p * q) * (p * q)) card_renc_paillier).
Local Notation residue_fdist :=
  (residue_fdist (R:=R) 'Z_((p * q) * (p * q)) (p * q) card_renc_paillier).

(* Decisional composite residuosity at modulus p q: the residuosity
   assumption of residuosity_game.v at the ring Z/(pq)^2 Z and the exponent
   p q, which is Paillier 1999 Conjecture 1.  A record of this type carries
   an extensional Boolean class of distinguishers, one epsilon, and the
   assumption that every classified distinguisher tells a uniform unit from
   a (p q)-th power with advantage at most that epsilon.  It is the single
   computational premise the Paillier bounds of this file are read at. *)
Definition dcr_assumption : Type :=
  residuosity_assumption (R:=R) 'Z_((p * q) * (p * q)) (p * q)
    card_renc_paillier.

(* The advantage a decisional composite residuosity record assumes of the
   distinguishers its class admits.  It is the currency every Paillier
   IND-CPA bound of this file is priced in: an IND-CPA epsilon at one key is
   twice it, one call per hop of the reduction below, and a trace bound that
   replaces a ciphertext at two keys spends it four times.
   Naming: [dcr] names the game the epsilon belongs to, distinguishing it
   from the IND-CPA epsilon it prices. *)
Definition dcr_epsilon (A : dcr_assumption) : R :=
  residuosity_assumption_epsilon A.

(* The first of the two reductions: an IND-CPA adversary run on the
   residuosity challenge multiplied by g raised to the adversary's own
   plaintext.  At the residue challenge the multiplied challenge is an
   encryption of that plaintext, so this distinguisher runs the real
   experiment; at the unit challenge the multiplier erases the plaintext. *)
Definition dcr_of_adversary (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) AHE) :
    residuosity_distinguisher (R:=R) 'Z_((p * q) * (p * q)) :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c (g ^+ adv_plain c * x) |}.

(* The second reduction: the same adversary run on the residuosity challenge
   unchanged.  At the residue challenge the challenge is an encryption of
   zero, so this distinguisher runs the zero experiment. *)
Definition dcr_of_adversary_zero (adv : indcpa_adversary (R:=R) AHE) :
    residuosity_distinguisher (R:=R) 'Z_((p * q) * (p * q)) :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c x |}.

(* The real experiment is the multiplying reduction at the residue
   challenge.  Both sides draw the state the same way and compose two
   pushforwards, so the identity is one fdistmap_comp per state. *)
Lemma real_accept_dcrE (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) AHE) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (paillier_enc g (adv_plain c))
           (fdist_uniform (R:=R) card_renc_paillier))) [set true]
  = residuosity_accept (dcr_of_adversary g adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _); congr (_ >>= _).
by apply/funext => c; rewrite !fdistmap_comp.
Qed.

(* The zero experiment is the plain reduction at the residue challenge: an
   encryption of zero is the (p q)-th power alone, the generator entering to
   the power zero. *)
Lemma zero_accept_dcrE (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) AHE) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (paillier_enc g 0)
           (fdist_uniform (R:=R) card_renc_paillier))) [set true]
  = residuosity_accept (dcr_of_adversary_zero adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _); congr (_ >>= _).
apply/funext => c; rewrite !fdistmap_comp; congr (fdistmap _ _).
by apply/funext => u; rewrite /paillier_enc expr0 /= mul1r.
Qed.

(* At the unit challenge the two reductions accept with the same
   probability.  This is the hop of the hybrid that costs nothing: it is the
   key fact, multiplication by a unit fixes the uniform law, applied state by
   state at the multiplier g ^+ (adv_plain c). *)
Lemma unit_accept_dcrE (g : 'Z_((p * q) * (p * q))) (gn : g ^+ (p * q) = 1)
    (adv : indcpa_adversary (R:=R) AHE) :
  residuosity_accept (dcr_of_adversary g adv) unit_fdist
  = residuosity_accept (dcr_of_adversary_zero adv) unit_fdist.
Proof.
have pq_gt0 : (0 < p * q)%N := ltnW pq_gt1.
(* Both sides draw the state c the same way; compare the inner laws at each
   fixed c. *)
rewrite !residuosity_acceptE /=; congr (Pr _ _); congr (_ >>= _).
apply/funext => c.
(* g ^+ (p q) = 1 makes g a unit, hence every power of g is a unit. *)
have Ug : g ^+ adv_plain c \is a GRing.unit.
  by rewrite unitrX // -(unitrX_pos _ pq_gt0) gn unitr1.
(* The key fact at this state's multiplier.  This step is not a pointwise
   probability computation in the ring: it treats multiplication by the fixed
   unit g ^+ (adv_plain c) as a permutation of the unit group.  fdistmap_comp
   and fdistmap_bij_uniform prove that this permutation leaves the uniform
   law unchanged, the result is pushed back to the ring along val, and so the
   two acceptance probabilities are equal. *)
exact: unit_fdistmap_translateE 'Z_((p * q) * (p * q)) card_renc_paillier
  (adv_decide c) (FinRing.unit _ Ug).
Qed.

(* The reduction, priced.  An adversary whose two residuosity reductions the
   residuosity class admits has IND-CPA advantage at most 2 eps_DCR at every
   key built from a private key, one eps_DCR per hop of the two-step hybrid:
   the first hop moves the real experiment from the residue challenge to the
   unit challenge, the second moves the zero experiment back, and the middle
   equality between them is unit_accept_dcrE.  This is Katz and Lindell 2015
   Theorem 13.13, read at any generator whose order divides p q. *)
Lemma paillier_dcr_epsilon_le (A : dcr_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) AHE) :
  residuosity_admissible A (dcr_of_adversary (priv_gen dk) adv) ->
  residuosity_admissible A (dcr_of_adversary_zero adv) ->
  indcpa_epsilon (R:=R) card_renc_paillier rand_of_renc_paillier
    (pub_of_priv dk) adv
  <= 2 * dcr_epsilon A.
Proof.
move=> Hg Hz.
rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE.
rewrite !enc_fdist_paillierE /= real_accept_dcrE zero_accept_dcrE.
rewrite /dcr_epsilon mulr_natl mulr2n.
apply: le_trans (ler_distD (residuosity_accept
  (dcr_of_adversary (priv_gen dk) adv) unit_fdist) _ _) _.
apply: lerD; first exact: residuosity_admissible_epsilon_le _ _ Hg.
rewrite (unit_accept_dcrE (priv_gen_order dk) adv) distrC.
exact: residuosity_admissible_epsilon_le _ _ Hz.
Qed.

(* The IND-CPA class a residuosity assumption induces: the adversaries whose
   multiplying reduction is classified at every generator and whose plain
   reduction is classified.  The quantification is over every ring element
   because the bound above is read at an arbitrary private key, whose
   generator the class leaves free. *)
Definition paillier_dcr_admissible (A : dcr_assumption)
    (adv : indcpa_adversary (R:=R) AHE) : bool :=
  [forall g, residuosity_admissible A (dcr_of_adversary g adv)]
  && residuosity_admissible A (dcr_of_adversary_zero adv).

(* The same 2 eps_DCR bound with the two premises read off that one Boolean,
   which is the shape the assumption record's proof field takes.
   Naming: paillier_dcr_admissible_epsilon_le mirrors the field it
   discharges, indcpa_admissible_epsilon_le of indcpa_game.v, with the
   scheme and the problem in front. *)
Lemma paillier_dcr_admissible_epsilon_le (A : dcr_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) AHE) :
  paillier_dcr_admissible A adv ->
  indcpa_epsilon (R:=R) card_renc_paillier rand_of_renc_paillier
    (pub_of_priv dk) adv
  <= 2 * dcr_epsilon A.
Proof.
by move=> /andP[/forallP Hg Hz]; apply: paillier_dcr_epsilon_le (Hg _) Hz.
Qed.

(* The IND-CPA assumption of Paillier at this modulus, derived rather than
   assumed: the class induced by A, the epsilon 2 eps_DCR the two hops cost,
   and the lemma above in place of a hypothesis.  Every Paillier bound the
   DSDP files read off is read at a record of this form, so the computational
   premise those bounds carry is decisional composite residuosity. *)
Definition paillier_indcpa_assumption (A : dcr_assumption) :
    indcpa_epsilon_assumption (R:=R) card_renc_paillier
      rand_of_renc_paillier :=
  {| indcpa_admissible := paillier_dcr_admissible A ;
     indcpa_assumption_epsilon := 2 * dcr_epsilon A ;
     indcpa_admissible_epsilon_le := @paillier_dcr_admissible_epsilon_le A |}.

(* At the zero-epsilon residuosity witness the induced class admits every
   adversary whose decision ignores the ciphertext: such an adversary ignores
   the challenge under both reductions, multiplied or not.  So the derived
   record has an inhabited class at an epsilon that is proved rather than
   assumed, and a statement restricted to the derived class is not empty for
   want of an adversary to read it at.
   Naming: paillier_dcr_admissible_cipher_constant composes the two class
   names it relates, paillier_dcr_admissible here and
   adv_decide_cipher_constant of indcpa_game.v. *)
Lemma paillier_dcr_admissible_cipher_constant
    (adv : indcpa_adversary (R:=R) AHE) :
  adv_decide_cipher_constant adv ->
  paillier_dcr_admissible
    (decide_constant_assumption 'Z_((p * q) * (p * q)) (p * q)
       card_renc_paillier) adv.
Proof.
move=> /'forall_'forall_forallP Hc; apply/andP; split; last first.
  by apply/'forall_'forall_forallP => c x y; exact: Hc.
by apply/'forall_'forall_'forall_forallP => g c x y; exact: Hc.
Qed.

(* What the derived assumption says of Paillier, with the experiment written
   out.  For every private key and every adversary the induced class admits,
   the probability that the adversary accepts an encryption of its chosen
   plaintext under the key's generator and the probability that it accepts an
   encryption of zero differ by at most 2 eps_DCR.  The key ranges over every
   PaillierPrivKey record, so the bound is universal over keys rather than
   averaged over a key-generation law, and the adversary holds the public key
   alone. *)
Lemma paillier_indcpa_epsilon_le (A : dcr_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) AHE) :
  paillier_dcr_admissible A adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_paillier))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) 0)
              (fdist_uniform card_renc_paillier))) [set true] |
  <= 2 * dcr_epsilon A.
Proof.
move/(paillier_dcr_admissible_epsilon_le dk).
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
  !enc_fdist_paillierE.
Qed.

End paillier_indcpa_scheme.

Section paillier_indcpa_scheme_sequence.
Context {R : realType}.
Variables p q : nat -> nat.
Hypothesis p_gt1 : forall k, (1 < p k)%N.
Hypothesis q_gt1 : forall k, (1 < q k)%N.

(* The Paillier IND-CPA scheme at parameter k is the fixed scheme above taken
   at p k and q k: the packaging Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)),
   the coin type renc_paillier (p k) (q k), the pinned cardinality
   card_renc_paillier (p k) (q k), and the coin map
   rand_of_renc_paillier (p_gt1 k) (q_gt1 k), which is
   paillier_indcpa_scheme (p_gt1 k) (q_gt1 k).  A sequence of decisional
   composite residuosity records at those moduli is the per-k form of the
   single computational premise the scheme carries; the IND-CPA assumption at
   each k is derived from it by paillier_indcpa_assumption. *)
Variable D : forall k, dcr_assumption (R:=R) (p k) (q k).

(* The inverse modulus sequence 1/(p k * q k), the form a growth condition on
   the moduli is stated in. *)
Definition f_pq k : R := (((p k * q k)%N)%:R : R)^-1.

(* The inverse plaintext-cardinality sequence at Paillier: the
   information-theoretic summand of every guessing bound read off along the
   sequence. *)
Definition f_size_paillier k : R :=
  (#|plain (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))|%:R : R)^-1.

(* The assumed residuosity-advantage sequence: the epsilon D k assumes at
   each k, the asymptotic form of decisional composite residuosity. *)
Definition f_dcr_paillier k : R := dcr_epsilon (D k).

(* The derived IND-CPA advantage sequence: twice f_dcr_paillier, the two hops
   of the reduction charged once each at the key of parameter k. *)
Definition f_adv_paillier k : R :=
  indcpa_assumption_epsilon
    (paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (D k)).

(* The bound sequence 1/(p k * q k) + 2 * eps k, at the derived IND-CPA
   advantage eps k: the shape of the class-conditional guessing bound at each
   k, before any protocol is named.  In residuosity currency it reads
   1/(p k * q k) + 4 eps_DCR, the factor two here being the two keys a trace
   bound spends an IND-CPA epsilon at, and the factor two inside
   f_adv_paillier being the two hops of the reduction at one key. *)
Definition f_bound_paillier k : R := f_pq k + 2 * f_adv_paillier k.

(* The moduli outgrow every polynomial in k.  At Paillier the modulus is the
   plaintext cardinality, so this is the growth of the plaintext space, and
   negligible is the asymptotic acceptance criterion for the guessing
   residue an inverse plaintext cardinality concedes. *)
Hypothesis f_pq_negligible : negligible_fun f_pq.

(* The residuosity advantage the assumption sequence assumes is negligible:
   the asymptotic form of decisional composite residuosity along the moduli
   p k q k. *)
Hypothesis f_dcr_paillier_negligible : negligible_fun f_dcr_paillier.

(* The inverse plaintext cardinality along the sequence is negligible: the
   plaintext space at k is Z/(p k * q k)Z, so modulus growth is plaintext
   growth.  This is the scheme-side summand of every guessing bound of the
   shape 1/#|plain| + 2 * eps read off along the sequence. *)
Lemma f_size_paillier_negligible : negligible_fun f_size_paillier.
Proof.
rewrite /f_size_paillier.
under eq_fun => k do rewrite (card_plain_paillier_pq (p_gt1 k) (q_gt1 k)).
exact: f_pq_negligible.
Qed.

(* The derived IND-CPA advantage along the sequence is negligible: it is
   twice the residuosity advantage at each k, one factor per hop of the
   reduction, and doubling preserves negligibility.  This is where the
   asymptotic content of decisional composite residuosity becomes the
   asymptotic content of Paillier IND-CPA. *)
Lemma f_adv_paillier_negligible : negligible_fun f_adv_paillier.
Proof. exact: negligible_fun_double f_dcr_paillier_negligible. Qed.

(* The bound sequence is negligible.  This is the whole asymptotic content of
   the Paillier IND-CPA scheme sequence, stated before any protocol is
   named: a bound of this shape at each k, whatever protocol produced it,
   vanishes in the security parameter. *)
Lemma f_bound_paillier_negligible : negligible_fun f_bound_paillier.
Proof.
exact: negligible_fun_predictor_bound f_pq_negligible
         f_adv_paillier_negligible.
Qed.

End paillier_indcpa_scheme_sequence.
