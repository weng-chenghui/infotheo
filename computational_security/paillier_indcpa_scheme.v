From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba extra_algebra.
Require Import homomorphic_encryption residuosity_game.
Require Import paillier_enc paillier_ahe paillier_fdist_instance.
Require Import negligible indcpa_game indcpa_scheme_sequence epshop.

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
(* the DSDP files read off at Paillier, and the Paillier section of           *)
(* dsdp_alice_main.v is where those bounds are read off.                      *)
(*                                                                            *)
(* At this scheme the coin index type is the scheme's own randomness, the     *)
(* finite unit group of Z/(pq)^2 Z, and the coin map is the identity.  The    *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* The modulus bound pq_gt1 comes from extra_algebra.v, so the exported       *)
(* statements below and a downstream file restating them name one proof       *)
(* term.  Two proofs of the card_renc_paillier equation would likewise give   *)
(* bounds that compose only through a rewrite.                                *)
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
(* The loss is 2 eps_DCR at each key, one DCR call per hop of a two-step      *)
(* hybrid: the first hop moves the real experiment from the residue           *)
(* challenge to the unit challenge, the second moves the zero experiment      *)
(* back.  Between them the multiplier erases the plaintext, so the middle     *)
(* step is an identity and loses nothing.                                     *)
(*                                                                            *)
(* The two hops and the identity between them are written in the epsHop       *)
(* language of computational_security/epshop.v: paillier_chain starts at the  *)
(* real experiment, hops to the unit challenge, crosses the middle identity   *)
(* at no loss, and hops back to the zero experiment.  Its loss is the list    *)
(* of the two labels the bound rests on, one per residuosity call, and        *)
(* paillier_claim, the dictionary written on the program's delimiter, fixes   *)
(* for each label the two experiments its call moves between and the epsilon  *)
(* it assumes.  The chain returns twice the residuosity epsilon as its        *)
(* bound, which is the number in paillier_dcr_epsilon_le.  The two class      *)
(* memberships are variables of the section the chain sits in, so             *)
(* paillier_dcr_epsilon_le assumes exactly what building the chain spends.    *)
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
(* security parameter k, and the record paillier_sequence packs the whole     *)
(* sequence as one object.  The parameter is a key length there: the modulus  *)
(* at k has at least k bits, from which the negligibility of the inverse      *)
(* plaintext cardinality is derived rather than assumed, and the assumed      *)
(* residuosity advantages fall below every inverse polynomial.                *)
(*                                                                            *)
(* ```                                                                        *)
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
(*           dcr_epsilon dcr == the advantage that record assumes, the        *)
(*                              epsilon every Paillier bound is a multiple of *)
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
(*            paillier_label == the two labels of the reduction, dcr_g for    *)
(*                              the hop that runs the multiplying reduction   *)
(*                              and dcr_0 for the hop that runs the plain one *)
(* paillier_claim dcr dk adv == what each label claims: the two acceptance    *)
(*                              probabilities its residuosity call moves      *)
(*                              between, and the epsilon it assumes           *)
(*            dcr_totalE dcr == the closed form of the two-call loss, twice   *)
(*                              the residuosity epsilon                       *)
(* paillier_chain admissible_g admissible_0 ==                                *)
(*                              the two hops and the identity between them    *)
(*                              as one chain over acceptance probabilities,   *)
(*                              at the two class memberships it spends,       *)
(*                              returning twice the residuosity epsilon as    *)
(*                              its bound                                     *)
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
(*        f_dcr_paillier dcr == the residuosity-advantage sequence a          *)
(*                              sequence of residuosity records assumes       *)
(*         paillier_sequence == the moduli at each k, their bounds, the       *)
(*                              residuosity record and the modulus bit        *)
(*                              length there, the asymptotic form of that     *)
(*                              assumption, and the key material, as one      *)
(*                              record                                        *)
(*                    f_pq P == the inverse modulus sequence 1/(p k * q k)    *)
(*         f_size_paillier P == the inverse plaintext-cardinality sequence    *)
(*                              at Paillier                                   *)
(*          f_adv_paillier P == the derived IND-CPA advantage sequence,       *)
(*                              twice f_dcr_paillier                          *)
(* f_size_paillier_negligible ==                                              *)
(*                             the k-bit modulus makes f_size_paillier        *)
(*                             negligible                                     *)
(* f_adv_paillier_negligible ==                                               *)
(*                             f_adv_paillier is negligible when              *)
(*                             f_dcr_paillier is                              *)
(*  paillier_scheme_sequence == the Paillier reading of                       *)
(*                              indcpa_scheme_sequence, every field read off  *)
(*                              a paillier_sequence                           *)
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

Local Notation AHE := (Paillier_AHEnc (pq_gt1 p_gt1 q_gt1)).

(* The coin index type here: the unit group of Z/(pq)^2 Z, the scheme's own
   randomness carrier.  Coins and randomness are separate in the abstract
   development, and at a concrete scheme they coincide. *)
Definition renc_paillier : finType := {unit 'Z_((p * q) * (p * q))}.

(* The coin map here is the identity.  The coin index type above is
   definitionally the scheme's randomness, so a coin is already that
   randomness. *)
Definition rand_of_renc_paillier : renc_paillier -> rand AHE := idfun.

(* The coin space is nonempty, in the successor form fdist_uniform takes.
   Every statement below is read at this one proof term, since a second proof
   is not convertible. *)
Lemma card_renc_paillier : #|renc_paillier| = #|renc_paillier|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The Paillier scheme as one indcpa_scheme: the packaging at modulus p q,
   its coin type, cardinality, and coin map.  The DSDP files instantiate the
   game here, so every Paillier bound is read at this record. *)
Definition paillier_indcpa_scheme : indcpa_scheme :=
  {| scheme_AHE := AHE ; scheme_renc := renc_paillier ;
     scheme_card_renc := card_renc_paillier ;
     scheme_rand_of_renc := rand_of_renc_paillier |}.

(* The IND-CPA challenger at this packaging is the Paillier encryption of
   paillier_enc.v under uniform unit-group randomness.  Every advantage below
   is measured against this law, c = g^m * u^n mod (pq)^2 with u uniform. *)
Lemma enc_fdist_paillierE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) (S:=paillier_indcpa_scheme) pk v
  = fdistmap (paillier_enc (pub_gen pk) v) (fdist_uniform card_renc_paillier).
Proof. by []. Qed.

(* The two challenge laws of the residuosity problem here: a uniform unit of
   Z/(pq)^2 Z, and its (p q)-th power.  The second is the law of a Paillier
   encryption of zero. *)
Local Notation unit_fdist :=
  (unit_fdist (R:=R) 'Z_((p * q) * (p * q)) card_renc_paillier).
Local Notation residue_fdist :=
  (residue_fdist (R:=R) 'Z_((p * q) * (p * q)) (p * q) card_renc_paillier).

(* Decisional composite residuosity at modulus p q, Paillier 1999
   Conjecture 1: a class of distinguishers and an epsilon.  Every classified
   distinguisher tells a uniform unit of Z/(pq)^2 Z from a (p q)-th power,
   with advantage at most epsilon. *)
Definition dcr_assumption : Type :=
  residuosity_assumption (R:=R) 'Z_((p * q) * (p * q)) (p * q)
    card_renc_paillier.

(* The advantage a decisional composite residuosity record assumes of its
   classified distinguishers.  Every Paillier bound below is a multiple of it:
   twice it at one key, four times at two. *)
Definition dcr_epsilon (dcr : dcr_assumption) : R :=
  residuosity_assumption_epsilon dcr.

(* The first reduction: the adversary run on the residuosity challenge times
   g to its own plaintext.  At the residue challenge it runs the real
   experiment, at the unit challenge the multiplier erases the plaintext. *)
Definition dcr_of_adversary (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
    residuosity_distinguisher (R:=R) 'Z_((p * q) * (p * q)) :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c (g ^+ adv_plain c * x) |}.

(* The second reduction: the same adversary run on the residuosity challenge
   unchanged.  At the residue challenge the challenge is an encryption of
   zero, so this distinguisher runs the zero experiment. *)
Definition dcr_of_adversary_zero
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
    residuosity_distinguisher (R:=R) 'Z_((p * q) * (p * q)) :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c x |}.

(* An encryption of m under g is g^m times a (p q)-th power of a uniform
   unit.  The real experiment is therefore the multiplying reduction at the
   residue challenge, where the chain opens. *)
Lemma real_accept_dcrE (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (paillier_enc g (adv_plain c))
           (fdist_uniform (R:=R) card_renc_paillier))) [set true]
  = residuosity_accept (dcr_of_adversary g adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _); congr (_ >>= _).
by apply/funext => c; rewrite !fdistmap_comp.
Qed.

(* An encryption of zero is the (p q)-th power alone, the generator entering
   to the power zero.  The zero experiment is therefore the plain reduction at
   the residue challenge. *)
Lemma zero_accept_dcrE (g : 'Z_((p * q) * (p * q)))
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
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

(* At the unit challenge the two reductions accept with the same probability.
   Multiplication by the unit g ^+ (adv_plain c) fixes the uniform law, and
   this step adds no loss. *)
Lemma unit_accept_dcrE (g : 'Z_((p * q) * (p * q))) (gn : g ^+ (p * q) = 1)
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
  residuosity_accept (dcr_of_adversary g adv) unit_fdist
  = residuosity_accept (dcr_of_adversary_zero adv) unit_fdist.
Proof.
have pq_gt0 : (0 < p * q)%N := ltnW (pq_gt1 p_gt1 q_gt1).
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

(* The acceptance probability of a residuosity distinguisher, under the short
   name the chain below reads at. *)
Local Notation accept := (residuosity_accept (R:=R)).

(* The two labels, one per residuosity call: dcr_g for dcr_of_adversary at
   the key's generator, dcr_0 for dcr_of_adversary_zero.  A label names the
   reduction its hop invokes, so a finished loss lists the assumption
   calls. *)
Variant paillier_label := dcr_g | dcr_0.

(* What each label claims: the two acceptance probabilities its residuosity
   call moves between, and the epsilon that call assumes.  Each hop's loss,
   target and justification is checked against its label's claim, so no step
   invents a call. *)
Definition paillier_claim (dcr : dcr_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme)
    (l : paillier_label) : claim R :=
  let D_g := dcr_of_adversary (priv_gen dk) adv in
  let D_0 := dcr_of_adversary_zero adv in
  match l with
  | dcr_g =>
      Claim (accept D_g residue_fdist) (accept D_g unit_fdist)
        (dcr_epsilon dcr)
  | dcr_0 =>
      Claim (accept D_0 unit_fdist) (accept D_0 residue_fdist)
        (dcr_epsilon dcr)
  end.

Local Open Scope epshop_scope.

(* The closed form of the loss the chain below accumulates: one residuosity
   epsilon per hop, twice the assumed epsilon.  The chain returns its bound by
   this identity, and every factor two in this file comes from here. *)
Lemma dcr_totalE (dcr : dcr_assumption) :
  dcr_epsilon dcr + dcr_epsilon dcr = 2 * dcr_epsilon dcr.
Proof. by rewrite mulr_natl mulr2n. Qed.

(* The two-step hybrid as one chain over acceptance probabilities.  It starts
   at the real experiment, which is the multiplying reduction at the residue
   challenge; hops to that reduction at the unit challenge, where the
   residuosity assumption bounds the move; crosses to the plain reduction at
   the unit challenge, where the multiplier erases the plaintext and the move
   is an identity; and hops to the plain reduction at the residue challenge,
   which is the zero experiment.  Its two endpoints are the acceptance
   probabilities the IND-CPA advantage compares, and its loss names the two
   residuosity calls that comparison spends.  The two class memberships are
   variables of the section, spent in the justification of the hop each one
   licenses, so a chain that exists has already spent them and leaves nothing
   to discharge. *)
Section paillier_chain.
Variable dcr : dcr_assumption.
Variable dk : priv_key AHE.
Variable adv : indcpa_adversary (R:=R) paillier_indcpa_scheme.
Hypothesis admissible_g :
  residuosity_admissible dcr (dcr_of_adversary (priv_gen dk) adv).
Hypothesis admissible_0 :
  residuosity_admissible dcr (dcr_of_adversary_zero adv).

(* The two reductions the chain moves between, under the short names its
   steps read at.  D_g multiplies at the key's generator, D_0 hands the
   challenge over unchanged. *)
Local Notation D_g := (dcr_of_adversary (priv_gen dk) adv).
Local Notation D_0 := (dcr_of_adversary_zero adv).
Local Notation eps := (dcr_epsilon dcr).

Definition paillier_chain :=
  \epsilon[ paillier_claim dcr dk adv ]{
            (* the real experiment *)
            start (accept D_g residue_fdist) ;
            (* the first residuosity call, through D_g *)
            hop dcr_g eps to (accept D_g unit_fdist)
              by residuosity_admissible_epsilon_le _ _ admissible_g ;
            (* the free step: at the unit challenge the multiplier erases the
               plaintext, Katz and Lindell 2015 Lemma 11.15 *)
            same to (accept D_0 unit_fdist)
              by unit_accept_dcrE (priv_gen_order dk) adv ;
            (* the second residuosity call, through D_0 run backwards, and
               the zero experiment *)
            hop dcr_0 eps to (accept D_0 residue_fdist)
              by residuosity_admissible_epsilon_leC _ _ admissible_0 ;;
            (* the gap between the two experiments, at the two calls it
               spent *)
            bound (2 * eps) by dcr_totalE dcr }.

(* An adversary whose two reductions the class admits has IND-CPA advantage
   at most 2 eps_DCR.  This is Katz and Lindell 2015 Theorem 13.13, one
   assumption-conditional eps_DCR per residuosity call. *)
Lemma paillier_dcr_epsilon_le :
  indcpa_epsilon (R:=R) (S:=paillier_indcpa_scheme)
    (pub_of_priv dk) adv
  <= 2 * dcr_epsilon dcr.
Proof.
rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE.
rewrite !enc_fdist_paillierE /= real_accept_dcrE zero_accept_dcrE.
exact: result_sound paillier_chain.
Qed.

End paillier_chain.

(* The IND-CPA class a residuosity assumption induces: both reductions of the
   adversary are classified, the multiplying one at every generator.  The
   quantification runs over every ring element because the class leaves the
   key's generator free. *)
Definition paillier_dcr_admissible (dcr : dcr_assumption)
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) : bool :=
  [forall g, residuosity_admissible dcr (dcr_of_adversary g adv)]
  && residuosity_admissible dcr (dcr_of_adversary_zero adv).

(* The same 2 eps_DCR bound with the two premises read off one Boolean.  It
   is the shape the assumption record's proof field takes. *)
Lemma paillier_dcr_admissible_epsilon_le (dcr : dcr_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
  paillier_dcr_admissible dcr adv ->
  indcpa_epsilon (R:=R) (S:=paillier_indcpa_scheme)
    (pub_of_priv dk) adv
  <= 2 * dcr_epsilon dcr.
Proof.
move=> /andP[/forallP admissible_g admissible_0].
exact: paillier_dcr_epsilon_le (admissible_g _) admissible_0.
Qed.

(* The IND-CPA assumption of Paillier, derived rather than assumed: the
   induced class, 2 eps_DCR, and the lemma above.  Every Paillier bound in the
   DSDP files carries decisional composite residuosity as its computational
   premise. *)
Definition paillier_indcpa_assumption (dcr : dcr_assumption) :
    indcpa_epsilon_assumption (R:=R) paillier_indcpa_scheme :=
  {| indcpa_admissible := paillier_dcr_admissible dcr ;
     indcpa_assumption_epsilon := 2 * dcr_epsilon dcr ;
     indcpa_admissible_epsilon_le := @paillier_dcr_admissible_epsilon_le dcr |}.

(* At the zero-epsilon residuosity witness the induced class admits every
   adversary whose decision ignores the ciphertext.  The class is inhabited at
   a proved epsilon, so a bound restricted to it has an adversary. *)
Lemma paillier_dcr_admissible_cipher_constant
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
  adv_decide_cipher_constant adv ->
  paillier_dcr_admissible
    (decide_constant_assumption 'Z_((p * q) * (p * q)) (p * q)
       card_renc_paillier) adv.
Proof.
move=> /'forall_'forall_forallP Hc; apply/andP; split; last first.
  by apply/'forall_'forall_forallP => c x y; exact: Hc.
by apply/'forall_'forall_'forall_forallP => g c x y; exact: Hc.
Qed.

(* For every key and every admitted adversary, the real and the zero
   acceptance probabilities differ by at most 2 eps_DCR.  The key ranges over
   every PaillierPrivKey record, so the bound is universal over keys rather
   than averaged. *)
Lemma paillier_indcpa_epsilon_le (dcr : dcr_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) paillier_indcpa_scheme) :
  paillier_dcr_admissible dcr adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_paillier))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (paillier_enc (priv_gen dk) 0)
              (fdist_uniform card_renc_paillier))) [set true] |
  <= 2 * dcr_epsilon dcr.
Proof.
move/(paillier_dcr_admissible_epsilon_le dk).
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
  !enc_fdist_paillierE.
Qed.

End paillier_indcpa_scheme.

Section paillier_dcr_advantage.
Context {R : realType}.

(* The advantage a sequence of residuosity records assumes at k.  It reads a
   sequence of records, so that the record below can state the asymptotic form
   of its own assumption. *)
Definition f_dcr_paillier (p q : nat -> nat)
    (dcr : forall k, dcr_assumption (R:=R) (p k) (q k)) (k : nat) : R :=
  dcr_epsilon (dcr k).

End paillier_dcr_advantage.

(* A Paillier scheme sequence: the moduli, their bounds, the residuosity
   record, the modulus bit length, and the key material.  The parameter is a
   key length by paillier_modulus_bits, from which the size term is
   derived. *)
Record paillier_sequence (R : realType) := {
  (* the first factor of the modulus at k *)
  paillier_p : nat -> nat ;
  (* the second factor of the modulus at k *)
  paillier_q : nat -> nat ;
  (* the first factor exceeds one, the bound the Paillier packaging takes *)
  paillier_p_gt1 : forall k, (1 < paillier_p k)%N ;
  (* the second factor exceeds one *)
  paillier_q_gt1 : forall k, (1 < paillier_q k)%N ;
  (* decisional composite residuosity at the modulus of parameter k *)
  paillier_dcr : forall k,
    dcr_assumption (R:=R) (paillier_p k) (paillier_q k) ;
  (* the modulus at k has at least k bits: k is the key length *)
  paillier_modulus_bits : forall k,
    (2 ^ k <= paillier_p k * paillier_q k)%N ;
  (* the assumed residuosity advantage falls below every inverse polynomial *)
  paillier_dcr_negligible : negligible_fun (f_dcr_paillier paillier_dcr) ;
  (* the seed spaces and private keys along the sequence *)
  paillier_keygen : keygen_sequence
    (fun k => Paillier_AHEnc (pq_gt1 (paillier_p_gt1 k) (paillier_q_gt1 k))) }.

Section paillier_indcpa_scheme_sequence.
Context {R : realType}.
Variable P : paillier_sequence R.

(* The two modulus bounds of P, under the short names the statements below
   read the Paillier packaging at. *)
Local Notation p_gt1 := (paillier_p_gt1 P).
Local Notation q_gt1 := (paillier_q_gt1 P).

(* The inverse modulus sequence 1/(p k * q k), the form a growth condition on
   the moduli is stated in. *)
Definition f_pq k : R := (((paillier_p P k * paillier_q P k)%N)%:R : R)^-1.

(* The inverse plaintext-cardinality sequence at Paillier: the
   information-theoretic summand of every guessing bound read off along the
   sequence. *)
Definition f_size_paillier k : R :=
  (#|plain (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))|%:R : R)^-1.

(* The derived IND-CPA advantage sequence: twice the residuosity advantage.
   The reduction makes one residuosity call per hop at the key of parameter
   k. *)
Definition f_adv_paillier k : R :=
  indcpa_assumption_epsilon
    (paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (paillier_dcr P k)).

(* The inverse plaintext cardinality along the sequence is negligible, derived
   from the modulus bit length.  The plaintext space at k is Z/(p k * q k)Z,
   so a k-bit modulus is a k-bit plaintext space. *)
Lemma f_size_paillier_negligible : negligible_fun f_size_paillier.
Proof.
rewrite /f_size_paillier.
under eq_fun => k do rewrite (card_plain_paillier_pq (p_gt1 k) (q_gt1 k)).
exact: (negligible_fun_inv_ge_exp2 (paillier_modulus_bits P)).
Qed.

(* The derived IND-CPA advantage along the sequence is negligible, being twice
   a negligible residuosity advantage.  The asymptotic content of decisional
   composite residuosity becomes that of Paillier IND-CPA. *)
Lemma f_adv_paillier_negligible : negligible_fun f_adv_paillier.
Proof. exact: negligible_fun_double (paillier_dcr_negligible P). Qed.

(* The Paillier reading of indcpa_scheme_sequence: the scheme at k, the
   assumption derived from residuosity, the key material, and both
   negligibility facts.  Nothing is assumed here beyond what P carries. *)
Definition paillier_scheme_sequence : indcpa_scheme_sequence R := {|
  scheme_at := fun k => paillier_indcpa_scheme (p_gt1 k) (q_gt1 k) ;
  scheme_assumption := fun k =>
    paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (paillier_dcr P k) ;
  scheme_keygen := paillier_keygen P ;
  scheme_size_negligible := f_size_paillier_negligible ;
  scheme_adv_negligible := f_adv_paillier_negligible |}.

End paillier_indcpa_scheme_sequence.
