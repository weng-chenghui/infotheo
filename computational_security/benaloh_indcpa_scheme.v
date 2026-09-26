From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption residuosity_game.
Require Import benaloh_enc benaloh_ahe.
Require Import negligible indcpa_game indcpa_scheme_sequence epshop.

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
(* every computational bound the DSDP files read off at Benaloh, and the      *)
(* Benaloh section of dsdp_alice_main.v is where those bounds are read off.   *)
(*                                                                            *)
(* At this scheme the coin index type is the scheme's own randomness, the     *)
(* finite unit group of Z/nZ, and the coin map is the identity.  The          *)
(* abstract development keeps the two apart because he_types.v gives rand as  *)
(* a bare Type, over which no distribution is well-typed.                     *)
(*                                                                            *)
(* The additively homomorphic mixin is built at r > 1, which is why r_gt1     *)
(* enters the packaging Benaloh_AHEnc.  Bounds stated at two proofs of the    *)
(* card_renc_benaloh equation would compose only through a rewrite.           *)
(* benaloh_residuosity_admissible_cipher_constant inhabits the derived class  *)
(* at epsilon zero and does not show it inhabited at a useful epsilon.        *)
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
(* The reduction below is written on the tactic surface of                    *)
(* computational_security/epshop.v.  Its objects are the four acceptance      *)
(* probabilities the hybrid passes through, and the type of benaloh_script    *)
(* names the two-label list residuosity_y and residuosity_0, whose claims     *)
(* benaloh_claim fixes, each label carrying the r-th residuosity epsilon its  *)
(* call assumes.  The bound of benaloh_residuosity_epsilon_le is read off the *)
(* script through hop_script_total and residuosity_totalE, and its two        *)
(* hypotheses are the two class memberships the script is proved at, so the   *)
(* bound comes from the script rather than from a triangle inequality of its  *)
(* own.  The script differs from the Paillier script of                       *)
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
(* the security parameter k, and the record benaloh_sequence packs the whole  *)
(* sequence as one object.  It carries two bit lengths, which are separate    *)
(* here: the block size r k, the plaintext space Z/rZ, has at least k bits,   *)
(* and that is what the size term is derived from, while the modulus n k,     *)
(* which sizes the ciphertext space, has at least k bits as the key length.   *)
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
(*                            epsilon every Benaloh bound is a multiple of    *)
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
(*              benaloh_label == the two labels of the reduction,             *)
(*                               residuosity_y for the hop that carries the   *)
(*                               real arm to the unit law and residuosity_0   *)
(*                               for the hop that carries the zero arm back   *)
(* benaloh_claim residuosity dk adv ==                                        *)
(*                            what each label claims: the two acceptance      *)
(*                            probabilities its residuosity call moves        *)
(*                            between, and the epsilon it assumes             *)
(* residuosity_totalE residuosity ==                                          *)
(*                            the closed form of the two-call loss, twice     *)
(*                            the residuosity epsilon                         *)
(* benaloh_script admissible_y admissible_0 ==                                *)
(*                            the reduction as a script of two hops around    *)
(*                            one equality, from the real arm to the zero     *)
(*                            arm, spending residuosity_y and residuosity_0   *)
(*                            at the two class memberships                    *)
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
(* f_residuosity_benaloh residuosity ==                                       *)
(*                            the residuosity-advantage sequence a sequence   *)
(*                            of residuosity records assumes                  *)
(*          benaloh_sequence == the modulus and block size at each k, their   *)
(*                              bounds, the residuosity record there, the     *)
(*                              two bit lengths, the asymptotic form of that  *)
(*                              assumption, and the key material, as one      *)
(*                              record                                        *)
(*                      f_r B == the inverse block-size sequence 1/(r k)      *)
(*           f_size_benaloh B == the inverse plaintext-cardinality sequence   *)
(*                               at Benaloh                                   *)
(*            f_adv_benaloh B == the derived advantage sequence, twice        *)
(*                               f_residuosity_benaloh                        *)
(* f_size_benaloh_negligible ==                                               *)
(*                              the k-bit block size makes f_size_benaloh     *)
(*                              negligible                                    *)
(*   f_adv_benaloh_negligible == f_adv_benaloh is negligible when             *)
(*                               f_residuosity_benaloh is                     *)
(*   benaloh_scheme_sequence == the Benaloh reading of                        *)
(*                              indcpa_scheme_sequence, every field read off  *)
(*                              a benaloh_sequence                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import EpsHopTac.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section benaloh_indcpa_scheme.
Context {R : realType}.
Variables n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* The Benaloh AHEncType at modulus n and block size r, the additively
   homomorphic packaging of benaloh_ahe.v.  The condition n > 1 is weaker than
   the composite modulus security rests on, and nothing below reads it. *)
Definition Benaloh_AHEnc : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r) (@Benaloh_isEncDec n r)
      (@Benaloh_isAHEnc n r r_gt1)).

Local Notation AHE := Benaloh_AHEnc.

(* The coin index type here: the unit group of Z/nZ, the scheme's own
   randomness carrier.  Coins and randomness are separate in the abstract
   development, and at a concrete scheme they coincide. *)
Definition renc_benaloh : finType := {unit 'Z_n}.

(* The coin map here is the identity.  The coin index type above is
   definitionally the scheme's randomness, so a coin is already that
   randomness. *)
Definition rand_of_renc_benaloh : renc_benaloh -> rand AHE := idfun.

(* The coin space is nonempty, in the successor form fdist_uniform takes.
   Every statement below is read at this one proof term, since a second proof
   is not convertible. *)
Lemma card_renc_benaloh : #|renc_benaloh| = #|renc_benaloh|.-1.+1.
Proof. by rewrite prednK //; apply/card_gt0P; exists 1%g; rewrite inE. Qed.

(* The Benaloh scheme as one indcpa_scheme: the packaging at modulus n and
   block size r, plus its coin data.  The DSDP files instantiate the game
   here, so every Benaloh bound is read at this record. *)
Definition benaloh_indcpa_scheme : indcpa_scheme :=
  {| scheme_AHE := AHE ; scheme_renc := renc_benaloh ;
     scheme_card_renc := card_renc_benaloh ;
     scheme_rand_of_renc := rand_of_renc_benaloh |}.

(* The IND-CPA challenger at this packaging is the Benaloh encryption of
   benaloh_enc.v under uniform unit-group randomness.  Every advantage below
   is measured against this law, c = y^m * u^r mod n with u uniform. *)
Lemma enc_fdist_benalohE (pk : pub_key AHE) (v : plain AHE) :
  enc_fdist (R:=R) (S:=benaloh_indcpa_scheme) pk v
  = fdistmap (benaloh_enc (pub_gen pk) v) (fdist_uniform card_renc_benaloh).
Proof. by []. Qed.

(* The two challenge laws of the residuosity game here: a uniform unit of
   Z/nZ, and its r-th power.  The second is the law of a Benaloh encryption of
   zero, the first the law it moves to. *)
Local Notation unit_fdist := (unit_fdist (R:=R) 'Z_n card_renc_benaloh).
Local Notation residue_fdist :=
  (residue_fdist (R:=R) 'Z_n r card_renc_benaloh).

(* The r-th residuosity assumption at modulus n, Benaloh 1994: a class of
   distinguishers and an epsilon.  Every classified distinguisher tells an
   r-th residue of Z/nZ from a uniform unit, with advantage at most
   epsilon. *)
Definition benaloh_residuosity_assumption : Type :=
  residuosity_assumption (R:=R) 'Z_n r card_renc_benaloh.

(* The advantage an r-th residuosity record assumes of its classified
   distinguishers.  Every Benaloh bound below is a multiple of it: twice it at
   one key, four times at two. *)
Definition benaloh_residuosity_epsilon
    (residuosity : benaloh_residuosity_assumption) : R :=
  residuosity_assumption_epsilon residuosity.

(* The first reduction: the adversary run on the residuosity challenge times
   y ^+ m.  Under the residue law it runs the real arm, under the unit law the
   multiplier erases m. *)
Definition residuosity_of_adversary (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
    residuosity_distinguisher (R:=R) 'Z_n :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c (val y ^+ (adv_plain c) * x) |}.

(* The second reduction: the same adversary with its challenge passed through
   unchanged.  Under the residue law the challenge is already an encryption of
   zero, so it runs the zero arm. *)
Definition residuosity_of_adversary_zero
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
    residuosity_distinguisher (R:=R) 'Z_n :=
  {| state := adv_state adv ;
     state_fdist := adv_choose adv ;
     decide := fun c x => adv_decide c x |}.

(* An encryption of m under generator y is y ^+ m times the r-th power of a
   uniform unit.  The real arm is therefore the first reduction against the
   residue law, where the script opens. *)
Lemma real_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
  Pr (c <- adv_choose adv ;
      fdistmap (adv_decide c)
        (fdistmap (benaloh_enc y (adv_plain c))
           (fdist_uniform card_renc_benaloh))) [set true]
  = residuosity_accept (residuosity_of_adversary y adv) residue_fdist.
Proof.
rewrite residuosity_acceptE /residue_fdist /=; congr (Pr _ _).
by congr (_ >>= _); apply/funext => c; rewrite !fdistmap_comp.
Qed.

(* At plaintext zero an encryption is the r-th power of a uniform unit alone.
   The zero arm is therefore the second reduction against the residue law, at
   plaintext (0 : plain AHE). *)
Lemma zero_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
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

(* Under the unit law the two reductions accept alike, multiplication by val
   y ^+ (adv_plain c) fixing the uniform law.  That multiplier is a unit
   whatever y and m are, so the generator needs no order condition. *)
Lemma unit_accept_residuosityE (y : ring_units 'Z_n)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
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
   name the script below reads at. *)
Local Notation accept := (residuosity_accept (R:=R)).

(* The two labels, one per residuosity call: residuosity_y for the
   multiplying reduction, residuosity_0 for the plain one.  A label names the
   reduction its hop invokes, so a finished loss lists the assumption
   calls. *)
Variant benaloh_label := residuosity_y | residuosity_0.

(* What each label claims: the two acceptance probabilities its residuosity
   call moves between, and the epsilon that call assumes.  Each hop's loss,
   target and justification is checked against its label's claim, so no step
   invents a call. *)
Definition benaloh_claim (residuosity : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme)
    (l : benaloh_label) : claim R :=
  let D_y := residuosity_of_adversary (priv_gen dk) adv in
  let D_0 := residuosity_of_adversary_zero adv in
  match l with
  | residuosity_y =>
      Claim (accept D_y residue_fdist) (accept D_y unit_fdist)
        (benaloh_residuosity_epsilon residuosity)
  | residuosity_0 =>
      Claim (accept D_0 unit_fdist) (accept D_0 residue_fdist)
        (benaloh_residuosity_epsilon residuosity)
  end.

Local Open Scope epshop_scope.

(* The closed form of the loss the script below spends: one residuosity
   epsilon per hop, twice the assumed epsilon.  The bound is read through this
   identity, and every factor two in this file comes from here. *)
Lemma residuosity_totalE (residuosity : benaloh_residuosity_assumption) :
  benaloh_residuosity_epsilon residuosity
  + benaloh_residuosity_epsilon residuosity
  = 2 * benaloh_residuosity_epsilon residuosity.
Proof. by rewrite mulr_natl mulr2n. Qed.

(* The reduction as a script over acceptance probabilities.  It starts at the
   real arm, the multiplying reduction accepting under the residue law; one
   residuosity call moves that reduction to the unit law, where the generator
   power cancels; the middle equality replaces the multiplying reduction by
   the plain one at no loss; and a second call moves the plain reduction back
   to the residue law, where its acceptance is the zero arm.  The type of the
   script names the two assumptions the derived bound rests on, both variables
   of the section, spent in the justification of the hop each one licenses. *)
Section benaloh_script.
Variable residuosity : benaloh_residuosity_assumption.
Variable dk : priv_key AHE.
Variable adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme.
Hypothesis admissible_y :
  residuosity_admissible residuosity
    (residuosity_of_adversary (priv_gen dk) adv).
Hypothesis admissible_0 :
  residuosity_admissible residuosity (residuosity_of_adversary_zero adv).

(* The two reductions the script moves between, under the short names its
   steps read at.  D_y multiplies at the key's generator, D_0 passes the
   challenge through unchanged. *)
Local Notation D_y := (residuosity_of_adversary (priv_gen dk) adv).
Local Notation D_0 := (residuosity_of_adversary_zero adv).
(* The two-call hybrid as a script from the real arm to the zero arm,
   spending one residuosity call per hop.  Its type names the two calls the
   IND-CPA bound rests on. *)
Lemma benaloh_script :
  \hops[ benaloh_claim residuosity dk adv ]
    `| accept D_y residue_fdist - accept D_0 residue_fdist |
    <= [:: residuosity_y; residuosity_0].
Proof.
(* the first residuosity call, through D_y *)
hop residuosity_y to (accept D_y unit_fdist)
  by (residuosity_admissible_epsilon_le _ _ admissible_y).
(* the free step: under the unit law the multiplier erases the plaintext,
   Katz and Lindell 2015 Lemma 11.15 *)
same to (accept D_0 unit_fdist) by (unit_accept_residuosityE (priv_gen dk) adv).
(* the second residuosity call, through D_0 run backwards, and the zero arm *)
hop residuosity_0 to (accept D_0 residue_fdist)
  by (residuosity_admissible_epsilon_leC _ _ admissible_0).
stop.
Qed.

(* An adversary whose two reductions the class admits has IND-CPA advantage
   at most twice the residuosity epsilon.  Both terms are
   assumption-conditional, one residuosity call per arm, so the whole bound is
   computational. *)
Lemma benaloh_residuosity_epsilon_le :
  indcpa_epsilon (R:=R) (S:=benaloh_indcpa_scheme)
    (pub_of_priv dk) adv
  <= 2 * benaloh_residuosity_epsilon residuosity.
Proof.
rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE.
rewrite !enc_fdist_benalohE /= real_accept_residuosityE.
rewrite zero_accept_residuosityE -(residuosity_totalE residuosity).
exact: hop_script_total benaloh_script.
Qed.

End benaloh_script.

(* The IND-CPA class the derived assumption carries: the adversaries whose two
   residuosity reductions the residuosity class admits.  The first quantifier
   runs over the whole unit group of Z/nZ because the class is fixed before
   any key. *)
Definition benaloh_residuosity_admissible
    (residuosity : benaloh_residuosity_assumption)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) : bool :=
  [forall y : ring_units 'Z_n,
     residuosity_admissible residuosity (residuosity_of_adversary y adv)]
  && residuosity_admissible residuosity (residuosity_of_adversary_zero adv).

(* The same bound under that Boolean class, the shape the third field of an
   IND-CPA assumption record takes. *)
Lemma benaloh_residuosity_admissible_epsilon_le
    (residuosity : benaloh_residuosity_assumption) (dk : priv_key AHE)
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
  benaloh_residuosity_admissible residuosity adv ->
  indcpa_epsilon (R:=R) (S:=benaloh_indcpa_scheme)
    (pub_of_priv dk) adv
  <= 2 * benaloh_residuosity_epsilon residuosity.
Proof.
case/andP => /forallP admissible_y admissible_0.
exact: benaloh_residuosity_epsilon_le (admissible_y _) admissible_0.
Qed.

(* The IND-CPA assumption of Benaloh, derived rather than assumed: the class
   above, twice the residuosity epsilon, and the lemma.  Every Benaloh bound
   in the DSDP files is a multiple of the r-th residuosity epsilon. *)
Definition benaloh_indcpa_assumption
    (residuosity : benaloh_residuosity_assumption) :
    indcpa_epsilon_assumption (R:=R) benaloh_indcpa_scheme :=
  {| indcpa_admissible := benaloh_residuosity_admissible residuosity ;
     indcpa_assumption_epsilon := 2 * benaloh_residuosity_epsilon residuosity ;
     indcpa_admissible_epsilon_le :=
       @benaloh_residuosity_admissible_epsilon_le residuosity |}.

(* At the zero-epsilon residuosity assumption the derived class admits every
   adversary whose verdict ignores the ciphertext.  The class is inhabited at
   a proved epsilon zero, so a bound restricted to it has an adversary. *)
Lemma benaloh_residuosity_admissible_cipher_constant
    (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
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

(* At every key, an admitted adversary's real and zero acceptance
   probabilities differ by at most twice the residuosity epsilon.  The key
   ranges over every BenalohPrivKey record, so the bound is universal over
   keys rather than averaged. *)
Lemma benaloh_indcpa_epsilon_le (residuosity : benaloh_residuosity_assumption)
    (dk : priv_key AHE) (adv : indcpa_adversary (R:=R) benaloh_indcpa_scheme) :
  benaloh_residuosity_admissible residuosity adv ->
  `| Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (adv_plain c))
              (fdist_uniform card_renc_benaloh))) [set true]
   - Pr (c <- adv_choose adv ;
         fdistmap (adv_decide c)
           (fdistmap (benaloh_enc (priv_gen dk) (0 : plain AHE))
              (fdist_uniform card_renc_benaloh))) [set true] |
  <= 2 * benaloh_residuosity_epsilon residuosity.
Proof.
move=> Hadm; have := benaloh_residuosity_admissible_epsilon_le dk Hadm.
by rewrite /indcpa_epsilon indcpa_success_realE indcpa_success_zeroE
           !enc_fdist_benalohE.
Qed.

End benaloh_indcpa_scheme.

(* The advantage a sequence of r-th residuosity records assumes at k.  It
   reads a sequence of records, so that the record below can state the
   asymptotic form of its own assumption. *)
Definition f_residuosity_benaloh {R : realType} {n r : nat -> nat}
    (residuosity : forall k, benaloh_residuosity_assumption (R:=R) (n k) (r k))
    (k : nat) : R :=
  benaloh_residuosity_epsilon (residuosity k).

(* A Benaloh scheme sequence: modulus and block size, their bounds, the
   residuosity record, two bit lengths, and key material.  The block size
   carries the size term and the modulus is the key length. *)
Record benaloh_sequence (R : realType) := {
  (* the modulus at k *)
  benaloh_n : nat -> nat ;
  (* the block size at k, the cardinality of the plaintext space *)
  benaloh_r : nat -> nat ;
  (* the modulus exceeds one *)
  benaloh_n_gt1 : forall k, (1 < benaloh_n k)%N ;
  (* the block size exceeds one, the bound the Benaloh packaging takes *)
  benaloh_r_gt1 : forall k, (1 < benaloh_r k)%N ;
  (* r-th residuosity at the modulus and block size of parameter k *)
  benaloh_residuosity : forall k,
    benaloh_residuosity_assumption (R:=R) (benaloh_n k) (benaloh_r k) ;
  (* the plaintext block at k has at least k bits, the growth the size term
     of every bound along the sequence needs *)
  benaloh_block_bits : forall k, (2 ^ k <= benaloh_r k)%N ;
  (* the modulus at k has at least k bits: k is the key length *)
  benaloh_modulus_bits : forall k, (2 ^ k <= benaloh_n k)%N ;
  (* the assumed residuosity advantage falls below every inverse polynomial *)
  benaloh_residuosity_negligible :
    negligible_fun (f_residuosity_benaloh benaloh_residuosity) ;
  (* the seed spaces and private keys along the sequence *)
  benaloh_keygen : keygen_sequence
    (fun k => Benaloh_AHEnc (benaloh_n k) (benaloh_r_gt1 k)) }.

Section benaloh_indcpa_scheme_sequence.
Context {R : realType}.
Variable B : benaloh_sequence R.

(* The block-size bound of B, under the short name the statements below read
   the Benaloh packaging at. *)
Local Notation r_gt1 := (benaloh_r_gt1 B).

(* The inverse block-size sequence 1/(r k), the form a growth condition on the
   block sizes is stated in. *)
Definition f_r k : R := ((benaloh_r B k)%:R : R)^-1.

(* The inverse plaintext-cardinality sequence at Benaloh: the
   information-theoretic summand of every guessing bound read off along the
   sequence. *)
Definition f_size_benaloh k : R :=
  (#|plain (Benaloh_AHEnc (benaloh_n B k) (r_gt1 k))|%:R : R)^-1.

(* The derived IND-CPA advantage sequence: twice the residuosity advantage at
   k.  The reduction spends two residuosity calls at one key. *)
Definition f_adv_benaloh k : R :=
  indcpa_assumption_epsilon
    (benaloh_indcpa_assumption (r_gt1 k) (benaloh_residuosity B k)).

(* The inverse plaintext cardinality along the sequence is negligible, derived
   from the block-size bit length.  The plaintext space at k is Z/(r k)Z, so a
   k-bit block is a k-bit plaintext space. *)
Lemma f_size_benaloh_negligible : negligible_fun f_size_benaloh.
Proof.
rewrite /f_size_benaloh.
under eq_fun => k do rewrite card_ord (Zp_cast (r_gt1 k)).
exact: negligible_fun_inv_ge_exp2 (benaloh_block_bits B).
Qed.

(* The derived IND-CPA advantage is negligible, twice a negligible function
   being negligible.  The residuosity hypothesis now implies what a sequence
   of IND-CPA assumptions had to take, at a factor two. *)
Lemma f_adv_benaloh_negligible : negligible_fun f_adv_benaloh.
Proof. exact: negligible_fun_double (benaloh_residuosity_negligible B). Qed.

(* The Benaloh reading of indcpa_scheme_sequence: the scheme at k, the
   assumption derived from residuosity, the key material, and both
   negligibility facts.  Nothing is assumed here beyond what B carries. *)
Definition benaloh_scheme_sequence : indcpa_scheme_sequence R := {|
  scheme_at := fun k => benaloh_indcpa_scheme (benaloh_n B k) (r_gt1 k) ;
  scheme_assumption := fun k =>
    benaloh_indcpa_assumption (r_gt1 k) (benaloh_residuosity B k) ;
  scheme_keygen := benaloh_keygen B ;
  scheme_size_negligible := f_size_benaloh_negligible ;
  scheme_adv_negligible := f_adv_benaloh_negligible |}.

End benaloh_indcpa_scheme_sequence.
