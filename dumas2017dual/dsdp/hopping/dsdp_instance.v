From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import negligible indcpa_game indcpa_scheme_sequence.

(**md**************************************************************************)
(* # The data of a DSDP instance and of a sequence of instances               *)
(*                                                                            *)
(* One DSDP instance is an IND-CPA scheme together with the data the          *)
(* corrupted-Alice development runs on: Alice's four weights with Charlie's   *)
(* weight invertible, and the three private keys.  The six encryption coins   *)
(* of a run are not instance data: the programs draw them, and                *)
(* dsdp_enc_coins is the sample space they are drawn from.                    *)
(*                                                                            *)
(* The scheme enters as one field rather than as its four                     *)
(* data, so that an instance and the IND-CPA assumption made about it name    *)
(* the same scheme value, and in particular the same pinned coin-space        *)
(* cardinality.  The coercion inst_scheme is what lets a game-layer constant  *)
(* read an instance.                                                          *)
(*                                                                            *)
(* Two things stay outside the record.  The adversary and the two class       *)
(* premises restrict the reduction adversaries a predictor induces, so they   *)
(* speak about the adversary rather than about the execution.  The real field *)
(* stays outside as well: a sequence lives over one R, which only the         *)
(* assumption record and the probabilities mention.                           *)
(*                                                                            *)
(* A sequence indexes instances by the security parameter and makes the       *)
(* IND-CPA assumption at each of them.  Two summand sequences are read off    *)
(* it, f_size the inverse plaintext cardinality and f_adv the advantage       *)
(* assumed at k, and dsdp_asymptotic holds the two negligibility facts about  *)
(* them.  Those two facts are the two terms of every trace bound along the    *)
(* sequence, the unconditional one and the assumption-conditional one, and    *)
(* they are a record of their own because only the statements that let the    *)
(* parameter grow spend them.                                                 *)
(*                                                                            *)
(* A sequence and its asymptotic content are built from one scheme sequence   *)
(* of computational_security/indcpa_scheme_sequence.v: the schemes, the       *)
(* assumptions and the private keys are read off that record, and the two     *)
(* negligibility facts come with it, so the DSDP side supplies the weights    *)
(* and the key seeds alone and assumes nothing further.                       *)
(*                                                                            *)
(* The file carries data alone.  It sits below the corrupted-Alice hopping    *)
(* and trace files, which state their bounds over an instance of it.          *)
(*                                                                            *)
(* ```                                                                        *)
(*                 pkey_of_dk == the public key of each party, read off its   *)
(*                               private key                                  *)
(*            dsdp_enc_coins == the six encryption coins one run consumes,    *)
(*                               packed as one record                         *)
(*       card_dsdp_enc_coins == that record type is nonempty                  *)
(*       dsdp_enc_coins_fdist == the uniform law on the coin record           *)
(*              dsdp_instance == one instance of the sequence, the section    *)
(*                               variables of the corrupted-Alice trace       *)
(*                               development packed as one record             *)
(*                inst_scheme == the IND-CPA scheme an instance runs on, a    *)
(*                               coercion                                     *)
(*         inst_pkey_of_party == the public-key table of its three private    *)
(*                               keys                                         *)
(*     dsdp_instance_sequence == a sequence of instances indexed by the       *)
(*                               security parameter, with the assumption      *)
(*                               made at each k                               *)
(*          sequence_instance == the instance at k                            *)
(*        sequence_assumption == the IND-CPA assumption made at k             *)
(*                     f_size == the inverse plaintext-cardinality sequence   *)
(*                      f_adv == the class-epsilon sequence                   *)
(*            dsdp_asymptotic == the two negligibility facts about a          *)
(*                               sequence, its asymptotic content             *)
(*            size_negligible == f_size is a negligible sequence, the         *)
(*                               unconditional term of every bound along      *)
(*                               the sequence                                 *)
(*             adv_negligible == f_adv is a negligible sequence, the          *)
(*                               assumption-conditional term of every         *)
(*                               bound along the sequence                     *)
(*            dsdp_alice_data == the four weight sequences, the invertibility *)
(*                               of the third, and the three key seeds        *)
(*           mk_dsdp_instance == the instance at k built from a scheme        *)
(*                               sequence and one dsdp_alice_data             *)
(*  mk_dsdp_instance_sequence == the sequence of those instances, its         *)
(*                               assumption at k the one the scheme           *)
(*                               sequence makes                               *)
(*         mk_dsdp_asymptotic == the two negligibility facts about that       *)
(*                               sequence, both read off the scheme sequence  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* The public key of each party, read off that party's private key.
   Decryption under it then holds by conversion, so no key hypothesis is
   carried. *)
Definition pkey_of_dk (AHE : AHEncType) (dk_a dk_b dk_c : priv_key AHE)
    (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

(* The six encryption coins one DSDP execution consumes.  Two are the coins of
   the ciphertexts Alice receives, two are her combine coins, and two are the
   second-hop coins. *)
Record dsdp_enc_coins (S : indcpa_scheme) := {
  (* the coin of Bob's encryption of his input to Alice *)
  coin_rb1 : scheme_renc S ;
  (* the coin of Charlie's encryption of his input to Alice *)
  coin_rc1 : scheme_renc S ;
  (* the coin of Alice's first combine *)
  coin_ra1 : scheme_renc S ;
  (* the coin of Alice's second combine *)
  coin_ra2 : scheme_renc S ;
  (* the coin of Bob's encryption to Charlie *)
  coin_rb2 : scheme_renc S ;
  (* the coin of Charlie's re-encryption to Alice *)
  coin_rc2 : scheme_renc S }.

Section dsdp_enc_coins_finite.
Variable S : indcpa_scheme.
Local Notation Renc := (scheme_renc S).

(* The six-fold product the coin record is in bijection with.  The finite
   structure lives on the product and the record borrows it. *)
Definition enc_coins_tupleT := (Renc * Renc * Renc * Renc * Renc * Renc)%type.

Definition tuple_of_enc_coins (c : dsdp_enc_coins S) : enc_coins_tupleT :=
  (coin_rb1 c, coin_rc1 c, coin_ra1 c, coin_ra2 c, coin_rb2 c, coin_rc2 c).

Definition enc_coins_of_tuple (t : enc_coins_tupleT) : dsdp_enc_coins S :=
  {| coin_rb1 := t.1.1.1.1.1 ; coin_rc1 := t.1.1.1.1.2 ;
     coin_ra1 := t.1.1.1.2 ; coin_ra2 := t.1.1.2 ;
     coin_rb2 := t.1.2 ; coin_rc2 := t.2 |}.

(* Reading the six coins off the record and rebuilding it loses nothing. *)
Lemma tuple_of_enc_coinsK : cancel tuple_of_enc_coins enc_coins_of_tuple.
Proof. by case. Qed.

HB.instance Definition _ :=
  Equality.copy (dsdp_enc_coins S) (can_type tuple_of_enc_coinsK).
HB.instance Definition _ :=
  Choice.copy (dsdp_enc_coins S) (can_type tuple_of_enc_coinsK).
HB.instance Definition _ :=
  Countable.copy (dsdp_enc_coins S) (can_type tuple_of_enc_coinsK).
HB.instance Definition _ : isFinite (dsdp_enc_coins S) :=
  CanIsFinite tuple_of_enc_coinsK.

(* The coin record is nonempty, in the successor form fdist_uniform takes. *)
Lemma card_dsdp_enc_coins :
  #|{: dsdp_enc_coins S}| = #|{: dsdp_enc_coins S}|.-1.+1.
Proof.
have /card_gt0P[x _] : (0 < #|Renc|)%N by rewrite scheme_card_renc.
rewrite prednK //; apply/card_gt0P.
by exists (Build_dsdp_enc_coins x x x x x x).
Qed.

(* The law of one execution's encryption randomness: the uniform product on
   the six coordinates.  Every coin is uniform, independent of the others, and
   fresh, which is what the IND-CPA reductions read off. *)
Definition dsdp_enc_coins_fdist (R : realType) : R.-fdist (dsdp_enc_coins S) :=
  fdist_uniform card_dsdp_enc_coins.

End dsdp_enc_coins_finite.


(* One DSDP execution as a record: the IND-CPA scheme, Alice's input and three
   weights, and three private keys.  The weight on Charlie's input is a
   unit. *)
Record dsdp_instance := {
  (* the IND-CPA scheme the execution runs on *)
  inst_scheme  :> indcpa_scheme ;
  (* Alice's own input *)
  inst_v1      : plain (scheme_AHE inst_scheme) ;
  (* Alice's weight on her own input *)
  inst_u1      : plain (scheme_AHE inst_scheme) ;
  (* Alice's weight on Bob's input *)
  inst_u2      : plain (scheme_AHE inst_scheme) ;
  (* Alice's weight on Charlie's input *)
  inst_u3      : plain (scheme_AHE inst_scheme) ;
  (* that weight is invertible, so the output determines Charlie's input *)
  inst_u3_unit : inst_u3 \is a GRing.unit ;
  (* Alice's private key *)
  inst_dk_a    : priv_key (scheme_AHE inst_scheme) ;
  (* Bob's private key *)
  inst_dk_b    : priv_key (scheme_AHE inst_scheme) ;
  (* Charlie's private key *)
  inst_dk_c    : priv_key (scheme_AHE inst_scheme) }.

(* The public-key table of an instance's three private keys.  It stays
   transparent, so the table read off a record and pkey_of_dk of its three
   keys are the same term. *)
Definition inst_pkey_of_party (I : dsdp_instance) :=
  pkey_of_dk (inst_dk_a I) (inst_dk_b I) (inst_dk_c I).

(* A sequence of DSDP instances indexed by the security parameter, with the
   IND-CPA assumption made at each k.  Consecutive instances are unrelated:
   each one is supplied on its own. *)
Record dsdp_instance_sequence (R : realType) := {
  (* the instance at the security parameter k *)
  sequence_instance : nat -> dsdp_instance ;
  (* the IND-CPA assumption made at the instance at k *)
  sequence_assumption : forall k,
    indcpa_epsilon_assumption (R:=R) (sequence_instance k) }.

(* The inverse plaintext cardinality at k along Q.  Every trace guessing bound
   along Q carries it as the leaked-output term. *)
Definition f_size {R : realType} (Q : dsdp_instance_sequence R) (k : nat)
    : R := (#|plain (scheme_AHE (sequence_instance Q k))|%:R : R)^-1.

(* The advantage the IND-CPA assumption at k assumes.  It is the summand
   every bound along Q carries once per hop of the ladder. *)
Definition f_adv {R : realType} (Q : dsdp_instance_sequence R) (k : nat)
    : R := indcpa_assumption_epsilon (sequence_assumption Q k).

(* The two negligibility facts about a sequence Q, one for each term of every
   bound read off along it.  They are a record of their own because a
   statement made at a single security parameter needs neither of them. *)
Record dsdp_asymptotic (R : realType) (Q : dsdp_instance_sequence R) := {
  (* the unconditional term: the inverse plaintext cardinality vanishes *)
  size_negligible : negligible_fun (f_size Q) ;
  (* the assumption-conditional term: the assumed advantage vanishes *)
  adv_negligible : negligible_fun (f_adv Q) }.

(* The corrupted-Alice data along a scheme sequence: Alice's input, her three
   weights with Charlie's invertible, and the three key seeds.  It is what the
   DSDP side supplies beside the scheme sequence, at every k at once. *)
Record dsdp_alice_data (R : realType) (Q : indcpa_scheme_sequence R) := {
  (* Alice's own input at k *)
  data_v1 : forall k, plain (scheme_AHE (scheme_at Q k)) ;
  (* Alice's weight on her own input at k *)
  data_u1 : forall k, plain (scheme_AHE (scheme_at Q k)) ;
  (* Alice's weight on Bob's input at k *)
  data_u2 : forall k, plain (scheme_AHE (scheme_at Q k)) ;
  (* Alice's weight on Charlie's input at k *)
  data_u3 : forall k, plain (scheme_AHE (scheme_at Q k)) ;
  (* that weight is invertible at every k *)
  data_u3_unit : forall k, data_u3 k \is a GRing.unit ;
  (* the seed Alice's key is generated from at k *)
  data_seed_a : forall k, keygen_seedT (scheme_keygen Q) k ;
  (* the seed Bob's key is generated from at k *)
  data_seed_b : forall k, keygen_seedT (scheme_keygen Q) k ;
  (* the seed Charlie's key is generated from at k *)
  data_seed_c : forall k, keygen_seedT (scheme_keygen Q) k }.

Section dsdp_of_scheme_sequence.
Context {R : realType}.
Variable Q : indcpa_scheme_sequence R.
Variable D : dsdp_alice_data Q.

(* The instance at k: the scheme the sequence carries there, the four weights,
   and the keys the three seeds generate. *)
Definition mk_dsdp_instance (k : nat) : dsdp_instance := {|
  inst_scheme  := scheme_at Q k ;
  inst_v1 := data_v1 D k ; inst_u1 := data_u1 D k ;
  inst_u2 := data_u2 D k ; inst_u3 := data_u3 D k ;
  inst_u3_unit := data_u3_unit D k ;
  inst_dk_a    := keygen_priv_key (scheme_keygen Q) k (data_seed_a D k) ;
  inst_dk_b    := keygen_priv_key (scheme_keygen Q) k (data_seed_b D k) ;
  inst_dk_c    := keygen_priv_key (scheme_keygen Q) k (data_seed_c D k) |}.

(* The sequence of those instances.  Its assumption at k is the one the scheme
   sequence makes, so instance and assumption name the same scheme value. *)
Definition mk_dsdp_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := mk_dsdp_instance ;
  sequence_assumption := scheme_assumption Q |}.

(* The asymptotic content of that sequence, both facts read off Q.  What a
   protocol file used to carry as two negligibility hypotheses beside its
   scheme variables is discharged here. *)
(* The record literal cannot solve the ascribed sequence index, so the
   constructor is applied to it. *)
Definition mk_dsdp_asymptotic : dsdp_asymptotic mk_dsdp_instance_sequence :=
  @Build_dsdp_asymptotic R mk_dsdp_instance_sequence
    (scheme_size_negligible Q) (scheme_adv_negligible Q).

End dsdp_of_scheme_sequence.

(* The scheme sequence stays an explicit argument: a call site names the
   sequence it reads its schemes off. *)
Arguments mk_dsdp_instance {R} Q D k.
Arguments mk_dsdp_instance_sequence {R} Q D.
Arguments mk_dsdp_asymptotic {R} Q D.
