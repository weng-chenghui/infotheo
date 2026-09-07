From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import negligible indcpa_game.

(**md**************************************************************************)
(* # The data of a DSDP instance and of a sequence of instances               *)
(*                                                                            *)
(* One DSDP instance is an IND-CPA scheme together with the data the          *)
(* corrupted-Alice development runs on: Alice's four weights with Charlie's   *)
(* weight invertible, the three private keys, and Bob's and Charlie's         *)
(* second-hop coins.  The scheme enters as one field rather than as its four  *)
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
(* The file carries data alone.  It sits below the corrupted-Alice hopping    *)
(* and trace files, which state their bounds over an instance of it.          *)
(*                                                                            *)
(* ```                                                                        *)
(*                 pkey_of_dk == the public key of each party, read off its   *)
(*                               private key                                  *)
(*              dsdp_instance == one instance of the sequence, the section    *)
(*                               variables of the corrupted-Alice trace       *)
(*                               development packed as one record             *)
(*                inst_scheme == the IND-CPA scheme an instance runs on, a    *)
(*                               coercion                                     *)
(*         inst_pkey_of_party == the public-key table of its three private    *)
(*                               keys                                         *)
(*              inst_with_rc2 == the instance with Charlie's second-hop coin  *)
(*                               replaced, the one field a statement that     *)
(*                               samples that coin leaves free                *)
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
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

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

(* One DSDP execution as a record: the IND-CPA scheme, Alice's input and three
   weights, three private keys, and two coins.  The weight on Charlie's input
   is a unit. *)
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
  inst_dk_c    : priv_key (scheme_AHE inst_scheme) ;
  (* the coin of Bob's encryption to Charlie *)
  inst_rb2     : scheme_renc inst_scheme ;
  (* the coin of Charlie's encryption to Alice *)
  inst_rc2     : scheme_renc inst_scheme }.

(* The public-key table of an instance's three private keys.  It stays
   transparent, so the table read off a record and pkey_of_dk of its three
   keys are the same term. *)
Definition inst_pkey_of_party (I : dsdp_instance) :=
  pkey_of_dk (inst_dk_a I) (inst_dk_b I) (inst_dk_c I).

(* The instance with the coin of Charlie's encryption replaced.  Sampling that
   coin makes a statement speak about the protocol rather than one
   execution. *)
Definition inst_with_rc2 (I : dsdp_instance) (w : scheme_renc I)
    : dsdp_instance :=
  {| inst_scheme := inst_scheme I ;
     inst_v1 := inst_v1 I ; inst_u1 := inst_u1 I ;
     inst_u2 := inst_u2 I ; inst_u3 := inst_u3 I ;
     inst_u3_unit := inst_u3_unit I ;
     inst_dk_a := inst_dk_a I ; inst_dk_b := inst_dk_b I ;
     inst_dk_c := inst_dk_c I ;
     inst_rb2 := inst_rb2 I ; inst_rc2 := w |}.

(* The instance stays an explicit argument: a call site names the instance it
   replaces the coin of, and the coin alone would leave it implicit. *)
Arguments inst_with_rc2 : clear implicits.

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
