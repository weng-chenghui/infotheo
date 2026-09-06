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
(*          expnn_gt_monomial == (k+2)^(k+2) exceeds every monomial k^c past  *)
(*                               c                                            *)
(*   negligible_fun_inv_expnn == the inverse of (k+2)^(k+2) is negligible     *)
(* negligible_fun_inv_ge_expnn == a sequence dominating (k+2)^(k+2) has a     *)
(*                               negligible inverse                           *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* Every party's public key is the one associated with its private key, so
   dec_correct fires by conversion and no key hypothesis is needed. *)
Definition pkey_of_dk (AHE : AHEncType) (dk_a dk_b dk_c : priv_key AHE)
    (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

(* One instance of a security-parameter-indexed sequence of DSDP executions:
   an IND-CPA scheme, the four weights with Charlie's weight invertible, the
   three private keys, and the two hop coins.  These are exactly the section
   variables of the corrupted-Alice trace development
   (dsdp_alice_trace_link.v), so every concrete trace bound applies at a
   record unchanged.
   The scheme enters as one field rather than as its four data because an
   IND-CPA assumption is made about an indcpa_scheme: an instance and the
   assumption made about it then name the same scheme value, and in
   particular the same pinned coin-space cardinality.  It is a coercion, so
   the scheme projections scheme_AHE, scheme_renc, scheme_card_renc and
   scheme_rand_of_renc read an instance directly.
   Two things stay outside.  The adversary and the two class premises, which
   restrict the reduction adversaries a predictor induces and so speak about
   the adversary rather than about the execution.  And the real field: a
   sequence lives over one R, which only the assumption record and the
   probabilities mention. *)
Record dsdp_instance := {
  inst_scheme  :> indcpa_scheme ;
  inst_v1      : plain (scheme_AHE inst_scheme) ;
  inst_u1      : plain (scheme_AHE inst_scheme) ;
  inst_u2      : plain (scheme_AHE inst_scheme) ;
  inst_u3      : plain (scheme_AHE inst_scheme) ;
  inst_u3_unit : inst_u3 \is a GRing.unit ;
  inst_dk_a    : priv_key (scheme_AHE inst_scheme) ;
  inst_dk_b    : priv_key (scheme_AHE inst_scheme) ;
  inst_dk_c    : priv_key (scheme_AHE inst_scheme) ;
  inst_rb2     : scheme_renc inst_scheme ;
  inst_rc2     : scheme_renc inst_scheme }.

(* The public-key table the corrupted-Alice sections read off an instance's
   three private keys.  It stays a transparent Definition: the hop-level
   pkey_of_party of a record and the trace-level pkey_of_dk of its three keys
   are then the same term by delta alone. *)
Definition inst_pkey_of_party (I : dsdp_instance) :=
  pkey_of_dk (inst_dk_a I) (inst_dk_b I) (inst_dk_c I).

(* A sequence of DSDP instances indexed by the security parameter, with the
   IND-CPA assumption made at each k.
   The record fixes no relation between consecutive k: each instance is
   supplied on its own, and an asymptotic statement along the sequence reads
   its content off a dsdp_asymptotic value below rather than off a recurrence
   between the instances. *)
Record dsdp_instance_sequence (R : realType) := {
  sequence_instance : nat -> dsdp_instance ;
  sequence_assumption : forall k,
    indcpa_epsilon_assumption (R:=R) (scheme_card_renc (sequence_instance k))
      (@scheme_rand_of_renc (sequence_instance k)) }.

(* The inverse plaintext cardinality at k along Q.  It counts the DSDP
   solution fiber the leaked output confines Bob's input to, and it is the
   summand every trace guessing bound along Q carries for that output. *)
Definition f_size {R : realType} (Q : dsdp_instance_sequence R) (k : nat)
    : R := (#|plain (scheme_AHE (sequence_instance Q k))|%:R : R)^-1.

(* The advantage the IND-CPA assumption at k assumes.  It is the summand
   every bound along Q carries once per hop of the ladder. *)
Definition f_adv {R : realType} (Q : dsdp_instance_sequence R) (k : nat)
    : R := indcpa_assumption_epsilon (sequence_assumption Q k).

(* The two negligibility facts about a sequence Q, the asymptotic content of
   every bound read off along it.
   The two facts are the two terms of the bound, and the record keeps them
   apart.  size_negligible is the unconditional one: the inverse plaintext
   cardinality is the guessing residue the leaked output concedes, it is
   measured in the plaintext space alone, and it holds against an adversary of
   any running time.  adv_negligible is the assumption-conditional one: it is
   the advantage each assumption record assumes, and it is the only place a
   computational hypothesis enters.
   They are a record of their own and not fields of Q because a statement made
   at one security parameter needs the instance and the assumption there and
   neither of these two facts, so only the statements that let the parameter
   grow carry them. *)
Record dsdp_asymptotic (R : realType) (Q : dsdp_instance_sequence R) := {
  size_negligible : negligible_fun (f_size Q) ;
  adv_negligible : negligible_fun (f_adv Q) }.

(* Superpolynomial growth of (k+2)^(k+2): past c the sequence dominates
   every monomial k^c, by base and exponent monotonicity alone. *)
Lemma expnn_gt_monomial (c n : nat) : (c < n)%N -> (n ^ c < n.+2 ^ n.+2)%N.
Proof.
move=> Hcn; apply: leq_ltn_trans (_ : (n.+2) ^ c < _)%N; last first.
  by rewrite ltn_exp2l //; exact: (leq_trans Hcn (leqW (leqnSn n))).
move: Hcn; case: c => [_|c _]; first by rewrite !expn0.
by rewrite leq_exp2r //; exact: (leqW (leqnSn n)).
Qed.

Section negligible_helpers.
Context {R : realType}.

(* The inverse of (k+2)^(k+2) falls below every inverse polynomial: the
   growth rate the witness sequence's plaintext spaces follow. *)
Lemma negligible_fun_inv_expnn :
  negligible_fun (fun k : nat => (((k.+2) ^ k.+2)%N%:R : R)^-1).
Proof.
move=> c; exists c => n Hn.
have Hn0 : (0 < n)%N by apply: leq_ltn_trans Hn.
rewrite -natrX ltf_pV2 ?ltr_nat ?expnn_gt_monomial //.
  by rewrite posrE ltr0n expn_gt0.
by rewrite posrE ltr0n expn_gt0 Hn0.
Qed.

(* A sequence dominating (k+2)^(k+2) has negligible inverse.  The checkable
   modulus-growth condition of the scheme sequences: a Paillier or Benaloh
   sequence whose modulus (block size) grows at least this fast satisfies the
   information-theoretic negligibility field.
   Naming: extends [negligible_fun_inv_expnn] with the [ge] token marking the
   domination premise that replaces the exact sequence. *)
Lemma negligible_fun_inv_ge_expnn (f : nat -> nat) :
  (forall k, ((k.+2) ^ k.+2 <= f k)%N) ->
  negligible_fun (fun k => ((f k)%:R : R)^-1).
Proof.
move=> Hf; apply: negligible_fun_le negligible_fun_inv_expnn => k.
rewrite lef_pV2 ?ler_nat //.
  by rewrite posrE ltr0n (leq_trans _ (Hf k)) // expn_gt0.
by rewrite posrE ltr0n expn_gt0.
Qed.

End negligible_helpers.
