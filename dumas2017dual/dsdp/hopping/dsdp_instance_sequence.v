From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import idealized_ahe paillier_fdist_instance.
Require Import indcpa_game paillier_indcpa_scheme benaloh_indcpa_scheme.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.

(**md**************************************************************************)
(* # A security-parameter-indexed sequence of DSDP executions                 *)
(*                                                                            *)
(* Every corrupted-Alice bound of dsdp_alice_trace_link.v is stated at one    *)
(* fixed instance: one IND-CPA scheme, three private keys, four weights, one  *)
(* real epsilon.  negligible_fun of indcpa_game.v speaks about sequences      *)
(* indexed by a security parameter.  This file supplies the two objects that  *)
(* join them, a record holding one indcpa_scheme and the remaining section    *)
(* variables of that development, and a record packing a sequence of those    *)
(* with the assumption made at each k and the two negligibility facts, and    *)
(* reads the concrete class-conditional guessing bound off along such a       *)
(* sequence.                                                                  *)
(*                                                                            *)
(* The class restriction lands on the two reduction adversaries a predictor   *)
(* induces, never on the predictor itself.  That is what separates the        *)
(* headline from the predictor that decrypts Bob's ciphertext off the trace,  *)
(* whose guessing probability is 1: the companion corollary shows that the    *)
(* same two negligibility facts eventually reject that predictor's reduction  *)
(* adversary.  The witness section answers the vacuity question from the      *)
(* other side, discharging every hypothesis of the headline at once on the    *)
(* idealized scheme of idealized_ahe.v.                                       *)
(*                                                                            *)
(* The four scheme sections read the fixed and the asymptotic bound off at    *)
(* the Paillier and Benaloh IND-CPA schemes of paillier_indcpa_scheme.v and   *)
(* benaloh_indcpa_scheme.v.  Those two files carry the scheme side alone: the *)
(* packaging, the coin type and coin map, the assumption record and its       *)
(* sequence in k.  Everything DSDP, the four weights, the three keys, the two *)
(* hop coins and the two reduction adversaries, is declared here.  The        *)
(* information-theoretic term is discharged at each scheme, 1/(pq) at the     *)
(* Paillier modulus and 1/r at the Benaloh block size; the advantage stays    *)
(* the parameter the scheme file leaves it.                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*              dsdp_instance == one instance of the sequence, the section    *)
(*                               variables of the corrupted-Alice trace       *)
(*                               development packed as one record             *)
(*                inst_scheme == the IND-CPA scheme an instance runs on       *)
(*                   inst_AHE == its encryption packaging                     *)
(*                  inst_renc == its coin index type                          *)
(*             inst_card_renc == its pinned coin-space cardinality            *)
(*          inst_rand_of_renc == its coin map                                 *)
(*         inst_pkey_of_party == the public-key table of its three private    *)
(*                               keys                                         *)
(*     dsdp_instance_sequence == a sequence of instances indexed by the       *)
(*                               security parameter, the assumption made at   *)
(*                               each k, and the two negligibility facts that *)
(*                               give the sequence its asymptotic content     *)
(*          sequence_instance == the instance at k                            *)
(*        sequence_assumption == the IND-CPA assumption made at k             *)
(*   sequence_size_negligible == the inverse plaintext cardinalities are a    *)
(*                               negligible sequence, the unconditional       *)
(*                               currency                                     *)
(*    sequence_adv_negligible == the assumed advantages are a negligible      *)
(*                               sequence, the assumption-conditional         *)
(*                               currency                                     *)
(*          expnn_gt_monomial == (k+2)^(k+2) exceeds every monomial k^c past  *)
(*                               c                                            *)
(*   negligible_fun_inv_expnn == the inverse of (k+2)^(k+2) is negligible     *)
(* negligible_fun_inv_ge_expnn == a sequence dominating (k+2)^(k+2) has a     *)
(*                               negligible inverse                           *)
(*        negligible_fun_cst0 == the zero sequence is negligible              *)
(*     bob_trace_adversary_at == the Bob-key reduction adversary at k         *)
(* charlie_trace_adversary_at == the Charlie-key reduction adversary at k     *)
(* alice_trace_guess_V2_pr_at == the trace guessing probability at k          *)
(*                     f_size == the inverse plaintext-cardinality sequence   *)
(*                      f_adv == the assumed-advantage sequence               *)
(*                 f_guess_V2 == the trace guessing-probability sequence      *)
(*                    f_bound == f_size plus two copies of f_adv              *)
(* alice_trace_guess_V2_negligible ==                                         *)
(*                               the trace guessing sequence is negligible    *)
(*                               under the two class premises                 *)
(* decrypt_reduction_admissible_eventuallyF ==                                *)
(*                               the sequence's own negligibility fields      *)
(*                               eventually reject the decrypting             *)
(*                               predictor's reduction adversary              *)
(*             card_renc_ord1 == the one-element coin space, in successor     *)
(*                               form                                         *)
(*    idealized_indcpa_scheme == the idealized scheme of idealized_ahe.v as   *)
(*                               one scheme record                            *)
(*         idealized_instance == the idealized-scheme witness at k            *)
(* idealized_instance_sequence ==                                             *)
(*                               the witness sequence, with the               *)
(*                               cipher-constant assumption at each k         *)
(* idealized_bob_cipher_constant ==                                           *)
(*                               the witness Bob reduction ignores the        *)
(*                               challenge ciphertext                         *)
(* idealized_charlie_cipher_constant ==                                       *)
(*                               its Charlie counterpart                      *)
(* alice_trace_guess_V2_idealized_negligible ==                               *)
(*                               the witness discharges every hypothesis of   *)
(*                               the headline                                 *)
(* alice_trace_guess_V2_paillier_le ==                                        *)
(*                               the class-conditional trace guessing bound   *)
(*                               at Paillier, with 1/(p * q) as its           *)
(*                               information-theoretic term                   *)
(*          paillier_instance == the DSDP instance at k carried by a          *)
(*                               sequence of Paillier moduli                  *)
(* paillier_instance_sequence == that instance sequence with its assumption   *)
(*                               and its two negligibility facts              *)
(* alice_trace_guess_V2_paillier_negligible ==                                *)
(*                               the asymptotic form of that bound, under     *)
(*                               modulus growth and an assumed negligible     *)
(*                               advantage sequence                           *)
(* alice_trace_guess_V2_benaloh_le ==                                         *)
(*                               the class-conditional trace guessing bound   *)
(*                               at Benaloh, with 1/r as its information-     *)
(*                               theoretic term                               *)
(*           benaloh_instance == the DSDP instance at k carried by a          *)
(*                               sequence of Benaloh block sizes              *)
(*  benaloh_instance_sequence == that instance sequence with its assumption   *)
(*                               and its two negligibility facts              *)
(* alice_trace_guess_V2_benaloh_negligible ==                                 *)
(*                               the asymptotic form of that bound, under     *)
(*                               block-size growth and an assumed negligible  *)
(*                               advantage sequence                           *)
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

(* One instance of a security-parameter-indexed sequence of DSDP executions:
   an IND-CPA scheme, the four weights with Charlie's weight invertible, the
   three private keys, and the two hop coins.  These are exactly the section
   variables of the corrupted-Alice trace development
   (dsdp_alice_trace_link.v), so every concrete trace bound applies at a
   record unchanged.
   The scheme enters as one field rather than as its four data because an
   IND-CPA assumption is made about an indcpa_scheme: an instance and the
   assumption made about it then name the same scheme value, and in
   particular the same pinned coin-space cardinality.
   Two things stay outside.  The adversary and the two class premises, which
   restrict the reduction adversaries a predictor induces and so speak about
   the adversary rather than about the execution.  And the real field: a
   sequence lives over one R, which only the assumption record and the
   probabilities mention. *)
Record dsdp_instance := {
  inst_scheme  : indcpa_scheme ;
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

(* The four scheme data under the names the corrupted-Alice sections state
   their bounds over, together with the public-key table those sections read
   off the three private keys.  Keeping the old names is what lets a bound
   stated over section variables apply at a record unchanged.  They stay
   transparent Definitions: the hop-level pkey_of_party of a record and the
   trace-level pkey_of_dk of its three keys are then the same term by delta
   alone. *)
Definition inst_AHE (I : dsdp_instance) := scheme_AHE (inst_scheme I).
Definition inst_renc (I : dsdp_instance) := scheme_renc (inst_scheme I).
Definition inst_card_renc (I : dsdp_instance) :=
  scheme_card_renc (inst_scheme I).
Definition inst_rand_of_renc (I : dsdp_instance) :=
  @scheme_rand_of_renc (inst_scheme I).
Definition inst_pkey_of_party (I : dsdp_instance) :=
  pkey_of_dk (inst_dk_a I) (inst_dk_b I) (inst_dk_c I).

(* A sequence of DSDP instances indexed by the security parameter, the
   IND-CPA assumption made at each k, and the two facts that give the
   sequence its asymptotic content.
   The two facts are the two currencies of the bound, and the record keeps
   them apart.  sequence_size_negligible is the unconditional one: the
   inverse plaintext cardinality is the guessing residue the leaked output
   concedes, it is priced in the plaintext space alone, and it holds against
   an adversary of any running time.  sequence_adv_negligible is the
   assumption-conditional one: it is the advantage each assumption record
   assumes, and it is the only place a computational hypothesis enters.
   The record fixes no relation between consecutive k: each instance is
   supplied on its own, and the asymptotic statement comes from the two
   negligibility fields rather than from a recurrence between them. *)
Record dsdp_instance_sequence (R : realType) := {
  sequence_instance : nat -> dsdp_instance ;
  sequence_assumption : forall k,
    indcpa_epsilon_assumption (R:=R) (inst_card_renc (sequence_instance k))
      (@inst_rand_of_renc (sequence_instance k)) ;
  sequence_size_negligible :
    negligible_fun
      (fun k => (#|plain (inst_AHE (sequence_instance k))|%:R : R)^-1) ;
  sequence_adv_negligible :
    negligible_fun
      (fun k => indcpa_assumption_epsilon (sequence_assumption k)) }.

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
   information-theoretic negligibility field. *)
Lemma negligible_fun_inv_ge_expnn (f : nat -> nat) :
  (forall k, ((k.+2) ^ k.+2 <= f k)%N) ->
  negligible_fun (fun k => ((f k)%:R : R)^-1).
Proof.
move=> Hf; apply: negligible_fun_le negligible_fun_inv_expnn => k.
rewrite lef_pV2 ?ler_nat //.
  by rewrite posrE ltr0n (leq_trans _ (Hf k)) // expn_gt0.
by rewrite posrE ltr0n expn_gt0.
Qed.

(* The zero sequence is negligible: what the cipher-constant assumption
   sequence contributes to the witness. *)
Lemma negligible_fun_cst0 : negligible_fun (fun _ : nat => 0 : R).
Proof. by move=> c; exists 0 => n Hn; rewrite invr_gt0 exprn_gt0 // ltr0n. Qed.

End negligible_helpers.

Section dsdp_instance_sequence_bounds.
Context {R : realType}.
Variable Q : dsdp_instance_sequence R.
Local Notation I := (sequence_instance Q).
Local Notation A := (sequence_assumption Q).
Variable predict : forall k,
    predictor (inst_AHE (I k)) (alice_traceT (inst_AHE (I k))).
Arguments predict : clear implicits.

(* The Bob-key reduction adversary at k: the concrete constant applied
   at the record fields of I k.  Sequence plumbing; the mathematics is in the
   constant it applies. *)
Definition bob_trace_adversary_at k
    (D : distinguisher (trace_jointT (inst_AHE (I k)))) :=
  bob_trace_adversary (R:=R) (inst_card_renc (I k))
    (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rc2 (I k)) D.

(* The Charlie-key counterpart of bob_trace_adversary_at. *)
Definition charlie_trace_adversary_at k
    (D : distinguisher (trace_jointT (inst_AHE (I k)))) :=
  charlie_trace_adversary (R:=R) (inst_card_renc (I k))
    (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rc2 (I k)) D.

(* The probability that a predictor reading Alice's executed trace at k
   returns Bob's input.  The two hop coins enter here and not in the two
   reduction adversaries, which fix Bob's coin by the challenge. *)
Definition alice_trace_guess_V2_pr_at k
    (p : predictor (inst_AHE (I k)) (alice_traceT (inst_AHE (I k)))) : R :=
  alice_trace_guess_V2_pr (inst_card_renc (I k)) (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rb2 (I k)) (inst_rc2 (I k)) p.

(* The inverse plaintext-cardinality function used in the sequence theorem. *)
Definition f_size k : R := (#|plain (inst_AHE (I k))|%:R : R)^-1.

(* The assumed IND-CPA advantage function used in the sequence theorem. *)
Definition f_adv k : R := indcpa_assumption_epsilon (A k).

(* The trace guessing-probability function used in the sequence theorem. *)
Definition f_guess_V2 k : R := alice_trace_guess_V2_pr_at (predict k).

(* The pointwise upper-bound function used in the sequence theorem. *)
Definition f_bound k : R := f_size k + f_adv k + f_adv k.

(* A sequence of predictors reading Alice's executed traces along a sequence
   of DSDP instances matches Bob's input with negligible probability,
   provided the two reduction adversaries at each k are admitted by the class
   at that k.  The two negligibility facts the bound consumes, the inverse
   plaintext cardinalities and the assumed advantages, are fields of Q and so
   are read off the sequence; the two class premises stay premises of the
   theorem, because they restrict the reduction adversaries a predictor
   induces and so speak about the adversary rather than about the sequence.
   That is also what separates this statement from the decrypting
   counterexample: decrypt_guess_prE puts the guessing probability at 1 for
   the predictor that decrypts Bob's ciphertext off the trace, and
   decrypt_reduction_admissible_eventuallyF below shows the same two
   negligibility fields eventually force that predictor's reduction adversary
   out of the class.  Every currency is hypothesis-conditional, priced at
   each k as in the concrete bound. *)
Theorem alice_trace_guess_V2_negligible :
  (forall k, indcpa_admissible (A k)
     (bob_trace_adversary_at (distinguisher_of_predictor (predict k)))) ->
  (forall k, indcpa_admissible (A k)
     (charlie_trace_adversary_at (distinguisher_of_predictor (predict k)))) ->
  negligible_fun f_guess_V2.
Proof.
move=> HB HC.
have size_negligible := sequence_size_negligible Q.
have adv_negligible := sequence_adv_negligible Q.
have Hbound : negligible_fun f_bound.
  exact: negligible_fun_add (negligible_fun_add size_negligible adv_negligible)
           adv_negligible.
apply: negligible_fun_le Hbound => k.
rewrite /f_guess_V2 /f_bound /f_size /f_adv.
apply: le_trans (alice_trace_guess_V2_admissible_le
  (inst_u3_unit (I k)) (inst_rb2 (I k)) (HB k) (HC k)) _.
by rewrite mulr_natl mulr2n addrA.
Qed.

(* Under the two negligibility fields Q carries, the decrypting predictor's
   Bob-side reduction adversary is eventually outside the class: the
   parallel-track counterexample is excluded by the sequence's own fields,
   not by the information-theoretic term. *)
Corollary decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (A k)
      (bob_trace_adversary_at (distinguisher_of_predictor
         (bob_decrypt_predictor (@inst_rand_of_renc (I k))
            (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
            (inst_rc2 (I k))))) = false.
Proof.
have size_negligible := sequence_size_negligible Q.
have adv_negligible := sequence_adv_negligible Q.
have [N1 HN1] := size_negligible 1%N; have [N2 HN2] := adv_negligible 1%N.
exists (maxn (maxn N1 N2) 1) => k.
rewrite !gtn_max => /andP[/andP[Hk1 Hk2] Hk3].
have Hk0 : (0 < k%:R :> R) by rewrite ltr0n ltnW.
move: (HN1 k Hk1) (HN2 k Hk2); rewrite !expr1 => Hinv' Heps'.
have Hhalf : (k%:R : R)^-1 <= 1 - (k%:R : R)^-1.
  rewrite lerBrDr -div1r -mulrDl ler_pdivrMr // mul1r -(natrD R 1 1).
  by rewrite ler_nat.
apply: (decrypt_reduction_admissibleF (inst_v1 (I k)) (inst_u1 (I k))
          (inst_u2 (I k)) (inst_u3_unit (I k)) (inst_dk_a (I k))
          (inst_dk_b (I k)) (inst_dk_c (I k)) (inst_rb2 (I k))
          (inst_rc2 (I k))).
apply: lt_le_trans Heps' _; apply: le_trans Hhalf _.
by rewrite lerD2l lerN2 ltW.
Qed.

End dsdp_instance_sequence_bounds.

Section idealized_witness.
Context {R : realType}.

(* The one-element coin space, in the successor form the uniform coin of the
   abstract development takes. *)
Fact card_renc_ord1 : #|'I_1| = #|'I_1|.-1.+1.
Proof. by rewrite card_ord. Qed.

(* The idealized scheme of idealized_ahe.v as one value of the scheme record
   the IND-CPA game is quantified over: encryption on the plaintext ring
   msgT returns the message and ignores its randomness, so a single coin
   exhausts the coin space and the coin map is constant.  It is the scheme
   that answers the vacuity question for every bound stated at an
   indcpa_scheme: the game is well-typed here, and the cipher-constant class
   admits the reduction adversaries at advantage 0. *)
Definition idealized_indcpa_scheme (msgT : finComUnitRingType) :
    indcpa_scheme := {|
  scheme_AHE          := Idealized_HETypes msgT ;
  scheme_renc         := 'I_1 ;
  scheme_card_renc    := card_renc_ord1 ;
  scheme_rand_of_renc := fun _ => 0 |}.

(* The witness instance at k: the idealized scheme of idealized_ahe.v over a
   plaintext space of cardinality (k+2)^(k+2), with the first three weights
   zero, Charlie's weight 1, zero keys and the single coin.
   It hides nothing; its role is exactly that the headline's hypotheses
   are jointly satisfiable, and on it the guessing probability is
   1/#|plain|, not 0, so the conclusion has content here. *)
Definition idealized_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := idealized_indcpa_scheme 'Z_((k.+2) ^ k.+2) ;
  inst_v1 := 0 ; inst_u1 := 0 ; inst_u2 := 0 ; inst_u3 := 1 ;
  inst_u3_unit      := GRing.unitr1 _ ;
  inst_dk_a := 0 ; inst_dk_b := 0 ; inst_dk_c := 0 ;
  inst_rb2 := ord0 ; inst_rc2 := ord0 |}.

(* The witness plaintext space at k has cardinality (k+2)^(k+2). *)
Let card_plain_idealized (k : nat) :
  #|plain (inst_AHE (idealized_instance k))| = ((k.+2) ^ k.+2)%N.
Proof. by rewrite card_ord Zp_cast // -{1}(expn0 k.+2) ltn_exp2l. Qed.

(* The unconditional currency of the witness sequence: its plaintext spaces
   grow as (k+2)^(k+2), so their inverse cardinalities fall below every
   inverse polynomial. *)
Let idealized_size_negligible :
  negligible_fun (fun k =>
    (#|plain (inst_AHE (idealized_instance k))|%:R : R)^-1).
Proof.
apply: negligible_fun_le negligible_fun_inv_expnn => k.
by rewrite card_plain_idealized.
Qed.

(* The witness sequence: the idealized instances above, the cipher-constant
   assumption of indcpa_game.v at each k, and the two negligibility facts
   discharged rather than assumed.  Its advantage currency is zero at every
   k, so the whole content of the bound along it is the unconditional
   1/#|plain| term. *)
Definition idealized_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := idealized_instance ;
  sequence_assumption := fun k =>
    cipher_constant_assumption (inst_card_renc (idealized_instance k))
      (@inst_rand_of_renc (idealized_instance k)) ;
  sequence_size_negligible := idealized_size_negligible ;
  sequence_adv_negligible := negligible_fun_cst0 |}.

(* The constant predictor's distinguisher reads only the state slot, so the
   Bob-key reduction adversary ignores the challenge ciphertext and the
   cipher-constant class admits it. *)
Lemma idealized_bob_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (inst_card_renc (idealized_instance k))
       (@inst_rand_of_renc (idealized_instance k)))
    (bob_trace_adversary (R:=R) (inst_card_renc (idealized_instance k))
       (@inst_rand_of_renc (idealized_instance k))
       (inst_v1 (idealized_instance k)) (inst_u1 (idealized_instance k))
       (inst_u2 (idealized_instance k)) (inst_u3 (idealized_instance k))
       (inst_dk_a (idealized_instance k)) (inst_dk_b (idealized_instance k))
       (inst_dk_c (idealized_instance k)) (inst_rc2 (idealized_instance k))
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of idealized_bob_cipher_constant. *)
Lemma idealized_charlie_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (inst_card_renc (idealized_instance k))
       (@inst_rand_of_renc (idealized_instance k)))
    (charlie_trace_adversary (R:=R) (inst_card_renc (idealized_instance k))
       (@inst_rand_of_renc (idealized_instance k))
       (inst_v1 (idealized_instance k)) (inst_u1 (idealized_instance k))
       (inst_u2 (idealized_instance k)) (inst_u3 (idealized_instance k))
       (inst_dk_a (idealized_instance k)) (inst_dk_b (idealized_instance k))
       (inst_dk_c (idealized_instance k)) (inst_rc2 (idealized_instance k))
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The headline's hypotheses hold together at least once: the witness
   sequence carries both negligibility fields, and the constant predictor's
   two reduction adversaries are in the cipher-constant class at every k. *)
Corollary alice_trace_guess_V2_idealized_negligible :
  negligible_fun (fun k =>
    alice_trace_guess_V2_pr (R:=R) (inst_card_renc (idealized_instance k))
      (@inst_rand_of_renc (idealized_instance k))
      (inst_v1 (idealized_instance k)) (inst_u1 (idealized_instance k))
      (inst_u2 (idealized_instance k)) (inst_u3 (idealized_instance k))
      (inst_dk_a (idealized_instance k)) (inst_dk_b (idealized_instance k))
      (inst_dk_c (idealized_instance k)) (inst_rb2 (idealized_instance k))
      (inst_rc2 (idealized_instance k)) (fun _ => 0)).
Proof.
apply: (alice_trace_guess_V2_negligible
          (Q := idealized_instance_sequence)
          (predict := fun k => fun _ => 0)).
- exact: idealized_bob_cipher_constant.
- exact: idealized_charlie_cipher_constant.
Qed.

End idealized_witness.

Section paillier_dsdp_instance.
Context {R : realType}.
Variables p q : nat.
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.

(* The Paillier IND-CPA instance of paillier_indcpa_scheme.v at this
   modulus, pinned once under the names that file exports them by. *)
Local Notation AHE := (Paillier_AHEnc (pq_gt1 p_gt1 q_gt1)).
Local Notation card_renc_paillier := (card_renc_paillier p q).
Local Notation rand_of_renc_paillier := (rand_of_renc_paillier p_gt1 q_gt1).

(* The plaintext space of this instantiation has cardinality p * q, the form
   the composite-modulus DSDP bounds consume. *)
Let card_plain_pq : #|plain AHE| = (p * q)%N.
Proof. exact: card_plain_paillier_pq. Qed.

Variables (v1 u1 u2 u3 : plain AHE).

(* Charlie's weight is invertible.  This is what makes the DSDP solution
   fiber a bijective image of the plaintext space, and so what turns the
   leaked output into the 1/(p * q) term of the bound below rather than into
   a determination of Bob's input. *)
Hypothesis u3_unit : u3 \is a GRing.unit.

Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (rb2 rc2 : renc_paillier p q).

(* The IND-CPA assumption of Paillier at this modulus, the record
   paillier_indcpa_scheme.v leaves a parameter. *)
Variable paillier_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_paillier rand_of_renc_paillier.

Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c rc2).
Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) card_renc_paillier rand_of_renc_paillier
     v1 u1 u2 u3 dk_a dk_b dk_c rb2 rc2).

(* A predictor reading Alice's executed DSDP trace at the Paillier
   instantiation returns Bob's input with probability at most 1/(p * q) plus
   twice the assumed advantage.

   The 1/(p * q) is unconditional.  It comes from Sout, the output Alice
   knows by design.  2 * epsilon is conditional on
   paillier_indcpa_assumption, and prices the two ciphertext replacements
   at Bob's key and at Charlie's. *)
Corollary alice_trace_guess_V2_paillier_le
    (predict : predictor AHE (alice_traceT AHE)) :
  indcpa_admissible paillier_indcpa_assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)) ->
  indcpa_admissible paillier_indcpa_assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)) ->
  alice_trace_guess_V2_pr predict
    <= ((p%:R : R) * q%:R)^-1
       + 2 * indcpa_assumption_epsilon paillier_indcpa_assumption.
Proof.
exact: (alice_trace_guess_V2_admissible_pq_le
          u3_unit rb2 card_plain_pq).
Qed.

End paillier_dsdp_instance.

Section paillier_dsdp_instance_sequence.
Context {R : realType}.
Variables p q : nat -> nat.
Hypothesis p_gt1 : forall k, (1 < p k)%N.
Hypothesis q_gt1 : forall k, (1 < q k)%N.
Variables (v1 u1 u2 u3 :
  forall k, plain (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))).
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.
Variables (dk_a dk_b dk_c :
  forall k, priv_key (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k)))).
Variables (rb2 rc2 : forall k, renc_paillier (p k) (q k)).

(* The DSDP instance at parameter k on the Paillier IND-CPA scheme at k: the
   scheme record paillier_indcpa_scheme (p_gt1 k) (q_gt1 k) of
   paillier_indcpa_scheme.v, with the weights, keys, and coins supplied as
   sequences.  Everything number-theoretic about the moduli beyond 1 < p, q
   stays assumed, as in the fixed-instance section above. *)
Definition paillier_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := paillier_indcpa_scheme (p_gt1 k) (q_gt1 k) ;
  inst_v1 := v1 k ; inst_u1 := u1 k ; inst_u2 := u2 k ;
  inst_u3 := u3 k ; inst_u3_unit := u3_unit k ;
  inst_dk_a := dk_a k ; inst_dk_b := dk_b k ; inst_dk_c := dk_c k ;
  inst_rb2 := rb2 k ; inst_rc2 := rc2 k |}.

Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (paillier_instance k))
    (@inst_rand_of_renc (paillier_instance k)).

(* Supplies the unconditional summand of the bound
   Pr_k <= 1/(p k * q k) + 2 * eps k, through f_size_paillier_negligible,
   which reads the plaintext cardinality at k as the modulus p k * q k.

   The summand 1/(p k * q k) is the guessing probability the leaked
   output Sout concedes: at Paillier #|plain| is the modulus p k * q k,
   and Sout confines the uniform V2 to a fiber of that size.  Negligible
   is the acceptance criterion of the asymptotic reading: the concrete
   analysis already treats this residue as the acceptable leak, and this
   hypothesis states that acceptability uniformly in k, the residue
   falling below every inverse polynomial. *)
Hypothesis f_pq_negligible : negligible_fun (f_pq (R:=R) p q).

(* The advantage the assumption sequence assumes is negligible: the
   asymptotic IND-CPA reading of decisional composite residuosity. *)
Hypothesis f_adv_negligible :
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)).

(* The Paillier instance sequence: the instances above, the assumption made
   at each k, and the two negligibility facts, the unconditional one read at
   the modulus and the assumption-conditional one assumed.  It is the value
   the sequence headline is applied at below. *)
Definition paillier_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := paillier_instance ;
  sequence_assumption := A ;
  sequence_size_negligible :=
    f_size_paillier_negligible p_gt1 q_gt1 f_pq_negligible ;
  sequence_adv_negligible := f_adv_negligible |}.

Variable predict : forall k, predictor (inst_AHE (paillier_instance k))
    (alice_traceT (inst_AHE (paillier_instance k))).
Arguments predict : clear implicits.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=paillier_instance_sequence) predict).

(* The class of the assumption sequence admits the Bob-side reduction
   adversary induced by every predictor in the sequence. *)
Hypothesis bob_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (bob_trace_adversary_at (Q:=paillier_instance_sequence)
       (distinguisher_of_predictor (predict k))).

(* The Charlie-side twin of bob_reduction_admissible. *)
Hypothesis charlie_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (charlie_trace_adversary_at (Q:=paillier_instance_sequence)
       (distinguisher_of_predictor (predict k))).

(* The conclusion is negligible_fun of the sequence k |-> Pr_k, where Pr_k
   is the probability that the k-th predictor guesses Bob's input V2 at
   the k-th Paillier instance.

   It follows in three steps.  At each k the two class premises yield the
   bound of alice_trace_guess_V2_admissible_le, Pr_k <= 1/(p k * q k) +
   2 * eps k, with eps k the advantage A k assumes.  The two negligibility
   fields of paillier_instance_sequence make f_size and f_adv negligible,
   f_size through the scheme-side reading of modulus growth as plaintext
   growth.  Closure under addition twice makes f_bound negligible, and the
   pointwise bound transfers negligibility from f_bound to f_guess_V2.

   The assumption sequence is the per-k form of paillier_indcpa_assumption;
   decisional composite residuosity remains the source a proved record
   sequence would start from. *)
Corollary alice_trace_guess_V2_paillier_negligible : negligible_fun f_guess_V2.
Proof.
exact: (alice_trace_guess_V2_negligible
          bob_reduction_admissible charlie_reduction_admissible).
Qed.

End paillier_dsdp_instance_sequence.

Section benaloh_dsdp_instance.
Context {R : realType}.
Variables n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* The Benaloh IND-CPA instance of benaloh_indcpa_scheme.v at these
   parameters, pinned once under the names that file exports them by. *)
Local Notation AHE := (Benaloh_AHEnc n r_gt1).
Local Notation card_renc_benaloh := (card_renc_benaloh n).
Local Notation rand_of_renc_benaloh := (rand_of_renc_benaloh (n:=n) r_gt1).

(* The plaintext space of this instantiation is Z/rZ, so its cardinality is
   the block size r.  It is r, not the modulus n, that the information-
   theoretic term of the bound below is read off: at Benaloh the plaintext
   space is the block Z/rZ fixed by the order condition on the private key's
   generator, while n sizes the ciphertext space. *)
Let card_plain_r : #|plain AHE| = r.
Proof. by rewrite card_ord Zp_cast. Qed.

Variables (v1 u1 u2 u3 : plain AHE).

(* Charlie's weight is invertible in Z/rZ.  This is what makes the DSDP
   solution fiber a bijective image of the plaintext space, and so what turns
   the leaked output into the 1/r term of the bound below rather than into a
   determination of Bob's input. *)
Hypothesis u3_unit : u3 \is a GRing.unit.

Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (rb2 rc2 : renc_benaloh n).

(* The IND-CPA assumption of Benaloh at these parameters, the record
   benaloh_indcpa_scheme.v leaves a parameter. *)
Variable benaloh_indcpa_assumption :
  indcpa_epsilon_assumption (R:=R) card_renc_benaloh rand_of_renc_benaloh.

Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c rc2).
Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) card_renc_benaloh rand_of_renc_benaloh
     v1 u1 u2 u3 dk_a dk_b dk_c rb2 rc2).

(* The inverse plaintext cardinality at the Benaloh block size. *)
Let inv_r_cardE : (r%:R : R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_r. Qed.

(* A predictor reading Alice's executed DSDP trace at the Benaloh
   instantiation returns Bob's input with probability at most 1/r plus twice
   the assumed advantage.

   The 1/r is unconditional. It comes from Sout, the output Alice knows by
   design.
   2 * epsilon is conditional on benaloh_indcpa_assumption, and prices the
   two ciphertext replacements at Bob's key and at Charlie's. *)
Corollary alice_trace_guess_V2_benaloh_le
    (predict : predictor AHE (alice_traceT AHE)) :
  indcpa_admissible benaloh_indcpa_assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)) ->
  indcpa_admissible benaloh_indcpa_assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)) ->
  alice_trace_guess_V2_pr predict
    <= (r%:R : R)^-1
       + 2 * indcpa_assumption_epsilon benaloh_indcpa_assumption.
Proof.
rewrite inv_r_cardE.
exact: (alice_trace_guess_V2_admissible_le u3_unit rb2).
Qed.

End benaloh_dsdp_instance.

Section benaloh_dsdp_instance_sequence.
Context {R : realType}.
Variables n r : nat -> nat.
Hypothesis n_gt1 : forall k, (1 < n k)%N.
Hypothesis r_gt1 : forall k, (1 < r k)%N.
Variables (v1 u1 u2 u3 :
  forall k, plain (Benaloh_AHEnc (n k) (r_gt1 k))).
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.
Variables (dk_a dk_b dk_c :
  forall k, priv_key (Benaloh_AHEnc (n k) (r_gt1 k))).
Variables (rb2 rc2 : forall k, renc_benaloh (n k)).

(* The DSDP instance at parameter k on the Benaloh IND-CPA scheme at k: the
   scheme record benaloh_indcpa_scheme (n k) (r_gt1 k) of
   benaloh_indcpa_scheme.v, with the weights, keys, and coins supplied as
   sequences.  Everything number-theoretic about the modulus and the block
   size beyond 1 < n, r stays assumed, as in the fixed-instance section
   above. *)
Definition benaloh_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := benaloh_indcpa_scheme (n k) (r_gt1 k) ;
  inst_v1 := v1 k ; inst_u1 := u1 k ; inst_u2 := u2 k ;
  inst_u3 := u3 k ; inst_u3_unit := u3_unit k ;
  inst_dk_a := dk_a k ; inst_dk_b := dk_b k ; inst_dk_c := dk_c k ;
  inst_rb2 := rb2 k ; inst_rc2 := rc2 k |}.

Variable A : forall k, indcpa_epsilon_assumption (R:=R)
    (inst_card_renc (benaloh_instance k))
    (@inst_rand_of_renc (benaloh_instance k)).

(* Supplies the unconditional summand of the bound
   Pr_k <= 1/(r k) + 2 * eps k, through f_size_benaloh_negligible, which
   reads the plaintext cardinality at k as the block size r k.

   The summand 1/(r k) is the guessing probability the leaked output
   Sout concedes: at Benaloh #|plain| is the block size r k, and Sout
   confines the uniform V2 to a fiber of that size.  Negligible is the
   acceptance criterion of the asymptotic reading: the concrete analysis
   already treats this residue as the acceptable leak, and this
   hypothesis states that acceptability uniformly in k, the residue
   falling below every inverse polynomial. *)
Hypothesis f_r_negligible : negligible_fun (f_r (R:=R) r).

(* The advantage the assumption sequence assumes is negligible: the
   asymptotic IND-CPA reading of r-th residuosity. *)
Hypothesis f_adv_negligible :
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)).

(* The Benaloh instance sequence: the instances above, the assumption made at
   each k, and the two negligibility facts, the unconditional one read at the
   block size and the assumption-conditional one assumed.  It is the value
   the sequence headline is applied at below. *)
Definition benaloh_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := benaloh_instance ;
  sequence_assumption := A ;
  sequence_size_negligible :=
    f_size_benaloh_negligible n r_gt1 f_r_negligible ;
  sequence_adv_negligible := f_adv_negligible |}.

Variable predict : forall k, predictor (inst_AHE (benaloh_instance k))
    (alice_traceT (inst_AHE (benaloh_instance k))).
Arguments predict : clear implicits.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=benaloh_instance_sequence) predict).

(* The class of the assumption sequence admits the Bob-side reduction
   adversary induced by every predictor in the sequence. *)
Hypothesis bob_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (bob_trace_adversary_at (Q:=benaloh_instance_sequence)
       (distinguisher_of_predictor (predict k))).

(* The Charlie-side twin of bob_reduction_admissible. *)
Hypothesis charlie_reduction_admissible : forall k,
  indcpa_admissible (A k)
    (charlie_trace_adversary_at (Q:=benaloh_instance_sequence)
       (distinguisher_of_predictor (predict k))).

(* The conclusion is negligible_fun of the sequence k |-> Pr_k, where Pr_k
   is the probability that the k-th predictor guesses Bob's input V2 at
   the k-th Benaloh instance.

   It follows in three steps.  At each k the two class premises yield the
   bound of alice_trace_guess_V2_admissible_le, Pr_k <= 1/(r k) + 2 * eps k,
   with eps k the advantage A k assumes.  The two negligibility fields of
   benaloh_instance_sequence make f_size and f_adv negligible, f_size
   through the scheme-side reading of block-size growth as plaintext growth.
   Closure under addition twice makes f_bound negligible, and the pointwise
   bound transfers negligibility from f_bound to f_guess_V2.

   The assumption sequence is the per-k form of benaloh_indcpa_assumption;
   r-th residuosity remains the source a proved record sequence would start
   from. *)
Corollary alice_trace_guess_V2_benaloh_negligible : negligible_fun f_guess_V2.
Proof.
exact: (alice_trace_guess_V2_negligible
          bob_reduction_admissible charlie_reduction_admissible).
Qed.

End benaloh_dsdp_instance_sequence.
