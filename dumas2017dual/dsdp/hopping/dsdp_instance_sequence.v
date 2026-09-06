From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption residuosity_game.
Require Import idealized_ahe paillier_fdist_instance.
Require Import negligible epshop epshop_family.
Require Import indcpa_game paillier_indcpa_scheme benaloh_indcpa_scheme.
Require Import dsdp_instance.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.

(**md**************************************************************************)
(* # A security-parameter-indexed sequence of DSDP executions                 *)
(*                                                                            *)
(* Every corrupted-Alice bound of dsdp_alice_trace_link.v is stated at one    *)
(* fixed instance: one IND-CPA scheme, three private keys, four weights, one  *)
(* real epsilon.  negligible_fun of indcpa_game.v speaks about sequences      *)
(* indexed by a security parameter.  The three records that join them, an     *)
(* instance, a sequence of instances with the assumption made at each k, and  *)
(* the two negligibility facts about such a sequence, are the data of         *)
(* dsdp_instance.v.  This file reads the concrete class-conditional guessing  *)
(* bound off along a sequence and an asymptotic value for it.  A second       *)
(* statement is read off the same way, the distance a test sees between       *)
(* Alice's executed trace and the simulation, which is computational          *)
(* indistinguishability of her view from the simulation.                      *)
(*                                                                            *)
(* The class restriction lands on the two reduction adversaries a predictor   *)
(* induces, never on the predictor itself.  That is what separates the        *)
(* headline from the predictor that decrypts Bob's ciphertext off the trace,  *)
(* whose guessing probability is 1: the companion corollary shows that the    *)
(* same asymptotic value eventually rejects that predictor's reduction        *)
(* adversary.  The witness section answers the vacuity question from the      *)
(* other side, discharging every hypothesis of the headline at once on the    *)
(* idealized scheme of idealized_ahe.v.                                       *)
(*                                                                            *)
(* The four scheme sections read the fixed and the asymptotic bound off at    *)
(* the Paillier and Benaloh IND-CPA schemes of paillier_indcpa_scheme.v and   *)
(* benaloh_indcpa_scheme.v.  Those two files carry the scheme side alone: the *)
(* packaging, the coin type and coin map, the derived assumption record and   *)
(* its sequence in k.  Everything DSDP, the four weights, the three keys, the *)
(* two hop coins and the two reduction adversaries, is declared here.  The    *)
(* information-theoretic term is discharged at each scheme, 1/(pq) at the     *)
(* Paillier modulus and 1/r at the Benaloh block size.                        *)
(*                                                                            *)
(* The computational term is discharged too.  Each scheme section takes a     *)
(* residuosity assumption, decisional composite residuosity at modulus p q or *)
(* r-th residuosity at modulus n, and derives its IND-CPA assumption from it, *)
(* so no advantage is left as a parameter here.  The scheme reduction costs   *)
(* two residuosity calls per key and the trace bound spends an IND-CPA        *)
(* epsilon at Bob's key and at Charlie's, so the fixed bounds read            *)
(* 1/(pq) + 4 eps and 1/r + 4 eps, with the first summand unconditional and   *)
(* the second conditional on the residuosity record.  Four lemmas show the    *)
(* class premises of those bounds satisfiable at the challenge-ignoring       *)
(* residuosity record of residuosity_game.v.                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*                 f_guess_V2 == the trace guessing-probability sequence      *)
(* alice_claims_admissible_at k ==                                            *)
(*                               the dictionary of the class-conditional      *)
(*                               argument at the k-th instance                *)
(* alice_label_negligible_at == every label of that dictionary costs a        *)
(*                               negligible family along the sequence         *)
(* alice_claims_admissible_negligible ==                                      *)
(*                               that dictionary registered as a              *)
(*                               negligibleClaims                             *)
(* alice_trace_chain_admissible_at k ==                                       *)
(*                               the class-conditional program at the k-th    *)
(*                               instance                                     *)
(*       f_guess_V2_advantageE == the guessing sequence is the advantage      *)
(*                               that program bounds                          *)
(* alice_trace_guess_V2_negligible ==                                         *)
(*                               the trace guessing sequence is negligible    *)
(*                               under the two class premises                 *)
(* decrypt_reduction_admissible_eventuallyF ==                                *)
(*                               an asymptotic value for the sequence         *)
(*                               eventually rejects the decrypting            *)
(*                               predictor's reduction adversary              *)
(*      alice_sim_claims_at k == the dictionary of the trace simulation       *)
(*                               argument at the k-th instance                *)
(* alice_sim_label_negligible_at ==                                           *)
(*                               every label of that dictionary costs a       *)
(*                               negligible family along the sequence         *)
(* alice_sim_claims_negligible ==                                             *)
(*                               that dictionary registered as a              *)
(*                               negligibleClaims                             *)
(* alice_trace_sim_chain_admissible_at k ==                                   *)
(*                               the class-conditional trace simulation       *)
(*                               program at the k-th instance                 *)
(*            f_sim_advantage == the trace simulation distance sequence       *)
(*            f_sim_advantageE == the distance sequence is the advantage      *)
(*                               that program bounds                          *)
(* alice_trace_sim_advantage_negligible ==                                    *)
(*                               the trace simulation distance sequence       *)
(*                               is negligible under the two class            *)
(*                               premises                                     *)
(*             card_renc_ord1 == the one-element coin space, in successor     *)
(*                               form                                         *)
(*    idealized_indcpa_scheme == the idealized scheme of idealized_ahe.v as   *)
(*                               one scheme record                            *)
(*         idealized_instance == the idealized-scheme witness at k            *)
(* idealized_instance_sequence ==                                             *)
(*                               the witness sequence, with the               *)
(*                               cipher-constant assumption at each k         *)
(*       idealized_asymptotic == the two negligibility facts about that       *)
(*                               sequence, discharged rather than assumed     *)
(* idealized_bob_cipher_constant ==                                           *)
(*                               the witness Bob reduction ignores the        *)
(*                               challenge ciphertext                         *)
(* idealized_charlie_cipher_constant ==                                       *)
(*                               its Charlie counterpart                      *)
(* alice_trace_guess_V2_idealized_negligible ==                               *)
(*                               the witness discharges every hypothesis of   *)
(*                               the headline                                 *)
(*      paillier_epsilon_dcrE == the epsilon the derived assumption is stated *)
(*                               at is twice the residuosity epsilon          *)
(* paillier_trace_guess_V2_admissible_le ==                                   *)
(*                               the trace guessing bound at this modulus,    *)
(*                               the inverse plaintext count plus four        *)
(*                               residuosity epsilons                         *)
(* paillier_trace_guess_V2_admissible_pq_le ==                                *)
(*                               the same bound with its unconditional term   *)
(*                               written 1/(p * q)                            *)
(* paillier_bob_decide_constant_admissible ==                                 *)
(*                               at the challenge-ignoring residuosity        *)
(*                               record the constant predictor's Bob-key      *)
(*                               reduction adversary is in the derived class  *)
(* paillier_charlie_decide_constant_admissible ==                             *)
(*                               its Charlie-key counterpart                  *)
(*   paillier_fixed_instance == the DSDP instance at one modulus, the value   *)
(*                               the fixed Paillier bounds are read at        *)
(*          paillier_instance == the DSDP instance at k carried by a          *)
(*                               sequence of Paillier moduli                  *)
(* paillier_instance_sequence == that instance sequence with the IND-CPA      *)
(*                               assumption derived at each k from a          *)
(*                               residuosity record                           *)
(* paillier_assumption_at_dcrE ==                                             *)
(*                               the assumption the sequence makes at k is    *)
(*                               the one derived from dcr k                   *)
(*   paillier_epsilon_at_dcrE == the epsilon at k is twice the residuosity    *)
(*                               epsilon dcr k assumes                        *)
(*        paillier_asymptotic == its two negligibility facts, the             *)
(*                               unconditional one at the modulus and the     *)
(*                               assumption-conditional one at the            *)
(*                               residuosity hypothesis                       *)
(* paillier_decrypt_reduction_admissible_eventuallyF ==                       *)
(*                               the assumption sequence eventually rejects   *)
(*                               the decrypting predictor's Bob-key reduction *)
(*                               adversary                                    *)
(* paillier_trace_guess_V2_negligible ==                                      *)
(*                               the asymptotic form of that bound, under     *)
(*                               modulus growth and a negligible residuosity  *)
(*                               advantage sequence                           *)
(* benaloh_epsilon_residuosityE ==                                            *)
(*                               the epsilon the derived assumption is stated *)
(*                               at is twice the residuosity epsilon          *)
(* benaloh_trace_guess_V2_admissible_le ==                                    *)
(*                               the trace guessing bound at this block size, *)
(*                               the inverse plaintext count plus four        *)
(*                               residuosity epsilons                         *)
(* benaloh_trace_guess_V2_admissible_pq_le ==                                 *)
(*                               the same bound at a block size written as a  *)
(*                               product of two primes, 1/(p * q)             *)
(* benaloh_bob_decide_constant_admissible ==                                  *)
(*                               at the challenge-ignoring residuosity        *)
(*                               record the constant predictor's Bob-key      *)
(*                               reduction adversary is in the derived class  *)
(* benaloh_charlie_decide_constant_admissible ==                              *)
(*                               its Charlie-key counterpart                  *)
(*    benaloh_fixed_instance == the DSDP instance at one modulus and block    *)
(*                               size, the value the fixed Benaloh bounds     *)
(*                               are read at                                  *)
(*           benaloh_instance == the DSDP instance at k carried by a          *)
(*                               sequence of Benaloh block sizes              *)
(*  benaloh_instance_sequence == that instance sequence with the IND-CPA      *)
(*                               assumption derived at each k from a          *)
(*                               residuosity record                           *)
(* benaloh_assumption_at_residuosityE ==                                      *)
(*                               the assumption the sequence makes at k is    *)
(*                               the one derived from residuosity k           *)
(* benaloh_epsilon_at_residuosityE ==                                         *)
(*                               the epsilon at k is twice the residuosity    *)
(*                               epsilon residuosity k assumes                *)
(*         benaloh_asymptotic == its two negligibility facts, the             *)
(*                               unconditional one at the block size and      *)
(*                               the assumption-conditional one at the        *)
(*                               residuosity hypothesis                       *)
(* benaloh_decrypt_reduction_admissible_eventuallyF ==                        *)
(*                               the assumption sequence eventually rejects   *)
(*                               the decrypting predictor's Bob-key reduction *)
(*                               adversary                                    *)
(* benaloh_trace_guess_V2_negligible ==                                       *)
(*                               the asymptotic form of that bound, under     *)
(*                               block-size growth and a negligible           *)
(*                               residuosity advantage sequence               *)
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

Section dsdp_instance_sequence_bounds.
Context {R : realType}.
Variable Q : dsdp_instance_sequence R.

(* The asymptotic content the negligibility statements of this section spend;
   the per-k bounds below hold without it. *)
Variable N : dsdp_asymptotic Q.

Local Notation I := (sequence_instance Q).
Local Notation assumption := (sequence_assumption Q).
Variable predict : forall k,
    predictor (I k) (alice_traceT (I k)).
Arguments predict : clear implicits.

(* The two class premises of the whole section: at every security parameter
   the class of the assumption made there admits the two reduction adversaries
   the k-th predictor induces.  They restrict the adversaries a predictor
   induces and so speak about the adversary rather than about the sequence,
   which is why they stay premises and are not fields of Q. *)
Hypothesis bob_admissible : forall k,
  indcpa_admissible (assumption k)
    (bob_trace_adversary (distinguisher_of_predictor (predict k))).
Hypothesis charlie_admissible : forall k,
  indcpa_admissible (assumption k)
    (charlie_trace_adversary (distinguisher_of_predictor (predict k))).

(* The trace guessing-probability function used in the sequence theorem: the
   probability that the k-th predictor, reading Alice's executed trace at the
   k-th instance, returns Bob's input. *)
Definition f_guess_V2 k : R := alice_trace_guess_V2_pr (predict k).

(* The dictionary of the class-conditional argument at the k-th instance, as
   a family indexed by the security parameter.  It is a named constant rather
   than a lambda because canonical inference keys on the head constant of the
   family, and an application of a lambda has none.
   Naming: extends [alice_claim_admissible] with the [_at] token naming the
   instance the dictionary is read at, the plural marking the family. *)
Definition alice_claims_admissible_at (k : nat) : alice_label -> claim R :=
  alice_claim_admissible (assumption k)
    (hop_tuple_distinguisher (distinguisher_of_predictor (predict k))).

(* Every label of that dictionary costs a negligible family along the
   sequence: both hop labels cost the epsilon the assumption at k assumes,
   which is the assumption-conditional field of N read directly, and the
   terminal label costs the inverse plaintext cardinality, its unconditional
   field.  This is the whole asymptotic content of the argument, stated once
   for the dictionary rather than once per statement proved over it.
   Naming: intentional; [_negligible] is this development's suffix for a
   negligible_fun conclusion, and [_at] names the instance the family is read
   at, as at [alice_claims_admissible_at]. *)
Lemma alice_label_negligible_at (l : alice_label) :
  negligible_fun (fun k => claim_cost (alice_claims_admissible_at k l)).
Proof.
case: l.
- exact: adv_negligible N.
- exact: adv_negligible N.
- exact: size_negligible N.
Qed.

Canonical alice_claims_admissible_negligible :=
  NegligibleClaims alice_claims_admissible_at alice_label_negligible_at.

(* The class-conditional program at the k-th instance, the value of the
   family monad the terminal below reads.  The return type names the
   dictionary, which is what lets canonical inference find the negligibility
   of the labels the program spends.
   Naming: extends [alice_trace_chain_admissible] with the [_at] token naming
   the instance the program is read at. *)
Definition alice_trace_chain_admissible_at (k : nat)
    : chain_result (alice_claims_admissible_at k) :=
  alice_trace_chain_admissible (bob_admissible k) (charlie_admissible k).

(* The quantity the theorem below is about is the advantage that program
   bounds, its guessing probability being its distance from the zero game. *)
Lemma f_guess_V2_advantageE k :
  f_guess_V2 k = result_advantage (alice_trace_chain_admissible_at k).
Proof.
by rewrite /f_guess_V2 /alice_trace_guess_V2_pr guess_V2_acceptE
   -(advantage0 (accept_ge0 _ _)).
Qed.

Local Open Scope epshop_scope.

(* A sequence of predictors reading Alice's executed traces along a sequence
   of DSDP instances matches Bob's input with negligible probability, under
   the two class premises of this section.  It is the terminal of the family
   monad read over the class-conditional program: the program spends the same
   three labels at every security parameter, and the cost of each of them
   along the sequence is one of the two fields of N, supplied once through
   the registered instance rather than summed by hand at each
   statement.  Two of the three summands are assumption-conditional, the
   class epsilon at Bob's key and at Charlie's, and the third is
   unconditional, the residue the leaked output leaves along the DSDP
   solution fiber.
   That is also what separates this statement from the decrypting
   counterexample: decrypt_guess_prE puts the guessing probability at 1 for
   the predictor that decrypts Bob's ciphertext off the trace, and
   decrypt_reduction_admissible_eventuallyF below shows the same two fields
   of N eventually force that predictor's reduction adversary out of the
   class. *)
Theorem alice_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
exact: (\negligible[ f_guess_V2 by f_guess_V2_advantageE ]
          alice_trace_chain_admissible_at).
Qed.

(* Under the two fields of N, the decrypting predictor's Bob-side reduction
   adversary is eventually outside the class: the parallel-track
   counterexample is excluded by the asymptotic value the headline is stated
   at, not by the information-theoretic term. *)
Corollary decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (assumption k)
      (bob_trace_adversary (distinguisher_of_predictor
         (bob_decrypt_predictor (I:=I k)))) = false.
Proof.
have [N1 HN1] := size_negligible N 1%N; have [N2 HN2] := adv_negligible N 1%N.
exists (maxn (maxn N1 N2) 1) => k.
rewrite !gtn_max => /andP[/andP[Hk1 Hk2] Hk3].
have Hk0 : (0 < k%:R :> R) by rewrite ltr0n ltnW.
move: (HN1 k Hk1) (HN2 k Hk2); rewrite !expr1 => Hinv' Heps'.
have Hhalf : (k%:R : R)^-1 <= 1 - (k%:R : R)^-1.
  rewrite lerBrDr -div1r -mulrDl ler_pdivrMr // mul1r -(natrD R 1 1).
  by rewrite ler_nat.
apply: (decrypt_reduction_admissibleF (I:=I k)).
apply: lt_le_trans Heps' _; apply: le_trans Hhalf _.
by rewrite lerD2l lerN2 ltW.
Qed.

(* A family of Boolean tests of Alice's executed trace, one at each security
   parameter.  A test is what an indistinguishability statement quantifies
   over, where the predictor family above is what a guessing statement
   quantifies over, so the family declared here is a second observer of the
   same sequence and not a specialisation of the first.  The [clear implicits]
   directive keeps the security parameter an explicit argument, which is what
   makes trace_distinguishers k the test at k rather than the family read at
   an input. *)
Variable trace_distinguishers : forall k,
  distinguisher (plain (scheme_AHE (I k)) * plain (scheme_AHE (I k))
                 * alice_traceT (I k))%type.
Arguments trace_distinguishers : clear implicits.

(* The two class premises of the statement below: at every security parameter
   the class of the assumption made there admits the two reduction adversaries
   the k-th test induces.  They are to the indistinguishability statement what
   bob_admissible and charlie_admissible are to the guessing statement, and
   they are premises for the same reason, restricting the adversaries a test
   induces rather than the sequence. *)
Hypothesis bob_admissible_distinguisher : forall k,
  indcpa_admissible (assumption k)
    (bob_trace_adversary (trace_distinguishers k)).
Hypothesis charlie_admissible_distinguisher : forall k,
  indcpa_admissible (assumption k)
    (charlie_trace_adversary (trace_distinguishers k)).

(* The dictionary of the trace simulation argument at the k-th instance.  It
   is a second dictionary rather than alice_claims_admissible_at because that
   one
   is pinned to the test a predictor induces, and a statement made at the
   predictor's own test would be strictly weaker than indistinguishability,
   which quantifies over every test.  It is a named constant for the same
   reason as the other, canonical inference keying on the head constant of the
   family.
   Naming: parallels [alice_claims_admissible_at] with [sim] naming the
   argument the dictionary is read for. *)
Definition alice_sim_claims_at (k : nat) : alice_label -> claim R :=
  alice_claim_admissible (assumption k)
    (hop_tuple_distinguisher (trace_distinguishers k)).

(* Every label of that dictionary costs a negligible family along the
   sequence, the two hop labels the class epsilon and the terminal label
   the inverse plaintext cardinality.  The terminal branch is owed although
   the program below never spends that label, the condition quantifying over
   the whole label type rather than over the labels one program names.
   Naming: intentional; mirrors [alice_label_negligible_at], with [sim] naming
   the argument the dictionary is read for. *)
Lemma alice_sim_label_negligible_at (l : alice_label) :
  negligible_fun (fun k => claim_cost (alice_sim_claims_at k l)).
Proof.
case: l.
- exact: adv_negligible N.
- exact: adv_negligible N.
- exact: size_negligible N.
Qed.

Canonical alice_sim_claims_negligible :=
  NegligibleClaims alice_sim_claims_at alice_sim_label_negligible_at.

(* The trace simulation program at the k-th instance, the value of the family
   monad the terminal below reads.  The return type names the dictionary,
   which is what lets canonical inference find the negligibility of the two
   labels the program spends.
   Naming: extends [alice_trace_sim_chain_admissible] with the [_at] token
   naming the instance the program is read at. *)
Definition alice_trace_sim_chain_admissible_at (k : nat)
    : chain_result (alice_sim_claims_at k) :=
  alice_trace_sim_chain_admissible
    (bob_admissible_distinguisher k) (charlie_admissible_distinguisher k).

(* The trace simulation distance function used in the sequence theorem: the
   distance the k-th Boolean test sees at the k-th instance between Alice's
   executed trace and the simulation. *)
Definition f_sim_advantage k : R :=
  alice_trace_sim_advantage (trace_distinguishers k).

(* The quantity the theorem below is about is the advantage that program
   bounds, the two games it joins being the executed trace and the
   simulation. *)
Lemma f_sim_advantageE k :
  f_sim_advantage k = result_advantage (alice_trace_sim_chain_admissible_at k).
Proof.
rewrite /f_sim_advantage /alice_trace_sim_chain_admissible_at.
exact: (alice_trace_sim_advantageE
          (bob_admissible_distinguisher k)
          (charlie_admissible_distinguisher k)).
Qed.

(* Along a sequence of DSDP instances, every family of Boolean tests of
   Alice's executed trace whose two induced reduction adversaries the
   assumption at k admits separates that trace from the simulation by a
   negligible amount.  This is computational indistinguishability of Alice's
   view from the simulation, the form a simulation-based secrecy claim takes
   once the parameter is free to grow, and the guessing statement above is a
   claim about one predictor where this one is a claim about every test.
   It is the second reading of alice_trace_sim_chain_admissible: that program
   spends the two hop labels and nothing else, so the whole distance is the
   class-epsilon family and no plaintext-size term enters, which is what
   separates this bound from the guessing bound.
   Naming: [_negligible] marks a negligible_fun theorem over the named
   quantity family, paired with that family's [_advantageE] identification
   lemma, as at [alice_trace_guess_V2_negligible]. *)
Theorem alice_trace_sim_advantage_negligible :
  negligible_fun f_sim_advantage.
Proof.
exact: (\negligible[ f_sim_advantage by f_sim_advantageE ]
          alice_trace_sim_chain_admissible_at).
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
  #|plain (scheme_AHE (idealized_instance k))| = ((k.+2) ^ k.+2)%N.
Proof. by rewrite card_ord Zp_cast // -{1}(expn0 k.+2) ltn_exp2l. Qed.

(* The unconditional term of every bound along the witness sequence: its
   plaintext spaces grow as (k+2)^(k+2), so their inverse cardinalities fall
   below every inverse polynomial. *)
Let idealized_size_negligible :
  negligible_fun (fun k =>
    (#|plain (scheme_AHE (idealized_instance k))|%:R : R)^-1).
Proof.
apply: negligible_fun_le negligible_fun_inv_expnn => k.
by rewrite card_plain_idealized.
Qed.

(* The witness sequence: the idealized instances above, under the
   cipher-constant assumption of indcpa_game.v at each k. *)
Definition idealized_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := idealized_instance ;
  sequence_assumption := fun k =>
    cipher_constant_assumption (idealized_instance k) |}.

(* The two negligibility facts about the witness sequence, discharged rather
   than assumed.  Its assumed advantage is zero at every k, so the whole
   content of a bound along it is the unconditional 1/#|plain| term. *)
Definition idealized_asymptotic :
    dsdp_asymptotic idealized_instance_sequence :=
  @Build_dsdp_asymptotic R idealized_instance_sequence
    idealized_size_negligible negligible_fun_cst0.

(* The constant predictor's distinguisher reads only the state slot, so the
   Bob-key reduction adversary ignores the challenge ciphertext and the
   cipher-constant class admits it. *)
Lemma idealized_bob_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (bob_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of idealized_bob_cipher_constant. *)
Lemma idealized_charlie_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (charlie_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The headline's hypotheses hold together at least once: the witness
   sequence has an asymptotic value, and the constant predictor's two
   reduction adversaries are in the cipher-constant class at every k. *)
Corollary alice_trace_guess_V2_idealized_negligible :
  negligible_fun (fun k =>
    alice_trace_guess_V2_pr (R:=R) (I:=idealized_instance k) (fun _ => 0)).
Proof.
apply: (alice_trace_guess_V2_negligible idealized_asymptotic
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

(* The inverse plaintext cardinality at the composite modulus. *)
Let inv_pq_cardE : ((p * q)%N%:R : R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_pq. Qed.

Variables (v1 u1 u2 u3 : plain AHE).

(* Charlie's weight is invertible.  This is what makes the DSDP solution
   fiber a bijective image of the plaintext space, and so what turns the
   leaked output into the 1/(p * q) term of the bound below rather than into
   a determination of Bob's input. *)
Hypothesis u3_unit : u3 \is a GRing.unit.

Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (rb2 rc2 : renc_paillier p q).

(* The DSDP instance this section's bounds are read at: the Paillier IND-CPA
   scheme at this modulus carrying the weights, keys and coins above.  It is
   the value that lets a source theorem stated over one instance be read
   here without restating it. *)
Definition paillier_fixed_instance : dsdp_instance := {|
  inst_scheme       := paillier_indcpa_scheme p_gt1 q_gt1 ;
  inst_v1 := v1 ; inst_u1 := u1 ; inst_u2 := u2 ;
  inst_u3 := u3 ; inst_u3_unit := u3_unit ;
  inst_dk_a := dk_a ; inst_dk_b := dk_b ; inst_dk_c := dk_c ;
  inst_rb2 := rb2 ; inst_rc2 := rc2 |}.

(* Decisional composite residuosity at modulus p q, the only computational
   premise the Paillier bounds of this section are read at.  The IND-CPA
   assumption they consume is derived from it by paillier_indcpa_assumption
   of paillier_indcpa_scheme.v, so those bounds are stated in residuosity
   epsilons rather than in an advantage left free. *)
Variable dcr : dcr_assumption (R:=R) p q.

(* A predictor of Bob's input reading Alice's executed trace at this
   instance, with the two class premises the trace bound below is conditional
   on: the class the residuosity record induces admits the two reduction
   adversaries that predictor induces.  The restriction lands on those two
   adversaries and never on the predictor itself, which is what leaves the
   trace-decrypting predictor outside the bound rather than inside it. *)
Variable predict :
  predictor paillier_fixed_instance (alice_traceT paillier_fixed_instance).
Hypothesis bob_admissible :
  indcpa_admissible (paillier_indcpa_assumption p_gt1 q_gt1 dcr)
    (bob_trace_adversary (I:=paillier_fixed_instance)
       (distinguisher_of_predictor predict)).
Hypothesis charlie_admissible :
  indcpa_admissible (paillier_indcpa_assumption p_gt1 q_gt1 dcr)
    (charlie_trace_adversary (I:=paillier_fixed_instance)
       (distinguisher_of_predictor predict)).

(* The epsilon the derived IND-CPA assumption is stated at is twice the
   residuosity epsilon, one residuosity call per hop of the scheme reduction.
   It is the conversion that restates a Paillier bound in decisional
   composite residuosity epsilons. *)
Lemma paillier_epsilon_dcrE :
  indcpa_assumption_epsilon (paillier_indcpa_assumption p_gt1 q_gt1 dcr)
  = 2 * dcr_epsilon dcr.
Proof. by []. Qed.

(* Both ciphertext hops of the trace bound written in residuosity epsilons,
   on the two class premises: the bound spends an IND-CPA epsilon at Bob's
   key and at Charlie's, and the scheme reduction costs two residuosity calls
   per key, hence 4 eps.  The first summand is unconditional, the residue the
   leaked output concedes along the DSDP solution fiber; the second is
   conditional on the residuosity record. *)
Corollary paillier_trace_guess_V2_admissible_le :
  alice_trace_guess_V2_pr (I:=paillier_fixed_instance) predict
  <= (#|plain AHE|%:R : R)^-1 + 4 * dcr_epsilon dcr.
Proof.
have := alice_trace_guess_V2_admissible_le (I:=paillier_fixed_instance)
          bob_admissible charlie_admissible.
by rewrite paillier_epsilon_dcrE mulrA -(natrM R 2 2).
Qed.

(* The same bound with its unconditional summand read as 1/(p * q), the
   counting axis's reading of the cardinality the two axes share. *)
Corollary paillier_trace_guess_V2_admissible_pq_le :
  alice_trace_guess_V2_pr (I:=paillier_fixed_instance) predict
  <= ((p * q)%N%:R : R)^-1 + 4 * dcr_epsilon dcr.
Proof.
rewrite inv_pq_cardE; exact: paillier_trace_guess_V2_admissible_le.
Qed.

(* The class premises of the bound above are satisfiable at a residuosity
   record that exists: at the challenge-ignoring assumption of
   residuosity_game.v, whose epsilon is zero and proved, the constant
   predictor's Bob-key reduction adversary is in the derived class.  A
   statement restricted to that class is therefore not empty for want of a
   record and a predictor to read it at.  The decrypting predictor stays
   outside the class at that record, by decrypt_reduction_admissibleF at
   epsilon zero.
   Naming: [paillier_dcr_admissible] is the class the conclusion asserts,
   [bob] the key its adversary attacks, and [decide_constant] the residuosity
   record it is read at, after idealized_bob_cipher_constant. *)
Lemma paillier_bob_decide_constant_admissible :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R) 'Z_((p * q) * (p * q)) (p * q)
       card_renc_paillier)
    (bob_trace_adversary (I:=paillier_fixed_instance)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of paillier_bob_decide_constant_admissible,
   which the bound above needs beside it: both class premises hold at the
   same record and the same predictor.
   Naming: the Charlie-key spelling of
   paillier_bob_decide_constant_admissible. *)
Lemma paillier_charlie_decide_constant_admissible :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R) 'Z_((p * q) * (p * q)) (p * q)
       card_renc_paillier)
    (charlie_trace_adversary (I:=paillier_fixed_instance)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
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

(* A decisional composite residuosity record at each modulus p k q k, the
   per-k form of the section's only computational premise.  The IND-CPA
   assumption at k is derived from it by paillier_indcpa_assumption, so the
   sequence below carries no assumed advantage. *)
Variable dcr : forall k, dcr_assumption (R:=R) (p k) (q k).

(* The Paillier instance sequence: the instances above, with the IND-CPA
   assumption derived at each k from dcr k.  It is the value the sequence
   headline is applied at below. *)
Definition paillier_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := paillier_instance ;
  sequence_assumption := fun k =>
    paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k) |}.

(* The assumption every bound along this sequence is read at is the one
   paillier_indcpa_scheme.v derives from dcr k, and at no other record.  The
   equation holds by unfolding, so the identification is a conversion and not
   a rewrite a later statement could route around. *)
Lemma paillier_assumption_at_dcrE k :
  sequence_assumption paillier_instance_sequence k
  = paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k).
Proof. by []. Qed.

(* The epsilon those bounds are stated at is twice the residuosity epsilon at
   k, one residuosity call per hop of the scheme reduction. *)
Lemma paillier_epsilon_at_dcrE k :
  indcpa_assumption_epsilon (sequence_assumption paillier_instance_sequence k)
  = 2 * dcr_epsilon (dcr k).
Proof. by []. Qed.

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

(* The residuosity advantage the assumption sequence assumes is negligible:
   the asymptotic form of decisional composite residuosity along the moduli
   p k q k, and the only computational hypothesis the sequence makes. *)
Hypothesis f_dcr_negligible : negligible_fun (f_dcr_paillier dcr).

(* The two negligibility facts about the Paillier sequence, the unconditional
   one read at the modulus and the assumption-conditional one derived from
   the residuosity hypothesis by doubling. *)
Definition paillier_asymptotic :
    dsdp_asymptotic paillier_instance_sequence :=
  @Build_dsdp_asymptotic R paillier_instance_sequence
    (f_size_paillier_negligible p_gt1 q_gt1 f_pq_negligible)
    (f_adv_paillier_negligible p_gt1 q_gt1 f_dcr_negligible).

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k: the predictor whose
   guessing probability is 1 is excluded by the two negligibility facts
   above, and not by the information-theoretic term of the bound. *)
Corollary paillier_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption paillier_instance_sequence k)
      (bob_trace_adversary (I:=paillier_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=paillier_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF paillier_asymptotic).
Qed.

Variable predict : forall k, predictor (paillier_instance k)
    (alice_traceT (paillier_instance k)).
Arguments predict : clear implicits.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=paillier_instance_sequence) predict).

(* The class of the assumption sequence admits the Bob-side reduction
   adversary induced by every predictor in the sequence.  The class is the
   derived one, which is paillier_dcr_admissible (dcr k) by delta: the
   adversary's two residuosity reductions are classified at k. *)
Hypothesis bob_reduction_admissible : forall k,
  indcpa_admissible (paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k))
    (bob_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

(* The Charlie-side twin of bob_reduction_admissible. *)
Hypothesis charlie_reduction_admissible : forall k,
  indcpa_admissible (paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k))
    (charlie_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

(* The conclusion is negligible_fun of the sequence k |-> Pr_k, where Pr_k
   is the probability that the k-th predictor guesses Bob's input V2 at
   the k-th Paillier instance.

   It follows in three steps.  At each k the two class premises yield the
   bound of alice_trace_guess_V2_admissible_le, Pr_k <= 1/(p k * q k) +
   2 * eps k, with eps k the advantage dcr k assumes.  The two fields of
   paillier_asymptotic make f_size and f_adv negligible,
   f_size through the scheme-side reading of modulus growth as plaintext
   growth.  Those two are the costs the three labels of the program carry, so
   the terminal of the family monad reads the bound off the label list and
   transfers negligibility to f_guess_V2.

   The assumption sequence is derived: eps k is twice the residuosity
   epsilon dcr k assumes, so the whole computational content of the conclusion
   is decisional composite residuosity along the moduli p k q k. *)
Corollary paillier_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
exact: (alice_trace_guess_V2_negligible paillier_asymptotic
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

(* The DSDP instance this section's bounds are read at: the Benaloh IND-CPA
   scheme at this modulus and block size carrying the weights, keys and coins
   above.  It is the value that lets a source theorem stated over one
   instance be read here without restating it. *)
Definition benaloh_fixed_instance : dsdp_instance := {|
  inst_scheme       := benaloh_indcpa_scheme n r_gt1 ;
  inst_v1 := v1 ; inst_u1 := u1 ; inst_u2 := u2 ;
  inst_u3 := u3 ; inst_u3_unit := u3_unit ;
  inst_dk_a := dk_a ; inst_dk_b := dk_b ; inst_dk_c := dk_c ;
  inst_rb2 := rb2 ; inst_rc2 := rc2 |}.

(* r-th residuosity at modulus n, the only computational premise the Benaloh
   bounds of this section are read at.  The IND-CPA assumption they consume
   is derived from it by benaloh_indcpa_assumption of
   benaloh_indcpa_scheme.v, so those bounds are stated in residuosity
   epsilons rather than in an advantage left free. *)
Variable residuosity : benaloh_residuosity_assumption (R:=R) n r.

(* The inverse plaintext cardinality at the Benaloh block size. *)
Let inv_r_cardE : (r%:R : R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_r. Qed.

(* A predictor of Bob's input reading Alice's executed trace at this
   instance, with the two class premises the trace bound below is conditional
   on: the class the residuosity record induces admits the two reduction
   adversaries that predictor induces.  The restriction lands on those two
   adversaries and never on the predictor itself, which is what leaves the
   trace-decrypting predictor outside the bound rather than inside it. *)
Variable predict :
  predictor benaloh_fixed_instance (alice_traceT benaloh_fixed_instance).
Hypothesis bob_admissible :
  indcpa_admissible (benaloh_indcpa_assumption r_gt1 residuosity)
    (bob_trace_adversary (I:=benaloh_fixed_instance)
       (distinguisher_of_predictor predict)).
Hypothesis charlie_admissible :
  indcpa_admissible (benaloh_indcpa_assumption r_gt1 residuosity)
    (charlie_trace_adversary (I:=benaloh_fixed_instance)
       (distinguisher_of_predictor predict)).

(* The epsilon the derived IND-CPA assumption is stated at is twice the
   residuosity epsilon, one residuosity call per hop of the scheme reduction.
   It is the conversion that restates a Benaloh bound in r-th residuosity
   epsilons. *)
Lemma benaloh_epsilon_residuosityE :
  indcpa_assumption_epsilon (benaloh_indcpa_assumption r_gt1 residuosity)
  = 2 * benaloh_residuosity_epsilon residuosity.
Proof. by []. Qed.

(* Both ciphertext hops of the trace bound written in residuosity epsilons,
   on the two class premises: the bound spends an IND-CPA epsilon at Bob's
   key and at Charlie's, and the scheme reduction costs two residuosity calls
   per key, hence 4 eps.  The first summand is unconditional, the residue the
   leaked output concedes along the DSDP solution fiber; the second is
   conditional on the residuosity record. *)
Corollary benaloh_trace_guess_V2_admissible_le :
  alice_trace_guess_V2_pr (I:=benaloh_fixed_instance) predict
  <= (#|plain AHE|%:R : R)^-1 + 4 * benaloh_residuosity_epsilon residuosity.
Proof.
have := alice_trace_guess_V2_admissible_le (I:=benaloh_fixed_instance)
          bob_admissible charlie_admissible.
by rewrite benaloh_epsilon_residuosityE mulrA -(natrM R 2 2).
Qed.

(* The block size as a product of two primes' successors, the form the
   counting axis states its modulus in. *)
Variables (p_minus_2 q_minus_2 : nat).
Hypothesis r_pq : r = (p_minus_2.+2 * q_minus_2.+2)%N.

(* The same bound with its unconditional summand read as 1/(p * q) at that
   block size, the counting axis's reading of the cardinality the two axes
   share. *)
Corollary benaloh_trace_guess_V2_admissible_pq_le :
  alice_trace_guess_V2_pr (I:=benaloh_fixed_instance) predict
  <= ((p_minus_2.+2 * q_minus_2.+2)%N%:R : R)^-1
     + 4 * benaloh_residuosity_epsilon residuosity.
Proof.
rewrite -r_pq inv_r_cardE; exact: benaloh_trace_guess_V2_admissible_le.
Qed.

(* The class premises of the bound above are satisfiable at a residuosity
   record that exists: at the challenge-ignoring assumption of
   residuosity_game.v, whose epsilon is zero and proved, the constant
   predictor's Bob-key reduction adversary is in the derived class.  A
   statement restricted to that class is therefore not empty for want of a
   record and a predictor to read it at.  The decrypting predictor stays
   outside the class at that record, by decrypt_reduction_admissibleF at
   epsilon zero.
   Naming: [benaloh_residuosity_admissible] is the class the conclusion
   asserts, [bob] the key its adversary attacks, and [decide_constant] the
   residuosity record it is read at, after idealized_bob_cipher_constant. *)
Lemma benaloh_bob_decide_constant_admissible :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_n r card_renc_benaloh)
    (bob_trace_adversary (I:=benaloh_fixed_instance)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of benaloh_bob_decide_constant_admissible,
   which the bound above needs beside it: both class premises hold at the
   same record and the same predictor.
   Naming: the Charlie-key spelling of
   benaloh_bob_decide_constant_admissible. *)
Lemma benaloh_charlie_decide_constant_admissible :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_n r card_renc_benaloh)
    (charlie_trace_adversary (I:=benaloh_fixed_instance)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
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

(* An r-th residuosity record at each modulus n k and exponent r k, the per-k
   form of the section's only computational premise.  The IND-CPA assumption
   at k is derived from it by benaloh_indcpa_assumption, so the sequence
   below carries no assumed advantage. *)
Variable residuosity :
  forall k, benaloh_residuosity_assumption (R:=R) (n k) (r k).

(* The Benaloh instance sequence: the instances above, with the IND-CPA
   assumption derived at each k from residuosity k.  It is the value the
   sequence headline is applied at below. *)
Definition benaloh_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := benaloh_instance ;
  sequence_assumption := fun k =>
    benaloh_indcpa_assumption (r_gt1 k) (residuosity k) |}.

(* The assumption every bound along this sequence is read at is the one
   benaloh_indcpa_scheme.v derives from residuosity k, and at no other
   record.  The equation holds by unfolding, so the identification is a
   conversion and not a rewrite a later statement could route around. *)
Lemma benaloh_assumption_at_residuosityE k :
  sequence_assumption benaloh_instance_sequence k
  = benaloh_indcpa_assumption (r_gt1 k) (residuosity k).
Proof. by []. Qed.

(* The epsilon those bounds are stated at is twice the residuosity epsilon at
   k, one residuosity call per hop of the scheme reduction. *)
Lemma benaloh_epsilon_at_residuosityE k :
  indcpa_assumption_epsilon (sequence_assumption benaloh_instance_sequence k)
  = 2 * benaloh_residuosity_epsilon (residuosity k).
Proof. by []. Qed.

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

(* The residuosity advantage the assumption sequence assumes is negligible:
   the asymptotic form of r-th residuosity along the moduli n k, and the only
   computational hypothesis the sequence makes. *)
Hypothesis f_residuosity_negligible :
  negligible_fun (f_residuosity_benaloh residuosity).

(* The two negligibility facts about the Benaloh sequence, the unconditional
   one read at the block size and the assumption-conditional one derived from
   the residuosity hypothesis by doubling. *)
Definition benaloh_asymptotic :
    dsdp_asymptotic benaloh_instance_sequence :=
  @Build_dsdp_asymptotic R benaloh_instance_sequence
    (f_size_benaloh_negligible n r_gt1 f_r_negligible)
    (f_adv_benaloh_negligible r_gt1 f_residuosity_negligible).

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k: the predictor whose
   guessing probability is 1 is excluded by the two negligibility facts
   above, and not by the information-theoretic term of the bound. *)
Corollary benaloh_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
      (bob_trace_adversary (I:=benaloh_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=benaloh_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF benaloh_asymptotic).
Qed.

Variable predict : forall k, predictor (benaloh_instance k)
    (alice_traceT (benaloh_instance k)).
Arguments predict : clear implicits.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=benaloh_instance_sequence) predict).

(* The class of the assumption sequence admits the Bob-side reduction
   adversary induced by every predictor in the sequence.  The class is the
   derived one, which is benaloh_residuosity_admissible (residuosity k) by
   delta: the adversary's two residuosity reductions are classified at k. *)
Hypothesis bob_reduction_admissible : forall k,
  indcpa_admissible (benaloh_indcpa_assumption (r_gt1 k) (residuosity k))
    (bob_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

(* The Charlie-side twin of bob_reduction_admissible. *)
Hypothesis charlie_reduction_admissible : forall k,
  indcpa_admissible (benaloh_indcpa_assumption (r_gt1 k) (residuosity k))
    (charlie_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

(* The conclusion is negligible_fun of the sequence k |-> Pr_k, where Pr_k
   is the probability that the k-th predictor guesses Bob's input V2 at
   the k-th Benaloh instance.

   It follows in three steps.  At each k the two class premises yield the
   bound of alice_trace_guess_V2_admissible_le, Pr_k <= 1/(r k) + 2 * eps k,
   with eps k the advantage residuosity k assumes.  The two fields of
   benaloh_asymptotic make f_size and f_adv negligible, f_size
   through the scheme-side reading of block-size growth as plaintext growth.
   Those two are the costs the three labels of the program carry, so the
   terminal of the family monad reads the bound off the label list and
   transfers negligibility to f_guess_V2.

   The assumption sequence is derived: eps k is twice the residuosity epsilon
   residuosity k assumes, so the whole computational content of the conclusion
   is r-th residuosity along the moduli n k. *)
Corollary benaloh_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
exact: (alice_trace_guess_V2_negligible benaloh_asymptotic
          bob_reduction_admissible charlie_reduction_admissible).
Qed.

End benaloh_dsdp_instance_sequence.
