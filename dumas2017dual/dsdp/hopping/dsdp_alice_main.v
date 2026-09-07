From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba.
Require Import extra_proba extra_entropy.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_program dsdp_pismc.
Require Import negligible epshop epshop_sequence.
Require Import indcpa_game.
Require Import dsdp_instance.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy: the chain programs and their readings      *)
(*                                                                            *)
(* Alice is the corrupted party of a DSDP run at one instance of              *)
(* dsdp_instance.v.  What her view leaves her about Bob's input is measured   *)
(* by a sequence of games, written here as epsHop programs. The file has four *)
(* regions: the lemmas a program line is allowed to name, the programs at one *)
(* instance, the statements read off them, and the same argument along a      *)
(* sequence of instances indexed by a security parameter.                     *)
(*                                                                            *)
(* Before the programs sit the facts they cite.  bob_challenge_adversary and  *)
(* charlie_challenge_adversary turn a test on Alice's hopping tuple into an   *)
(* IND-CPA adversary at Bob's key and at Charlie's, and hop0_advantageE and   *)
(* hop1_advantageE identify the gap each ciphertext replacement spans with    *)
(* the advantage of the corresponding reduction, so a hop line spends one     *)
(* key's assumption and no more.  accept_trace_tupleE and                     *)
(* accept_trace_ideal_tupleE carry a test between Alice's executed trace and  *)
(* her hopping tuple at either end of a trace program, at no loss, which is   *)
(* what lets the interpreter's own run stand as the first game.               *)
(* all_zero_game_V2_le_invm bounds the all-zero game by the inverse           *)
(* plaintext count: the one term of every total that rests on no              *)
(* computational assumption, the mass the leaked output leaves along the DSDP *)
(* solution fiber.  alice_claim and alice_claim_admissible are the two        *)
(* dictionaries a program is read at, the first charging a hop at the         *)
(* advantage its own reduction shows, the second at the epsilon an            *)
(* adversary-class assumption promises.                                       *)
(*                                                                            *)
(* Two programs follow, each charging a hop at the advantage its own          *)
(* reduction shows, and both opening at the trace the interpreter hands       *)
(* Alice when it runs the protocol.  alice_trace_sim_chain loses the two      *)
(* IND-CPA advantages and nothing else.  alice_trace_chain adds the fiber     *)
(* term and returns one over the plaintext count plus those two advantages.   *)
(*                                                                            *)
(* The readings follow.  alice_sim_advantage_le and                           *)
(* alice_trace_sim_advantage_le bound what a Boolean test sees between the    *)
(* real and the simulated law; alice_tuple_guess_V2_le and                    *)
(* alice_trace_guess_V2_le bound what a predictor recovers of Bob's input.    *)
(* The tail sections restate the trace bounds at the raw interpreter trace    *)
(* and at a sampled re-encryption coin, and decrypt_bob_epsilon_ge places     *)
(* the class premises of the class-conditional bounds where they cannot be    *)
(* dropped: a predictor holding Bob's private key induces a reduction of      *)
(* advantage at least 1 - 1/#|plain|.                                         *)
(*                                                                            *)
(* The abstract form of that obstruction, in indcpa_game.v, reaches the value *)
(* 1 instead, because it lets the adversary choose a nonzero challenge        *)
(* plaintext. Here the challenge plaintext is fixed by the protocol to Bob's  *)
(* uniformly distributed input, and the zero branch still succeeds on a fiber *)
(* of mass 1/#|plain|. The decrypting counterexample is the other half of the *)
(* same point: decrypt_guess_prE puts the guessing probability at 1 for the   *)
(* predictor that decrypts Bob's ciphertext off the trace, and                *)
(* decrypt_reduction_admissible_eventuallyF shows that the two negligibility  *)
(* facts of the sequence eventually force that predictor's reduction          *)
(* adversary out of the class.                                                *)
(*                                                                            *)
(* The last region reads the same two trace arguments along a sequence of     *)
(* instances, with both ciphertext replacements charged at the epsilon an     *)
(* adversary-class assumption promises rather than at the advantage each      *)
(* reduction shows.  Those two class-conditional programs are written         *)
(* inline under the terminal that reads them, one for the guessing            *)
(* argument and one for the simulation argument, so the class-conditional     *)
(* program text lives at the sequence alone:                                  *)
(* alice_trace_guess_V2_admissible_le is the guessing bound at one            *)
(* instance, read off the sequence that repeats it, and                       *)
(* alice_trace_guess_V2_admissible_pq_le restates that bound at a plaintext   *)
(* space of size p * q.                                                       *)
(*                                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(* Before the programs                                                        *)
(*                                                                            *)
(*   bob_challenge_adversary == the IND-CPA adversary at Bob's key built from *)
(*                              a test on Alice's hopping tuple               *)
(* charlie_challenge_adversary == its Charlie-key counterpart                 *)
(*      hop0_real_challengeE == the real experiment read as the real bit of   *)
(*                              the Bob-key challenge                         *)
(*      hop0_zero_challengeE == the Bob-zero experiment read as the zero bit  *)
(*                              of that challenge                             *)
(*          hop0_advantageE == the gap between them is the Bob-key advantage  *)
(*      hop1_real_challengeE == the Bob-zero experiment read as the real bit  *)
(*                              of the Charlie-key challenge                  *)
(*      hop1_zero_challengeE == the all-zero experiment read as its zero bit  *)
(*          hop1_advantageE == the gap between them is the Charlie-key        *)
(*                              advantage                                     *)
(*         guess_V2_acceptE == a predictor's success probability is the       *)
(*                              acceptance probability of its distinguisher   *)
(*   all_zero_game_V2_le_invm == the all-zero game is at most the inverse     *)
(*                              plaintext count                               *)
(*             alice_idealE == the ideal law is the all-zero experiment       *)
(*   hop_tuple_distinguisher == a trace test lifted to the hopping tuple      *)
(*       bob_trace_adversary == the Bob-key reduction of a trace test         *)
(*   charlie_trace_adversary == its Charlie-key counterpart                   *)
(*       accept_trace_tupleE == a trace test accepts as often as its lift     *)
(*  accept_trace_ideal_tupleE == the same at the simulated trace              *)
(*   alice_trace_guess_V2_pr == the probability a trace predictor returns     *)
(*                              Bob's input                                   *)
(* bob_trace_predictor_epsilon == the Bob-key advantage of a trace            *)
(*                              predictor's reduction                         *)
(* charlie_trace_predictor_epsilon == its Charlie-key counterpart             *)
(*              alice_label == the three labels: the two IND-CPA hops and     *)
(*                              the fiber term                                *)
(*              alice_claim == what each label claims at its own advantage    *)
(*   alice_claim_admissible == what each label claims at a class epsilon      *)
(*             alice_totalE == the loss of alice_trace_chain in the order     *)
(*                              its bound reads it                            *)
(*  alice_admissible_totalE == the same for a class-conditional total         *)
(*                                                                            *)
(* The programs                                                               *)
(*                                                                            *)
(*        alice_trace_chain == the two ciphertext replacements at the         *)
(*                              executed trace, with the fiber term added     *)
(*    alice_trace_sim_chain == the executed trace against the simulated       *)
(*                              trace, losing the two advantages              *)
(*                                                                            *)
(* The readings                                                               *)
(*                                                                            *)
(*   alice_sim_advantage_le == the simulation bound at the hopping tuple      *)
(*   alice_tuple_guess_V2_le == the guessing bound at the hopping tuple       *)
(* alice_trace_sim_advantage_le == the simulation bound at the executed       *)
(*                              trace                                         *)
(*  alice_trace_sim_advantage == the distance a trace test sees               *)
(*   alice_trace_guess_V2_le == the guessing bound at the executed trace      *)
(*    decrypt_bob_epsilon_ge == a key-holding predictor forces the Bob-key    *)
(*                              advantage above 1 - 1/#|plain|                *)
(* decrypt_reduction_admissibleF == a small promised epsilon rejects that     *)
(*                              reduction                                     *)
(* decrypt_guess_V2_premise_free_lt == the class premises cannot be dropped   *)
(* alice_raw_trace_sim_advantage_le == the simulation bound at the raw        *)
(*                              interpreter trace                             *)
(* alice_raw_trace_guess_V2_le == the guessing bound there                    *)
(*                                                                            *)
(* Along a sequence of instances                                              *)
(*                                                                            *)
(*                f_guess_V2 == the trace guessing-probability sequence       *)
(* alice_claims_admissible_at k ==                                            *)
(*                              the dictionary of the class-conditional       *)
(*                              guessing argument at the k-th instance        *)
(* alice_label_negligible_at == every label of that dictionary has a loss     *)
(*                              negligible along the sequence                 *)
(* alice_claims_admissible_negligible ==                                      *)
(*                              that dictionary registered as a               *)
(*                              negligibleClaims                              *)
(*     f_guess_V2_advantageE == the guessing sequence read as the distance of *)
(*                              the trace game from the zero game             *)
(* alice_trace_guess_V2_negligible ==                                         *)
(*                              the trace guessing sequence is negligible     *)
(*                              under the two class premises                  *)
(*            f_guess_V2_le k == the bound the same program returns at k      *)
(* decrypt_reduction_admissible_eventuallyF ==                                *)
(*                              an asymptotic value for the sequence          *)
(*                              eventually rejects the decrypting             *)
(*                              predictor's reduction adversary               *)
(*      alice_sim_claims_at k == the dictionary of the trace simulation       *)
(*                              argument at the k-th instance                 *)
(* alice_sim_label_negligible_at ==                                           *)
(*                              every label of that dictionary has a loss     *)
(*                              negligible along the sequence                 *)
(* alice_sim_claims_negligible ==                                             *)
(*                              that dictionary registered as a               *)
(*                              negligibleClaims                              *)
(*           f_sim_advantage == the trace simulation distance sequence        *)
(*          f_sim_advantageE == that distance read as the gap between the     *)
(*                              executed trace and the simulated trace        *)
(* alice_trace_sim_advantage_negligible ==                                    *)
(*                              the trace simulation distance sequence is     *)
(*                              negligible under the two class premises       *)
(* alice_trace_guess_V2_admissible_le ==                                      *)
(*                              the guessing bound at one instance, at one    *)
(*                              class epsilon                                 *)
(* alice_trace_guess_V2_admissible_pq_le ==                                   *)
(*                              the same bound at a plaintext space of size   *)
(*                              p * q                                         *)
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
Local Open Scope proc_scope.
Local Open Scope sproc_scope.

Section dsdp_alice_main.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names this development gives them.  They
   are the scheme data, Alice's input, the three weights, the three keys and
   the key table. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation card_renc := (scheme_card_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_b := (inst_dk_b I).
Local Notation dk_c := (inst_dk_c I).
Local Notation pkey_of_dk := (inst_pkey_of_party I).

(* The game layer at the instance's scheme, which the coercion supplies. *)
Local Notation indcpa_adversary := (indcpa_adversary (R:=R) I).
Local Notation indcpa_success_real := (indcpa_success_real (R:=R) (S:=I)).
Local Notation indcpa_success_zero := (indcpa_success_zero (R:=R) (S:=I)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation indcpa_fdist_acceptE := (indcpa_fdist_acceptE (R:=R) (S:=I)).
Local Notation predictor := (predictor I).

(* The declarations of dsdp_alice_hop_secrecy.v and dsdp_alice_trace_link.v
   take these parameters explicitly.  Each abbreviation pins them once, and
   the shadowing is not recursive. *)
Local Notation alice_sampleT := (alice_sampleT I).
Local Notation alice_sample_fdist := (alice_sample_fdist (R:=R) I).
Local Notation alice_hop_tupleT := (alice_hop_tupleT I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation RB1 := (RB1 (R:=R) (I:=I)).
Local Notation RC1 := (RC1 (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation alice_tuple_bob_zero := (alice_tuple_bob_zero (R:=R) (I:=I)).
Local Notation alice_tuple_all_zero := (alice_tuple_all_zero (R:=R) (I:=I)).
Local Notation bob_pkey := (bob_pkey I).
Local Notation charlie_pkey := (charlie_pkey I).
Local Notation hop0_stateT := (hop0_stateT I).
Local Notation hop1_stateT := (hop1_stateT I).
Local Notation Hop0State := (Hop0State (R:=R) (I:=I)).
Local Notation Hop1State := (Hop1State (R:=R) (I:=I)).
Local Notation hop0_assemble := (hop0_assemble (I:=I)).
Local Notation hop1_assemble := (hop1_assemble (I:=I)).
Local Notation hop0_state_prodE := (hop0_state_prodE (R:=R) I).
Local Notation hop1_state_prodE := (hop1_state_prodE (R:=R) I).
Local Notation alice_simulator := (alice_simulator (R:=R) (I:=I)).
Local Notation alice_ideal := (alice_ideal (R:=R) I).
Local Notation all_zero_guess_V2_le_invm :=
  (all_zero_guess_V2_le_invm (R:=R) (I:=I)).
Local Notation dsdp_alice_hop_tuple_cond_sim :=
  (dsdp_alice_hop_tuple_cond_sim (R:=R) (I:=I)).
Local Notation trace_dataT := (trace_dataT I).
Local Notation alice_traceT := (alice_traceT I).
Local Notation alice_trace_of_hop_tuple := (alice_trace_of_hop_tuple (I:=I)).
Local Notation dsdp_protocol := (dsdp_protocol (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).
Local Notation alice_trace_realE := (alice_trace_realE (R:=R) I).
Local Notation alice_trace_ideal := (alice_trace_ideal (R:=R) I).
Local Notation alice_trace_idealE := (alice_trace_idealE (R:=R) I).


(* A distinguisher D is a Boolean test on one sampled joint value.  This value
   contains V2 and V3 together with one of the three hopping tuples.
   Returning true means that D accepts the sampled value.  Its acceptance
   probability on a joint law G is the probability, over x sampled from G,
   that D x is true:

     accept D G = Pr G [set x | D x].

   ## bob_challenge_adversary

   bob_challenge_adversary D packages the following procedure:

     1. Sample (V2, V3, R2, R3, RA1, RA2, RC1, RB2, RC2).
     2. Select V2 as the real challenge plaintext.  The experiment returns a
        challenge ciphertext ch encrypting either V2 or zero under Bob's key.
     3. Compute Sout, use ch as Bob's ciphertext, and use RC1 and RC2 to
        construct Charlie's ciphertext and his re-encryption.
     4. Call D on the resulting joint value, shown flattened as

          (V2, V3, R2, R3, RA1, RA2, Sout, ch,
           enc charlie_pkey V3 (rand_of_renc RC1),
           enc alice_pkey (Sout - u1 * v1 + R2 + R3) (rand_of_renc RC2)),

        and return its Boolean result.

   It is called a "reduction" because it converts a distinguishing problem
   into a security problem. The original problem is:

       Can D distinguish the protocol's hop-0 distribution from its hop-1
       distribution?

   The encryption-security problem is:

       Can an IND-CPA adversary distinguish an encryption of V2 from an
       encryption of zero under Bob's key?

   That advantage is indcpa_epsilon pk adv.

   The construction:

       D |--> bob_challenge_adversary(D)

   D accepts concrete (v_2,v_3,h) and returns a Boolean.
   The type does not require D to inspect only the challenged ciphertext.
   It may inspect every component of such a tuple. So A_i(D) wrap it
   to provide the assembled concrete values from the stateful experiment.

   turns any protocol distinguisher D into such an encryption adversary.
   The correspondence theorems prove

     accept D (`p_ [% V2, V3, alice_tuple_real])
       = indcpa_success_real
           bob_pkey (bob_challenge_adversary D),

   and

     accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
       = indcpa_success_zero
           bob_pkey (bob_challenge_adversary D).

   Therefore, the gap between the two experiments equals the real-or-zero
   advantage:

     `| accept D (`p_ [% V2, V3, alice_tuple_real])
        - accept D (`p_ [% V2, V3, alice_tuple_bob_zero]) |
       = indcpa_epsilon
           bob_pkey (bob_challenge_adversary D).

   In other words, this procedure lets the real and zero experiments
   reproduce the replacement of Bob's ciphertext slot.

      distinguishing the real and the Bob-zero experiment
              |
              | construct bob_challenge_adversary D
              v
      distinguishing Enc(pk_B, V2) and Enc(pk_B, 0)

   The second problem is the one the encryption-security property answers,
   and that is what bounds the first.
   Since D accepts the two honest inputs beside a complete tuple rather than an
   encryption challenge, bob_challenge_adversary D adapts D to the real-or-zero
   adversary interface.  It builds the joint value around the challenge
   ciphertext and calls D.  The correspondence theorems prove that D's gap
   between the real and the Bob-zero experiment equals the real-or-zero
   advantage of the resulting encryption adversary.

   ## charlie_challenge_adversary

   charlie_challenge_adversary D packages the following procedure:

     1. Sample

          (V2, V3, R2, R3, RA1, RA2, bob_zero_cipher),

        where bob_zero_cipher is Bob's encryption of zero.
     2. Select V3 as the real challenge plaintext.  The experiment returns a
        challenge ciphertext ch encrypting either V3 or zero under Charlie's
        key.
     3. Compute Sout and use ch as Charlie's ciphertext.
     4. Call D on the resulting joint value, shown flattened as

          (V2, V3, R2, R3, RA1, RA2, Sout, bob_zero_cipher, ch),

        and return its Boolean result.

   This procedure lets the real and zero experiments reproduce the
   replacement of Charlie's ciphertext slot.  The two correspondence theorems
   state

     accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
       = indcpa_success_real
           charlie_pkey (charlie_challenge_adversary D),

     accept D (`p_ [% V2, V3, alice_tuple_all_zero])
       = indcpa_success_zero
           charlie_pkey (charlie_challenge_adversary D).

   Therefore hop1_advantageE proves

     `| accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
        - accept D (`p_ [% V2, V3, alice_tuple_all_zero]) |
       = indcpa_epsilon
           charlie_pkey (charlie_challenge_adversary D).

   bob_challenge_adversary D and charlie_challenge_adversary D are adversary
   records supplied to
   the real and zero experiments.  They are not themselves complete
   experiments. *)

(* The IND-CPA adversary built from D at Bob's key, over the hop-0 state.  At
   the real bit it runs the real experiment, at the zero bit the Bob-zero
   one. *)
Definition bob_challenge_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
    indcpa_adversary :=
  {| adv_state := hop0_stateT ;
     adv_choose := `p_ Hop0State ;
     adv_plain := fun c => c.1.1.1.1 ;
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.

(* The IND-CPA adversary built from D at Charlie's key, over the hop-1 state.
   At the real bit it runs the Bob-zero experiment, at the zero bit the
   all-zero one. *)
Definition charlie_challenge_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
    indcpa_adversary :=
  {| adv_state := hop1_stateT ;
     adv_choose := `p_ Hop1State ;
     adv_plain := fun c => c.1.1.1.1.2 ;
     adv_decide := fun c ch => D (hop1_assemble c ch) |}.

(* D's acceptance probability on the real experiment equals the real-bit
   success probability of bob_challenge_adversary D against Bob's key. *)
Lemma hop0_real_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_real])
    = indcpa_success_real bob_pkey (bob_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_real]
        = `p_ (protocol_RV Hop0State RB1 bob_pkey
                 (fun c : hop0_stateT => c.1.1.1.1) hop0_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[v2 v3] [r2 r3]] [rb1 rc1 ra1 ra2 rb2 rc2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop0_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_realE.
Qed.

(* D accepts the Bob-zero experiment as often as bob_challenge_adversary D
   succeeds at the zero bit. *)
Lemma hop0_zero_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
    = indcpa_success_zero bob_pkey (bob_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_bob_zero]
        = `p_ (protocol_RV Hop0State RB1 bob_pkey
                 (fun _ : hop0_stateT => 0) hop0_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[v2 v3] [r2 r3]] [rb1 rc1 ra1 ra2 rb2 rc2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop0_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_zeroE.
Qed.

(* The gap D shows between the real and the Bob-zero experiment equals the
   advantage of bob_challenge_adversary D against Bob's key.  Zeroing Bob's
   slot loses exactly one IND-CPA advantage. *)
Lemma hop0_advantageE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| accept D (`p_ [% V2, V3, alice_tuple_real])
     - accept D (`p_ [% V2, V3, alice_tuple_bob_zero]) |
  = indcpa_epsilon bob_pkey (bob_challenge_adversary D).
Proof.
by rewrite /indcpa_epsilon hop0_real_challengeE hop0_zero_challengeE.
Qed.

(* D accepts the Bob-zero experiment as often as charlie_challenge_adversary D
   succeeds at the real bit.  That experiment is the zero side for Bob's key
   and the real side for Charlie's. *)
Lemma hop1_real_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
    = indcpa_success_real charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_bob_zero]
        = `p_ (protocol_RV Hop1State RC1 charlie_pkey
                 (fun c : hop1_stateT => c.1.1.1.1.2) hop1_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[v2 v3] [r2 r3]] [rb1 rc1 ra1 ra2 rb2 rc2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop1_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_realE.
Qed.

(* D's acceptance probability on the all-zero experiment equals the zero-bit
   success probability of charlie_challenge_adversary D against Charlie's
   key. *)
Lemma hop1_zero_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_all_zero])
    = indcpa_success_zero charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_all_zero]
        = `p_ (protocol_RV Hop1State RC1 charlie_pkey
                 (fun _ : hop1_stateT => 0) hop1_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[v2 v3] [r2 r3]] [rb1 rc1 ra1 ra2 rb2 rc2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop1_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_zeroE.
Qed.

(* The gap D shows between the Bob-zero and the all-zero experiment equals the
   advantage of charlie_challenge_adversary D against Charlie's key.  Zeroing
   Charlie's slot loses exactly one IND-CPA advantage. *)
Lemma hop1_advantageE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
     - accept D (`p_ [% V2, V3, alice_tuple_all_zero]) |
  = indcpa_epsilon charlie_pkey (charlie_challenge_adversary D).
Proof.
by rewrite /indcpa_epsilon hop1_real_challengeE hop1_zero_challengeE.
Qed.

(* A predictor matches Bob's input as often as its distinguisher accepts.  The
   observation is a parameter, so one equality serves the three tuple games
   and the trace. *)
Lemma guess_V2_acceptE (O : finType) (predict : predictor O)
    (H : {RV alice_sample_fdist -> O}) :
  Pr alice_sample_fdist
     [set t | (predict `o H) t == V2 t]
  = accept (distinguisher_of_predictor predict) (`p_ [% V2, V3, H]).
Proof.
rewrite acceptE /dist_of_RV Pr_fdistmap_preim.
by apply: eq_bigl => t; rewrite !inE.
Qed.

(* The all-zero game is at most 1/#|plain AHE|, the mass left along the DSDP
   solution fiber.  It is the one term of every total below resting on no
   computational assumption. *)
Lemma all_zero_game_V2_le_invm (predict : predictor alice_hop_tupleT) :
  accept (distinguisher_of_predictor predict)
         (`p_ [% V2, V3, alice_tuple_all_zero])
    <= #|plain AHE|%:R^-1.
Proof. rewrite -guess_V2_acceptE; exact: all_zero_guess_V2_le_invm. Qed.

(* The ideal-world law is the joint law of the two secret inputs and Alice's
   all-zero view.  The ideal world is therefore the all-zero experiment
   itself, and the simulation gap is the two-hop distance. *)
Lemma alice_idealE :
  alice_ideal = `p_ [% V2, V3, alice_tuple_all_zero].
Proof.
apply/fdist_ext => -[[v2 v3] v].
rewrite fdistbindE (bigD1 (v2, v3)) //= big1 ?addr0; last first.
  move=> [w2 w3] Hne; rewrite [X in _ * X]fdistmapE big1 ?mulr0 // => a.
  by rewrite !inE /= xpair_eqE (negbTE Hne).
rewrite [X in _ * X]fdistmapE (big_pred1 v); last first.
  by move=> a; rewrite !inE /= xpair_eqE eqxx.
rewrite !dist_of_RVE [RHS]pfwd1_pairC /unstable.swap /=.
case: (eqVneq `Pr[ [% V2, V3] = (v2, v3) ] 0) => [H0|H0].
  by rewrite H0 mul0r pfwd1_domin_RV1.
rewrite -[RHS]cpr_eqE_mul (dsdp_alice_hop_tuple_cond_sim v H0).
by rewrite mulrC /alice_simulator dist_of_RVE.
Qed.

(* A trace test D lifted to Alice's hopping tuple by alice_trace_of_hop_tuple.
   The lift is what lets the two ciphertext hops bound the trace distance.
     |accept D `p_[% V2, V3, AliceTrace]
      - accept D alice_trace_ideal| *)
Definition hop_tuple_distinguisher
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  D \o (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2)).

(* The IND-CPA adversary at Bob's key induced by a trace test D.  Its
   advantage is the first ciphertext hop of every trace program.
     |accept (hop_tuple_distinguisher D) `p_[% V2, V3, alice_tuple_real]
      - accept (hop_tuple_distinguisher D)
          `p_[% V2, V3, alice_tuple_bob_zero]| *)
Definition bob_trace_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  bob_challenge_adversary (hop_tuple_distinguisher D).

(* The Charlie-key counterpart of bob_trace_adversary.  Its advantage is the
   second ciphertext hop of every trace program.
     |accept (hop_tuple_distinguisher D) `p_[% V2, V3, alice_tuple_bob_zero]
      - accept (hop_tuple_distinguisher D)
          `p_[% V2, V3, alice_tuple_all_zero]| *)
Definition charlie_trace_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  charlie_challenge_adversary (hop_tuple_distinguisher D).

(* A trace test accepts as often as its lift on the hopping tuple.  The step
   loses nothing, so the interpreter's own run stands as the first game. *)
Lemma accept_trace_tupleE
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :
  accept D (`p_ [% V2, V3, AliceTrace])
  = accept (hop_tuple_distinguisher D) (`p_ [% V2, V3, alice_tuple_real]).
Proof.
by rewrite /accept /hop_tuple_distinguisher alice_trace_realE fdistmap_comp.
Qed.

(* A trace test accepts the simulated trace as often as its lift accepts the
   all-zero tuple.  The step loses nothing at the simulator end, as
   accept_trace_tupleE does at the protocol end. *)
Lemma accept_trace_ideal_tupleE
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :
  accept D alice_trace_ideal
  = accept (hop_tuple_distinguisher D)
      (`p_ [% V2, V3, alice_tuple_all_zero]).
Proof.
by rewrite /accept /hop_tuple_distinguisher alice_trace_idealE fdistmap_comp
   alice_idealE.
Qed.

(* The probability that a predictor reading Alice's executed trace returns
   Bob's input.  It is the quantity every trace guessing bound in this file
   bounds, the class-conditional ones included. *)
Definition alice_trace_guess_V2_pr (predict : predictor alice_traceT) : R :=
  Pr alice_sample_fdist [set t | (predict `o AliceTrace) t == V2 t].

(* The advantage against Bob's key of the adversary a trace predictor
   induces. *)
Definition bob_trace_predictor_epsilon (predict : predictor alice_traceT) : R :=
  indcpa_epsilon (pkey_of_dk Bob)
    (bob_trace_adversary (distinguisher_of_predictor predict)).

(* The advantage against Charlie's key of the adversary a trace predictor
   induces. *)
Definition charlie_trace_predictor_epsilon
    (predict : predictor alice_traceT) : R :=
  indcpa_epsilon (pkey_of_dk Charlie)
    (charlie_trace_adversary (distinguisher_of_predictor predict)).

(* The three experiments and the two IND-CPA advantages, under the short names
   the chains read at.  G0, G1 and G2 are the three games, in the order a
   chain visits them. *)
Local Notation G0 := (`p_ [% V2, V3, alice_tuple_real]).
Local Notation G1 := (`p_ [% V2, V3, alice_tuple_bob_zero]).
Local Notation G2 := (`p_ [% V2, V3, alice_tuple_all_zero]).
Local Notation eps_bob D :=
  (indcpa_epsilon bob_pkey (bob_challenge_adversary D)).
Local Notation eps_charlie D :=
  (indcpa_epsilon charlie_pkey (charlie_challenge_adversary D)).

Local Open Scope epshop_scope.

(* The three labels: cpa_bob, cpa_charlie for the two IND-CPA reductions,
   uniform_fiber for the plaintext-count term.  A label says which terms are
   conditional on an assumption, and at which key. *)
Variant alice_label := cpa_bob | cpa_charlie | uniform_fiber.

(* What each label claims: the two games a hop moves between, and the
   advantage it loses.  A step is checked against its label, so each advantage
   is charged to the key its reduction comes from. *)
Definition alice_claim
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type)
    (l : alice_label) : claim R :=
  match l with
  | cpa_bob => Claim (accept D G0) (accept D G1) (eps_bob D)
  | cpa_charlie => Claim (accept D G1) (accept D G2) (eps_charlie D)
  | uniform_fiber => Claim (accept D G2) 0 #|plain AHE|%:R^-1
  end.

(* The class-conditional reading of the same three games, each hop at the
   epsilon the class assumption promises.  A hop here is conditional on the
   class admitting its reduction adversary. *)
Definition alice_claim_admissible (A : indcpa_epsilon_assumption)
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type)
    (l : alice_label) : claim R :=
  match l with
  | cpa_bob =>
      Claim (accept D G0) (accept D G1) (indcpa_assumption_epsilon A)
  | cpa_charlie =>
      Claim (accept D G1) (accept D G2) (indcpa_assumption_epsilon A)
  | uniform_fiber => Claim (accept D G2) 0 #|plain AHE|%:R^-1
  end.

(* The loss alice_trace_chain accumulates, in the order
   alice_tuple_guess_V2_le states it.  The chain spends the two hops before
   the endpoint, so the bound reorders the three terms. *)
Lemma alice_totalE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  eps_bob D + eps_charlie D + #|plain AHE|%:R^-1
  = #|plain AHE|%:R^-1 + eps_bob D + eps_charlie D.
Proof. by rewrite addrAC [X in X + _]addrC. Qed.

(* The loss a chain over alice_claim_admissible accumulates, both hops at one
   class epsilon.  That is where the factor 2 of
   alice_trace_guess_V2_admissible_le comes from. *)
Lemma alice_admissible_totalE (A : indcpa_epsilon_assumption) :
  indcpa_assumption_epsilon A + indcpa_assumption_epsilon A
  + (#|plain AHE|%:R : R)^-1
  = (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A.
Proof. by rewrite mulr_natl mulr2n addrC. Qed.

(* Alice's trace secrecy as one program.  Its first game is the trace the
   interpreter hands Alice when it runs the DSDP protocol at the sampled
   inputs, so the object the argument starts from is the executed protocol
   itself rather than a tuple of values standing for it.  The bound the
   program returns is the statement of alice_trace_guess_V2_le.
   The trace is a deterministic image of the hopping tuple, so the step to
   the tuple loses nothing.  Each of the two ciphertext replacements carries
   the key its advantage is charged to, which is what the class-conditional
   reading and the sequence reading below read off a label.  The last line,
   the term labelled uniform_fiber, is what that theorem adds to the simulation
   bound: the mass the leaked output leaves along the DSDP solution fiber,
   unconditional where the two hop terms are conditional on the IND-CPA
   assumption at one key each. *)
Section alice_trace_chain.
Variable predict : predictor alice_traceT.

(* The predictor's test on the hopping tuple: it accepts when predict guesses
   Bob's input.  Its advantage against the zero game is that guessing
   probability.
     |accept _ `p_[% V2, V3, alice_tuple_real] - 0| *)
Local Notation tuple_distinguisher :=
  (hop_tuple_distinguisher (distinguisher_of_predictor predict)).

Definition alice_trace_chain :=
  \epsilon[ alice_claim tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor predict)
             (`p_ [% V2, V3, AliceTrace])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept tuple_distinguisher G0) by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at one IND-CPA advantage *)
    hop cpa_bob (eps_bob tuple_distinguisher)
      to (accept tuple_distinguisher G1)
      by le_of_eq (hop0_advantageE tuple_distinguisher) ;
    (* Charlie's slot zeroed, at a second IND-CPA advantage *)
    hop cpa_charlie (eps_charlie tuple_distinguisher)
      to (accept tuple_distinguisher G2)
      by le_of_eq (hop1_advantageE tuple_distinguisher) ;
    (* the guessing residue of the all-zero view, a term outside the
       hopping, added to the loss so the total bounds the trace game *)
    plus uniform_fiber #|plain AHE|%:R^-1
      by plus_le (accept_ge0 _ _)
           (all_zero_game_V2_le_invm
              (predict \o alice_trace_of_hop_tuple)) ;;
    (* the trace game, at the residue and the two advantages *)
    bound (#|plain AHE|%:R^-1 + eps_bob tuple_distinguisher
           + eps_charlie tuple_distinguisher)
      by alice_totalE tuple_distinguisher }.

End alice_trace_chain.

(* Alice's executed trace against the simulated trace as one chain.  It opens
   at the trace the interpreter hands Alice when it runs the DSDP protocol at
   a sample, steps to her hopping tuple at no loss, replaces the two
   ciphertext slots, and steps to the simulated trace at no loss.  The two
   steps that lose nothing are accept_trace_tupleE and its simulator-side
   twin, so the loss is the two hop labels and nothing else, and the gap
   result the chain returns on its own is the trace-level simulation bound: a
   test told the executed protocol apart from the simulation only as often as
   its lift tells the two ciphertext slots apart. *)
Section alice_trace_sim_chain.
Variable D : distinguisher (plain AHE * plain AHE * alice_traceT)%type.

(* The trace test D on the hopping tuple: it rebuilds Alice's trace and runs D
   on it.  Its advantage is the distance D sees between the executed trace and
   the simulated trace.
     |accept _ `p_[% V2, V3, alice_tuple_real]
      - accept _ `p_[% V2, V3, alice_tuple_all_zero]| *)
Local Notation tuple_distinguisher := (hop_tuple_distinguisher D).

Definition alice_trace_sim_chain :=
  \epsilon[ alice_claim tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept D (`p_ [% V2, V3, AliceTrace])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept tuple_distinguisher G0) by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at one IND-CPA advantage *)
    hop cpa_bob (eps_bob tuple_distinguisher)
      to (accept tuple_distinguisher G1)
      by le_of_eq (hop0_advantageE tuple_distinguisher) ;
    (* Charlie's slot zeroed, at a second IND-CPA advantage *)
    hop cpa_charlie (eps_charlie tuple_distinguisher)
      to (accept tuple_distinguisher G2)
      by le_of_eq (hop1_advantageE tuple_distinguisher) ;
    (* the simulated trace is that same image of the all-zero tuple *)
    same to (accept D alice_trace_ideal)
      by esym (accept_trace_ideal_tupleE D) }.

(* A trace test separates the real and simulated laws by at most the two hop
   advantages.  The steps at either end lose nothing, so only the two
   ciphertext replacements enter. *)
Theorem alice_trace_sim_advantage_le :
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr alice_trace_ideal [set x | D x] |
  <= indcpa_epsilon (pkey_of_dk Bob) (bob_trace_adversary D)
     + indcpa_epsilon (pkey_of_dk Charlie) (charlie_trace_adversary D).
Proof.
rewrite -!acceptE.
exact: result_sound alice_trace_sim_chain.
Qed.

(* The distance a trace test sees between Alice's executed trace and the
   simulator's trace.  It is the quantity every trace simulation bound of this
   file bounds. *)
Definition alice_trace_sim_advantage : R :=
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr alice_trace_ideal [set x | D x] |.

End alice_trace_sim_chain.

(* A distinguisher separates the real law from the ideal law by at most the
   two hop advantages.  The ideal law is the all-zero experiment, so the gap
   splits at G1.
     |accept D G0 - accept D G2| *)
Theorem alice_sim_advantage_le
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| Pr (`p_ [% V2, V3, alice_tuple_real]) [set x | D x]
     - Pr alice_ideal [set x | D x] |
  <= indcpa_epsilon bob_pkey (bob_challenge_adversary D)
     + indcpa_epsilon charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite alice_idealE -!acceptE.
apply: (le_trans (ler_distD (accept D G1) _ _)).
by rewrite hop0_advantageE hop1_advantageE.
Qed.

(* A predictor guesses V2 from the hopping tuple with probability at most
   1/#|plain AHE| + eps_bob D + eps_charlie D.  The proof adds the fiber
   residue at G2 to the simulation bound.
     |accept D G0 - accept D G2| <= eps_bob D + eps_charlie D *)
Theorem alice_tuple_guess_V2_le
    (predict : predictor alice_hop_tupleT) :
  Pr alice_sample_fdist [set t | (predict `o alice_tuple_real) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_epsilon bob_pkey
           (bob_challenge_adversary (distinguisher_of_predictor predict))
       + indcpa_epsilon charlie_pkey
           (charlie_challenge_adversary (distinguisher_of_predictor predict)).
Proof.
have step (x y u v : R) : y <= u -> `|x - y| <= v -> x <= u + v.
  move=> Hy Hv; have -> : x = y + (x - y) by ring.
  by apply: lerD => //; exact: le_trans (ler_norm _) Hv.
have Hsim : `| accept (distinguisher_of_predictor predict) G0
               - accept (distinguisher_of_predictor predict) G2 |
            <= eps_bob (distinguisher_of_predictor predict)
               + eps_charlie (distinguisher_of_predictor predict).
  by rewrite -alice_idealE 2!acceptE; exact: alice_sim_advantage_le.
rewrite guess_V2_acceptE -addrA.
apply: (step _ (accept (distinguisher_of_predictor predict) G2)).
  exact: all_zero_game_V2_le_invm.
exact: Hsim.
Qed.

(* The trace guessing bound, the trace-level simulation bound with the fiber
   term added. *)
Section alice_trace_guess.
Variable predict : predictor alice_traceT.

(* A predictor reading Alice's executed trace guesses Bob's input with
   probability at most 1/#|plain AHE| plus the two hop advantages.  The first
   term is unconditional, each hop term conditional on IND-CPA at one key. *)
Theorem alice_trace_guess_V2_le :
  Pr alice_sample_fdist [set t | (predict `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_epsilon (pkey_of_dk Bob)
           (bob_trace_adversary (distinguisher_of_predictor predict))
       + indcpa_epsilon (pkey_of_dk Charlie)
           (charlie_trace_adversary (distinguisher_of_predictor predict)).
Proof.
rewrite guess_V2_acceptE -(advantage0 (accept_ge0 _ _)).
exact: result_sound (alice_trace_chain predict).
Qed.

End alice_trace_guess.

End dsdp_alice_main.

(* The context of Section dsdp_alice_trace_centropy, which defines the
   decryptor and carries no u3_unit, extended by the u3_unit the guessing
   bounds below consume; the composite modulus of Section
   dsdp_alice_trace_pq plays no part in either. *)
Section dsdp_alice_trace_decrypt.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names this development gives them.  They
   are the scheme data, the weights, the three keys and the two second-hop
   coins. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation card_renc := (scheme_card_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation dk_b := (inst_dk_b I).

Local Notation P := (alice_sample_fdist (R:=R) I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation alice_tuple_bob_zero := (alice_tuple_bob_zero (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).
Local Notation alice_trace_of_hop_tuple := (alice_trace_of_hop_tuple (I:=I)).
Local Notation bob_decrypt_predictor := (bob_decrypt_predictor (I:=I)).
Local Notation bob_trace_predictor_epsilon :=
  (bob_trace_predictor_epsilon (R:=R) (I:=I)).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation bob_trace_adversary := (bob_trace_adversary (R:=R) (I:=I)).
Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) (I:=I)).

(* The decryptor succeeds on every sample. *)
Let decrypt_guess_prE :
  Pr P [set t | (bob_decrypt_predictor `o AliceTrace) t == V2 t] = 1.
Proof.
rewrite -alice_trace_decode_V2E.
rewrite (_ : finset _ = [set: alice_sampleT I]) ?Pr_setT //.
by apply/setP => t; rewrite !inE eqxx.
Qed.

(* A predictor holding Bob's private key induces a Bob-key reduction of
   advantage at least 1 - 1/#|plain AHE|.  At the real bit it decrypts and is
   always right, at the zero bit only on the fiber. *)
Corollary decrypt_bob_epsilon_ge :
  1 - (#|plain AHE|%:R : R)^-1
  <= bob_trace_predictor_epsilon bob_decrypt_predictor.
Proof.
pose lifted := bob_decrypt_predictor \o alice_trace_of_hop_tuple.
have Hlift : `| Pr P [set t | (lifted `o alice_tuple_real) t == V2 t]
              - Pr P [set t | (lifted `o alice_tuple_bob_zero) t == V2 t] |
            = bob_trace_predictor_epsilon bob_decrypt_predictor.
  by rewrite 2!guess_V2_acceptE hop0_advantageE.
have HV2 : lifted `o alice_tuple_real = V2.
  rewrite alice_trace_decode_V2E.
  by rewrite alice_trace_of_hop_tupleE.
have H0 : Pr P [set t | (lifted `o alice_tuple_real) t == V2 t] = 1.
  rewrite HV2 (_ : finset _ = [set: alice_sampleT I]) ?Pr_setT //.
  by apply/setP => t; rewrite !inE eqxx.
(* all_zero_guess_V2_le_invm is stated at alice_tuple_all_zero and used here
   at alice_tuple_bob_zero.  The reduction that carries it across is that
   trace_of_trace_tuple is a literal bseq, so nth 3 discards Charlie's slot,
   the only slot the two tuples differ in; Bob's slot is bob_zero_cipher in
   both.  Renumbering the trace slots or making trace_of_trace_tuple opaque
   breaks this step. *)
have H1 : Pr P [set t | (lifted `o alice_tuple_bob_zero) t == V2 t]
          <= #|plain AHE|%:R^-1.
  exact: (all_zero_guess_V2_le_invm lifted).
rewrite -Hlift H0.
exact: le_trans (lerB (lexx _) H1) (ler_norm _).
Qed.

(* An assumption promising an epsilon below 1 - 1/#|plain AHE| rejects the
   decrypting predictor's Bob-key reduction.  A key-holding adversary sits
   outside the public-key attack model an epsilon is measured in. *)
Lemma decrypt_reduction_admissibleF (A : indcpa_epsilon_assumption) :
  indcpa_assumption_epsilon A < 1 - (#|plain AHE|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary
       (distinguisher_of_predictor bob_decrypt_predictor)) = false.
Proof.
move=> Heps; apply/negbTE/negP => Hadm.
have Hle := le_trans decrypt_bob_epsilon_ge
              (indcpa_admissible_epsilon_le dk_b Hadm).
by move: (lt_le_trans Heps Hle); rewrite ltxx.
Qed.

(* At a small promised epsilon the premise-free bound sits strictly below what
   the decrypting predictor achieves.  With decrypt_reduction_admissibleF it
   places the truth of the guessing bound in the class restriction. *)
Lemma decrypt_guess_V2_premise_free_lt
    (A : indcpa_epsilon_assumption) :
  2 * indcpa_assumption_epsilon A < 1 - (#|plain AHE|%:R : R)^-1 ->
  (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A
    < alice_trace_guess_V2_pr bob_decrypt_predictor.
Proof.
move=> Heps.
have -> : alice_trace_guess_V2_pr bob_decrypt_predictor = 1
  := decrypt_guess_prE.
by rewrite -ltrBrDl.
Qed.

End dsdp_alice_trace_decrypt.

(* The raw-trace transfers of the two trace bounds.  The section carries the
   fixed-key decoder Alice's own trace is read through, and nothing else of
   the raw-trace layer. *)
Section dsdp_alice_raw_trace_bounds.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields the transfers read: the scheme through the
   coercion, Alice's private key and the key table. *)
Local Notation AHE := (scheme_AHE I).
Local Notation dk_a := (inst_dk_a I).

Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation trace_dataT := (trace_dataT I).
Local Notation alice_traceT := (alice_traceT I).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).
Local Notation alice_trace_ideal := (alice_trace_ideal (R:=R) I).
Local Notation alice_trace_of_hop_tuple := (alice_trace_of_hop_tuple (I:=I)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation bob_challenge_adversary :=
  (bob_challenge_adversary (R:=R) (I:=I)).
Local Notation charlie_challenge_adversary :=
  (charlie_challenge_adversary (R:=R) (I:=I)).
Local Notation alice_raw_trace := (alice_raw_trace (R:=R) (I:=I)).
Local Notation alice_raw_trace_decodeE :=
  (alice_raw_trace_decodeE (R:=R) (I:=I)).

(* Decoding at Alice's own key pair, the only setting in which the encoding
   is inverted.  [alice_raw_trace_decodeE] keeps the general two-key form
   because Alice's trace holds no public-key mark to constrain. *)
Local Notation decode_a := (di_data_of_trace_data dk_a (pub_of_priv dk_a)).

(* The simulation bound for a Boolean test reading the raw interpreter trace,
   through composition with the fixed-key decoder. *)
Corollary alice_raw_trace_sim_advantage_le
    (D_raw : plain AHE * plain AHE * seq (di_data DI) -> bool) :
  `| Pr (alice_sample_fdist (R:=R) I)
        [set t | D_raw (V2 t, V3 t, alice_raw_trace t)]
     - Pr alice_trace_ideal
          [set x : plain AHE * plain AHE * alice_traceT |
             D_raw (x.1.1, x.1.2, map decode_a x.2)] |
  <= indcpa_epsilon (pkey_of_dk Bob)
       (bob_challenge_adversary
         (fun x => D_raw (x.1.1, x.1.2,
            map decode_a (alice_trace_of_hop_tuple x.2))))
     + indcpa_epsilon (pkey_of_dk Charlie)
       (charlie_challenge_adversary
         (fun x => D_raw (x.1.1, x.1.2,
            map decode_a (alice_trace_of_hop_tuple x.2)))).
Proof.
set D := fun x : plain AHE * plain AHE * alice_traceT =>
           D_raw (x.1.1, x.1.2, map decode_a x.2).
have <- : Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
        = Pr (alice_sample_fdist (R:=R) I)
             [set t | D_raw (V2 t, V3 t, alice_raw_trace t)].
  rewrite /dist_of_RV Pr_fdistmap_preim; apply: eq_bigl => t; rewrite !inE.
  by rewrite -(alice_raw_trace_decodeE (pub_of_priv dk_a)).
exact: (alice_trace_sim_advantage_le D).
Qed.

(* The encoded-trace predictor a raw-trace predictor induces, decoding with
   Alice's fixed key context.  The binder is annotated because the
   bounded-sequence coercion is inserted only at a known domain. *)
Local Notation encoded_predictor g_raw :=
  (fun b : 18.-bseq trace_dataT =>
     g_raw (map decode_a b)).

(* The guessing bound restated at the raw interpreter trace, before any
   encoding.  Decoding under Alice's own key returns the run's own trace, so
   both formats agree. *)
Corollary alice_raw_trace_guess_V2_le
    (g_raw : seq (di_data DI) -> plain AHE) :
  Pr (alice_sample_fdist (R:=R) I)
     [set t | g_raw (alice_raw_trace t) == V2 t]
  <= (#|plain AHE|%:R : R)^-1
     + indcpa_epsilon (pkey_of_dk Bob)
         (bob_challenge_adversary
            (distinguisher_of_predictor
               (encoded_predictor g_raw \o alice_trace_of_hop_tuple)))
     + indcpa_epsilon (pkey_of_dk Charlie)
         (charlie_challenge_adversary
            (distinguisher_of_predictor
               (encoded_predictor g_raw \o alice_trace_of_hop_tuple))).
Proof.
have -> : [set t | g_raw (alice_raw_trace t) == V2 t]
        = [set t | (encoded_predictor g_raw `o AliceTrace) t == V2 t].
  by apply/setP => t; rewrite !inE /comp_RV alice_raw_trace_decodeE.
exact: (alice_trace_guess_V2_le (encoded_predictor g_raw)).
Qed.

End dsdp_alice_raw_trace_bounds.


(* The class-conditional argument along a sequence of DSDP instances: one
   instance at each security parameter, the IND-CPA assumption made there, and
   one observer of Alice's executed trace at each.  A bound at a fixed
   instance leaves open whether its two terms shrink as the parameter grows,
   and that is what the statements of this section settle: they hold the
   argument fixed and let the instance vary, so the two class-conditional
   programs are written here and nowhere else. *)
Section dsdp_alice_sequence.
Context {R : realType}.
Variable Q : dsdp_instance_sequence R.

Local Notation I := (sequence_instance Q).
Local Notation assumption := (sequence_assumption Q).

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter.  The [clear implicits] directive keeps the parameter an
   explicit argument, which is what makes predict k the predictor at k rather
   than the sequence read at a trace. *)
Variable predict : forall k, predictor (I k) (alice_traceT (I k)).
Arguments predict : clear implicits.

(* The two class premises of the guessing statements below: at every security
   parameter the class of the assumption made there admits the two reduction
   adversaries the k-th predictor induces.  They restrict the adversaries a
   predictor induces and so speak about the adversary rather than about the
   sequence, which is why they stay premises and are not fields of Q. *)
Hypothesis bob_admissible : forall k,
  indcpa_admissible (assumption k)
    (bob_trace_adversary (distinguisher_of_predictor (predict k))).
Hypothesis charlie_admissible : forall k,
  indcpa_admissible (assumption k)
    (charlie_trace_adversary (distinguisher_of_predictor (predict k))).

(* The trace guessing-probability sequence: at k, the probability that
   predict k returns Bob's input.  It reads Alice's executed trace at the k-th
   instance. *)
Definition f_guess_V2 k : R := alice_trace_guess_V2_pr (predict k).

(* The dictionary the guessing program below is written at, one at each
   security parameter.  It is a named constant rather than a lambda because
   canonical inference keys on the head constant of the sequence. *)
Definition alice_claims_admissible_at (k : nat) : alice_label -> claim R :=
  alice_claim_admissible (assumption k)
    (hop_tuple_distinguisher (distinguisher_of_predictor (predict k))).

(* The objects the programs of this section are written over, at the k-th
   instance.  They are the lifted trace test, the three experiments in
   visiting order, and the class epsilon. *)
Local Notation tuple_distinguisher k :=
  (hop_tuple_distinguisher (distinguisher_of_predictor (predict k))).
Local Notation G0 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k), alice_tuple_real (I:=I k)]).
Local Notation G1 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
         alice_tuple_bob_zero (I:=I k)]).
Local Notation G2 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
         alice_tuple_all_zero (I:=I k)]).
Local Notation eps k := (indcpa_assumption_epsilon (assumption k)).

(* The guessing sequence as the distance of the trace game from the zero game.
   It speaks of the games alone, so the program under the terminal below stays
   unnamed. *)
Lemma f_guess_V2_advantageE k :
  f_guess_V2 k
  = `| accept (distinguisher_of_predictor (predict k))
         (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
                AliceTrace (R:=R) (I:=I k)])
       - 0 |.
Proof.
by rewrite /f_guess_V2 /alice_trace_guess_V2_pr guess_V2_acceptE
   (advantage0 (accept_ge0 _ _)).
Qed.

(* The asymptotic content the negligibility statements of this section spend;
   the per-k bounds below hold without it. *)
Variable N : dsdp_asymptotic Q.

(* Every label of the guessing dictionary has a loss negligible along the
   sequence.  This is the whole asymptotic content, stated once for the
   dictionary. *)
Lemma alice_label_negligible_at (l : alice_label) :
  negligible_fun (fun k => claim_loss (alice_claims_admissible_at k l)).
Proof.
case: l.
- exact: adv_negligible N.
- exact: adv_negligible N.
- exact: size_negligible N.
Qed.

Canonical alice_claims_admissible_negligible :=
  NegligibleClaims alice_claims_admissible_at alice_label_negligible_at.

Local Open Scope epshop_scope.

(* Along a sequence of instances, a sequence of trace predictors guesses Bob's
   input with negligible probability.  The two hop terms are
   assumption-conditional, the plaintext-count term unconditional. *)
Theorem alice_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
exact: (\negligible[ f_guess_V2 by f_guess_V2_advantageE ]{ fun k =>
  \epsilon[ alice_claims_admissible_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor (predict k))
             (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
                    AliceTrace (R:=R) (I:=I k)])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept (tuple_distinguisher k) (G0 k))
      by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at the epsilon the assumption promises,
       which the class membership of the Bob-key reduction licenses *)
    hop cpa_bob (eps k) to (accept (tuple_distinguisher k) (G1 k))
      by le_trans (le_of_eq (hop0_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_b (I k))
                     (bob_admissible k)) ;
    (* Charlie's slot zeroed, at the same epsilon, licensed by the class
       membership of the Charlie-key reduction *)
    hop cpa_charlie (eps k) to (accept (tuple_distinguisher k) (G2 k))
      by le_trans (le_of_eq (hop1_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_c (I k))
                     (charlie_admissible k)) ;
    (* the guessing residue of the all-zero view, a term outside the
       hopping, added to the loss so the total bounds the trace game *)
    plus uniform_fiber #|plain (scheme_AHE (I k))|%:R^-1
      by plus_le (accept_ge0 _ _)
           (all_zero_game_V2_le_invm
              (predict k \o alice_trace_of_hop_tuple (I:=I k))) ;;
    (* the trace game, at the residue and twice the class epsilon *)
    bound ((#|plain (scheme_AHE (I k))|%:R : R)^-1 + 2 * eps k)
      by alice_admissible_totalE (assumption k) } }).
Qed.

(* The bound the same program returns at k: 1/#|plain| unconditional, plus
   twice the class epsilon.  It is what alice_trace_guess_V2_admissible_le
   reads at the sequence repeating one instance. *)
Lemma f_guess_V2_le k :
  f_guess_V2 k <= (#|plain (scheme_AHE (I k))|%:R : R)^-1 + 2 * eps k.
Proof.
(* The program is the one the terminal above is written over; the term there
   carries no name, so the text stands a second time and the kernel checks
   each copy on its own. *)
rewrite f_guess_V2_advantageE.
exact: (result_sound (\epsilon[ alice_claims_admissible_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor (predict k))
             (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
                    AliceTrace (R:=R) (I:=I k)])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept (tuple_distinguisher k) (G0 k))
      by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at the epsilon the assumption promises,
       which the class membership of the Bob-key reduction licenses *)
    hop cpa_bob (eps k) to (accept (tuple_distinguisher k) (G1 k))
      by le_trans (le_of_eq (hop0_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_b (I k))
                     (bob_admissible k)) ;
    (* Charlie's slot zeroed, at the same epsilon, licensed by the class
       membership of the Charlie-key reduction *)
    hop cpa_charlie (eps k) to (accept (tuple_distinguisher k) (G2 k))
      by le_trans (le_of_eq (hop1_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_c (I k))
                     (charlie_admissible k)) ;
    (* the guessing residue of the all-zero view, a term outside the
       hopping, added to the loss so the total bounds the trace game *)
    plus uniform_fiber #|plain (scheme_AHE (I k))|%:R^-1
      by plus_le (accept_ge0 _ _)
           (all_zero_game_V2_le_invm
              (predict k \o alice_trace_of_hop_tuple (I:=I k))) ;;
    (* the trace game, at the residue and twice the class epsilon *)
    bound ((#|plain (scheme_AHE (I k))|%:R : R)^-1 + 2 * eps k)
      by alice_admissible_totalE (assumption k) })).
Qed.

(* Under the two negligibility facts of N, the decrypting predictor's Bob-key
   reduction adversary is eventually outside the class.  The two facts exclude
   the predictor whose guessing probability is 1. *)
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

(* A sequence of Boolean tests of Alice's executed trace, one at each security
   parameter.  A test is what an indistinguishability statement quantifies
   over, where the predictor sequence above is what a guessing statement
   quantifies over, so the sequence declared here is a second observer of the
   same sequence and not a specialisation of the first.  The [clear implicits]
   directive keeps the security parameter an explicit argument, which is what
   makes trace_distinguishers k the test at k rather than the sequence read
   at an input. *)
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
   is second because alice_claims_admissible_at is pinned to one predictor's
   test. *)
Definition alice_sim_claims_at (k : nat) : alice_label -> claim R :=
  alice_claim_admissible (assumption k)
    (hop_tuple_distinguisher (trace_distinguishers k)).

(* Every label of that dictionary has a loss negligible along the
   sequence.  The terminal branch is owed because the condition quantifies
   over the whole label type. *)
Lemma alice_sim_label_negligible_at (l : alice_label) :
  negligible_fun (fun k => claim_loss (alice_sim_claims_at k l)).
Proof.
case: l.
- exact: adv_negligible N.
- exact: adv_negligible N.
- exact: size_negligible N.
Qed.

Canonical alice_sim_claims_negligible :=
  NegligibleClaims alice_sim_claims_at alice_sim_label_negligible_at.

(* The trace simulation distance sequence, at the k-th test and the k-th
   instance.  It is the distance between Alice's executed trace and the
   simulation. *)
Definition f_sim_advantage k : R :=
  alice_trace_sim_advantage (trace_distinguishers k).

(* That distance as the gap between the two games the simulation program
   joins.  It is stated on the games alone, as f_guess_V2_advantageE is. *)
Lemma f_sim_advantageE k :
  f_sim_advantage k
  = `| accept (trace_distinguishers k)
         (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
                AliceTrace (R:=R) (I:=I k)])
       - accept (trace_distinguishers k) (alice_trace_ideal (R:=R) (I k)) |.
Proof. by rewrite /f_sim_advantage /alice_trace_sim_advantage -!acceptE. Qed.

(* Along a sequence of instances, a sequence of trace tests has negligible
   simulation advantage.  The class admits its two reduction adversaries at
   every k.
     |accept (trace_distinguishers k)
        `p_[% V2, V3, AliceTrace]
      - accept (trace_distinguishers k) (alice_trace_ideal (I k))| *)
Theorem alice_trace_sim_advantage_negligible :
  negligible_fun f_sim_advantage.
Proof.
exact: (\negligible[ f_sim_advantage by f_sim_advantageE ]{ fun k =>
  \epsilon[ alice_sim_claims_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (trace_distinguishers k)
             (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
                    AliceTrace (R:=R) (I:=I k)])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept (hop_tuple_distinguisher (trace_distinguishers k)) (G0 k))
      by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at the epsilon the assumption promises,
       which the class membership of the Bob-key reduction licenses *)
    hop cpa_bob (eps k)
      to (accept (hop_tuple_distinguisher (trace_distinguishers k)) (G1 k))
      by le_trans (le_of_eq (hop0_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_b (I k))
                     (bob_admissible_distinguisher k)) ;
    (* Charlie's slot zeroed, at the same epsilon, licensed by the class
       membership of the Charlie-key reduction *)
    hop cpa_charlie (eps k)
      to (accept (hop_tuple_distinguisher (trace_distinguishers k)) (G2 k))
      by le_trans (le_of_eq (hop1_advantageE _))
                  (indcpa_admissible_epsilon_le (inst_dk_c (I k))
                     (charlie_admissible_distinguisher k)) ;
    (* the simulated trace is that same image of the all-zero tuple *)
    same to (accept (trace_distinguishers k) (alice_trace_ideal (R:=R) (I k)))
      by esym (accept_trace_ideal_tupleE _) } }).
Qed.

End dsdp_alice_sequence.

(* The class-conditional guessing bound at one instance, the sequence bound
   of f_guess_V2_le read along the sequence that repeats that instance.  The two
   class premises are the same restriction on the adversaries the predictor
   induces, made at a single security parameter. *)
Section dsdp_alice_admissible.
Context {R : realType}.
Variable I : dsdp_instance.
Local Notation AHE := (scheme_AHE I).
Variable assumption : indcpa_epsilon_assumption (R:=R) I.
Variable predict : predictor I (alice_traceT I).
Hypothesis bob_admissible :
  indcpa_admissible assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)).
Hypothesis charlie_admissible :
  indcpa_admissible assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)).

(* The instance repeated at every security parameter, under the assumption
   made once.  A statement quantified over sequences is then read at one
   instance. *)
Let const_sequence : dsdp_instance_sequence R :=
  {| sequence_instance := fun _ => I ;
     sequence_assumption := fun _ => assumption |}.

(* The trace guessing bound at one class epsilon: 1/#|plain AHE| plus twice
   that epsilon.  The two premises restrict the adversaries the predictor
   induces, and are assumed here. *)
Corollary alice_trace_guess_V2_admissible_le :
  alice_trace_guess_V2_pr predict
    <= (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon assumption.
Proof.
exact: (f_guess_V2_le (Q:=const_sequence) (predict:=fun _ => predict)
          (fun _ => bob_admissible) (fun _ => charlie_admissible) 0).
Qed.

End dsdp_alice_admissible.

Section dsdp_alice_trace_pq.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names this development gives them.  They
   are the scheme data, the weights, the three keys and the two second-hop
   coins. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation card_renc := (scheme_card_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Variables (p q : nat).
(* No positivity hypotheses: #|plain AHE| > 0 is a theorem, so the equation
   already forces 0 < p and 0 < q. *)
Hypothesis card_plain_pq : #|plain AHE| = (p * q)%N.

Local Notation alice_traceT := (alice_traceT I).
Local Notation predictor := (predictor I).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation bob_trace_adversary := (bob_trace_adversary (R:=R) (I:=I)).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) (I:=I)).

Local Notation alice_trace_guess_V2_pr :=
  (alice_trace_guess_V2_pr (R:=R) (I:=I)).

(* The inverse plaintext cardinality at the composite modulus. *)
Let card_plain_pq_invE : ((p%:R : R) * q%:R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_pq natrM. Qed.

(* The class-conditional trace guessing bound with its unconditional term
   written 1/(p * q).  Its premises are those of
   alice_trace_guess_V2_admissible_le. *)
Corollary alice_trace_guess_V2_admissible_pq_le
    (assumption : indcpa_epsilon_assumption)
    (predict : predictor alice_traceT) :
  indcpa_admissible assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)) ->
  indcpa_admissible assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)) ->
  alice_trace_guess_V2_pr predict
    <= ((p%:R : R) * q%:R)^-1 + 2 * indcpa_assumption_epsilon assumption.
Proof.
rewrite card_plain_pq_invE.
exact: alice_trace_guess_V2_admissible_le.
Qed.

End dsdp_alice_trace_pq.
