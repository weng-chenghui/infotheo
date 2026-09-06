From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba.
Require Import extra_proba extra_entropy.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption dsdp_interface dsdp_program dsdp_pismc.
Require Import negligible epshop epshop_family.
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
(* Four programs follow, each charging a hop at the advantage its own         *)
(* reduction shows.  alice_hops and alice_trace_sim_chain lose the two        *)
(* IND-CPA advantages and nothing else, the first at the hopping tuple and    *)
(* the second at the executed trace.  alice_chain and alice_trace_chain add   *)
(* the fiber term and return one over the plaintext count plus those two      *)
(* advantages.                                                                *)
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
(*             alice_totalE == the loss of alice_chain in the order its       *)
(*                              bound reads it                                *)
(*  alice_admissible_totalE == the same for a class-conditional total         *)
(*                                                                            *)
(* The programs                                                               *)
(*                                                                            *)
(*               alice_hops == the two ciphertext replacements at the hopping *)
(*                              tuple, losing the two advantages              *)
(*              alice_chain == alice_hops with the fiber term added           *)
(*        alice_trace_chain == the same argument opened at the executed trace *)
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
(* alice_raw_trace_real_experiment_avg == the raw-trace experiment at a       *)
(*                              sampled re-encryption coin                    *)
(* alice_raw_trace_ideal_experiment_avg == its simulated counterpart          *)
(* alice_raw_trace_sim_advantage_avg_le == the simulation bound at that coin  *)
(*                                                                            *)
(* Along a sequence of instances                                              *)
(*                                                                            *)
(*                f_guess_V2 == the trace guessing-probability sequence       *)
(* alice_claims_admissible_at k ==                                            *)
(*                              the dictionary of the class-conditional       *)
(*                              guessing argument at the k-th instance        *)
(* alice_label_negligible_at == every label of that dictionary costs a        *)
(*                              negligible family along the sequence          *)
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
(*                              every label of that dictionary costs a        *)
(*                              negligible family along the sequence          *)
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
(* ```                                                                        *)
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
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys and the key table they
   induce. *)
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

(* The declarations discharged by dsdp_alice_hop_secrecy.v and by
   dsdp_alice_trace_link.v take these parameters explicitly.  Each
   abbreviation pins them once, under the name it abbreviates; the shadowing
   is not recursive, since the right-hand side resolves against the
   constant. *)
Local Notation alice_sampleT := (alice_sampleT I).
Local Notation alice_sample_fdist := (alice_sample_fdist (R:=R) I).
Local Notation alice_hop_tupleT := (alice_hop_tupleT I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation Rho2 := (Rho2 (R:=R) (I:=I)).
Local Notation Rho3 := (Rho3 (R:=R) (I:=I)).
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
Local Notation trace_of_run := (trace_of_run (R:=R) (I:=I)).
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

     1. Sample (V2, V3, R2, R3, RA1, RA2, Rho3).
     2. Select V2 as the real challenge plaintext.  The experiment returns a
        challenge ciphertext ch encrypting either V2 or zero under Bob's key.
     3. Compute Sout, use ch as Bob's ciphertext, and use Rho3 to construct
        Charlie's ciphertext.
     4. Call D on the resulting joint value, shown flattened as

          (V2, V3, R2, R3, RA1, RA2, Sout, ch,
           enc charlie_pkey V3 (rand_of_renc Rho3)),

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

(* The IND-CPA adversary built from D at Bob's key: it samples the hop-0 state,
   submits Bob's input V2 as the challenge plaintext, and answers with D run on
   the joint value assembled around the challenge ciphertext.  At the real bit
   it reproduces the real experiment and at the zero bit the Bob-zero one. *)
Definition bob_challenge_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
    indcpa_adversary :=
  {| adv_state := hop0_stateT ;
     adv_choose := `p_ Hop0State ;
     adv_plain := fun c => c.1.1.1.1 ;
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.

(* The IND-CPA adversary built from D at Charlie's key: it samples the hop-1
   state, submits Charlie's input V3 as the challenge plaintext, and answers
   with D run on the joint value assembled around the challenge ciphertext.  At
   the real bit it reproduces the Bob-zero experiment and at the zero bit the
   all-zero one. *)
Definition charlie_challenge_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
    indcpa_adversary :=
  {| adv_state := hop1_stateT ;
     adv_choose := `p_ Hop1State ;
     adv_plain := fun c => c.1.1.1.2 ;
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
        = `p_ (protocol_RV Hop0State Rho2 bob_pkey
                 (fun c : hop0_stateT => c.1.1.1.1) hop0_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop0_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_realE.
Qed.

(* D's acceptance probability on the experiment whose Bob slot carries zero
   equals the zero-bit success probability of bob_challenge_adversary D
   against Bob's key. *)
Lemma hop0_zero_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
    = indcpa_success_zero bob_pkey (bob_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_bob_zero]
        = `p_ (protocol_RV Hop0State Rho2 bob_pkey
                 (fun _ : hop0_stateT => 0) hop0_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop0_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_zeroE.
Qed.

(* The gap D shows between the real and the Bob-zero experiment equals the
   advantage of bob_challenge_adversary D against Bob's key.  Zeroing Bob's
   slot costs exactly one IND-CPA advantage. *)
Lemma hop0_advantageE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| accept D (`p_ [% V2, V3, alice_tuple_real])
     - accept D (`p_ [% V2, V3, alice_tuple_bob_zero]) |
  = indcpa_epsilon bob_pkey (bob_challenge_adversary D).
Proof.
by rewrite /indcpa_epsilon hop0_real_challengeE hop0_zero_challengeE.
Qed.

(* D's acceptance probability on the Bob-zero experiment equals the real-bit
   success probability of charlie_challenge_adversary D against Charlie's key.
   That experiment is the zero side for Bob's key and the real side for
   Charlie's, which is what joins the two replacements. *)
Lemma hop1_real_challengeE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
    = indcpa_success_real charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite acceptE.
have -> : `p_ [% V2, V3, alice_tuple_bob_zero]
        = `p_ (protocol_RV Hop1State Rho3 charlie_pkey
                 (fun c : hop1_stateT => c.1.1.1.2) hop1_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
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
        = `p_ (protocol_RV Hop1State Rho3 charlie_pkey
                 (fun _ : hop1_stateT => 0) hop1_assemble).
  rewrite /dist_of_RV; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (protocol_indcpa_fdistE _ _ _ hop1_state_prodE).
by rewrite indcpa_fdist_acceptE indcpa_success_zeroE.
Qed.

(* The gap D shows between the Bob-zero and the all-zero experiment equals the
   advantage of charlie_challenge_adversary D against Charlie's key.  Zeroing
   Charlie's slot costs exactly one IND-CPA advantage. *)
Lemma hop1_advantageE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| accept D (`p_ [% V2, V3, alice_tuple_bob_zero])
     - accept D (`p_ [% V2, V3, alice_tuple_all_zero]) |
  = indcpa_epsilon charlie_pkey (charlie_challenge_adversary D).
Proof.
by rewrite /indcpa_epsilon hop1_real_challengeE hop1_zero_challengeE.
Qed.

(* The event that a predictor matches Bob's input is the acceptance event of
   the associated distinguisher on the law of the inputs beside the
   observation the predictor reads.  The observation is a parameter, so the
   same equality serves the real, the Bob-zero and the all-zero experiment at
   the hopping tuple and serves Alice's executed trace as well: a guessing
   statement and a game of a hopping argument are one number wherever the
   predictor sits. *)
Lemma guess_V2_acceptE (O : finType) (predict : predictor O)
    (H : {RV alice_sample_fdist -> O}) :
  Pr alice_sample_fdist
     [set t | (predict `o H) t == V2 t]
  = accept (distinguisher_of_predictor predict) (`p_ [% V2, V3, H]).
Proof.
rewrite acceptE /dist_of_RV Pr_fdistmap_preim.
by apply: eq_bigl => t; rewrite !inE.
Qed.

(* The all-zero game read as a bound on the inverse plaintext-space
   cardinality: all_zero_guess_V2_le_invm carried through the joint law of the
   honest inputs and Alice's tuple, which is the form the terminal statement
   of the chain below takes.  It is the only place the DSDP solution fiber
   enters the chain.
   Naming: [game] names the acceptance probability being bounded, as [guess]
   names the success probability in all_zero_guess_V2_le_invm, [all_zero] the
   view it reads, and [invm] the inverse plaintext-space cardinality bounding
   it. *)
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
by rewrite -[RHS]cpr_eqE_mul (dsdp_alice_hop_tuple_cond_sim v H0) mulrC.
Qed.

(* The distinguisher D of Alice's trace, turned into a distinguisher of her
   hopping tuple: given a tuple, it rebuilds the trace with
   alice_trace_of_hop_tuple and runs D on it.  It exists so that the two
   hops, stated between
     `p_[% V2, V3,
        [% [% R2, R3], [% RA1, RA2], Sout,
           bob_real_cipher, charlie_real_cipher]]
   and
     `p_[% V2, V3,
        [% [% R2, R3], [% RA1, RA2], Sout,
           bob_zero_cipher, charlie_zero_cipher]],
   bound D's advantage
   |accept D `p_[% V2, V3, trace_of_run dsdp_protocol Alice]
    - accept D alice_trace_ideal|,
   alice_trace_ideal being the simulator's trace built from the leaked
   output Sout alone. *)
Definition hop_tuple_distinguisher
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  D \o (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2)).

(* The IND-CPA adversary against Bob's key induced by a trace test D: it
   embeds the challenge in the ciphertext of Bob's input V2, rebuilds
   Alice's executed trace around it, and decides with D.  Its advantage at
   Bob's key is
   |indcpa_success_real (pkey_of_dk Bob) _
    - indcpa_success_zero (pkey_of_dk Bob) _|,
   which is the gap
   |accept (hop_tuple_distinguisher D)
      `p_[% V2, V3,
          [% [% R2, R3], [% RA1, RA2], Sout,
             bob_real_cipher, charlie_real_cipher]]
    - accept (hop_tuple_distinguisher D)
      `p_[% V2, V3,
          [% [% R2, R3], [% RA1, RA2], Sout,
             bob_zero_cipher, charlie_real_cipher]]|
   the first hop of every trace program spans. *)
Definition bob_trace_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  bob_challenge_adversary (hop_tuple_distinguisher D).

(* The Charlie-key counterpart of bob_trace_adversary: its advantage is the
   gap between
   `p_[% V2, V3,
      [% [% R2, R3], [% RA1, RA2], Sout,
         bob_zero_cipher, charlie_real_cipher]]
   and
   `p_[% V2, V3,
      [% [% R2, R3], [% RA1, RA2], Sout,
         bob_zero_cipher, charlie_zero_cipher]],
   the second hop of every trace program. *)
Definition charlie_trace_adversary
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :=
  charlie_challenge_adversary (hop_tuple_distinguisher D).

(* A Boolean test reading Alice's executed trace beside the two honest inputs
   accepts as often as its lift reading her hopping tuple there, the trace
   being a deterministic image of the tuple.  This is the step at which the
   protocol costs nothing: it lets the run of the interpreter stand as the
   first game of an argument whose remaining games live at the hopping tuple,
   so that what an adversary is shown is the executed protocol rather than a
   tuple standing for it.
   Naming: after [centropy_V2_trace_tupleE], with [accept] naming the
   quantity the two levels agree on. *)
Lemma accept_trace_tupleE
    (D : distinguisher (plain AHE * plain AHE * alice_traceT)%type) :
  accept D (`p_ [% V2, V3, AliceTrace])
  = accept (hop_tuple_distinguisher D) (`p_ [% V2, V3, alice_tuple_real]).
Proof.
by rewrite /accept /hop_tuple_distinguisher alice_trace_realE fdistmap_comp.
Qed.

(* A Boolean trace test accepts the simulated trace law as often as its lift
   accepts the all-zero hopping tuple beside the two honest inputs.  The
   simulated trace law is the image of the tuple-level simulator law under
   the trace map, and that tuple-level law is the all-zero experiment itself
   by alice_idealE, so the test reads the same number at either level.  This
   is the step that costs nothing at the simulator end of a trace-level
   argument, as accept_trace_tupleE is the step that costs nothing at the
   executed-protocol end.
   Naming: extends [accept_trace_tupleE] with [ideal] naming the law the
   test reads. *)
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
   Bob's input.  This is the quantity every trace guessing bound in this file
   bounds, and it is the spelling the class-conditional bounds use, so that a
   reader can see at a glance that they bound the same number the
   unconditional bounds do.
   Naming: [_pr] marks the probability of the event just named, with the
   [alice_trace] stem naming whose observation the predictor reads. *)
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

(* The three experiments, the acceptance probability of a distinguisher on
   one of them, and the two IND-CPA advantages a hop of the chain below logs,
   under the short names that chain reads at.  G0, G1 and G2 are the three
   boxes of the figure, in the order the chain visits them. *)
Local Notation G0 := (`p_ [% V2, V3, alice_tuple_real]).
Local Notation G1 := (`p_ [% V2, V3, alice_tuple_bob_zero]).
Local Notation G2 := (`p_ [% V2, V3, alice_tuple_all_zero]).
Local Notation eps_bob D :=
  (indcpa_epsilon bob_pkey (bob_challenge_adversary D)).
Local Notation eps_charlie D :=
  (indcpa_epsilon charlie_pkey (charlie_challenge_adversary D)).

Local Open Scope epshop_scope.

(* The three labels of the argument: cpa_bob and cpa_charlie for the two
   IND-CPA reductions, at Bob's key and at Charlie's, and uniform_fiber for
   the plaintext-space bound at the all-zero endpoint.  The labels are what
   let a reader of an accumulated loss tell which of its terms are
   conditional on a computational assumption, and at which key: the two hop
   labels are, and the terminal label is not, its term being the residue the
   leaked output leaves along the DSDP solution fiber.
   Naming: [cpa] is the game an advantage belongs to and [bob], [charlie] the
   key it is read at; [uniform] is the law the residue is measured against
   and [fiber] the DSDP solution fiber that law is carried on. *)
Variant alice_label := cpa_bob | cpa_charlie | uniform_fiber.

(* What each label claims: for a hop label the two acceptance probabilities
   its ciphertext replacement moves between and the advantage that
   replacement costs, and for uniform_fiber the all-zero game against the
   zero game, at the inverse plaintext-space cardinality.  The claims are
   written here rather than at the steps of the chain, and that is what makes
   a step check: the cost, the target and the justification of a step are
   each compared with the claim of the label it stands under, so an advantage
   cannot be charged to a key whose reduction it does not come from. *)
Definition alice_claim
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type)
    (l : alice_label) : claim R :=
  match l with
  | cpa_bob => Claim (accept D G0) (accept D G1) (eps_bob D)
  | cpa_charlie => Claim (accept D G1) (accept D G2) (eps_charlie D)
  | uniform_fiber => Claim (accept D G2) 0 #|plain AHE|%:R^-1
  end.

(* The dictionary of the class-conditional reading of the same argument: the
   three games are those of alice_claim, and the two hop labels cost the
   epsilon an adversary-class assumption promises rather than the advantage
   the reduction at that key actually shows.  A hop under this dictionary is
   therefore conditional on the class admitting its reduction adversary, and
   the justification it demands is that class membership rather than an
   equality of advantages; the label whose target is the zero game costs
   the same information-theoretic residue under both dictionaries.
   Naming: extends [alice_claim] with the [admissible] variant token naming
   the quantity the hop labels are charged at, the same token the bound
   [alice_trace_guess_V2_admissible_le] already carries. *)
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

(* The closed form of the loss the chain below accumulates, written in the
   order alice_tuple_guess_V2_le states: the plaintext-space residue first,
   then the Bob-key advantage, then the Charlie-key advantage.  The chain
   accumulates them in the order it spends them, the two hops before the
   endpoint, so the return statement reorders. *)
Lemma alice_totalE
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  eps_bob D + eps_charlie D + #|plain AHE|%:R^-1
  = #|plain AHE|%:R^-1 + eps_bob D + eps_charlie D.
Proof. by rewrite addrAC [X in X + _]addrC. Qed.

(* The closed form of the loss a chain over alice_claim_admissible
   accumulates, written in the order alice_trace_guess_V2_admissible_le
   states it: the plaintext-space residue first, then the two hops, both
   charged at one and the same class epsilon, which is where the factor two
   of that statement comes from.
   Naming: extends [alice_totalE] with the [admissible] token naming the
   dictionary whose loss is totalled. *)
Lemma alice_admissible_totalE (A : indcpa_epsilon_assumption) :
  indcpa_assumption_epsilon A + indcpa_assumption_epsilon A
  + (#|plain AHE|%:R : R)^-1
  = (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A.
Proof. by rewrite mulr_natl mulr2n addrC. Qed.

(* The two ciphertext replacements as one fragment: from the real hopping
   tuple to the tuple whose two ciphertext slots both carry zero, at the two
   advantages the reductions at Bob's key and at Charlie's actually show.
   hop0_advantageE and hop1_advantageE are equalities, so each term is
   exactly the gap its hop spans, and composing the two is where the one
   triangle inequality of the argument is spent.  The fragment carries no
   terminal, so it is a chain, and the gap result it returns on its own is
   the bound on the distance between Alice's real view and her all-zero
   view, which is the simulation bound of alice_sim_advantage_le, the one
   statement it carries.
   Naming: [hops] names the two hop steps the fragment is made of. *)
Definition alice_hops
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :=
  \epsilon[ alice_claim D ]{
            (* the real view, both ciphertext slots carrying their
               plaintexts *)
            start (accept D G0) ;
            (* Bob's ciphertext slot zeroed, at one IND-CPA advantage *)
            hop cpa_bob (eps_bob D) to (accept D G1)
              by le_of_eq (hop0_advantageE D) ;
            (* Charlie's slot zeroed, at a second IND-CPA advantage *)
            hop cpa_charlie (eps_charlie D) to (accept D G2)
              by le_of_eq (hop1_advantageE D) }.

(* The computational-security argument of this file written as one program:
   the two ciphertext replacements, then the all-zero endpoint bounded.  The
   bound the program returns is the statement of alice_tuple_guess_V2_le,
   and its distinguisher is the predictor scored against Bob's input, so the
   game the bound is about is the probability that predict returns V2 from
   the real hopping tuple.
   Each of the two hops carries the key its advantage is charged to, which is
   what the class-conditional reading of dsdp_alice_trace_link.v and the
   family reading of dsdp_instance_sequence.v read off a label.  The last
   line, the term labelled uniform_fiber, is what that theorem adds to the
   simulation bound: the mass the leaked output leaves along the DSDP
   solution fiber, unconditional where the two hop terms are conditional on
   the IND-CPA assumption at one key each. *)
Definition alice_chain (predict : predictor alice_hop_tupleT) :=
  \epsilon[ alice_claim (distinguisher_of_predictor predict) ]{
            (* the real view, both ciphertext slots carrying their
               plaintexts *)
            start (accept (distinguisher_of_predictor predict) G0) ;
            (* Bob's ciphertext slot zeroed, at one IND-CPA advantage *)
            hop cpa_bob (eps_bob (distinguisher_of_predictor predict))
              to (accept (distinguisher_of_predictor predict) G1)
              by le_of_eq
                   (hop0_advantageE (distinguisher_of_predictor predict)) ;
            (* Charlie's slot zeroed, at a second IND-CPA advantage *)
            hop cpa_charlie (eps_charlie (distinguisher_of_predictor predict))
              to (accept (distinguisher_of_predictor predict) G2)
              by le_of_eq
                   (hop1_advantageE (distinguisher_of_predictor predict)) ;
            (* the guessing residue of the all-zero view, a term outside the
               hopping, added to the loss so the total bounds the real view *)
            plus uniform_fiber #|plain AHE|%:R^-1
              by plus_le (accept_ge0 _ _)
                   (all_zero_game_V2_le_invm predict) ;;
            (* the real-view game, at the residue and the two advantages *)
            bound (#|plain AHE|%:R^-1
                   + eps_bob (distinguisher_of_predictor predict)
                   + eps_charlie (distinguisher_of_predictor predict))
              by alice_totalE (distinguisher_of_predictor predict) }.


(* Alice's trace secrecy as one program.  Its first game is the trace the
   interpreter hands Alice when it runs the DSDP protocol at the sampled
   inputs, so the object the argument starts from is the executed protocol
   itself rather than a tuple of values standing for it.  The bound the
   program returns is the statement of alice_trace_guess_V2_le.
   The trace is a deterministic image of the hopping tuple, so the step to
   the tuple costs nothing.  Each of the two ciphertext replacements carries
   the key its advantage is charged to, which is what the class-conditional
   reading below and the family reading of dsdp_instance_sequence.v read off
   a label.  The last line, the term labelled uniform_fiber, is what that
   theorem adds to the simulation bound: the mass the leaked output leaves
   along the DSDP solution fiber, unconditional where the two hop terms are
   conditional on the IND-CPA assumption at one key each. *)
Section alice_trace_chain.
Variable predict : predictor alice_traceT.

(* The predictor's distinguisher on the hopping tuple.  Given (V2, V3, tuple):
   1. rebuild Alice's trace from the tuple with alice_trace_of_hop_tuple;
   2. let predict guess V2 from that trace;
   3. accept when the guess equals V2.
   Its advantage is against the zero game,
   |accept _ `p_[% V2, V3,
                  [% [% R2, R3], [% RA1, RA2], Sout,
                     bob_real_cipher, charlie_real_cipher]]
    - 0|,
   the probability that the predictor guesses V2 from the real trace. *)
Local Notation tuple_distinguisher :=
  (hop_tuple_distinguisher (distinguisher_of_predictor predict)).

Definition alice_trace_chain :=
  \epsilon[ alice_claim tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor predict)
             (`p_ [% V2, V3, trace_of_run dsdp_protocol Alice])) ;
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
   steps that cost nothing are accept_trace_tupleE and its simulator-side
   twin, so the loss is the two hop labels and nothing else, and the gap
   result the chain returns on its own is the trace-level simulation bound: a
   test told the executed protocol apart from the simulation only as often as
   its lift tells the two ciphertext slots apart.
   Naming: extends [alice_trace_chain] with [sim] naming the statement its
   gap result carries, as [alice_sim_advantage_le] does at the tuple. *)
Section alice_trace_sim_chain.
Variable D : distinguisher (plain AHE * plain AHE * alice_traceT)%type.

(* The trace test D on the hopping tuple: it rebuilds Alice's trace from a
   tuple and runs D on it.  Its advantage is
   |accept _ `p_[% V2, V3,
                  [% [% R2, R3], [% RA1, RA2], Sout,
                     bob_real_cipher, charlie_real_cipher]]
    - accept _ `p_[% V2, V3,
                     [% [% R2, R3], [% RA1, RA2], Sout,
                        bob_zero_cipher, charlie_zero_cipher]]|,
   which the two zero-loss end steps identify with the distance D sees
   between `p_[% V2, V3, trace_of_run dsdp_protocol Alice] and
   alice_trace_ideal. *)
Local Notation tuple_distinguisher := (hop_tuple_distinguisher D).

Definition alice_trace_sim_chain :=
  \epsilon[ alice_claim tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept D (`p_ [% V2, V3, trace_of_run dsdp_protocol Alice])) ;
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

(* A Boolean trace test separates the real and simulated joint laws by at most
   the two hop advantages of its lifted hopping-tuple test.  The bound is the
   gap result of alice_trace_sim_chain, whose two zero-loss steps carry the
   test between the executed trace and the hopping tuple at either end, so
   nothing outside the two ciphertext replacements enters the total.
   Naming: after [alice_sim_advantage_le] with [alice_trace] as the object
   stem; the transfer corollary [alice_raw_trace_sim_advantage_le] keeps that
   stem and names the observation read before [sim_advantage]. *)
Theorem alice_trace_sim_advantage_le :
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr alice_trace_ideal [set x | D x] |
  <= indcpa_epsilon (pkey_of_dk Bob) (bob_trace_adversary D)
     + indcpa_epsilon (pkey_of_dk Charlie) (charlie_trace_adversary D).
Proof.
rewrite -!acceptE.
exact: result_sound alice_trace_sim_chain.
Qed.

(* The distance a Boolean trace test sees between the law of Alice's executed
   trace beside the two honest inputs and the law the simulator produces from
   the leaked output alone.  This is the quantity every trace simulation bound
   of this file bounds, and the one the sequence statement of
   dsdp_instance_sequence.v reads along the security parameter, so that the
   bound at a fixed instance and its asymptotic form are visibly about the
   same number.
   Naming: the subject of [alice_trace_sim_advantage_le] under its own name,
   as [alice_trace_guess_V2_pr] is the subject of
   [alice_trace_guess_V2_le]. *)
Definition alice_trace_sim_advantage : R :=
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr alice_trace_ideal [set x | D x] |.

End alice_trace_sim_chain.

(* A distinguisher separates the real joint law of the two secret inputs and
   Alice's view from the ideal-world joint law by at most the sum of the
   advantages of the two hop reductions.  This is the simulation-based reading
   of the same two hops: the real world is the real experiment, the ideal world
   the all-zero one, and the distance between them is the sum of the two
   IND-CPA advantages.  The bound is the gap result of the fragment
   alice_hops, so the one triangle inequality the two hops need is spent
   inside the language and not again here.
   Naming: [sim_advantage] rather than [advantage_sim] because the statement
   bounds a distinguishing gap between two laws rather than instantiating a
   simulation-advantage predicate. *)
Theorem alice_sim_advantage_le
    (D : distinguisher (plain AHE * plain AHE * alice_hop_tupleT)%type) :
  `| Pr (`p_ [% V2, V3, alice_tuple_real]) [set x | D x]
     - Pr alice_ideal [set x | D x] |
  <= indcpa_epsilon bob_pkey (bob_challenge_adversary D)
     + indcpa_epsilon charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite alice_idealE -!acceptE.
exact: result_sound (alice_hops D).
Qed.

(* A predictor reading Alice's real view returns Bob's input with probability at
   most the inverse plaintext-space cardinality plus the advantages of the two
   hop reductions.  It is the simulation bound of alice_sim_advantage_le with
   one term added: the ideal side of that bound is the all-zero experiment by
   alice_idealE, and a predictor scored there is confined to the fiber the
   leaked output leaves, of mass at most the inverse cardinality.  So the first
   term is information-theoretic and each of the two advantages is what zeroing
   one ciphertext slot costs, conditional on the IND-CPA assumption at that
   slot's key.  The right-hand side is the bound alice_chain returns, the loss
   it accumulated in the order this statement reads it.
   Naming: [tuple] names the real-tuple conditioner, [V2] the input bounded,
   and [le] the direction of the bound. *)
Theorem alice_tuple_guess_V2_le
    (predict : predictor alice_hop_tupleT) :
  Pr alice_sample_fdist [set t | (predict `o alice_tuple_real) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_epsilon bob_pkey
           (bob_challenge_adversary (distinguisher_of_predictor predict))
       + indcpa_epsilon charlie_pkey
           (charlie_challenge_adversary (distinguisher_of_predictor predict)).
Proof.
rewrite guess_V2_acceptE -(advantage0 (accept_ge0 _ _)).
exact: result_sound (alice_chain predict).
Qed.

(* The trace guessing bound, the trace-level simulation bound with the fiber
   term added. *)
Section alice_trace_guess.
Variable predict : predictor alice_traceT.

(* Every predictor reading the trace the interpreter produces for Alice
   matches Bob's input with probability at most one over the plaintext-space
   cardinality plus the real-or-zero advantages of the two per-hop
   reductions.  It is alice_trace_sim_advantage_le with one term added: the
   simulated trace law is the all-zero experiment read through the trace map
   by accept_trace_ideal_tupleE, and a predictor scored there is confined to
   the fiber the leaked output leaves.  The cardinality term is therefore
   information-theoretic and the two advantages are what the two ciphertext
   replacements cost, one at Bob's key and one at Charlie's.  The right-hand
   side is the bound alice_trace_chain returns. *)
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
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys, and Bob's and Charlie's
   second-hop coins as indices into the coin space. *)
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

(* Bob's key alone already carries that whole gap.  The decryptor separates
   the two branches of the hop-0 challenge: at the real bit it reads Bob's
   input off the challenge ciphertext and is right always, and at the zero
   bit it reads zero and is right only on the fiber the leaked output leaves,
   of mass at most 1/#|plain AHE|.  The Charlie-key term of the corollary
   above is therefore not needed: this proof consumes the hop-0 half of the
   ladder alone, never the composite two-hop bound
   alice_trace_guess_V2_le.
   Naming: as above, with [bob] naming the single epsilon the bound
   charges. *)
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

(* An assumption that promises a small epsilon has no choice about the
   decrypting predictor: its classifier must answer false on the reduction
   that predictor induces at Bob's key, because that reduction holds Bob's
   private key and its advantage is provably at least 1 - 1/#|plain AHE|.
   Key-holding behavior sits outside the public-key-only attack model every
   meaningful epsilon is measured in, so rejecting it is forced, not
   bookkeeping.
   Naming: the [F] suffix is MathComp's marker for a conclusion that is the
   boolean false. *)
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

(* Dropping the membership premises of the class-conditional guessing bound
   leaves a false statement: whenever the promised epsilon is meaningfully
   small, the premise-free right-hand side sits strictly below what the
   decrypting predictor achieves, at every such assumption.
   decrypt_reduction_admissibleF is the complementary half: it shows the
   missing premises cannot be supplied for this predictor.  Together they
   place the bound's truth in the class restriction.
   Naming: the decrypting predictor is the subject, as in
   decrypt_reduction_admissibleF; [premise_free] marks the bound with its two
   class premises dropped. *)
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

(* The simulator-advantage bound for a Boolean test reading the raw
   interpreter trace, via composition with the fixed-key decoder.
   Naming: extends [alice_trace_sim_advantage_le] with [raw]
   marking the observation read. *)
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
  (fun b : 15.-bseq trace_dataT =>
     g_raw (map decode_a b)).

(* The guessing bound restated at the raw interpreter trace, before any
   encoding is applied.

   Encoding neither costs Alice anything nor withholds anything from her.
   Her trace carries no public-key mark, so decoding it under her own key
   returns the run's own trace, and a predictor reading either format
   recovers Bob's input on exactly the same samples.
   Naming: extends [alice_trace_guess_V2_le] with [raw]
   marking the observation read. *)
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

Section dsdp_alice_raw_trace_avg.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys, and Bob's and Charlie's
   second-hop coins as indices into the coin space. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation card_renc := (scheme_card_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation dk_a := (inst_dk_a I).

(* Each abbreviation reads the instance, except the per-coin ones, which read
   the instance with Charlie's second-hop coin replaced by w.  The two
   reduction adversaries are among them: their state distribution is built
   from the sample space of that instance, so the summand at w names them
   there. *)
Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation trace_dataT := (trace_dataT I).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation AliceRawTrace_coin w :=
  (alice_raw_trace (R:=R) (I:=inst_with_rc2 I w)).
Local Notation ideal_avg := (alice_trace_ideal_avg (R:=R) I).
Local Notation alice_trace_of_hop_tuple_coin w :=
  (alice_trace_of_hop_tuple (I:=inst_with_rc2 I w)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation bob_challenge_adversary_coin w :=
  (bob_challenge_adversary (R:=R) (I:=inst_with_rc2 I w)).
Local Notation charlie_challenge_adversary_coin w :=
  (charlie_challenge_adversary (R:=R) (I:=inst_with_rc2 I w)).

(* Decoding at Alice's own key pair, the only setting in which the encoding
   is inverted.  [alice_raw_trace_decodeE] keeps the general two-key form
   because Alice's trace holds no public-key mark to constrain. *)
Local Notation decode_a := (di_data_of_trace_data dk_a (pub_of_priv dk_a)).

(* The encoded-trace test a raw-trace test induces, decoding with Alice's
   fixed key context.  The binder is annotated because the bounded-sequence
   coercion is inserted only at a known domain. *)
Local Notation encoded_distinguisher D_raw :=
  (fun x : plain AHE * plain AHE * 15.-bseq trace_dataT =>
     D_raw (x.1.1, x.1.2,
            map decode_a x.2)).

(* The Boolean real raw-trace experiment: the re-encryption coin sampled
   uniformly, then the test applied to the two honest inputs and Alice's
   raw interpreter trace at that coin.
   Naming: after [alice_raw_trace], with [experiment] marking the Boolean
   image and [avg] the sampled coin. *)
Definition alice_raw_trace_real_experiment_avg
    (D_raw : plain AHE * plain AHE * seq (di_data DI) -> bool) :
    R.-fdist bool :=
  fdist_uniform card_renc >>= (fun w =>
    fdistmap (fun t => D_raw (V2 t, V3 t, AliceRawTrace_coin w t))
      (alice_sample_fdist (R:=R) (inst_with_rc2 I w))).

(* The Boolean ideal raw-trace experiment: the image of the averaged ideal
   trace joint law under the test composed with the fixed-key decoder.
   Naming: after [alice_trace_ideal_avg], with [raw] marking the observation
   read. *)
Definition alice_raw_trace_ideal_experiment_avg
    (D_raw : plain AHE * plain AHE * seq (di_data DI) -> bool) :
    R.-fdist bool :=
  fdistmap (encoded_distinguisher D_raw) ideal_avg.

(* The averaged gap a Boolean test reading Alice's raw interpreter trace
   sees between the real and the ideal experiment is at most the average of
   the two per-coin hop advantages of the decoded test.
   Naming: extends [alice_raw_trace_sim_advantage_le] with the
   [avg] variant token before [le]. *)
Theorem alice_raw_trace_sim_advantage_avg_le
    (D_raw : plain AHE * plain AHE * seq (di_data DI) -> bool) :
  `| Pr (alice_raw_trace_real_experiment_avg D_raw) [set true]
     - Pr (alice_raw_trace_ideal_experiment_avg D_raw) [set true] |
  <= \sum_(w in Renc)
       (fdist_uniform card_renc : R.-fdist Renc) w
       * (indcpa_epsilon (pkey_of_dk Bob)
            (bob_challenge_adversary_coin w (fun x =>
               D_raw (x.1.1, x.1.2,
                      map decode_a (alice_trace_of_hop_tuple_coin w x.2))))
          + indcpa_epsilon (pkey_of_dk Charlie)
            (charlie_challenge_adversary_coin w (fun x =>
               D_raw (x.1.1, x.1.2,
                      map decode_a (alice_trace_of_hop_tuple_coin w x.2))))).
Proof.
(* Push the decoded test through the outer coin bind; each branch is then
   the per-coin corollary, which consumes the round trip of
   alice_raw_trace_decodeE. *)
rewrite /alice_raw_trace_real_experiment_avg
  /alice_raw_trace_ideal_experiment_avg.
rewrite /alice_trace_ideal_avg fdistmap_bind.
apply: fdist_mixture_advantage_le => w; rewrite 2!Pr_fdistmap_bool.
exact: (alice_raw_trace_sim_advantage_le (I:=inst_with_rc2 I w) D_raw).
Qed.

End dsdp_alice_raw_trace_avg.

(* The class-conditional argument along a sequence of DSDP instances: one
   instance at each security parameter, the IND-CPA assumption made there, and
   one observer of Alice's executed trace at each.  A bound at a fixed
   instance leaves open whether its two terms shrink as the parameter grows,
   and that is what the statements of this section settle: they hold the
   argument fixed and let the instance vary, so the two class-conditional
   programs are written here and nowhere else. *)
Section dsdp_alice_family.
Context {R : realType}.
Variable Q : dsdp_instance_sequence R.

Local Notation I := (sequence_instance Q).
Local Notation assumption := (sequence_assumption Q).

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter.  The [clear implicits] directive keeps the parameter an
   explicit argument, which is what makes predict k the predictor at k rather
   than the family read at a trace. *)
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

(* The trace guessing-probability sequence: the probability that the k-th
   predictor, reading Alice's executed trace at the k-th instance, returns
   Bob's input. *)
Definition f_guess_V2 k : R := alice_trace_guess_V2_pr (predict k).

(* The dictionary the guessing program below is written at, as a family
   indexed by the security parameter.  It is a named constant rather than a
   lambda because canonical inference keys on the head constant of the family,
   and an application of a lambda has none.
   Naming: extends [alice_claim_admissible] with the [_at] token naming the
   instance the dictionary is read at, the plural marking the family. *)
Definition alice_claims_admissible_at (k : nat) : alice_label -> claim R :=
  alice_claim_admissible (assumption k)
    (hop_tuple_distinguisher (distinguisher_of_predictor (predict k))).

(* The objects the programs of this section are written over, at the k-th
   instance: a trace test lifted to the hopping tuple, the law of Alice's
   executed trace beside the two honest inputs, the three hopping-tuple
   experiments in the order a program visits them, and the epsilon the k-th
   assumption promises for its class. *)
Local Notation tuple_distinguisher k :=
  (hop_tuple_distinguisher (distinguisher_of_predictor (predict k))).
Local Notation trace_game k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
         trace_of_run (I:=I k) (dsdp_protocol (R:=R) (I:=I k)) Alice]).
Local Notation G0 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k), alice_tuple_real (I:=I k)]).
Local Notation G1 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
         alice_tuple_bob_zero (I:=I k)]).
Local Notation G2 k :=
  (`p_ [% sample_V2 (I:=I k), sample_V3 (I:=I k),
         alice_tuple_all_zero (I:=I k)]).
Local Notation eps k := (indcpa_assumption_epsilon (assumption k)).

(* The guessing sequence as the distance of the trace game from the zero
   game, which is the form the terminal below reads it in.  It speaks of the
   games alone, which is what lets the program under that terminal stay
   unnamed. *)
Lemma f_guess_V2_advantageE k :
  f_guess_V2 k
  = `| accept (distinguisher_of_predictor (predict k)) (trace_game k) - 0 |.
Proof.
by rewrite /f_guess_V2 /alice_trace_guess_V2_pr guess_V2_acceptE
   (advantage0 (accept_ge0 _ _)).
Qed.

(* The asymptotic content the negligibility statements of this section spend;
   the per-k bounds below hold without it. *)
Variable N : dsdp_asymptotic Q.

(* Every label of the guessing dictionary costs a negligible family along the
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

Local Open Scope epshop_scope.

(* A sequence of predictors reading Alice's executed traces along a sequence
   of DSDP instances matches Bob's input with negligible probability, under
   the two class premises of this section.  The program at k opens at the
   trace the interpreter hands Alice, steps to her hopping tuple at no loss,
   replaces the two ciphertext slots at the epsilon the k-th assumption
   promises, and adds the residue the leaked output leaves along the DSDP
   solution fiber; two of its three terms are assumption-conditional, the
   class epsilon at Bob's key and at Charlie's, and the third is
   unconditional.  What the terminal contributes is that each of the three
   labels costs a negligible family, supplied once through the registered
   dictionary rather than summed by hand.
   That is also what separates this statement from the decrypting
   counterexample: decrypt_guess_prE puts the guessing probability at 1 for
   the predictor that decrypts Bob's ciphertext off the trace, and
   decrypt_reduction_admissible_eventuallyF below shows the same two fields
   of N eventually force that predictor's reduction adversary out of the
   class. *)
Theorem alice_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
exact: (\negligible[ f_guess_V2 by f_guess_V2_advantageE ]{ fun k =>
  \epsilon[ alice_claims_admissible_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor (predict k)) (trace_game k)) ;
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

(* The bound the same program returns at every security parameter, three
   levels of conditionality deep: one over the plaintext-space cardinality,
   information-theoretic and unconditional; twice the assumption's epsilon,
   assumption-conditional, one ciphertext replacement at Bob's key and one at
   Charlie's; and the two class premises, which restrict the adversaries the
   predictor induces.  It is what alice_trace_guess_V2_admissible_le reads at
   the sequence that repeats one instance. *)
Lemma f_guess_V2_le k :
  f_guess_V2 k <= (#|plain (scheme_AHE (I k))|%:R : R)^-1 + 2 * eps k.
Proof.
(* The program is the one the terminal above is written over; the term there
   carries no name, so the text stands a second time and the kernel checks
   each copy on its own. *)
rewrite f_guess_V2_advantageE.
exact: (result_sound (\epsilon[ alice_claims_admissible_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor (predict k)) (trace_game k)) ;
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
   one is pinned to the test a predictor induces, and a statement made at the
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

(* The trace simulation distance sequence: the distance the k-th Boolean test
   sees at the k-th instance between Alice's executed trace and the
   simulation. *)
Definition f_sim_advantage k : R :=
  alice_trace_sim_advantage (trace_distinguishers k).

(* That distance as the gap between the two games the simulation program
   joins, the executed trace at one end and the simulated trace at the other.
   Stated on the games alone, as f_guess_V2_advantageE is. *)
Lemma f_sim_advantageE k :
  f_sim_advantage k
  = `| accept (trace_distinguishers k) (trace_game k)
       - accept (trace_distinguishers k) (alice_trace_ideal (R:=R) (I k)) |.
Proof. by rewrite /f_sim_advantage /alice_trace_sim_advantage -!acceptE. Qed.

(* Along a sequence of DSDP instances, every family of Boolean tests of
   Alice's executed trace whose two induced reduction adversaries the
   assumption at k admits separates that trace from the simulation by a
   negligible amount.  This is computational indistinguishability of Alice's
   view from the simulation, the form a simulation-based secrecy claim takes
   once the parameter is free to grow, and the guessing statement above is a
   claim about one predictor where this one is a claim about every test.
   The program at k spends the two hop labels and nothing else, the steps at
   its two ends carrying the test between the executed trace and the hopping
   tuple at no loss, so the whole distance is the class-epsilon family and no
   plaintext-size term enters, which is what separates this bound from the
   guessing bound.
   Naming: [_negligible] marks a negligible_fun theorem over the named
   quantity family, paired with that family's [_advantageE] identification
   lemma, as at [alice_trace_guess_V2_negligible]. *)
Theorem alice_trace_sim_advantage_negligible :
  negligible_fun f_sim_advantage.
Proof.
exact: (\negligible[ f_sim_advantage by f_sim_advantageE ]{ fun k =>
  \epsilon[ alice_sim_claims_at k ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (trace_distinguishers k) (trace_game k)) ;
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

End dsdp_alice_family.

(* The class-conditional guessing bound at one instance, the family bound of
   f_guess_V2_le read along the sequence that repeats that instance.  The two
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
   made once, so that a statement quantified over sequences can be read at one
   instance. *)
Let const_sequence : dsdp_instance_sequence R :=
  {| sequence_instance := fun _ => I ;
     sequence_assumption := fun _ => assumption |}.

(* The trace guessing bound with both hop advantages replaced by the single
   epsilon an adversary-class assumption carries.  The bound has three levels
   of conditionality.  One over the plaintext-space cardinality is
   information-theoretic and unconditional, the residue of the leaked output
   along the DSDP solution fiber.  Twice the assumption's epsilon is
   assumption-conditional: it measures the two ciphertext replacements, one at
   Bob's key and one at Charlie's, each at the advantage the assumption
   promises rather than at its own value.  The two premises are
   class-conditional, since an assumption covers only the adversaries its
   classifier admits.
   Those premises restrict the adversary and are not proved here.  Nothing
   here shows that the two reduction adversaries built from a trace predictor
   lie in the class, and decrypt_bob_epsilon_ge shows that an assumption whose
   classifier admits every adversary is forced to an epsilon of at least
   1 - 1/#|plain AHE|.  The abstract version of that obstruction, in
   indcpa_game.v, reaches the value 1 instead, because it lets the adversary
   choose a nonzero challenge plaintext; here the challenge plaintext is fixed
   by the protocol to be Bob's uniformly distributed input, and the zero
   branch still succeeds on a fiber of mass 1/#|plain AHE|.
   Naming: extends [alice_trace_guess_V2_le] with the [admissible] variant
   token before [le]. *)
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
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys, and Bob's and Charlie's
   second-hop coins as indices into the coin space. *)
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
Let inv_pq_cardE : ((p%:R : R) * q%:R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_pq natrM. Qed.

(* The class-conditional trace guessing bound with its unconditional term
   written at the composite modulus p * q, the modulus of the Paillier-style
   instantiations.  The three levels of conditionality are the ones of
   alice_trace_guess_V2_admissible_le, with 1/(p * q) naming the
   information-theoretic term at the instance a concrete scheme supplies.
   Naming: extends [alice_trace_guess_V2_admissible_le] with the
   [pq] variant token before [le]. *)
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
rewrite inv_pq_cardE.
exact: alice_trace_guess_V2_admissible_le.
Qed.

End dsdp_alice_trace_pq.
