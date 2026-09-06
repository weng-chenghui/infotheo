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
Require Import epshop.
Require Import dsdp_instance.
Require Import dsdp_alice_hop_secrecy.

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy at the executed piSMC trace                 *)
(*                                                                            *)
(* This file connects the secrecy proof for Alice's protocol view to the      *)
(* trace produced by the piSMC interpreter. It first proves what the DSDP run *)
(* records for Alice, Bob, and Charlie.                                       *)
(*                                                                            *)
(* Alice's trace can be computed from the hopping tuple used in the secrecy   *)
(* proof. Therefore, a predictor or Boolean test on the trace can be turned   *)
(* into one on the hopping tuple.                                             *)
(*                                                                            *)
(* This gives two trace-level guarantees. A predictor's chance of recovering  *)
(* Bob's input is at most uniform guessing plus the advantages for replacing  *)
(* Bob's and Charlie's ciphertexts. A Boolean test sees at most the same two  *)
(* advantages between the real trace and a simulated trace.                   *)
(*                                                                            *)
(* Both bounds are read off epsHop programs. The simulation bound is the gap  *)
(* result of a chain that opens at the executed trace, steps to the hopping   *)
(* tuple at no loss, runs the two ciphertext replacements, and steps to the   *)
(* simulated trace at no loss, so its whole loss is the two hop advantages.   *)
(*                                                                            *)
(* The honest inputs are sampled uniformly and the public keys are fixed.     *)
(* Every section runs over one instance of dsdp_instance.v, whose fields are  *)
(* the scheme, the weights, the three private keys and the two second-hop     *)
(* coins. The averaging results read the same instance with its              *)
(* re-encryption coin replaced, so that coin is sampled rather than fixed.    *)
(* Adversaries are modeled as functions, without a running-time bound.        *)
(*                                                                            *)
(* The file also proves that Alice's trace, view, and hopping tuple leave the *)
(* same conditional entropy about Bob's input. This entropy result is         *)
(* separate from the guessing bound above.                                    *)
(*                                                                            *)
(* ```                                                                        *)
(* Execution and trace construction                                           *)
(*                                                                            *)
(*               trace_dataT == the finite observation type for traces, which *)
(*                              keeps messages and ciphertexts but hides key  *)
(*                              values behind marks                           *)
(*     trace_data_of_di_data == encodes raw interpreter data as finite trace  *)
(*                              observations                                  *)
(*            dsdp_procs_std == the DSDP programs for an additively           *)
(*                              homomorphic encryption scheme                 *)
(*          dsdp_run_tracesE == identifies the traces produced for Alice,     *)
(*                              Bob, and Charlie by the standard execution    *)
(*      dsdp_run_traces_encE == rewrites each trace ciphertext as one         *)
(*                              encryption, exposing the message and combined *)
(*                              randomness used in the security proof         *)
(*                                                                            *)
(* The bridge from the protocol view to Alice's trace                         *)
(*                                                                            *)
(*              alice_traceT == Alice's executed-trace carrier, the           *)
(*                              fifteen-round bounded sequence of encoded     *)
(*                              trace data                                    *)
(*  alice_trace_of_hop_tuple == constructs Alice's trace from the hopping     *)
(*                              tuple used in the secrecy proof               *)
(*             dsdp_protocol == runs the three programs with the values from  *)
(*                              one experiment sample                         *)
(*         trace_of_run ps i == the encoded trace party i sees in a run of    *)
(*                              the process list ps by the interpreter, as a  *)
(*                              random variable on the sample space           *)
(*                AliceTrace == Alice's encoded interpreter trace as a random *)
(*                              observation                                   *)
(* alice_trace_of_hop_tupleE == proves that the executed trace is exactly the *)
(*                              trace constructed from the hopping tuple      *)
(*                                                                            *)
(* Primary trace-security statements                                          *)
(*                                                                            *)
(*       accept_trace_tupleE == a Boolean test accepts Alice's executed       *)
(*                              trace as often as its lift accepts her        *)
(*                              hopping tuple                                 *)
(* hop_tuple_distinguisher D == the trace test D read on the hopping tuple,   *)
(*                              rebuilding the trace from a tuple and         *)
(*                              running D on it                               *)
(* alice_trace_chain predict == Alice's trace secrecy as one epsHop           *)
(*                              program, opening at the trace of a run of the *)
(*                              protocol by the interpreter                   *)
(* alice_trace_chain_admissible ==                                            *)
(*                              the same program with both hops charged at    *)
(*                              the epsilon the assumption promises, the two  *)
(*                              class memberships spent in the hop            *)
(*                              justifications                                *)
(*     bob_trace_adversary D == embeds Bob's challenge in the ciphertext of   *)
(*                              V2, rebuilds Alice's trace around it, and     *)
(*                              decides with D                                *)
(* charlie_trace_adversary D == the Charlie-key counterpart of                *)
(*                              bob_trace_adversary                           *)
(* bob_trace_predictor_epsilon predict ==                                     *)
(*                              the advantage against Bob's key of the        *)
(*                              adversary a trace predictor induces           *)
(* charlie_trace_predictor_epsilon predict ==                                 *)
(*                              the Charlie-key counterpart of                *)
(*                              bob_trace_predictor_epsilon                   *)
(*   alice_trace_guess_V2_le == bounds recovery of Bob's input from Alice's   *)
(*                              trace by uniform guessing plus the costs of   *)
(*                              the two ciphertext hops                       *)
(* alice_trace_guess_V2_pr predict ==                                         *)
(*                              the probability that a trace predictor        *)
(*                              returns Bob's input                           *)
(* alice_trace_guess_V2_admissible_le ==                                      *)
(*                              charges both ciphertext hops to the single    *)
(*                              epsilon of an adversary-class assumption,     *)
(*                              under the premise that both reduction         *)
(*                              adversaries are in the class                  *)
(*   alice_trace_simulator s == produces an ideal trace using only the leaked *)
(*                              output                                        *)
(*         alice_trace_ideal == pairs the honest inputs with the ideal trace  *)
(*                              generated from their leaked output            *)
(* accept_trace_ideal_tupleE == a Boolean test accepts the ideal trace law as *)
(*                              often as its lift accepts the all-zero tuple  *)
(*     alice_trace_sim_chain == Alice's executed trace against the ideal      *)
(*                              trace as one epsHop program, opening at the   *)
(*                              trace of a run and closing at the ideal       *)
(*                              trace, both end steps costing nothing         *)
(* alice_trace_sim_advantage_le ==                                            *)
(*                              bounds every Boolean test between the real    *)
(*                              and ideal trace laws by the costs of the two  *)
(*                              ciphertext hops                               *)
(*  alice_trace_sim_advantage == the distance a Boolean trace test sees       *)
(*                              between Alice's executed trace and the        *)
(*                              simulated one                                 *)
(* alice_trace_sim_chain_admissible ==                                        *)
(*                              the same program with both hops charged at    *)
(*                              the epsilon the assumption promises, the two  *)
(*                              class memberships spent in the hop            *)
(*                              justifications                                *)
(* alice_trace_sim_advantageE ==                                              *)
(*                              that distance is the advantage the            *)
(*                              class-conditional program bounds              *)
(*                                                                            *)
(* Why the trace preserves the relevant information                           *)
(*                                                                            *)
(*        alice_trace_tupleT == the part of the hopping tuple that Alice's    *)
(*                              trace reveals                                 *)
(*           AliceTraceTuple == that trace-visible information in the real    *)
(*                              experiment                                    *)
(*        alice_sample_restT == the sampled data other than Alice's private   *)
(*                              combine coins                                 *)
(*           AliceSampleRest == those remaining sample values as one random   *)
(*                              observation                                   *)
(*          AliceCombineRand == Alice's two private combine coins as one      *)
(*                              random observation                            *)
(* combine_rand_rest_uniformE ==                                              *)
(*                              separates the uniform sample into Alice's     *)
(*                              combine coins and all remaining data          *)
(*     combine_rand_uniformE == Alice's combine coins are uniformly sampled   *)
(*      sample_rest_uniformE == all remaining sample data is uniformly        *)
(*                              sampled                                       *)
(*   combine_rand_rest_indep == Alice's combine coins carry no information    *)
(*                              about the remaining sampled data              *)
(* v2_trace_tuple_of_sample_rest ==                                           *)
(*                              reconstructs Bob's input and the visible      *)
(*                              trace information without the combine coins   *)
(*  combine_rand_trace_indep == Alice's combine coins carry no information    *)
(*                              about Bob's input together with the visible   *)
(*                              trace information                             *)
(*   hop_tuple_of_rand_trace == rebuilds the hopping tuple from the private   *)
(*                              combine coins and visible trace information   *)
(*   rand_trace_of_hop_tuple == separates a hopping tuple into those private  *)
(*                              coins and visible trace information           *)
(* alice_hop_tuple_rand_traceE ==                                             *)
(*                              expresses the hopping tuple through this      *)
(*                              private-and-visible split                     *)
(*      trace_of_trace_tuple == reconstructs Alice's trace from the visible   *)
(*                              trace information                             *)
(*          trace_data_plain == reads a plaintext from a trace entry          *)
(*         trace_data_cipher == reads a ciphertext from a trace entry         *)
(*      trace_tuple_of_trace == reads the visible information back from an    *)
(*                              encoded trace                                 *)
(*        alice_trace_tupleE == proves that Alice's trace depends only on the *)
(*                              trace-visible information                     *)
(*  centropy_V2_trace_tupleE == Alice's trace and hopping tuple leave the     *)
(*                              same uncertainty about Bob's input            *)
(*     bob_decrypt_predictor == reads Bob's ciphertext off the trace and      *)
(*                              decrypts it with Bob's private key            *)
(*    alice_trace_decode_V2E == Bob's input is that decryption of Alice's     *)
(*                              trace                                         *)
(*     centropy_V2_trace_eq0 == conditioning on Alice's trace leaves no       *)
(*                              uncertainty about Bob's input, so the Shannon *)
(*                              reading of the real trace is degenerate       *)
(*    decrypt_bob_epsilon_ge == the decryptor's Bob-key advantage alone is at *)
(*                              least 1 - 1/#|plain AHE|                      *)
(*                                                                            *)
(* Averaging the re-encryption coin                                           *)
(*                                                                            *)
(*    alice_trace_ideal_avg == the ideal trace law after sampling the         *)
(*                              re-encryption coin                            *)
(*                                                                            *)
(* Returning to the raw interpreter trace                                     *)
(*                                                                            *)
(* di_data_of_trace_data dk pk ==                                             *)
(*                              restores finite trace observations to raw     *)
(*                              interpreter data using fixed key values       *)
(*         alice_raw_trace s == Alice's unencoded interpreter trace for one   *)
(*                              experiment sample                             *)
(*   alice_raw_trace_decodeE == proves that decoding Alice's encoded trace    *)
(*                              recovers her raw interpreter trace            *)
(* alice_raw_trace_sim_advantage_le ==                                        *)
(*                              transfers the simulation bound to tests on    *)
(*                              Alice's raw trace with no additional cost     *)
(* alice_raw_trace_guess_V2_le ==                                             *)
(*                              transfers the guessing bound to predictors on *)
(*                              Alice's raw trace with no additional cost     *)
(* alice_raw_trace_real_experiment_avg ==                                     *)
(*                              samples the re-encryption coin and tests the  *)
(*                              resulting real raw trace                      *)
(* alice_raw_trace_ideal_experiment_avg ==                                    *)
(*                              tests the averaged ideal trace after decoding *)
(*                              it to the raw trace format                    *)
(* alice_raw_trace_sim_advantage_avg_le ==                                    *)
(*                              bounds the averaged raw-trace gap by the      *)
(*                              average costs of the two ciphertext hops      *)
(*                                                                            *)
(* Composite-modulus forms                                                    *)
(*                                                                            *)
(* alice_trace_guess_V2_admissible_pq_le ==                                   *)
(*                              states the class-conditional guessing bound   *)
(*                              when the plaintext space has size p * q       *)
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

Section dsdp_alice_trace_link.
Variable I : dsdp_instance.
(* The scheme the instance runs on, its coin space and its coin decoding,
   read off the instance through the coercion. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
(* Alice's input, the three protocol weights with Charlie's weight
   invertible, and the three private keys: the instance's fields, under the
   names the DSDP protocol gives them. *)
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_a := (inst_dk_a I).
Local Notation dk_b := (inst_dk_b I).
Local Notation dk_c := (inst_dk_c I).
(* Bob's and Charlie's second-hop coins, held as indices into Renc.  The
   generic rand of he_types.v is a bare Type and carries no distribution, so
   a uniformly sampled coin is quantified over the finType of indices, and
   rand_of_renc carries an index to the randomness the protocol encrypts
   with.  The w_ prefix marks the index side of that split: rb1, rc1, ra1
   and ra2 below are rand AHE values, these two are indices. *)
Local Notation w_rb2 := (inst_rb2 I).
Local Notation w_rc2 := (inst_rc2 I).

(* The key table of the instance's three private keys, under the name the
   protocol programs read it by. *)
Local Notation pkey_of_dk := (inst_pkey_of_party I).

Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier: plaintexts and
   ciphertexts kept, both key sorts erased to marks. The summand order
   mirrors std_data's msgT + encT + privT + pubT. *)
Definition trace_dataT : finType :=
  ((plain AHE + cipher AHE) + unit + unit)%type.

(* The encoding of one datum of the standard interface into that finite image,
   applied entrywise to a trace so that a trace becomes a value of a finType
   and a predictor on it can be quantified over.
   Naming: the _of_ form of the conversion rule of dsdp_interface.v, naming
   the source type it reads. *)
Definition trace_data_of_di_data (x : di_data DI) : trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr c))
  | inl (inr _) => inl (inr tt)
  | inr _ => inr tt
  end.

(* Alice's executed-trace carrier: the fifteen-round bounded sequence of
   encoded trace data. *)
Definition alice_traceT : finType := (15.-bseq trace_dataT)%type.

(* The decryption the three programs perform on receive. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

Variables (v2 v3 r2 r3 : plain AHE) (rb1 rc1 ra1 ra2 : rand AHE).

Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let kd := di_data_of_priv_key DI.

Let palice_inst :=
  @palice DI decode pkey_of_dk dk_a v1 u1 u2 u3 r2 r3 ra1 ra2.
Let pbob_inst := @pbob DI decode pkey_of_dk dk_b v2 rb1 (rand_of_renc w_rb2).
Let pcharlie_inst :=
  @pcharlie DI decode pkey_of_dk dk_c v3 rc1 (rand_of_renc w_rc2).

(* The three piSMC programs of the DSDP protocol at the standard interface of
   an AHE scheme, which is the program list every statement below runs.
   Naming: the std suffix keeps the name clear of the two other dsdp_procs, of
   dsdp_program.v and of dsdp_pismc.v, both in scope here. *)
Definition dsdp_procs_std : seq (proc (di_data DI)) :=
  erase_aprocs [aprocs palice_inst ; pbob_inst ; pcharlie_inst].

(* The traces of the fifteen-round run at the standard interface: eleven
   entries for Alice, four for Bob and three for Charlie, each ciphertext in
   the form the programs build it.
   The evaluation is staged at fuel 10, 2 and 3, one opening per stage, and
   runs under cbv with enc, Emul, Epow, dec and pub_of_priv kept folded.
   vm_compute unfolds those five projections of the section variable AHE into
   iota-blocked matches on which Epow_encE, Emul_encE and dec_correct no
   longer fire; the delta blacklist is what keeps the three decryption steps
   rewritable.  A further operation entering the programs has to be added to
   that list. *)
Lemma dsdp_run_tracesE :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * u3 + r3 + (v2 * u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
      [:: e (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) u3)
                  (enc (pkey_of_dk Charlie) r3 ra2));
          e (Emul (Epow (enc (pkey_of_dk Bob) v2 rb1) u2)
                  (enc (pkey_of_dk Bob) r2 ra1));
          d v2; kd dk_b];
      [:: e (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) u3)
                        (enc (pkey_of_dk Charlie) r3 ra2))
                  (enc (pkey_of_dk Charlie) (v2 * u2 + r2)
                       (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof.
have bob_decE : dec dk_b (Emul (Epow (enc (pub_of_priv dk_b) v2 rb1) u2)
                               (enc (pub_of_priv dk_b) r2 ra1))
                = Some (v2 * u2 + r2).
  by rewrite Epow_encE Emul_encE dec_correct.
have charlie_decE : dec dk_c
                      (Emul (Emul (Epow (enc (pub_of_priv dk_c) v3 rc1) u3)
                                  (enc (pub_of_priv dk_c) r3 ra2))
                            (enc (pub_of_priv dk_c) (v2 * u2 + r2)
                                 (rand_of_renc w_rb2)))
                    = Some (v3 * u3 + r3 + (v2 * u2 + r2)).
  by rewrite Epow_encE !Emul_encE dec_correct.
have alice_decE : dec dk_a (enc (pub_of_priv dk_a)
                                (v3 * u3 + r3 + (v2 * u2 + r2))
                                (rand_of_renc w_rc2))
                  = Some (v3 * u3 + r3 + (v2 * u2 + r2)).
  exact: dec_correct.
rewrite /run_interp.
have -> : (15 = 10 + 5)%N by [].
rewrite interp_fuelD.
move Ht: (interp 10 dsdp_procs_std (nseq (size dsdp_procs_std) [::])) => S.
cbv -[enc Emul Epow dec pub_of_priv] in Ht.
rewrite bob_decE in Ht.
have -> : (5 = 2 + 3)%N by [].
rewrite interp_fuelD.
move Ht2: (interp 2 S.1 S.2) => S2.
rewrite -Ht in Ht2.
cbv -[enc Emul Epow dec pub_of_priv] in Ht2.
rewrite charlie_decE in Ht2.
have -> : (3 = 1 + 2)%N by [].
rewrite interp_fuelD.
move Ht3: (interp 1 S2.1 S2.2) => S3.
rewrite -Ht2 in Ht3.
cbv -[enc Emul Epow dec pub_of_priv] in Ht3.
rewrite alice_decE in Ht3.
rewrite -Ht3.
by cbv -[enc Emul Epow dec pub_of_priv].
Qed.

(* The same traces with every ciphertext normalised to a single encryption:
   a combine's randomness is the homomorphic combination of the randomness of
   its arguments. *)
Lemma dsdp_run_traces_encE :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * u3 + r3 + (v2 * u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
      [:: e (enc (pkey_of_dk Charlie) (v3 * u3 + r3)
                 (rand_mul (rand_pow rc1 u3) ra2));
          e (enc (pkey_of_dk Bob) (v2 * u2 + r2)
                 (rand_mul (rand_pow rb1 u2) ra1));
          d v2; kd dk_b];
      [:: e (enc (pkey_of_dk Charlie) (v3 * u3 + r3 + (v2 * u2 + r2))
                 (rand_mul (rand_mul (rand_pow rc1 u3) ra2)
                           (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof. by rewrite dsdp_run_tracesE !Epow_encE !Emul_encE. Qed.

End dsdp_alice_trace_link.

(* Keep every parameter of the standard proc list explicit, so that the
   per-sample instantiation is positional and independent of
   implicit-argument inference. *)
Arguments dsdp_procs_std : clear implicits.

Section dsdp_alice_trace_rv.
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
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_b := (inst_dk_b I).
Local Notation dk_c := (inst_dk_c I).
Local Notation w_rc2 := (inst_rc2 I).

(* The declarations discharged by the preceding section and by
   dsdp_alice_hop_secrecy.v take these parameters explicitly. Each
   abbreviation pins them once, under the name it abbreviates; the shadowing
   is not recursive, since the right-hand side resolves against the
   constant. *)
Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation trace_dataT := (trace_dataT I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation R2 := (sample_R2 (R:=R) (I:=I)).
Local Notation R3 := (sample_R3 (R:=R) (I:=I)).
Local Notation Rho2 := (Rho2 (R:=R) (I:=I)).
Local Notation Rho3 := (Rho3 (R:=R) (I:=I)).
Local Notation RA1 := (RA1 (R:=R) (I:=I)).
Local Notation RA2 := (RA2 (R:=R) (I:=I)).
Local Notation Sout := (Sout (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation alice_tuple_bob_zero := (alice_tuple_bob_zero (R:=R) (I:=I)).
Local Notation alice_tuple_all_zero := (alice_tuple_all_zero (R:=R) (I:=I)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation bob_challenge_adversary :=
  (bob_challenge_adversary (R:=R) (I:=I)).
Local Notation charlie_challenge_adversary :=
  (charlie_challenge_adversary (R:=R) (I:=I)).
Local Notation alice_traceT := (alice_traceT I).
Local Notation predictor := (predictor I).
Local Notation alice_simulator := (alice_simulator (R:=R) (I:=I)).
Local Notation alice_ideal := (alice_ideal (R:=R) I).

(* Alice's executed trace read off a value of her hopping tuple: the leaked
   output, Charlie's re-encryption of it, the two received ciphertexts, the
   two masks, the four weights, and the erased key mark.
   Naming: the [_of_] connective names the source the conversion reads, after
   the repository's total-conversion family. *)
Definition alice_trace_of_hop_tuple
    (v : alice_hop_tupleT I) :
    15.-bseq trace_dataT :=
  [bseq inl (inl (inl v.1.1.2));
        inl (inl (inr
          (enc (pkey_of_dk Alice)
               (v.1.1.2 - u1 * v1 + v.1.1.1.1.1 + v.1.1.1.1.2)
               (rand_of_renc w_rc2))));
        inl (inl (inr v.2));
        inl (inl (inr v.1.2));
        inl (inl (inl v.1.1.1.1.2));
        inl (inl (inl v.1.1.1.1.1));
        inl (inl (inl u3)); inl (inl (inl u2));
        inl (inl (inl u1)); inl (inl (inl v1));
        inl (inr tt)].

(* The DSDP protocol: the three piSMC programs at the coordinates of one
   sample.  The name says which protocol the process list is, so that a
   security statement can open at the protocol itself rather than at a random
   variable derived from it. *)
Definition dsdp_protocol (s : alice_sampleT I) :
    seq (proc (di_data DI)) :=
  dsdp_procs_std I (V2 s) (V3 s) (R2 s) (R3 s) (rand_of_renc (Rho2 s))
    (rand_of_renc (Rho3 s)) (rand_of_renc (RA1 s)) (rand_of_renc (RA2 s)).

(* Fuel bounds the encoded trace of any party in any sample-indexed process
   list, since encoding preserves length. *)
Lemma trace_of_run_size
    (procs : alice_sampleT I -> seq (proc (di_data DI)))
    (i : party_id) (s : alice_sampleT I) :
  (size (map (@trace_data_of_di_data I)
           (nth [::] (run_interp 15 (procs s)).2 n( i ))) <= 15)%N.
Proof. by rewrite size_map; exact: size_traces_nth. Qed.

(* The encoded trace party i sees in a run of the process list procs by the
   interpreter, as a random variable on the sample space: the observation an
   adversary sitting at that party collects when the protocol is executed at
   the sampled inputs.  This is what makes a protocol a game of a hopping
   argument, the interpreter's run entering the argument as its first game
   rather than beside it.
   Naming: the [_of_] connective names the source the observation is read
   from, after the repository's total-conversion family. *)
Definition trace_of_run
    (procs : alice_sampleT I -> seq (proc (di_data DI)))
    (i : party_id) :
    {RV (alice_sample_fdist (R:=R) I) ->
     15.-bseq trace_dataT} :=
  fun s => Bseq (trace_of_run_size procs i s).

(* Alice's encoded executed trace as a random variable on the sample space:
   what the interpreter hands her in a run of the DSDP protocol. *)
Definition AliceTrace :
    {RV (alice_sample_fdist (R:=R) I) ->
     15.-bseq trace_dataT} :=
  trace_of_run dsdp_protocol Alice.

(* The leaked output the run computes is Alice's hopping tuple slot. *)
Let Sout_runE (s : alice_sampleT I) :
  V3 s * u3 + R3 s + (V2 s * u2 + R2 s) - R2 s - R3 s + u1 * v1
  = Sout s.
Proof. by rewrite SoutE; ring. Qed.

(* The plaintext Charlie re-encrypts is the leaked output net of Alice's own
   term and masks. *)
Let reenc_plainE (s : alice_sampleT I) :
  V3 s * u3 + R3 s + (V2 s * u2 + R2 s)
  = Sout s - u1 * v1 + R2 s + R3 s.
Proof. by rewrite SoutE; ring. Qed.

(* The trace the interpreter produces for Alice is the deterministic image of
   her hopping tuple. *)
Lemma alice_trace_of_hop_tupleE :
  AliceTrace = alice_trace_of_hop_tuple `o alice_tuple_real.
Proof.
apply: boolp.funext => s; apply/val_inj.
rewrite /AliceTrace /trace_of_run.
move: (trace_of_run_size dsdp_protocol Alice s).
rewrite /dsdp_protocol dsdp_run_tracesE.
by move=> ?; rewrite /= Sout_runE reenc_plainE.
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

(* The real executed-trace law is the deterministic image of the real
   hopping-tuple law: Alice's trace holds no coordinate her hopping tuple
   does not determine. *)
Let alice_trace_realE :
  `p_ [% V2, V3, AliceTrace]
  = fdistmap (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2))
      (`p_ [% V2, V3, alice_tuple_real]).
Proof.
by rewrite alice_trace_of_hop_tupleE /dist_of_RV fdistmap_comp.
Qed.

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

(* The three hopping-tuple experiments the chain below visits after leaving
   the trace, and the two IND-CPA advantages it logs, under the short names
   that chain reads at.  G0 is the law Alice's executed trace is the image
   of, G1 and G2 the same law with Bob's and with both ciphertext slots
   carrying zero. *)
Local Notation G0 := (`p_ [% V2, V3, alice_tuple_real]).
Local Notation G1 := (`p_ [% V2, V3, alice_tuple_bob_zero]).
Local Notation G2 := (`p_ [% V2, V3, alice_tuple_all_zero]).
Local Notation eps_bob D :=
  (indcpa_epsilon (pkey_of_dk Bob) (bob_challenge_adversary D)).
Local Notation eps_charlie D :=
  (indcpa_epsilon (pkey_of_dk Charlie) (charlie_challenge_adversary D)).

Local Open Scope epshop_scope.

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

(* The probability that a predictor reading Alice's executed trace returns
   Bob's input.  This is the quantity every trace guessing bound in this file
   bounds, and it is the spelling the class-conditional bounds use, so that a
   reader can see at a glance that they bound the same number the
   unconditional bounds do.
   Naming: [_pr] marks the probability of the event just named, with the
   [alice_trace] stem naming whose observation the predictor reads. *)
Definition alice_trace_guess_V2_pr (predict : predictor alice_traceT) : R :=
  Pr (alice_sample_fdist (R:=R) I)
     [set t | (predict `o AliceTrace) t == V2 t].

(* The same argument over the same games and the same three labels, with the
   two ciphertext replacements charged at the epsilon an adversary-class
   assumption promises rather than at the advantage each reduction shows.
   The two class memberships are variables of the section and are spent in
   the justification of the hop each one licenses, so a program that exists
   has already spent them and the bound read off it leaves nothing to
   discharge.  The residue at the all-zero endpoint is the same
   information-theoretic term as in alice_trace_chain, so the total adds one
   unconditional term to two class-conditional ones.
   Naming: extends [alice_trace_chain] with the [admissible] token naming
   the quantity its hops are charged at. *)
Section alice_trace_chain_admissible.
Variable assumption : indcpa_epsilon_assumption.
Variable predict : predictor alice_traceT.
Hypothesis bob_admissible :
  indcpa_admissible assumption
    (bob_trace_adversary (distinguisher_of_predictor predict)).
Hypothesis charlie_admissible :
  indcpa_admissible assumption
    (charlie_trace_adversary (distinguisher_of_predictor predict)).

(* The predictor's distinguisher on the hopping tuple, as in the section
   above, where its advantage is written out. *)
Local Notation tuple_distinguisher :=
  (hop_tuple_distinguisher (distinguisher_of_predictor predict)).
Local Notation eps := (indcpa_assumption_epsilon assumption).

(* Naming: extends [alice_trace_chain] with the [admissible] token naming the
   quantity its hops are charged at, as the section header states. *)
Definition alice_trace_chain_admissible :=
  \epsilon[ alice_claim_admissible assumption tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept (distinguisher_of_predictor predict)
             (`p_ [% V2, V3, trace_of_run dsdp_protocol Alice])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept tuple_distinguisher G0) by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at the epsilon the assumption promises,
       which the class membership of the Bob-key reduction licenses *)
    hop cpa_bob eps to (accept tuple_distinguisher G1)
      by le_trans (le_of_eq (hop0_advantageE tuple_distinguisher))
                  (indcpa_admissible_epsilon_le dk_b bob_admissible) ;
    (* Charlie's slot zeroed, at the same epsilon, licensed by the class
       membership of the Charlie-key reduction *)
    hop cpa_charlie eps to (accept tuple_distinguisher G2)
      by le_trans (le_of_eq (hop1_advantageE tuple_distinguisher))
                  (indcpa_admissible_epsilon_le dk_c charlie_admissible) ;
    (* the guessing residue of the all-zero view, a term outside the
       hopping, added to the loss so the total bounds the trace game *)
    plus uniform_fiber #|plain AHE|%:R^-1
      by plus_le (accept_ge0 _ _)
           (all_zero_game_V2_le_invm
              (predict \o alice_trace_of_hop_tuple)) ;;
    (* the trace game, at the residue and twice the class epsilon *)
    bound ((#|plain AHE|%:R : R)^-1 + 2 * eps)
      by alice_admissible_totalE assumption }.

(* The trace guessing bound with both hop advantages replaced by the single
   epsilon an adversary-class assumption carries.  The bound has three
   levels of conditionality.  One over the plaintext-space cardinality is
   information-theoretic and unconditional, the residue of the leaked output
   along the DSDP solution fiber.  Twice the assumption's epsilon is
   assumption-conditional: it measures the two ciphertext replacements, one
   at Bob's key and one at Charlie's, each at the advantage the assumption
   promises rather than at its own value.  The two
   premises are class-conditional, since an assumption covers only the
   adversaries its classifier admits.
   Those premises restrict the adversary and are not proved here.  Nothing
   here shows that the two reduction adversaries built from a trace predictor
   lie in the class, and decrypt_bob_epsilon_ge shows that an assumption
   whose classifier admits every adversary is forced to an epsilon of
   at least 1 - 1/#|plain AHE|.  The abstract version of that obstruction, in
   indcpa_game.v, reaches the value 1 instead, because it lets the adversary
   choose a nonzero challenge plaintext; here the challenge plaintext is
   fixed by the protocol to be Bob's uniformly distributed input, and the
   zero branch still succeeds on a fiber of mass 1/#|plain AHE|.
   Naming: extends [alice_trace_guess_V2_le] with the
   [admissible] variant token before [le]. *)
Corollary alice_trace_guess_V2_admissible_le :
  alice_trace_guess_V2_pr predict
    <= (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon assumption.
Proof.
rewrite /alice_trace_guess_V2_pr guess_V2_acceptE.
rewrite -(advantage0 (accept_ge0 _ _)).
exact: result_sound alice_trace_chain_admissible.
Qed.

End alice_trace_chain_admissible.

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

(* The distribution obtained by mapping the hopping-tuple simulator through
   the encoded trace function.
   Naming: after [alice_simulator] of the hopping-tuple level, with
   [trace] marking the carrier of the simulated observation. *)
Definition alice_trace_simulator (s : plain AHE) :
    R.-fdist (15.-bseq trace_dataT) :=
  fdistmap alice_trace_of_hop_tuple (alice_simulator s).

(* The joint law of the honest inputs and the simulated encoded trace: the
   honest input law bound to the trace simulator fed the leaked output
   computed from the sampled inputs.
   Naming: after [alice_ideal] of the hopping-tuple level. *)
Definition alice_trace_ideal :
    R.-fdist (plain AHE * plain AHE * 15.-bseq trace_dataT) :=
  `p_ [% V2, V3] >>= (fun vv =>
    fdistmap (fun tr => (vv.1, vv.2, tr))
      (alice_trace_simulator
        (dsdp_output v1 u1 u2 u3 vv.1 vv.2))).

(* The trace-level ideal law is the deterministic image of the hopping-tuple
   ideal law. *)
Let alice_trace_idealE :
  alice_trace_ideal
  = fdistmap (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2))
      alice_ideal.
Proof.
rewrite /alice_trace_ideal /alice_ideal fdistmap_bind.
congr (_ >>= _); apply: boolp.funext => vv.
by rewrite /alice_trace_simulator 2!fdistmap_comp.
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
  Pr (alice_sample_fdist (R:=R) I)
     [set t | (predict `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_epsilon (pkey_of_dk Bob)
           (bob_trace_adversary (distinguisher_of_predictor predict))
       + indcpa_epsilon (pkey_of_dk Charlie)
           (charlie_trace_adversary (distinguisher_of_predictor predict)).
Proof.
(* The trace game is the simulated game plus the distance between them, and
   the two are bounded separately. *)
have step (x y u v : R) : y <= u -> `|x - y| <= v -> x <= u + v.
  move=> Hy Hv.
  have -> : x = y + (x - y) by ring.
  by apply: lerD => //; exact: le_trans (ler_norm _) Hv.
have Hsim : `| accept (distinguisher_of_predictor predict)
                 (`p_ [% V2, V3, AliceTrace])
               - accept (distinguisher_of_predictor predict)
                   alice_trace_ideal |
             <= indcpa_epsilon (pkey_of_dk Bob)
                  (bob_trace_adversary (distinguisher_of_predictor predict))
                + indcpa_epsilon (pkey_of_dk Charlie)
                    (charlie_trace_adversary
                       (distinguisher_of_predictor predict)).
  by rewrite 2!acceptE; exact: alice_trace_sim_advantage_le.
rewrite guess_V2_acceptE -addrA.
apply: (step _ (accept (distinguisher_of_predictor predict)
                  alice_trace_ideal)).
  rewrite accept_trace_ideal_tupleE.
  exact: (all_zero_game_V2_le_invm (predict \o alice_trace_of_hop_tuple)).
exact: Hsim.
Qed.

End alice_trace_guess.

(* The same argument as alice_trace_sim_chain over the same four games, with
   the two ciphertext replacements charged at the epsilon an adversary-class
   assumption promises rather than at the advantage its own reduction shows.
   The two class memberships are variables of the section and are spent in
   the justification of the hop each one licenses, so a program that exists
   has already spent them.  The program carries no terminal statement, so
   what it returns on its own is the class-conditional trace simulation
   bound: a test tells Alice's executed trace from the simulation only as
   often as twice the class epsilon allows, and the two steps at the ends
   carry the test between the trace and the hopping tuple at no loss.  It is
   the program the sequence statement reads.
   Naming: extends [alice_trace_sim_chain] with the [admissible] token naming
   the quantity its hops are charged at, as [alice_trace_chain_admissible]
   extends [alice_trace_chain]. *)
Section alice_trace_sim_chain_admissible.
Variable assumption : indcpa_epsilon_assumption.
Variable D : distinguisher (plain AHE * plain AHE * alice_traceT)%type.
Hypothesis bob_admissible :
  indcpa_admissible assumption (bob_trace_adversary D).
Hypothesis charlie_admissible :
  indcpa_admissible assumption (charlie_trace_adversary D).

(* The trace test D on the hopping tuple, as in the section above, where the
   advantage it is read at is written out. *)
Local Notation tuple_distinguisher := (hop_tuple_distinguisher D).
Local Notation eps := (indcpa_assumption_epsilon assumption).

(* Naming: extends [alice_trace_sim_chain] with the [admissible] token naming
   the quantity its hops are charged at, as the section header states. *)
Definition alice_trace_sim_chain_admissible :=
  \epsilon[ alice_claim_admissible assumption tuple_distinguisher ]{
    (* the trace of a run of the protocol by the interpreter *)
    start (accept D (`p_ [% V2, V3, trace_of_run dsdp_protocol Alice])) ;
    (* her trace is a deterministic image of her hopping tuple *)
    same to (accept tuple_distinguisher G0) by accept_trace_tupleE _ ;
    (* Bob's ciphertext slot zeroed, at the epsilon the assumption promises,
       which the class membership of the Bob-key reduction licenses *)
    hop cpa_bob eps to (accept tuple_distinguisher G1)
      by le_trans (le_of_eq (hop0_advantageE tuple_distinguisher))
                  (indcpa_admissible_epsilon_le dk_b bob_admissible) ;
    (* Charlie's slot zeroed, at the same epsilon, licensed by the class
       membership of the Charlie-key reduction *)
    hop cpa_charlie eps to (accept tuple_distinguisher G2)
      by le_trans (le_of_eq (hop1_advantageE tuple_distinguisher))
                  (indcpa_admissible_epsilon_le dk_c charlie_admissible) ;
    (* the simulated trace is that same image of the all-zero tuple *)
    same to (accept D alice_trace_ideal)
      by esym (accept_trace_ideal_tupleE D) }.

(* The distance a trace test sees is the advantage the class-conditional
   program bounds.  That identification is what lets a statement about the
   program, such as the negligibility of its advantage along a sequence of
   security parameters, be read as a statement about the distance between the
   executed trace and the simulation.
   Naming: [_advantageE] marks the identification of the named quantity with
   the advantage of a program, as [f_guess_V2_advantageE] does at the
   sequence. *)
Lemma alice_trace_sim_advantageE :
  alice_trace_sim_advantage D
  = result_advantage alice_trace_sim_chain_admissible.
Proof. by rewrite /alice_trace_sim_advantage -!acceptE. Qed.

End alice_trace_sim_chain_admissible.

End dsdp_alice_trace_rv.

Section dsdp_alice_trace_centropy.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys, and Bob's and Charlie's
   second-hop coins as indices into the coin space. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_b := (inst_dk_b I).
Local Notation w_rc2 := (inst_rc2 I).

(* Each abbreviation pins, under the name it abbreviates, the parameters that
   dsdp_alice_hop_secrecy.v discharges; the shadowing is not recursive,
   since the right-hand side resolves against the constant. *)
Local Notation P := (alice_sample_fdist (R:=R) I).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation R2 := (sample_R2 (R:=R) (I:=I)).
Local Notation R3 := (sample_R3 (R:=R) (I:=I)).
Local Notation RA1 := (RA1 (R:=R) (I:=I)).
Local Notation RA2 := (RA2 (R:=R) (I:=I)).
Local Notation Sout := (Sout (R:=R) (I:=I)).
Local Notation bob_real_cipher := (bob_real_cipher (R:=R) (I:=I)).
Local Notation charlie_real_cipher := (charlie_real_cipher (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).

(* The part of Alice's hopping tuple her executed trace shows: the two masks,
   the leaked output and the two received ciphertexts. *)
Definition alice_trace_tupleT : finType :=
  ((plain AHE * plain AHE) * plain AHE * cipher AHE * cipher AHE)%type.

(* The trace-visible part of Alice's hopping tuple as a random variable on the
   sample space: the two masks, the leaked output, and the two received
   ciphertexts of the real experiment, both slots carrying real
   encryptions. *)
Definition AliceTraceTuple : {RV P -> alice_trace_tupleT} :=
  [% [% R2, R3], Sout, bob_real_cipher, charlie_real_cipher].

(* The sample coordinates other than Alice's two combine randomnesses: the two
   honest inputs, the two masks and the two hop encryption randomnesses. *)
Definition alice_sample_restT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE) * (Renc * Renc))%type.

(* The random variable of those coordinates. *)
Definition AliceSampleRest : {RV P -> alice_sample_restT} := fun t => t.1.

(* The random variable of Alice's two combine randomnesses. *)
Definition AliceCombineRand : {RV P -> (Renc * Renc)} := fun t => t.2.

Let card_combine_rand : #|((Renc * Renc)%type : finType)|
            = #|((Renc * Renc)%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceCombineRand). Qed.

Let card_sample_rest : #|alice_sample_restT| = #|alice_sample_restT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceSampleRest). Qed.

Let card_combine_rand_rest :
  #|(((Renc * Renc) * alice_sample_restT)%type : finType)|
  = #|(((Renc * Renc) * alice_sample_restT)%type : finType)|.-1.+1.
Proof.
exact: fdist_card_prednK (`p_ [% AliceCombineRand, AliceSampleRest]).
Qed.

(* Alice's combine randomnesses and the other sample coordinates are jointly
   uniform. *)
Lemma combine_rand_rest_uniformE :
  `p_ [% AliceCombineRand, AliceSampleRest]
  = (fdist_uniform card_combine_rand) `x (fdist_uniform card_sample_rest).
Proof.
rewrite -(fdist_uniform_prod card_combine_rand card_sample_rest
           card_combine_rand_rest)
        /dist_of_RV alice_sample_fdistE.
apply: fdistmap_bij_uniform.
exists (fun p : (Renc * Renc) * alice_sample_restT => (p.2, p.1)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[ra1 ra2] [[[v2 v3] [r2 r3]] [rho2 rho3]]].
Qed.

(* Alice's combine randomnesses are uniform. *)
Lemma combine_rand_uniformE :
  `p_ AliceCombineRand = fdist_uniform card_combine_rand.
Proof.
by rewrite -(fst_RV2 AliceCombineRand AliceSampleRest)
   combine_rand_rest_uniformE fdist_prod1.
Qed.

(* The other sample coordinates are uniform. *)
Lemma sample_rest_uniformE :
  `p_ AliceSampleRest = fdist_uniform card_sample_rest.
Proof.
by rewrite -(snd_RV2 AliceCombineRand AliceSampleRest)
   combine_rand_rest_uniformE fdist_prod2.
Qed.

(* Alice's combine randomnesses are independent of the other sample
   coordinates.
   Naming: [_indep] is the local spelling for an independence statement,
   after [alice_spectator_indep] and [spectator_pre_indep]; the [inde_]
   prefix is reserved for the general theory in [proba.v]. *)
Lemma combine_rand_rest_indep : P |= AliceCombineRand _|_ AliceSampleRest.
Proof.
by apply: inde_RV_of_prod;
   rewrite combine_rand_rest_uniformE combine_rand_uniformE
           sample_rest_uniformE.
Qed.

(* Bob's input and the trace-visible tuple, rebuilt from the sample
   coordinates other than Alice's combine randomnesses.
   The output slot is written with [uncurry] applied to an explicit pair
   because [Sout] is itself [uncurry (dsdp_output ...) `o [% V2, V3]]; the
   curried spelling is not convertible and breaks the proof below.
   Naming: [_of_] names the source the conversion reads, after the
   repository's total-conversion family; the length is a byproduct of
   naming both the pair it builds and the coordinates it reads. *)
Definition v2_trace_tuple_of_sample_rest (u : alice_sample_restT) :
    (plain AHE * alice_trace_tupleT) :=
  (u.1.1.1,
   ((u.1.2.1, u.1.2.2),
    uncurry (dsdp_output v1 u1 u2 u3) (u.1.1.1, u.1.1.2),
    enc (pkey_of_dk Bob) u.1.1.1 (rand_of_renc u.2.1),
    enc (pkey_of_dk Charlie) u.1.1.2 (rand_of_renc u.2.2))).

(* Alice's two combine randomnesses are independent of Bob's input taken
   jointly with everything her executed trace shows.
   Naming: [_indep] as in [combine_rand_rest_indep] above. *)
Lemma combine_rand_trace_indep :
  P |= [% RA1, RA2] _|_ [% V2, AliceTraceTuple].
Proof.
(* The pair function must stay eta-expanded: [prod] has no definitional eta,
   so [idfun] does not typecheck here. *)
exact: (inde_RV_comp (fun p : Renc * Renc => (p.1, p.2))
          v2_trace_tuple_of_sample_rest combine_rand_rest_indep).
Qed.

(* Alice's hopping tuple rebuilt from her combine randomnesses and the
   trace-visible tuple.
   Naming: [_of_] names the source the conversion reads, after the
   repository's total-conversion family. *)
Definition hop_tuple_of_rand_trace
    (p : ((Renc * Renc) * alice_trace_tupleT)) :
    alice_hop_tupleT I :=
  (p.2.1.1.1, p.1, p.2.1.1.2, p.2.1.2, p.2.2).

(* The combine randomnesses and the trace-visible tuple read back off a
   hopping tuple.
   Naming: [_of_] as in [hop_tuple_of_rand_trace], in the opposite
   direction. *)
Definition rand_trace_of_hop_tuple
    (v : alice_hop_tupleT I) :
    ((Renc * Renc) * alice_trace_tupleT) :=
  (v.1.1.1.2, (v.1.1.1.1, v.1.1.2, v.1.2, v.2)).

(* The two relabellings are mutually inverse.
   Naming: the [K] suffix marks a cancellation lemma, after MathComp. *)
Lemma hop_tuple_of_rand_traceK :
  cancel hop_tuple_of_rand_trace rand_trace_of_hop_tuple.
Proof. by case=> ra [[[m s] c0] c1]. Qed.

(* Alice's hopping tuple is her combine randomnesses together with the
   trace-visible tuple.
   Naming: the [E] suffix marks an equation, after [SoutE]. *)
Lemma alice_hop_tuple_rand_traceE :
  alice_tuple_real
  = hop_tuple_of_rand_trace `o [% [% RA1, RA2], AliceTraceTuple].
Proof.
(* The combine randomnesses stay eta-expanded as [% RA1, RA2]: [prod] has no
   definitional eta, so [AliceCombineRand] is not convertible with the pair
   the hopping tuple carries. *)
by [].
Qed.

(* Alice's executed trace read off the trace-visible tuple: the leaked
   output, Charlie's re-encryption of it, the two received ciphertexts, the
   two masks, the four weights, and the erased key mark.
   Naming: [_of_] as in [hop_tuple_of_rand_trace]. *)
Definition trace_of_trace_tuple (q : alice_trace_tupleT) :
    15.-bseq (trace_dataT I) :=
  [bseq inl (inl (inl q.1.1.2));
        inl (inl (inr
          (enc (pkey_of_dk Alice)
               (q.1.1.2 - u1 * v1 + q.1.1.1.1 + q.1.1.1.2)
               (rand_of_renc w_rc2))));
        inl (inl (inr q.2));
        inl (inl (inr q.1.2));
        inl (inl (inl q.1.1.1.2));
        inl (inl (inl q.1.1.1.1));
        inl (inl (inl u3)); inl (inl (inl u2));
        inl (inl (inl u1)); inl (inl (inl v1));
        inl (inr tt)].

(* The plaintext carried by a trace entry, zero at any other sort. *)
Definition trace_data_plain (x : trace_dataT I) :
    plain AHE :=
  if x is inl (inl (inl m)) then m else 0.

(* The ciphertext carried by a trace entry, a fixed encryption of zero at any
   other sort. *)
Definition trace_data_cipher (x : trace_dataT I) :
    cipher AHE :=
  if x is inl (inl (inr c)) then c
  else enc (pkey_of_dk Alice) 0 (rand_of_renc w_rc2).

(* The trace-visible tuple read back off an encoded trace, at the five
   positions the encoding writes it to.
   Naming: [_of_] as in [hop_tuple_of_rand_trace]. *)
Definition trace_tuple_of_trace
    (b : 15.-bseq (trace_dataT I)) :
    alice_trace_tupleT :=
  let s := bseqval b in
  ((trace_data_plain (nth (inr tt) s 5),
    trace_data_plain (nth (inr tt) s 4)),
   trace_data_plain (nth (inr tt) s 0),
   trace_data_cipher (nth (inr tt) s 3),
   trace_data_cipher (nth (inr tt) s 2)).

(* Encoding the trace-visible tuple into a trace is left-invertible.
   Naming: [K] as in [hop_tuple_of_rand_traceK]. *)
Lemma trace_of_trace_tupleK :
  cancel trace_of_trace_tuple trace_tuple_of_trace.
Proof. by case=> [[[m s] c0] c1]; case: m => r2 r3. Qed.

(* Alice's executed trace is the image of the trace-visible tuple. *)
Lemma alice_trace_tupleE :
  AliceTrace = trace_of_trace_tuple `o AliceTraceTuple.
Proof. by rewrite alice_trace_of_hop_tupleE. Qed.

(* Conditioning on Alice's executed trace leaves the same uncertainty about
   Bob's input as conditioning on her hopping tuple. *)
Theorem centropy_V2_trace_tupleE :
  `H( V2 | AliceTrace ) = `H( V2 | alice_tuple_real ).
Proof.
rewrite alice_trace_tupleE (can_centropy_eq trace_of_trace_tupleK).
rewrite alice_hop_tuple_rand_traceE
        (can_centropy_eq hop_tuple_of_rand_traceK).
by rewrite (inde_centropy_eq combine_rand_trace_indep).
Qed.

(* Bob's ciphertext slot of Alice's executed trace, decrypted with Bob's own
   private key: the predictor an adversary holding dk_b runs.  Slot 3 is
   where trace_of_trace_tuple writes the ciphertext Alice receives from Bob,
   and dec_correct inverts it, so this predictor names Bob's input on every
   sample.  It sits outside the attack model the hop ladder's bounds are
   stated in, which grants the public keys alone, and it is the witness that
   the ladder's bounds cannot be widened to every adversary.
   Both default branches are unreachable on the traces this predictor is run
   against.  Every trace in the image of trace_of_trace_tuple carries a
   ciphertext at slot 3, so the fixed zero encryption trace_data_cipher
   returns at any other sort is never read; and dec_correct sends that
   ciphertext to Some, so the plaintext zero returned on None is never
   returned either.
   Naming: the party owning the key comes first, as in
   [bob_trace_predictor_epsilon]; [decrypt] names what the predictor does with
   the slot it reads. *)
Definition bob_decrypt_predictor : predictor I (alice_traceT I) :=
  fun b => if dec dk_b (trace_data_cipher (nth (inr tt) (bseqval b) 3))
           is Some m then m else 0.

(* Bob's input is a deterministic function of Alice's executed trace.  The
   correctness of decryption is what makes it one: Alice's trace carries
   Bob's ciphertext, and a holder of dk_b reads the plaintext off it.  The
   protocol contributes only the fact that the ciphertext is in the trace.
   Naming: [decode] names the direction the equation is read in and [V2] the
   value recovered, after [alice_raw_trace_decodeE]; the [E] suffix marks the
   equation. *)
Lemma alice_trace_decode_V2E :
  V2 = bob_decrypt_predictor `o AliceTrace.
Proof.
rewrite alice_trace_tupleE; apply/boolp.funext => t.
by rewrite /comp_RV /bob_decrypt_predictor /= dec_correct.
Qed.

(* Conditioning on Alice's executed trace leaves no uncertainty about Bob's
   input.  The Shannon reading of the real trace is therefore degenerate, and
   the equality above transports that degeneracy to her hopping tuple.  The
   statements about the real trace that carry
   content are the guessing bounds, which quantify over predictors holding
   the public keys alone; conditional entropy quantifies over nothing and so
   charges the decryptor as well.
   Naming: [eq0] states the value the quantity takes, after MathComp. *)
Corollary centropy_V2_trace_eq0 : `H( V2 | AliceTrace ) = 0.
Proof. by rewrite {1}alice_trace_decode_V2E centropy_RV_comp0. Qed.

End dsdp_alice_trace_centropy.

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

Section dsdp_alice_trace_avg.
Context {R : realType}.
Variable I : dsdp_instance.
(* The instance's fields under the names the corrupted-Alice development
   gives them: the scheme data through the coercion, Alice's input and the
   three protocol weights, the three private keys, and Bob's and Charlie's
   second-hop coins as indices into the coin space. *)
Local Notation AHE := (scheme_AHE I).
Local Notation card_renc := (scheme_card_renc I).

(* Each abbreviation reads the instance, except the per-coin one, which reads
   the instance with Charlie's second-hop coin replaced by w. *)
Local Notation trace_dataT := (trace_dataT I).
Local Notation alice_trace_ideal_coin w :=
  (alice_trace_ideal (R:=R) (inst_with_rc2 I w)).

(* The ideal trace joint law with a uniformly sampled re-encryption coin.
   The coin the simulator re-encrypts with is drawn rather than fixed, which
   is what makes the raw-trace simulation bound of the section below a
   statement about the protocol rather than about one of its executions.
   Naming: after [alice_trace_ideal], with [avg] marking the sampled coin. *)
Definition alice_trace_ideal_avg :
    R.-fdist (plain AHE * plain AHE * 15.-bseq trace_dataT) :=
  fdist_uniform card_renc >>= (fun w =>
    (alice_trace_ideal_coin w
       : R.-fdist (plain AHE * plain AHE * 15.-bseq trace_dataT))).

End dsdp_alice_trace_avg.

Section dsdp_alice_raw_trace.
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
Local Notation u3 := (inst_u3 I).
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

(* The fixed-key decoding of one encoded trace datum: plaintexts and
   ciphertexts restored as themselves, the private-key mark restored as dk,
   the public-key mark as pk.  There is no global inverse: the encoding
   erases which key value each mark carried.
   Naming: the [_of_] connective names the source the conversion reads,
   after [trace_data_of_di_data], in the opposite direction. *)
Definition di_data_of_trace_data (dk : priv_key AHE) (pk : pub_key AHE)
    (x : trace_dataT) : di_data DI :=
  match x with
  | inl (inl (inl m)) => di_data_of_plain DI m
  | inl (inl (inr c)) => di_data_of_cipher DI c
  | inl (inr _) => di_data_of_priv_key DI dk
  | inr _ => di_data_of_pub_key DI pk
  end.

(* Decoding at Alice's own key pair, the only setting in which the encoding
   is inverted.  [alice_raw_trace_decodeE] keeps the general two-key form
   because Alice's trace holds no public-key mark to constrain. *)
Local Notation decode_a := (di_data_of_trace_data dk_a (pub_of_priv dk_a)).

(* Alice's raw interpreter trace at one sample.  A plain function: di_data
   DI is not a finType and no distribution on it is ever formed. *)
Definition alice_raw_trace (s : alice_sampleT I) :
    seq (di_data DI) :=
  nth [::]
      (run_interp 15 (dsdp_protocol (R:=R) s)).2 0.

(* The round trip on Alice's actual generated trace: decoding with her
   private key restores the raw interpreter trace.  The public key pk is
   universally quantified because her trace contains no public-key mark.
   Naming: the [E] suffix marks the round-trip equation. *)
Lemma alice_raw_trace_decodeE (pk : pub_key AHE)
    (s : alice_sampleT I) :
  map (di_data_of_trace_data dk_a pk) (AliceTrace s) = alice_raw_trace s.
Proof.
rewrite -map_comp /alice_raw_trace /dsdp_protocol.
by rewrite dsdp_run_tracesE.
Qed.

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

End dsdp_alice_raw_trace.

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
