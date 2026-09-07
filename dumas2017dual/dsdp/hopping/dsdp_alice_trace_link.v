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
(* alice_trace_of_hop_tupleE is what makes the trace level lose nothing: it   *)
(* lets the run the interpreter performs stand as the first game of a hopping *)
(* argument whose remaining games live at the tuple, so what an adversary is  *)
(* shown is the executed protocol rather than a tuple standing for it.        *)
(* alice_trace_simulator and alice_trace_ideal are the ideal world such an    *)
(* argument closes at, built from the leaked output alone.  The programs that *)
(* run between those two ends, and the bounds they return, are in             *)
(* dsdp_alice_main.v.                                                         *)
(*                                                                            *)
(* The honest inputs are sampled uniformly and the public keys are fixed.     *)
(* Every section runs over one instance of dsdp_instance.v, whose fields are  *)
(* the scheme, the weights and the three private keys.  The six encryption    *)
(* coins are sample coordinates, handed to the interpreter as the parties'    *)
(* seed streams.  Adversaries are modeled as functions, without a             *)
(* running-time bound.                                                        *)
(*                                                                            *)
(* Coins are held as indices into a finite coin space, because rand of        *)
(* he_types.v is a bare Type carrying no distribution and a uniformly sampled *)
(* coin has to range over a finType.  The std suffix of dsdp_procs_std        *)
(* separates that program list from the dsdp_procs of dsdp_program.v and of   *)
(* dsdp_pismc.v, both in scope here.                                          *)
(*                                                                            *)
(* The file also proves that Alice's trace, view, and hopping tuple leave the *)
(* same conditional entropy about Bob's input.  That is a Shannon reading of  *)
(* the real trace and is independent of the computational bounds.             *)
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
(*               dsdp_seeds c == the seed streams one coin record supplies to *)
(*                              the three parties                             *)
(*          dsdp_run_tracesE == identifies the traces produced for Alice,     *)
(*                              Bob, and Charlie by the standard execution    *)
(*      dsdp_run_traces_encE == rewrites each trace ciphertext as one         *)
(*                              encryption, exposing the message and combined *)
(*                              randomness used in the security proof         *)
(*                                                                            *)
(* The bridge from the protocol view to Alice's trace                         *)
(*                                                                            *)
(*              alice_traceT == Alice's executed-trace carrier, the           *)
(*                              eighteen-round bounded sequence of encoded    *)
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
(* The real and the ideal trace law                                           *)
(*                                                                            *)
(*         alice_trace_realE == the law of Alice's executed trace beside the  *)
(*                              honest inputs is the deterministic image of   *)
(*                              the real hopping-tuple law                    *)
(*   alice_trace_simulator s == produces an ideal trace using only the leaked *)
(*                              output                                        *)
(*         alice_trace_ideal == pairs the honest inputs with the ideal trace  *)
(*                              generated from their leaked output            *)
(*        alice_trace_idealE == that ideal law is the same image of the       *)
(*                              all-zero hopping-tuple ideal law              *)
(*                                                                            *)
(* Why the trace preserves the relevant information                           *)
(*                                                                            *)
(*         alice_trace_tuple == the record of the part of the hopping         *)
(*                              tuple that Alice's trace reveals              *)
(*           AliceTraceTuple == that trace-visible information in the real    *)
(*                              experiment                                    *)
(*        alice_sample_restT == the sampled data other than Alice's private   *)
(*                              combine coins                                 *)
(*           AliceSampleRest == those remaining sample values as one random   *)
(*                              observation                                   *)
(*          AliceCombineCoins == Alice's two private combine coins as one     *)
(*                              random observation                            *)
(* combine_coins_rest_uniformE ==                                             *)
(*                              separates the uniform sample into Alice's     *)
(*                              combine coins and all remaining data          *)
(*     combine_coins_uniformE == Alice's combine coins are uniformly sampled  *)
(*      sample_rest_uniformE == all remaining sample data is uniformly        *)
(*                              sampled                                       *)
(*   combine_coins_rest_indep == Alice's combine coins carry no information   *)
(*                              about the remaining sampled data              *)
(* v2_trace_tuple_of_sample_rest ==                                           *)
(*                              reconstructs Bob's input and the visible      *)
(*                              trace information without the combine coins   *)
(*  combine_coins_trace_indep == Alice's combine coins carry no information   *)
(*                              about Bob's input together with the visible   *)
(*                              trace information                             *)
(*   hop_tuple_of_coins_trace == rebuilds the hopping tuple from the private   *)
(*                              combine coins and visible trace information   *)
(*   coins_trace_of_hop_tuple == separates a hopping tuple into those private  *)
(*                              coins and visible trace information           *)
(* alice_hop_tuple_coins_traceE ==                                             *)
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
(*          trace_priv_keys == the private keys a raw trace records           *)
(* alice_raw_trace_priv_keysE == Alice's executed trace holds her own private *)
(*                              key and no other                              *)
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
   invertible, and the three private keys.  These are instance fields, under
   the names the DSDP protocol gives them. *)
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_a := (inst_dk_a I).
Local Notation dk_b := (inst_dk_b I).
Local Notation dk_c := (inst_dk_c I).

(* The key table of the instance's three private keys, under the name the
   protocol programs read it by. *)
Local Notation pkey_of_dk := (inst_pkey_of_party I).

Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier.  Plaintexts and
   ciphertexts are kept and the key and coin sorts erased to marks, in the
   summand order of std_data. *)
Definition trace_dataT : finType :=
  ((plain AHE + cipher AHE) + unit + unit)%type.

(* The encoding of one datum of the standard interface into that finite image.
   Applied entrywise, it makes a trace a finType value that a predictor can
   range over. *)
Definition trace_data_of_di_data (x : di_data DI) : trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr c))
  | inl (inr _) => inl (inr tt)
  | inr (inl _) => inr tt
  | inr (inr _) => inr tt
  end.

(* Alice's executed-trace carrier: the eighteen-round bounded sequence of
   encoded trace data. *)
Definition alice_traceT : finType := (18.-bseq trace_dataT)%type.

(* The decryption the three programs perform on receive. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

Variables (v2 v3 r2 r3 : plain AHE).

Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let kd := di_data_of_priv_key DI.
Let rd := di_data_of_rand DI.

Let palice_inst := @palice DI decode pkey_of_dk dk_a v1 u1 u2 u3 r2 r3.
Let pbob_inst := @pbob DI decode pkey_of_dk dk_b v2.
Let pcharlie_inst := @pcharlie DI decode pkey_of_dk dk_c v3.

(* The three piSMC programs of DSDP at the standard interface of an AHE
   scheme.  Every statement below runs this program list. *)
Definition dsdp_procs_std : seq (proc (di_data DI)) :=
  erase_aprocs [aprocs palice_inst ; pbob_inst ; pcharlie_inst].

(* The seed streams one coin record supplies, in the party order alice, bob,
   charlie.  Each party's stream holds the two coins its program draws, in the
   order it encrypts. *)
Definition dsdp_seeds (c : dsdp_enc_coins I) : seq (seq (di_data DI)) :=
  [:: [:: rd (rand_of_renc (coin_ra1 c)); rd (rand_of_renc (coin_ra2 c))];
      [:: rd (rand_of_renc (coin_rb1 c)); rd (rand_of_renc (coin_rb2 c))];
      [:: rd (rand_of_renc (coin_rc1 c)); rd (rand_of_renc (coin_rc2 c))]].

(* The traces of the eighteen-round run: eleven entries for Alice, four for
   Bob, three for Charlie.  Each ciphertext appears in the form the programs
   build it, under the coin the party drew. *)
Lemma dsdp_run_tracesE (c : dsdp_enc_coins I) :
  (run_interp 18 dsdp_procs_std (dsdp_seeds c)).1.2 =
  [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * u3 + r3 + (v2 * u2 + r2))
                 (rand_of_renc (coin_rc2 c)));
          e (enc (pkey_of_dk Charlie) v3 (rand_of_renc (coin_rc1 c)));
          e (enc (pkey_of_dk Bob) v2 (rand_of_renc (coin_rb1 c)));
          d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
      [:: e (Emul (Epow (enc (pkey_of_dk Charlie) v3
                             (rand_of_renc (coin_rc1 c))) u3)
                  (enc (pkey_of_dk Charlie) r3 (rand_of_renc (coin_ra2 c))));
          e (Emul (Epow (enc (pkey_of_dk Bob) v2
                             (rand_of_renc (coin_rb1 c))) u2)
                  (enc (pkey_of_dk Bob) r2 (rand_of_renc (coin_ra1 c))));
          d v2; kd dk_b];
      [:: e (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3
                                   (rand_of_renc (coin_rc1 c))) u3)
                        (enc (pkey_of_dk Charlie) r3
                             (rand_of_renc (coin_ra2 c))))
                  (enc (pkey_of_dk Charlie) (v2 * u2 + r2)
                       (rand_of_renc (coin_rb2 c))));
          d v3; kd dk_c]].
Proof.
(* The evaluation is staged, one opening per stage, and runs under cbv with
   enc, Emul, Epow, dec and pub_of_priv kept folded.  vm_compute unfolds those
   five projections of the section variable AHE into iota-blocked matches on
   which Epow_encE, Emul_encE and dec_correct no longer fire, and the delta
   blacklist is what keeps the three decryption steps rewritable.  A further
   operation entering the programs has to be added to that list. *)
have bob_decE : dec dk_b (Emul (Epow (enc (pub_of_priv dk_b) v2
                                          (rand_of_renc (coin_rb1 c))) u2)
                               (enc (pub_of_priv dk_b) r2
                                    (rand_of_renc (coin_ra1 c))))
                = Some (v2 * u2 + r2).
  by rewrite Epow_encE Emul_encE dec_correct.
have charlie_decE : dec dk_c
                      (Emul (Emul (Epow (enc (pub_of_priv dk_c) v3
                                              (rand_of_renc (coin_rc1 c))) u3)
                                  (enc (pub_of_priv dk_c) r3
                                       (rand_of_renc (coin_ra2 c))))
                            (enc (pub_of_priv dk_c) (v2 * u2 + r2)
                                 (rand_of_renc (coin_rb2 c))))
                    = Some (v3 * u3 + r3 + (v2 * u2 + r2)).
  by rewrite Epow_encE !Emul_encE dec_correct.
have alice_decE : dec dk_a (enc (pub_of_priv dk_a)
                                (v3 * u3 + r3 + (v2 * u2 + r2))
                                (rand_of_renc (coin_rc2 c)))
                  = Some (v3 * u3 + r3 + (v2 * u2 + r2)).
  exact: dec_correct.
rewrite /run_interp.
have -> : (18 = 12 + 6)%N by [].
rewrite interp_fuelD.
move Ht: (interp 12 dsdp_procs_std (nseq (size dsdp_procs_std) [::])
            (dsdp_seeds c)) => S.
cbv -[enc Emul Epow dec pub_of_priv] in Ht.
rewrite bob_decE in Ht.
have -> : (6 = 3 + 3)%N by [].
rewrite interp_fuelD.
move Ht2: (interp 3 S.1.1 S.1.2 S.2) => S2.
rewrite -Ht in Ht2.
cbv -[enc Emul Epow dec pub_of_priv] in Ht2.
rewrite charlie_decE in Ht2.
have -> : (3 = 2 + 1)%N by [].
rewrite interp_fuelD.
move Ht3: (interp 2 S2.1.1 S2.1.2 S2.2) => S3.
rewrite -Ht2 in Ht3.
cbv -[enc Emul Epow dec pub_of_priv] in Ht3.
rewrite alice_decE in Ht3.
rewrite -Ht3.
by cbv -[enc Emul Epow dec pub_of_priv].
Qed.

(* The same traces with every ciphertext normalised to a single encryption.
   A combine's randomness is the homomorphic combination of its arguments'
   randomness. *)
Lemma dsdp_run_traces_encE (c : dsdp_enc_coins I) :
  (run_interp 18 dsdp_procs_std (dsdp_seeds c)).1.2 =
  [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * u3 + r3 + (v2 * u2 + r2))
                 (rand_of_renc (coin_rc2 c)));
          e (enc (pkey_of_dk Charlie) v3 (rand_of_renc (coin_rc1 c)));
          e (enc (pkey_of_dk Bob) v2 (rand_of_renc (coin_rb1 c)));
          d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
      [:: e (enc (pkey_of_dk Charlie) (v3 * u3 + r3)
                 (rand_mul (rand_pow (rand_of_renc (coin_rc1 c)) u3)
                           (rand_of_renc (coin_ra2 c))));
          e (enc (pkey_of_dk Bob) (v2 * u2 + r2)
                 (rand_mul (rand_pow (rand_of_renc (coin_rb1 c)) u2)
                           (rand_of_renc (coin_ra1 c))));
          d v2; kd dk_b];
      [:: e (enc (pkey_of_dk Charlie) (v3 * u3 + r3 + (v2 * u2 + r2))
                 (rand_mul (rand_mul (rand_pow (rand_of_renc (coin_rc1 c)) u3)
                                     (rand_of_renc (coin_ra2 c)))
                           (rand_of_renc (coin_rb2 c))));
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
(* The scheme data, Alice's input, the three weights, and the three private
   keys.  These are instance fields, under the names the corrupted-Alice
   development gives them. *)
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

(* Each abbreviation pins, under the name it abbreviates, the parameters that
   the preceding section and dsdp_alice_hop_secrecy.v take explicitly.  The
   shadowing is not recursive, since the right-hand side resolves against the
   constant. *)
Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation trace_dataT := (trace_dataT I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation R2 := (sample_R2 (R:=R) (I:=I)).
Local Notation R3 := (sample_R3 (R:=R) (I:=I)).
Local Notation EncCoins := (EncCoins (R:=R) (I:=I)).
Local Notation Sout := (Sout (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation alice_tuple_bob_zero := (alice_tuple_bob_zero (R:=R) (I:=I)).
Local Notation alice_tuple_all_zero := (alice_tuple_all_zero (R:=R) (I:=I)).
Local Notation indcpa_epsilon := (indcpa_epsilon (R:=R) (S:=I)).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) I).
Local Notation alice_traceT := (alice_traceT I).
Local Notation predictor := (predictor I).
Local Notation alice_simulator := (alice_simulator (R:=R) (I:=I)).
Local Notation alice_ideal := (alice_ideal (R:=R) I).

(* Alice's executed trace read off a value of her hopping tuple.  It holds the
   leaked output, Charlie's re-encryption, two ciphertexts, two masks, four
   weights, and the key mark. *)
Definition alice_trace_of_hop_tuple
    (v : alice_hop_tuple I) :
    18.-bseq trace_dataT :=
  [bseq inl (inl (inl (hop_output v)));
        inl (inl (inr (hop_reenc_cipher v)));
        inl (inl (inr (hop_charlie_cipher v)));
        inl (inl (inr (hop_bob_cipher v)));
        inl (inl (inl (hop_mask3 v)));
        inl (inl (inl (hop_mask2 v)));
        inl (inl (inl u3)); inl (inl (inl u2));
        inl (inl (inl u1)); inl (inl (inl v1));
        inl (inr tt)].

(* The DSDP protocol: the three piSMC programs at the coordinates of one
   sample.  The name lets a security statement open at the protocol
   itself. *)
Definition dsdp_protocol (s : alice_sampleT I) :
    seq (proc (di_data DI)) :=
  dsdp_procs_std I (V2 s) (V3 s) (R2 s) (R3 s).

(* Fuel bounds the encoded trace of any party in any sample-indexed process
   list, since encoding preserves length. *)
Lemma trace_of_run_size
    (procs : alice_sampleT I -> seq (proc (di_data DI)))
    (seeds : alice_sampleT I -> seq (seq (di_data DI)))
    (i : party_id) (s : alice_sampleT I) :
  (size (map (@trace_data_of_di_data I)
           (nth [::] (run_interp 18 (procs s) (seeds s)).1.2 n( i ))) <= 18)%N.
Proof. by rewrite size_map; exact: size_traces_nth. Qed.

(* The encoded trace party i sees in a run of procs, as a random variable.
   The interpreter's run enters a hopping argument as its first game. *)
Definition trace_of_run
    (procs : alice_sampleT I -> seq (proc (di_data DI)))
    (seeds : alice_sampleT I -> seq (seq (di_data DI)))
    (i : party_id) :
    {RV (alice_sample_fdist (R:=R) I) -> 18.-bseq trace_dataT} :=
  fun s => Bseq (trace_of_run_size procs seeds i s).

(* Alice's encoded executed trace as a random variable on the sample space.
   The interpreter hands it to her in a run of the DSDP protocol on the
   sampled coins. *)
Definition AliceTrace :
    {RV (alice_sample_fdist (R:=R) I) -> 18.-bseq trace_dataT} :=
  trace_of_run dsdp_protocol (fun s => dsdp_seeds (EncCoins s)) Alice.

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
move: (trace_of_run_size dsdp_protocol (fun s => dsdp_seeds (EncCoins s))
         Alice s).
rewrite /dsdp_protocol dsdp_run_tracesE.
by move=> ?; rewrite /= Sout_runE reenc_plainE.
Qed.

(* The real executed-trace law is the deterministic image of the real
   hopping-tuple law.  Her hopping tuple determines every coordinate of
   Alice's trace. *)
Lemma alice_trace_realE :
  `p_ [% V2, V3, AliceTrace]
  = fdistmap (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2))
      (`p_ [% V2, V3, alice_tuple_real]).
Proof.
by rewrite alice_trace_of_hop_tupleE /dist_of_RV fdistmap_comp.
Qed.

(* The law a simulator produces at the trace level: the hopping-tuple
   simulator at s, mapped through the encoded trace function. *)
Definition alice_trace_simulator (s : plain AHE) :
    R.-fdist (18.-bseq trace_dataT) :=
  fdistmap alice_trace_of_hop_tuple (alice_simulator s).

(* The joint law of the honest inputs and the simulated encoded trace.  The
   honest input law is bound to the trace simulator fed the leaked output. *)
Definition alice_trace_ideal :
    R.-fdist (plain AHE * plain AHE * 18.-bseq trace_dataT) :=
  `p_ [% V2, V3] >>= (fun vv =>
    fdistmap (fun tr => (vv.1, vv.2, tr))
      (alice_trace_simulator
        (dsdp_output v1 u1 u2 u3 vv.1 vv.2))).

(* The trace-level ideal law is the deterministic image of the hopping-tuple
   ideal law. *)
Lemma alice_trace_idealE :
  alice_trace_ideal
  = fdistmap (fun x => (x.1.1, x.1.2, alice_trace_of_hop_tuple x.2))
      alice_ideal.
Proof.
rewrite /alice_trace_ideal /alice_ideal fdistmap_bind.
congr (_ >>= _); apply: boolp.funext => vv.
by rewrite /alice_trace_simulator !fdistmap_comp.
Qed.

End dsdp_alice_trace_rv.

(* The part of Alice's hopping tuple her trace shows: two masks, the leaked
   output, two received ciphertexts, and a re-encryption.  It is the hopping
   tuple without the two combine coins she keeps to herself. *)
Record alice_trace_tuple (S : indcpa_scheme) := {
  (* Alice's first mask *)
  trace_mask2 : plain (scheme_AHE S) ;
  (* Alice's second mask *)
  trace_mask3 : plain (scheme_AHE S) ;
  (* the weighted output Alice is allowed to learn *)
  trace_output : plain (scheme_AHE S) ;
  (* Bob's ciphertext to Alice *)
  trace_bob_cipher : cipher (scheme_AHE S) ;
  (* Charlie's ciphertext to Alice *)
  trace_charlie_cipher : cipher (scheme_AHE S) ;
  (* Charlie's re-encryption of the aggregate under Alice's key *)
  trace_reenc_cipher : cipher (scheme_AHE S) }.

Section alice_trace_tuple_finite.
Variable S : indcpa_scheme.
Local Notation AHE := (scheme_AHE S).

(* The six-fold product the trace-visible tuple is in bijection with.  The
   finite structure lives on the product and the record borrows it. *)
Definition alice_trace_prodT :=
  (plain AHE * plain AHE * plain AHE
   * cipher AHE * cipher AHE * cipher AHE)%type.

(* The six slots read off the record, in the order the record lists them. *)
Definition prod_of_alice_trace_tuple (q : alice_trace_tuple S) :
    alice_trace_prodT :=
  (trace_mask2 q, trace_mask3 q, trace_output q,
   trace_bob_cipher q, trace_charlie_cipher q, trace_reenc_cipher q).

(* The record rebuilt from those six slots. *)
Definition alice_trace_tuple_of_prod (t : alice_trace_prodT) :
    alice_trace_tuple S :=
  let: (m2, m3, s, c2, c3, c4) := t in
  {| trace_mask2 := m2 ; trace_mask3 := m3 ; trace_output := s ;
     trace_bob_cipher := c2 ; trace_charlie_cipher := c3 ;
     trace_reenc_cipher := c4 |}.

(* Reading the six slots off the record and rebuilding it loses nothing. *)
Lemma prod_of_alice_trace_tupleK :
  cancel prod_of_alice_trace_tuple alice_trace_tuple_of_prod.
Proof. by case. Qed.

HB.instance Definition _ :=
  Equality.copy (alice_trace_tuple S) (can_type prod_of_alice_trace_tupleK).
HB.instance Definition _ :=
  Choice.copy (alice_trace_tuple S) (can_type prod_of_alice_trace_tupleK).
HB.instance Definition _ :=
  Countable.copy (alice_trace_tuple S) (can_type prod_of_alice_trace_tupleK).
HB.instance Definition _ : isFinite (alice_trace_tuple S) :=
  CanIsFinite prod_of_alice_trace_tupleK.

End alice_trace_tuple_finite.

Section dsdp_alice_trace_centropy.
Context {R : realType}.
Variable I : dsdp_instance.
(* The scheme data, Alice's input, the three weights, and Bob's private key.
   These are instance fields, under the names the corrupted-Alice development
   gives them. *)
Local Notation AHE := (scheme_AHE I).
Local Notation Renc := (scheme_renc I).
Local Notation rand_of_renc := (@scheme_rand_of_renc I).
Local Notation v1 := (inst_v1 I).
Local Notation u1 := (inst_u1 I).
Local Notation u2 := (inst_u2 I).
Local Notation u3 := (inst_u3 I).
Local Notation dk_b := (inst_dk_b I).

(* Each abbreviation pins the parameters that dsdp_alice_hop_secrecy.v
   discharges.  The right-hand side resolves against the constant, so the
   shadowing terminates. *)
Local Notation P := (alice_sample_fdist (R:=R) I).
Local Notation pkey_of_dk := (inst_pkey_of_party I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation R2 := (sample_R2 (R:=R) (I:=I)).
Local Notation R3 := (sample_R3 (R:=R) (I:=I)).
Local Notation RB1 := (RB1 (R:=R) (I:=I)).
Local Notation RC1 := (RC1 (R:=R) (I:=I)).
Local Notation RA1 := (RA1 (R:=R) (I:=I)).
Local Notation RA2 := (RA2 (R:=R) (I:=I)).
Local Notation RB2 := (RB2 (R:=R) (I:=I)).
Local Notation RC2 := (RC2 (R:=R) (I:=I)).
Local Notation Sout := (Sout (R:=R) (I:=I)).
Local Notation bob_real_cipher := (bob_real_cipher (R:=R) (I:=I)).
Local Notation charlie_real_cipher := (charlie_real_cipher (R:=R) (I:=I)).
Local Notation charlie_reenc_cipher := (charlie_reenc_cipher (R:=R) (I:=I)).
Local Notation alice_tuple_real := (alice_tuple_real (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).

(* The trace-visible part of Alice's hopping tuple as a random variable.  All
   three ciphertext slots carry real encryptions. *)
Definition AliceTraceTuple : {RV P -> alice_trace_tuple I} :=
  fun t => {| trace_mask2 := R2 t ; trace_mask3 := R3 t ;
              trace_output := Sout t ;
              trace_bob_cipher := bob_real_cipher t ;
              trace_charlie_cipher := charlie_real_cipher t ;
              trace_reenc_cipher := charlie_reenc_cipher t |}.

(* The sample coordinates besides Alice's two combine coins: two inputs, two
   masks, and the four coins she does not draw. *)
Definition alice_sample_restT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc * Renc * Renc))%type.

(* The random variable of those coordinates. *)
Definition AliceSampleRest : {RV P -> alice_sample_restT} :=
  fun t => (t.1.1, t.1.2, (RB1 t, RC1 t, RB2 t, RC2 t)).

(* The random variable of Alice's two combine coins. *)
Definition AliceCombineCoins : {RV P -> (Renc * Renc)} :=
  fun t => (RA1 t, RA2 t).

Let card_combine_coins : #|((Renc * Renc)%type : finType)|
            = #|((Renc * Renc)%type : finType)|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceCombineCoins). Qed.

Let card_sample_rest : #|alice_sample_restT| = #|alice_sample_restT|.-1.+1.
Proof. exact: fdist_card_prednK (`p_ AliceSampleRest). Qed.

Let card_combine_rand_rest :
  #|(((Renc * Renc) * alice_sample_restT)%type : finType)|
  = #|(((Renc * Renc) * alice_sample_restT)%type : finType)|.-1.+1.
Proof.
exact: fdist_card_prednK (`p_ [% AliceCombineCoins, AliceSampleRest]).
Qed.

(* Alice's combine coins and the other sample coordinates are jointly
   uniform. *)
Lemma combine_coins_rest_uniformE :
  `p_ [% AliceCombineCoins, AliceSampleRest]
  = (fdist_uniform card_combine_coins) `x (fdist_uniform card_sample_rest).
Proof.
rewrite -(fdist_uniform_prod card_combine_coins card_sample_rest
           card_combine_rand_rest)
        /dist_of_RV alice_sample_fdistE.
apply: fdistmap_bij_uniform.
exists (fun p : (Renc * Renc) * alice_sample_restT =>
          (p.2.1.1, p.2.1.2,
           {| coin_rb1 := p.2.2.1.1.1 ; coin_rc1 := p.2.2.1.1.2 ;
              coin_ra1 := p.1.1 ; coin_ra2 := p.1.2 ;
              coin_rb2 := p.2.2.1.2 ; coin_rc2 := p.2.2.2 |})).
  by move=> [[vv ms] [rb1 rc1 ra1 ra2 rb2 rc2]].
by move=> [[ra1 ra2] [[vv ms] [[[rb1 rc1] rb2] rc2]]].
Qed.

(* Alice's combine coins are uniform. *)
Lemma combine_coins_uniformE :
  `p_ AliceCombineCoins = fdist_uniform card_combine_coins.
Proof.
by rewrite -(fst_RV2 AliceCombineCoins AliceSampleRest)
   combine_coins_rest_uniformE fdist_prod1.
Qed.

(* The other sample coordinates are uniform. *)
Lemma sample_rest_uniformE :
  `p_ AliceSampleRest = fdist_uniform card_sample_rest.
Proof.
by rewrite -(snd_RV2 AliceCombineCoins AliceSampleRest)
   combine_coins_rest_uniformE fdist_prod2.
Qed.

(* Alice's combine coins are independent of the other sample
   coordinates. *)
Lemma combine_coins_rest_indep : P |= AliceCombineCoins _|_ AliceSampleRest.
Proof.
by apply: inde_RV_of_prod;
   rewrite combine_coins_rest_uniformE combine_coins_uniformE
           sample_rest_uniformE.
Qed.

(* Bob's input and the trace-visible tuple, rebuilt from the sample
   coordinates other than Alice's combine coins. *)
Definition v2_trace_tuple_of_sample_rest (u : alice_sample_restT) :
    (plain AHE * alice_trace_tuple I) :=
  (* The output slot is written with uncurry applied to an explicit pair
     because Sout is itself uncurry (dsdp_output ...) composed with
     [% V2, V3].  The curried spelling is not convertible and breaks the
     proof below. *)
  (u.1.1.1,
   {| trace_mask2 := u.1.2.1 ; trace_mask3 := u.1.2.2 ;
      trace_output := uncurry (dsdp_output v1 u1 u2 u3) (u.1.1.1, u.1.1.2) ;
      trace_bob_cipher :=
        enc (pkey_of_dk Bob) u.1.1.1 (rand_of_renc u.2.1.1.1) ;
      trace_charlie_cipher :=
        enc (pkey_of_dk Charlie) u.1.1.2 (rand_of_renc u.2.1.1.2) ;
      trace_reenc_cipher :=
        enc (pkey_of_dk Alice)
          (uncurry (dsdp_output v1 u1 u2 u3) (u.1.1.1, u.1.1.2)
             - u1 * v1 + u.1.2.1 + u.1.2.2)
          (rand_of_renc u.2.2) |}).

(* Alice's two combine coins are independent of Bob's input taken
   jointly with everything her executed trace shows. *)
Lemma combine_coins_trace_indep :
  P |= [% RA1, RA2] _|_ [% V2, AliceTraceTuple].
Proof.
(* The pair function must stay eta-expanded: [prod] has no definitional eta,
   so [idfun] does not typecheck here. *)
exact: (inde_RV_comp (fun p : Renc * Renc => (p.1, p.2))
          v2_trace_tuple_of_sample_rest combine_coins_rest_indep).
Qed.

(* Alice's hopping tuple rebuilt from her combine coins and the
   trace-visible tuple. *)
Definition hop_tuple_of_coins_trace
    (p : ((Renc * Renc) * alice_trace_tuple I)) :
    alice_hop_tuple I :=
  {| hop_mask2 := trace_mask2 p.2 ; hop_mask3 := trace_mask3 p.2 ;
     hop_coin_a1 := p.1.1 ; hop_coin_a2 := p.1.2 ;
     hop_output := trace_output p.2 ;
     hop_bob_cipher := trace_bob_cipher p.2 ;
     hop_charlie_cipher := trace_charlie_cipher p.2 ;
     hop_reenc_cipher := trace_reenc_cipher p.2 |}.

(* The combine coins and the trace-visible tuple read back off a
   hopping tuple. *)
Definition coins_trace_of_hop_tuple
    (v : alice_hop_tuple I) :
    ((Renc * Renc) * alice_trace_tuple I) :=
  ((hop_coin_a1 v, hop_coin_a2 v),
   {| trace_mask2 := hop_mask2 v ; trace_mask3 := hop_mask3 v ;
      trace_output := hop_output v ;
      trace_bob_cipher := hop_bob_cipher v ;
      trace_charlie_cipher := hop_charlie_cipher v ;
      trace_reenc_cipher := hop_reenc_cipher v |}).

(* The two relabellings are mutually inverse. *)
Lemma hop_tuple_of_coins_traceK :
  cancel hop_tuple_of_coins_trace coins_trace_of_hop_tuple.
Proof. by case=> [[ra1 ra2] [m2 m3 s c2 c3 c4]]. Qed.

(* Alice's hopping tuple is her combine coins together with the
   trace-visible tuple. *)
Lemma alice_hop_tuple_coins_traceE :
  alice_tuple_real
  = hop_tuple_of_coins_trace `o [% [% RA1, RA2], AliceTraceTuple].
Proof.
(* The combine coins are spelled as the pair combine_coins_trace_indep is
   stated at.  The record keeps its two coin fields apart, so
   [AliceCombineCoins] is convertible with that pair here as well. *)
by [].
Qed.

(* Alice's executed trace read off the trace-visible tuple.  It holds the
   leaked output, Charlie's re-encryption, two ciphertexts, two masks, four
   weights, and the key mark. *)
Definition trace_of_trace_tuple (q : alice_trace_tuple I) :
    18.-bseq (trace_dataT I) :=
  [bseq inl (inl (inl (trace_output q)));
        inl (inl (inr (trace_reenc_cipher q)));
        inl (inl (inr (trace_charlie_cipher q)));
        inl (inl (inr (trace_bob_cipher q)));
        inl (inl (inl (trace_mask3 q)));
        inl (inl (inl (trace_mask2 q)));
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
  else enc (pkey_of_dk Alice) 0 (rand_of_renc (renc_default I)).

(* The trace-visible tuple read back off an encoded trace, at the six
   positions the encoding writes it to. *)
Definition trace_tuple_of_trace
    (b : 18.-bseq (trace_dataT I)) :
    alice_trace_tuple I :=
  let s := bseqval b in
  {| trace_mask2 := trace_data_plain (nth (inr tt) s 5) ;
     trace_mask3 := trace_data_plain (nth (inr tt) s 4) ;
     trace_output := trace_data_plain (nth (inr tt) s 0) ;
     trace_bob_cipher := trace_data_cipher (nth (inr tt) s 3) ;
     trace_charlie_cipher := trace_data_cipher (nth (inr tt) s 2) ;
     trace_reenc_cipher := trace_data_cipher (nth (inr tt) s 1) |}.

(* Encoding the trace-visible tuple into a trace is left-invertible: every
   slot of that tuple appears literally in the trace. *)
Lemma trace_of_trace_tupleK :
  cancel trace_of_trace_tuple trace_tuple_of_trace.
Proof. by case. Qed.

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
rewrite alice_hop_tuple_coins_traceE
        (can_centropy_eq hop_tuple_of_coins_traceK).
by rewrite (inde_centropy_eq combine_coins_trace_indep).
Qed.

(* Bob's ciphertext slot of Alice's executed trace, decrypted with Bob's own
   private key.  It witnesses that the hop bounds hold only for adversaries
   granted the public keys alone. *)
Definition bob_decrypt_predictor : predictor I (alice_traceT I) :=
  (* Both default branches are unreachable on the traces this predictor is
     run against.  Every trace in the image of trace_of_trace_tuple carries a
     ciphertext at slot 3, so the fixed zero encryption trace_data_cipher
     returns at any other sort is never read, and dec_correct sends that
     ciphertext to Some, so the plaintext zero returned on None is never
     returned either. *)
  fun b => if dec dk_b (trace_data_cipher (nth (inr tt) (bseqval b) 3))
           is Some m then m else 0.

(* Bob's input is a deterministic function of Alice's executed trace.
   Alice's trace carries Bob's ciphertext, and dk_b decrypts it. *)
Lemma alice_trace_decode_V2E :
  V2 = bob_decrypt_predictor `o AliceTrace.
Proof.
rewrite alice_trace_tupleE; apply/boolp.funext => t.
by rewrite /comp_RV /bob_decrypt_predictor /= dec_correct.
Qed.

(* Conditioning on Alice's executed trace leaves no uncertainty about Bob's
   input.  The guessing bounds carry the content, since they grant a predictor
   the public keys alone. *)
Corollary centropy_V2_trace_eq0 : `H( V2 | AliceTrace ) = 0.
Proof. by rewrite {1}alice_trace_decode_V2E centropy_RV_comp0. Qed.

End dsdp_alice_trace_centropy.

Section dsdp_alice_raw_trace.
Context {R : realType}.
Variable I : dsdp_instance.
(* The scheme data and Alice's private key.  These are instance fields, under
   the names the corrupted-Alice development gives them. *)
Local Notation AHE := (scheme_AHE I).
Local Notation dk_a := (inst_dk_a I).

Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation trace_dataT := (trace_dataT I).
Local Notation V2 := (sample_V2 (R:=R) (I:=I)).
Local Notation V3 := (sample_V3 (R:=R) (I:=I)).
Local Notation R2 := (sample_R2 (R:=R) (I:=I)).
Local Notation R3 := (sample_R3 (R:=R) (I:=I)).
Local Notation EncCoins := (EncCoins (R:=R) (I:=I)).
Local Notation AliceTrace := (AliceTrace (R:=R) (I:=I)).

(* Fixed-key decoding of one encoded trace datum: plaintexts and ciphertexts
   kept, the key marks sent to dk and pk.  There is no global inverse: the
   encoding erases which key value each mark carried. *)
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
      (run_interp 18 (dsdp_protocol (R:=R) s) (dsdp_seeds (EncCoins s))).1.2
      0.

(* Decoding Alice's encoded trace with her private key restores the raw
   interpreter trace.  The public key pk is universally quantified because her
   trace contains no public-key mark. *)
Lemma alice_raw_trace_decodeE (pk : pub_key AHE)
    (s : alice_sampleT I) :
  map (di_data_of_trace_data dk_a pk) (AliceTrace s) = alice_raw_trace s.
Proof.
rewrite -map_comp /alice_raw_trace /dsdp_protocol.
by rewrite dsdp_run_tracesE.
Qed.

(* The private keys a raw interpreter trace carries, in the order the trace
   records them.  Everything that is not a key mark is dropped, so the result
   is the key content of a party's view. *)
Definition trace_priv_keys (tr : seq (di_data DI)) : seq (priv_key AHE) :=
  pmap (di_get_priv_key DI) tr.

(* Alice's executed trace holds her own private key and no other.  The key
   erasure of trace_dataT discards exactly that constant, so a keygen argument
   needs no further hypothesis. *)
Lemma alice_raw_trace_priv_keysE (s : alice_sampleT I) :
  trace_priv_keys (alice_raw_trace s) = [:: dk_a].
Proof.
by rewrite /trace_priv_keys /alice_raw_trace /dsdp_protocol dsdp_run_tracesE.
Qed.

End dsdp_alice_raw_trace.
