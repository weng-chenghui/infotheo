From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
From mathcomp Require Import constructive_ereal.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba.
Require Import extra_proba extra_entropy.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption dsdp_interface dsdp_program dsdp_pismc.
Require Import dsdp_alice_fdist_secrecy.

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy at the executed piSMC trace                 *)
(*                                                                            *)
(* The corrupted-Alice bound of dsdp_alice_fdist_secrecy.v carried from a     *)
(* hand-transcribed view to the trace the piSMC interpreter produces when the *)
(* three DSDP programs are run at an abstract additively homomorphic scheme.  *)
(* The fifteen-round run is evaluated symbolically in three stages whose      *)
(* boundaries are the three decryptions of the protocol, so the contents of   *)
(* the trace are a theorem rather than a hypothesis.                          *)
(*                                                                            *)
(* Charlie's re-encryption randomness and Bob's forward randomness are        *)
(* parameters of the sections rather than coordinates of the sample space.    *)
(* Alice's encoded trace is then a deterministic function of the view of      *)
(* dsdp_alice_fdist_secrecy.v, and each trace-level statement is a            *)
(* corollary of the corresponding view-level result.                          *)
(*                                                                            *)
(* Headline results: dsdp_run_traces_ok computes the three traces of the run  *)
(* at the standard interface of an abstract scheme;                           *)
(* dsdp_alice_guess_fdist_trace_V2_real_le bounds the probability that a      *)
(* predictor reading Alice's encoded trace returns Bob's input by one over    *)
(* the cardinality of the plaintext space plus the real-or-zero advantages of *)
(* two explicitly constructed reductions;                                     *)
(* dsdp_alice_trace_predictor_unpredictability_fdist_ge restates that bound   *)
(* through the named quantity alice_trace_predictor_unpredictability;         *)
(* dsdp_alice_trace_sim_advantage_fdist_le bounds the gap any Boolean trace   *)
(* test sees between the real executed-trace joint law and the ideal trace    *)
(* joint law by the two lifted hop advantages.                                *)
(*                                                                            *)
(* ```                                                                        *)
(*             gdp, gde, gdk == the injections of a plaintext, of a           *)
(*                              ciphertext and of a private key into the      *)
(*                              generic data carrier                          *)
(*               gget_cipher == the partial read of a ciphertext out of that  *)
(*                              carrier                                       *)
(*                 gRecv_dec == a receive that decrypts the ciphertext it     *)
(*                              reads under a private key                     *)
(*                 gRecv_enc == a receive that keeps the ciphertext it reads  *)
(*     DSDP_Interface_of_ops == the DSDP interface assembled from abstract    *)
(*                              carriers and abstract operations              *)
(*                    gprocs == the three DSDP programs at that interface     *)
(* dsdp_run_traces_of_ops_ok == the traces of the fifteen-round run at        *)
(*                              abstract operations, under the three          *)
(*                              decryption equations of the run               *)
(*                pkey_of_dk == each party's public key, read off that        *)
(*                              party's private key                           *)
(*          dsdp_trace_dataT == the finite image of the interpreter's data    *)
(*                              carrier: plaintexts and ciphertexts kept,     *)
(*                              both key sorts erased to marks                *)
(*     trace_data_of_di_data == the encoding of one datum of the standard     *)
(*                              interface into that image                     *)
(*            dsdp_procs_std == the three programs at the standard interface  *)
(*                              of an AHE scheme                              *)
(*           dsdp_procs_stdE == the abstract instance at the standard         *)
(*                              interface is the standard instance            *)
(*        dsdp_run_traces_ok == the traces of the fifteen-round standard run: *)
(*                              eleven entries for Alice, four for Bob and    *)
(*                              three for Charlie                             *)
(*      dsdp_run_traces_encE == the same traces with every ciphertext         *)
(*                              normalised to a single encryption, whose      *)
(*                              randomness combines the randomness of the     *)
(*                              arguments                                     *)
(*   dsdp_trace_of_hop_tuple == Alice's executed trace read off a value of    *)
(*                              her hopping tuple                             *)
(*      dsdp_procs_of_sample == the three programs at the coordinates of one  *)
(*                              sample                                        *)
(*                AliceTrace == Alice's encoded executed trace as a random    *)
(*                              variable on the sample space                  *)
(*  dsdp_trace_of_hop_tupleE == the trace the interpreter produces for Alice  *)
(*                              is the deterministic image of her hopping     *)
(*                              tuple                                         *)
(* dsdp_alice_guess_fdist_trace_V2_real_le ==                                 *)
(*                              every predictor reading the trace the         *)
(*                              interpreter produces for Alice matches Bob's  *)
(*                              input with probability at most one over that  *)
(*                              cardinality plus the advantages of the two    *)
(*                              per-hop reductions                            *)
(* alice_trace_predictor_unpredictability g ==                                *)
(*                              the negative logarithm of the probability     *)
(*                              that the predictor g recovers Bob's input     *)
(*                              from Alice's encoded executed trace           *)
(* dsdp_alice_trace_predictor_unpredictability_fdist_ge ==                    *)
(*                              that trace guessing bound in                  *)
(*                              negative-logarithm form, stated through that  *)
(*                              named quantity                                *)
(* dsdp_alice_trace_simulator s ==                                            *)
(*                              the hopping-tuple simulator of one leaked     *)
(*                              output mapped to the encoded executed-trace   *)
(*                              carrier                                       *)
(*   alice_trace_ideal_joint == the joint law of the two honest inputs and    *)
(*                              the trace simulator run on their leaked       *)
(*                              output                                        *)
(* dsdp_alice_trace_sim_advantage_fdist_le ==                                 *)
(*                              every Boolean test separates the real         *)
(*                              executed-trace joint law from the ideal trace *)
(*                              joint law by at most the two lifted hop       *)
(*                              advantages                                    *)
(*   dsdp_alice_trace_tupleT == the trace-visible part of Alice's hopping     *)
(*                              tuple: the two masks, the leaked output and   *)
(*                              the two received ciphertexts                  *)
(*           AliceTraceTuple == that part as a random variable on the sample  *)
(*                              space                                         *)
(*        alice_sample_restT == the sample coordinates other than Alice's     *)
(*                              two combine randomnesses                      *)
(*           AliceSampleRest == the random variable of those coordinates      *)
(*          AliceCombineRand == the random variable of Alice's two combine    *)
(*                              randomnesses                                  *)
(* combine_rand_rest_uniformE ==                                              *)
(*                              Alice's combine randomnesses and the other    *)
(*                              sample coordinates are jointly uniform        *)
(*     combine_rand_uniformE == Alice's combine randomnesses are uniform      *)
(*      sample_rest_uniformE == the other sample coordinates are uniform      *)
(*   combine_rand_rest_indep == Alice's combine randomnesses are independent  *)
(*                              of the other sample coordinates               *)
(* v2_trace_tuple_of_sample_rest ==                                           *)
(*                              Bob's input and the trace-visible tuple,      *)
(*                              rebuilt from the other sample coordinates     *)
(*  combine_rand_trace_indep == Alice's combine randomnesses are              *)
(*                              independent of Bob's input taken jointly      *)
(*                              with the trace-visible tuple                  *)
(*   hop_tuple_of_rand_trace == Alice's hopping tuple rebuilt from her        *)
(*                              combine randomnesses and the trace-visible    *)
(*                              tuple                                         *)
(*   rand_trace_of_hop_tuple == the two read back off a hopping tuple         *)
(* alice_hop_tuple_rand_traceE ==                                             *)
(*                              Alice's hopping tuple is her combine          *)
(*                              randomnesses together with the trace-visible  *)
(*                              tuple                                         *)
(*      trace_of_trace_tuple == Alice's executed trace read off the           *)
(*                              trace-visible tuple                           *)
(*          trace_data_plain == the plaintext carried by a trace entry,       *)
(*                              zero at any other sort                        *)
(*         trace_data_cipher == the ciphertext carried by a trace entry, a    *)
(*                              fixed encryption of zero at any other sort    *)
(*      trace_tuple_of_trace == the trace-visible tuple read back off an      *)
(*                              encoded trace                                 *)
(*        alice_trace_tupleE == Alice's executed trace is the image of the    *)
(*                              trace-visible tuple                           *)
(* centropy_AliceTrace_AliceHopTuple ==                                       *)
(*                              conditioning on Alice's executed trace        *)
(*                              leaves the same uncertainty about Bob's       *)
(*                              input as conditioning on her hopping tuple    *)
(*   alice_hop_tuple_of_view == the hopping tuple is the first component      *)
(*                              of Alice's view                               *)
(* centropy_AliceView_AliceHopTuple ==                                        *)
(*                              conditioning on Alice's view leaves the       *)
(*                              same uncertainty about Bob's input as         *)
(*                              conditioning on her hopping tuple             *)
(* alice_trace_ideal_test D == the Boolean ideal trace experiment: sample     *)
(*                              the honest inputs, run the trace simulator    *)
(*                              on their leaked output, apply the test        *)
(*   alice_trace_ideal_testE == that experiment is the pushforward of the     *)
(*                              ideal trace joint law along the test          *)
(* dsdp_alice_trace_sim_advantage_fdist_test_le ==                            *)
(*                              the simulator-advantage bound with its ideal  *)
(*                              side written through the named experiment     *)
(* dsdp_trace_of_hop_tuple_pub ==                                             *)
(*                              the trace encoder with the reconstruction     *)
(*                              key passed as Alice's public key              *)
(* dsdp_alice_trace_simulator_pub ==                                          *)
(*                              the trace simulator with its setup passed as  *)
(*                              the three public keys it reads                *)
(* dsdp_trace_of_hop_tuple_pubE ==                                            *)
(*                              instantiating Alice's public key from her     *)
(*                              private key yields the existing encoder       *)
(* dsdp_alice_trace_simulator_pubE ==                                         *)
(*                              instantiating the three public keys from the  *)
(*                              private keys yields the existing simulator    *)
(* alice_trace_real_joint_avg ==                                              *)
(*                              the real executed-trace joint law with a      *)
(*                              uniformly sampled re-encryption coin          *)
(* alice_trace_ideal_joint_avg ==                                             *)
(*                              the ideal trace joint law with a uniformly    *)
(*                              sampled re-encryption coin                    *)
(* dsdp_alice_trace_sim_advantage_fdist_avg_le ==                             *)
(*                              the averaged real-versus-ideal gap is at      *)
(*                              most the average of the two per-coin hop      *)
(*                              advantages                                    *)
(* alice_trace_predictor_unpredictability_ereal g ==                          *)
(*                              the zero-safe unpredictability of Bob's       *)
(*                              input at Alice's encoded trace: infinite at   *)
(*                              zero predictor success, the negative          *)
(*                              logarithm otherwise                           *)
(* alice_trace_predictor_unpredictability_ereal_zeroE ==                      *)
(*                              zero success is infinite unpredictability     *)
(* alice_trace_predictor_unpredictability_ereal_gt0E ==                       *)
(*                              positive success is the finite negative       *)
(*                              logarithm                                     *)
(* alice_trace_predictor_unpredictability_ereal_finE ==                       *)
(*                              the real-valued definition is the finite      *)
(*                              branch                                        *)
(* dsdp_alice_trace_predictor_unpredictability_fdist_ereal_ge ==              *)
(*                              the trace guessing bound lifted to the        *)
(*                              zero-safe order, with no positivity premise   *)
(* di_data_of_trace_data dk pk ==                                             *)
(*                              the fixed-key decoding of one encoded trace   *)
(*                              datum: plaintexts and ciphertexts restored    *)
(*                              as themselves, the private-key mark as dk,    *)
(*                              the public-key mark as pk                     *)
(*         alice_raw_trace s == Alice's raw interpreter trace at one sample   *)
(*   alice_raw_trace_decodeE == decoding Alice's encoded trace with her       *)
(*                              private key restores the raw interpreter      *)
(*                              trace                                         *)
(* dsdp_alice_raw_trace_sim_advantage_fdist_le ==                             *)
(*                              the simulator-advantage bound for a Boolean   *)
(*                              test reading the raw interpreter trace, via   *)
(*                              composition with the fixed-key decoder        *)
(* ```                                                                        *)
(*                                                                            *)
(* DI and the parameter-pinning abbreviations that Section                    *)
(* dsdp_alice_trace_rv opens with are Local Notations of that section.        *)
(*                                                                            *)
(* Those abbreviations are Local Notation partial applications, each pinning  *)
(* under its own name the parameters that the preceding section and the view  *)
(* ladder discharge, for instance V2 for V2 (R:=R) (AHE:=AHE) card_renc.      *)
(* Notation X := (X args) is not recursive, since the right-hand side         *)
(* resolves against the constant, and rewrite /X still unfolds it.            *)
(*                                                                            *)
(* Scope. The statements are average-case over the honest inputs V2 and V3,   *)
(* which are sampled uniformly inside the experiment. Each per-hop epsilon is *)
(* a single-query advantage at a fixed key, a number related to but distinct  *)
(* from the multi-query party-indexed oracle advantage of                     *)
(* homomorphic_encryption/indcpa_ror.v. A bound here is informative to the    *)
(* extent that its epsilons are small, and holds vacuously once they exceed   *)
(* 1. The efficiency reading of the reductions stays on paper: the adversary  *)
(* is a plain function record, and complexity is argued outside the           *)
(* formalization. The forward randomness w_rb2 and the re-encryption          *)
(* randomness w_rc2 are universally quantified parameters rather than         *)
(* averaged sample coordinates, so the bounds hold at every value of the two, *)
(* including an adversarially chosen one, and imply the averaged bounds. The  *)
(* epsilons here are per-value, not averages over w_rc2.                      *)
(*                                                                            *)
(* The conditional-entropy results are stated for Bob's input V2 only. They   *)
(* say the three objects leave the same residual uncertainty about V2, which  *)
(* transfers conditional-entropy statements between them. They do not         *)
(* transfer the guessing bound: that reaches the trace by composing the       *)
(* predictor with dsdp_trace_of_hop_tuple, a separate argument. The trace is  *)
(* not in bijection with the hopping tuple, since it drops the two combine    *)
(* randomnesses whenever 0 < index_renc.                                      *)
(*                                                                            *)
(* Charlie-side re-encryption randomness reaches Alice's trace: the           *)
(* interpreter's step traces the datum a party receives rather than the       *)
(* argument its continuation is applied to (smc/smc_interpreter.v), so the    *)
(* ciphertext under Alice's key carrying rand_of_renc w_rc2 is one of her     *)
(* eleven trace entries.                                                      *)
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

Section dsdp_run_traces_of_ops.

Variables (gmsgT gcipherT grandT gprivT gpubT : Type).

Local Notation gdata := ((gmsgT + gcipherT + gprivT + gpubT)%type).

Variable genc : gpubT -> gmsgT -> grandT -> gcipherT.
Variable gemul : gcipherT -> gcipherT -> gcipherT.
Variable gepow : gcipherT -> gmsgT -> gcipherT.
Variable gadd gsub gmul : gmsgT -> gmsgT -> gmsgT.
Variable gdec : gprivT -> gcipherT -> option gmsgT.

(* The injection of a plaintext into the generic data carrier, in the summand
   order the interface fixes. *)
Definition gdp (x : gmsgT) : gdata := inl (inl (inl x)).

(* The injection of a ciphertext into the generic data carrier.               *)
Definition gde (x : gcipherT) : gdata := inl (inl (inr x)).

(* The injection of a private key into the generic data carrier.              *)
Definition gdk (x : gprivT) : gdata := inl (inr x).

(* The partial read of a ciphertext out of the generic data carrier, which is
   the guard of the two cipher-carrying receives below. *)
Definition gget_cipher (x : gdata) : option gcipherT :=
  if x is inl (inl (inr v)) then Some v else None.

(* A receive whose guard decrypts under a private key the ciphertext it reads,
   so that the continuation is applied to a plaintext. *)
Definition gRecv_dec (frm : nat) (dk : gprivT) (f : gmsgT -> proc gdata)
    : proc gdata :=
  Recv_param gdata (obind (gdec dk) \o gget_cipher) frm f.

(* A receive whose guard keeps the ciphertext it reads, so that the
   continuation is applied to a ciphertext. *)
Definition gRecv_enc (frm : nat) (f : gcipherT -> proc gdata) : proc gdata :=
  Recv_param gdata gget_cipher frm f.

(* The DSDP interface assembled from abstract carriers and abstract
   operations. The three protocol programs are written once against this
   interface, and the evaluation lemma below holds at every instance of it,
   the standard interface of an AHE scheme included.
   Naming: the mixed form follows Standard_DSDP_Interface of
   dsdp_interface.v. *)
Definition DSDP_Interface_of_ops : DSDP_Interface := {|
  di_msgT := gmsgT ;
  di_cipherT := gcipherT ;
  di_randT := grandT ;
  di_priv_keyT := gprivT ;
  di_pub_keyT := gpubT ;
  di_data := gdata ;
  di_data_of_plain := gdp ;
  di_data_of_cipher := gde ;
  di_data_of_priv_key := gdk ;
  di_data_of_pub_key := fun x => inr x ;
  di_get_cipher := gget_cipher ;
  di_encrypt := genc ;
  di_emul := gemul ;
  di_epow := gepow ;
  di_add := gadd ;
  di_sub := gsub ;
  di_mul := gmul ;
  di_Recv_dec := gRecv_dec ;
  di_Recv_enc := gRecv_enc |}.

Variables (gdka gdkb gdkc : gprivT).
Variable gek : party_id -> gpubT.
Variables (gv1 gv2 gv3 gu1 gu2 gu3 gr2 gr3 : gmsgT).
Variables (grb1 grb2 grc1 grc2 gra1 gra2 : grandT).
Variables (gm1 gm2 gm3 : gmsgT).

(* The four ciphertexts the run puts on the wire after the two openings. *)
Local Notation gCb :=
  (gemul (gepow (genc (gek Bob) gv2 grb1) gu2) (genc (gek Bob) gr2 gra1)).
Local Notation gCc3 :=
  (gemul (gepow (genc (gek Charlie) gv3 grc1) gu3)
         (genc (gek Charlie) gr3 gra2)).
Local Notation gCc := (gemul gCc3 (genc (gek Charlie) gm2 grb2)).
Local Notation gCa := (genc (gek Alice) gm3 grc2).

Hypothesis Hgb : gdec gdkb gCb = Some gm2.
Hypothesis Hgc : gdec gdkc gCc = Some gm3.
Hypothesis Hga : gdec gdka gCa = Some gm1.

Let gpalice :=
  @palice DSDP_Interface_of_ops gdec gek gdka gv1 gu1 gu2 gu3 gr2 gr3
          gra1 gra2.
Let gpbob := @pbob DSDP_Interface_of_ops gdec gek gdkb gv2 grb1 grb2.
Let gpcharlie := @pcharlie DSDP_Interface_of_ops gdec gek gdkc gv3 grc1 grc2.

Let gsaprocs : seq (aproc dsdp_dtype (di_data DSDP_Interface_of_ops)) :=
  [aprocs gpalice ; gpbob ; gpcharlie].

(* The three DSDP programs at that interface, with their session-type
   annotations erased, in the party order the interpreter indexes by. *)
Definition gprocs : seq (proc (di_data DSDP_Interface_of_ops)) :=
  erase_aprocs gsaprocs.

(* The raw traces of the fifteen-round run at abstract carriers and abstract
   operations, under the three decryption equations the openings need.
   Naming: the `of_ops` infix separates this abstract-operation statement from
   `dsdp_run_traces_ok`, the same equation at the standard AHE interface. *)
Lemma dsdp_run_traces_of_ops_ok :
  (run_interp 15 gprocs).2 =
  [:: [:: gdp (gadd (gsub (gsub gm1 gr2) gr3) (gmul gu1 gv1));
          gde gCa;
          gde (genc (gek Charlie) gv3 grc1);
          gde (genc (gek Bob) gv2 grb1);
          gdp gr3; gdp gr2; gdp gu3; gdp gu2; gdp gu1; gdp gv1; gdk gdka];
      [:: gde gCc3; gde gCb; gdp gv2; gdk gdkb];
      [:: gde gCc; gdp gv3; gdk gdkc]].
Proof.
rewrite /run_interp.
have -> : (15 = 10 + 5)%N by [].
rewrite interp_fuelD.
move Ht: (interp 10 gprocs (nseq (size gprocs) [::])) => S.
vm_compute in Ht.
rewrite Hgb in Ht.
have -> : (5 = 2 + 3)%N by [].
rewrite interp_fuelD.
move Ht2: (interp 2 S.1 S.2) => S2.
rewrite -Ht in Ht2.
vm_compute in Ht2.
rewrite Hgc in Ht2.
have -> : (3 = 1 + 2)%N by [].
rewrite interp_fuelD.
move Ht3: (interp 1 S2.1 S2.2) => S3.
rewrite -Ht2 in Ht3.
vm_compute in Ht3.
rewrite Hga in Ht3.
rewrite -Ht3.
by vm_compute.
Qed.

End dsdp_run_traces_of_ops.

(* Keep every parameter of the generic run explicit, so that instantiations
   are positional and independent of implicit-argument inference. *)
Arguments gprocs : clear implicits.

Section dsdp_alice_trace_link.
Variables (AHE : AHEncType) (Renc : finType).
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Every party's public key is the one associated with its private key, so
   dec_correct fires by conversion and no key hypothesis is needed. *)
Definition pkey_of_dk (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier: plaintexts and
   ciphertexts kept, both key sorts erased to marks. The summand order
   mirrors std_data's msgT + encT + privT + pubT. *)
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + cipher AHE) + unit + unit)%type.

(* The encoding of one datum of the standard interface into that finite image,
   applied entrywise to a trace so that a trace becomes a value of a finType
   and a predictor on it can be quantified over.
   Naming: the _of_ form of the conversion rule of dsdp_interface.v, naming
   the source type it reads. *)
Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr c))
  | inl (inr _) => inl (inr tt)
  | inr _ => inr tt
  end.

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

Let procs_of_ops :=
  gprocs (plain AHE) (cipher AHE) (rand AHE) (priv_key AHE) (pub_key AHE)
         (@enc AHE) (@Emul AHE) (@Epow AHE)
         +%R (fun a b : plain AHE => a - b) *%R (@dec AHE)
         dk_a dk_b dk_c pkey_of_dk
         v1 v2 v3 u1 u2 u3 r2 r3
         rb1 (rand_of_renc w_rb2) rc1 (rand_of_renc w_rc2) ra1 ra2.

(* The abstract instance at the standard interface is the standard instance,
   which is what carries the generic evaluation lemma to this file. *)
Lemma dsdp_procs_stdE : dsdp_procs_std = procs_of_ops.
Proof. by []. Qed.

(* The traces of the fifteen-round run at the standard interface: eleven
   entries for Alice, four for Bob and three for Charlie, each ciphertext in
   the form the programs build it. *)
Lemma dsdp_run_traces_ok :
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
rewrite dsdp_procs_stdE /procs_of_ops; apply: dsdp_run_traces_of_ops_ok.
- by rewrite Epow_encE Emul_encE dec_correct.
- by rewrite Epow_encE !Emul_encE dec_correct.
- exact: dec_correct.
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
Proof. by rewrite dsdp_run_traces_ok !Epow_encE !Emul_encE. Qed.

End dsdp_alice_trace_link.

(* Keep every parameter of the standard proc list explicit, so that the
   per-sample instantiation is positional and independent of
   implicit-argument inference. *)
Arguments dsdp_procs_std : clear implicits.

Section dsdp_alice_trace_rv.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
(* Naming: [u3_unit] reads "u3 is a unit", the subject_property hypothesis
   pattern; same premise as in dsdp_alice_fdist_secrecy.v. *)
Hypothesis u3_unit : u3 \is a GRing.unit.
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* The declarations discharged by the preceding section and by
   dsdp_alice_fdist_secrecy.v take these parameters explicitly. Each
   abbreviation pins them once, under the name it abbreviates; the shadowing
   is not recursive, since the right-hand side resolves against the
   constant. *)
Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation R2 := (R2 (R:=R) (AHE:=AHE) card_renc).
Local Notation R3 := (R3 (R:=R) (AHE:=AHE) card_renc).
Local Notation Rho2 := (Rho2 (R:=R) (AHE:=AHE) card_renc).
Local Notation Rho3 := (Rho3 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA1 := (RA1 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA2 := (RA2 (R:=R) (AHE:=AHE) card_renc).
Local Notation Sout :=
  (Sout (R:=R) (AHE:=AHE) card_renc v1 u1 u2 u3).
Local Notation AliceHopTuple i :=
  (AliceHopTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3 i).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation dsdp_alice_simulator :=
  (dsdp_alice_simulator (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk).
Local Notation alice_ideal_joint :=
  (alice_ideal_joint (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).

(* Alice's executed trace read off a value of her hopping tuple: the leaked
   output, Charlie's re-encryption of it, the two received ciphertexts, the
   two masks, the four weights, and the erased key mark.
   Naming: the [_of_] connective names the source the conversion reads, after
   the repository's total-conversion family. *)
Definition dsdp_trace_of_hop_tuple
    (v : dsdp_alice_hop_tupleT AHE Renc) :
    15.-bseq dsdp_trace_dataT :=
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

(* The three piSMC programs at the coordinates of one sample. *)
Definition dsdp_procs_of_sample (s : dsdp_alice_sampleT AHE Renc) :
    seq (proc (di_data DI)) :=
  dsdp_procs_std AHE Renc rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c
    w_rb2 w_rc2 (V2 s) (V3 s) (R2 s) (R3 s) (rand_of_renc (Rho2 s))
    (rand_of_renc (Rho3 s)) (rand_of_renc (RA1 s)) (rand_of_renc (RA2 s)).

(* Fuel bounds the encoded trace, since encoding preserves length. *)
Let size_alice_trace (s : dsdp_alice_sampleT AHE Renc) :
  (size (map (@trace_data_of_di_data AHE)
           (nth [::] (run_interp 15 (dsdp_procs_of_sample s)).2 0)) <= 15)%N.
Proof. by rewrite size_map; exact: size_traces_nth. Qed.

(* Alice's encoded executed trace as a random variable on the sample
   space. *)
Definition AliceTrace :
    {RV (alice_sample_fdist (R:=R) AHE card_renc) ->
     15.-bseq dsdp_trace_dataT} :=
  fun s => Bseq (size_alice_trace s).

(* The leaked output the run computes is Alice's hopping tuple slot. *)
Let Sout_runE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * u3 + R3 s + (V2 s * u2 + R2 s) - R2 s - R3 s + u1 * v1
  = Sout s.
Proof. by rewrite SoutE; ring. Qed.

(* The plaintext Charlie re-encrypts is the leaked output net of Alice's own
   term and masks. *)
Let recrypt_plainE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * u3 + R3 s + (V2 s * u2 + R2 s)
  = Sout s - u1 * v1 + R2 s + R3 s.
Proof. by rewrite SoutE; ring. Qed.

(* The trace the interpreter produces for Alice is the deterministic image of
   her hopping tuple. *)
Lemma dsdp_trace_of_hop_tupleE :
  AliceTrace = dsdp_trace_of_hop_tuple `o (AliceHopTuple 0).
Proof.
apply: boolp.funext => s; apply/val_inj.
rewrite /AliceTrace; move: (size_alice_trace s).
rewrite /dsdp_procs_of_sample dsdp_run_traces_ok.
by move=> ?; rewrite /= Sout_runE recrypt_plainE.
Qed.

(* Every predictor reading the trace the interpreter produces for Alice
   matches Bob's input with probability at most one over the plaintext-space
   cardinality plus the real-or-zero advantages of the two per-hop
   reductions. *)
Theorem dsdp_alice_guess_fdist_trace_V2_real_le
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) :
  Pr (alice_sample_fdist (R:=R) AHE card_renc)
     [set t | (g `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_fdist_epsilon (pkey_of_dk Bob)
           (hop0_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple)))
       + indcpa_fdist_epsilon (pkey_of_dk Charlie)
           (hop1_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple))).
Proof.
rewrite dsdp_trace_of_hop_tupleE.
exact: (dsdp_alice_guess_fdist_V2_real_le card_renc rand_of_renc
          pkey_of_dk v1 u1 u2 u3_unit
          (g \o dsdp_trace_of_hop_tuple)).
Qed.

(* The advantage against Bob's key of the hop-0 reduction of the distinguisher
   associated with a trace predictor composed with
   dsdp_trace_of_hop_tuple. *)
Let trace_eps0 (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_dk Bob)
    (hop0_reduction
       (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple))).

(* The advantage against Charlie's key of the hop-1 reduction of the
   distinguisher associated with a trace predictor composed with
   dsdp_trace_of_hop_tuple. *)
Let trace_eps1 (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_dk Charlie)
    (hop1_reduction
       (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple))).

(* The negative logarithm of the probability that g recovers Bob's input
   from Alice's encoded executed trace.
   Naming: after [alice_predictor_unpredictability] of the hopping-tuple
   level, with [trace] marking the observation g reads. *)
Definition alice_trace_predictor_unpredictability
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  - log
      (Pr (alice_sample_fdist (R:=R) AHE card_renc)
         [set t | (g `o AliceTrace) t == V2 t]).

Local Notation "'`H_unp^{' g '}'" :=
  (alice_trace_predictor_unpredictability g)
  (at level 0, g at level 200,
   format "'`H_unp^{' g '}'").

(* The predictor-specific unpredictability of Bob's input at Alice's executed
   trace is at least the negative-logarithm form of the trace guessing bound.
   Naming: after [dsdp_alice_predictor_unpredictability_fdist_ge], the
   theorem name extending [alice_trace_predictor_unpredictability] as
   there. *)
Theorem dsdp_alice_trace_predictor_unpredictability_fdist_ge
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE)
    (Hpos :
       0 < Pr (alice_sample_fdist (R:=R) AHE card_renc)
              [set t | (g `o AliceTrace) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R * (trace_eps0 g + trace_eps1 g))
  <= `H_unp^{g}.
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R).
  by rewrite ltr0n; apply/card_gt0P; exists 0; rewrite inE.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R * (trace_eps0 g + trace_eps1 g) :> R).
  by rewrite ltr_pwDl // mulr_ge0 // addr_ge0 // normr_ge0.
rewrite /alice_trace_predictor_unpredictability.
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_trace_V2_real_le.
Qed.

(* The two honest inputs and Alice's encoded trace obtained from a joint
   hopping-tuple value.
   Naming: the [_of_] connective names the source the conversion reads,
   here the joint carrier of [alice_hop_joint_fdist], not the bare tuple. *)
Let alice_trace_joint_of_hop_joint
    (x : plain AHE * plain AHE * dsdp_alice_hop_tupleT AHE Renc) :
    plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT :=
  (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2).

(* The hopping-tuple distinguisher that applies a trace test after the
   joint hopping-to-trace map.
   Naming: result first, after [distinguisher_of_guess]. *)
Let distinguisher_of_trace_test
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
    plain AHE * plain AHE * dsdp_alice_hop_tupleT AHE Renc -> bool :=
  D \o alice_trace_joint_of_hop_joint.

(* The distribution obtained by mapping the hopping-tuple simulator through
   the encoded trace function.
   Naming: after [dsdp_alice_simulator] of the hopping-tuple level, with
   [trace] marking the carrier of the simulated observation. *)
Definition dsdp_alice_trace_simulator (s : plain AHE) :
    R.-fdist (15.-bseq dsdp_trace_dataT) :=
  fdistmap dsdp_trace_of_hop_tuple (dsdp_alice_simulator s).

(* The joint law of the honest inputs and the simulated encoded trace: the
   honest input law bound to the trace simulator fed the leaked output
   computed from the sampled inputs.
   Naming: after [alice_ideal_joint] of the hopping-tuple level. *)
Definition alice_trace_ideal_joint :
    R.-fdist (plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT) :=
  `p_ [% V2, V3] >>= (fun vv =>
    fdistmap (fun tr => (vv.1, vv.2, tr))
      (dsdp_alice_trace_simulator
        (dsdp_output v1 u1 u2 u3 vv.1 vv.2))).

(* The trace-level ideal joint law is the deterministic image of the
   hopping-tuple ideal joint law. *)
Let alice_trace_ideal_jointE :
  alice_trace_ideal_joint
  = fdistmap alice_trace_joint_of_hop_joint alice_ideal_joint.
Proof.
rewrite /alice_trace_ideal_joint /alice_ideal_joint fdistmap_bind.
congr (_ >>= _); apply: boolp.funext => vv.
by rewrite /dsdp_alice_trace_simulator 2!fdistmap_comp.
Qed.

(* The real executed-trace joint law is the deterministic image of the real
   hopping-tuple joint law. *)
Let alice_trace_real_jointE :
  `p_ [% V2, V3, AliceTrace]
  = fdistmap alice_trace_joint_of_hop_joint
      (`p_ [% V2, V3, AliceHopTuple 0]).
Proof.
by rewrite dsdp_trace_of_hop_tupleE /dist_of_RV fdistmap_comp.
Qed.

(* A Boolean trace test separates the real and simulated joint laws by at most
   the two hop advantages of its lifted hopping-tuple test.
   Naming: after [dsdp_alice_sim_advantage_fdist_le] with [alice_trace] as
   the object stem, as in
   [dsdp_alice_trace_predictor_unpredictability_fdist_ge]; the transfer
   corollaries [dsdp_alice_guess_fdist_view_le] and
   [dsdp_alice_guess_fdist_trace_V2_real_le] keep the hop stem and append
   the observation read after [fdist]. *)
Theorem dsdp_alice_trace_sim_advantage_fdist_le
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr (fdistmap D alice_trace_ideal_joint) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_dk Bob)
       (hop0_reduction
         (fun x => D
           (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2)))
     + indcpa_fdist_epsilon (pkey_of_dk Charlie)
       (hop1_reduction
         (fun x => D
           (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2))).
Proof.
rewrite -Pr_fdistmap_bool alice_trace_real_jointE fdistmap_comp.
rewrite Pr_fdistmap_bool alice_trace_ideal_jointE fdistmap_comp.
exact: (dsdp_alice_sim_advantage_fdist_le card_renc rand_of_renc
          pkey_of_dk v1 u1 u2 u3
          (distinguisher_of_trace_test D)).
Qed.

End dsdp_alice_trace_rv.

Section dsdp_alice_trace_centropy.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Each abbreviation pins, under the name it abbreviates, the parameters that
   dsdp_alice_fdist_secrecy.v discharges; the shadowing is not recursive,
   since the right-hand side resolves against the constant. *)
Local Notation P := (alice_sample_fdist (R:=R) AHE card_renc).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation R2 := (R2 (R:=R) (AHE:=AHE) card_renc).
Local Notation R3 := (R3 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA1 := (RA1 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA2 := (RA2 (R:=R) (AHE:=AHE) card_renc).
Local Notation Sout :=
  (Sout (R:=R) (AHE:=AHE) card_renc v1 u1 u2 u3).
Local Notation hop0_cipher i :=
  (hop0_cipher (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_dk i).
Local Notation hop1_cipher i :=
  (hop1_cipher (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_dk i).
Local Notation AliceHopTuple i :=
  (AliceHopTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3 i).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) (AHE:=AHE) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* The part of Alice's hopping tuple her executed trace shows: the two masks,
   the leaked output and the two received ciphertexts. *)
Definition dsdp_alice_trace_tupleT : finType :=
  ((plain AHE * plain AHE) * plain AHE * cipher AHE * cipher AHE)%type.

(* The trace-visible part of Alice's hopping tuple as a random variable on the
   sample space: the two masks, the leaked output, and the two received
   ciphertexts at hop index 0, where both slots are the real encryptions. *)
Definition AliceTraceTuple : {RV P -> dsdp_alice_trace_tupleT} :=
  [% [% R2, R3], Sout, hop0_cipher 0, hop1_cipher 0].

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
    (plain AHE * dsdp_alice_trace_tupleT) :=
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
    (p : ((Renc * Renc) * dsdp_alice_trace_tupleT)) :
    dsdp_alice_hop_tupleT AHE Renc :=
  (p.2.1.1.1, p.1, p.2.1.1.2, p.2.1.2, p.2.2).

(* The combine randomnesses and the trace-visible tuple read back off a
   hopping tuple.
   Naming: [_of_] as in [hop_tuple_of_rand_trace], in the opposite
   direction. *)
Definition rand_trace_of_hop_tuple
    (v : dsdp_alice_hop_tupleT AHE Renc) :
    ((Renc * Renc) * dsdp_alice_trace_tupleT) :=
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
  AliceHopTuple 0
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
Definition trace_of_trace_tuple (q : dsdp_alice_trace_tupleT) :
    15.-bseq (dsdp_trace_dataT AHE) :=
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
Definition trace_data_plain (x : dsdp_trace_dataT AHE) :
    plain AHE :=
  if x is inl (inl (inl m)) then m else 0.

(* The ciphertext carried by a trace entry, a fixed encryption of zero at any
   other sort. *)
Definition trace_data_cipher (x : dsdp_trace_dataT AHE) :
    cipher AHE :=
  if x is inl (inl (inr c)) then c
  else enc (pkey_of_dk Alice) 0 (rand_of_renc w_rc2).

(* The trace-visible tuple read back off an encoded trace, at the five
   positions the encoding writes it to.
   Naming: [_of_] as in [hop_tuple_of_rand_trace]. *)
Definition trace_tuple_of_trace
    (b : 15.-bseq (dsdp_trace_dataT AHE)) :
    dsdp_alice_trace_tupleT :=
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
Proof. by rewrite dsdp_trace_of_hop_tupleE. Qed.

(* Conditioning on an injective image of a random variable leaves the same
   conditional entropy, since the two conditioning events coincide.
   Naming: local helper, from [cPr_centropy_RV_comp] of
   information_theory/entropy.v. *)
Let centropy_RV_cancel (A B C : finType) (g : B -> C) (h : C -> B)
    (gK : cancel g h) (X : {RV P -> A}) (Y : {RV P -> B}) :
  `H( X | g `o Y ) = `H( X | Y ).
Proof.
have gi : injective g := can_inj gK.
apply: cPr_centropy_RV_comp => x y _.
rewrite 2!cpr_eqE; congr (_ / _); last exact: pfwd1_comp.
have -> : [% X, g `o Y] = (fun p : A * B => (p.1, g p.2)) `o [% X, Y] by [].
have -> : (x, g y) = (fun p : A * B => (p.1, g p.2)) (x, y) by [].
by apply: pfwd1_comp => -[a b] [c d] [] -> /gi ->.
Qed.

(* A random variable independent of a pair drops out of the conditioning of
   the first component of that pair on the second.
   Naming: [_indep] is the local spelling for an independence statement, as
   in [combine_rand_rest_indep]. *)
Let centropy_RV_drop_indep (A B C : finType)
    (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) :
  P |= Z _|_ [% X, Y] -> `H( X | [% Z, Y] ) = `H( X | Y ).
Proof.
move=> HZ; apply: cinde_centropy_eq.
apply: cpr_prd_unit_RV; apply: weak_union.
by apply/cinde_RV_unit.
Qed.

(* Conditioning on Alice's executed trace leaves the same uncertainty about
   Bob's input as conditioning on her hopping tuple. *)
Theorem centropy_AliceTrace_AliceHopTuple :
  `H( V2 | AliceTrace ) = `H( V2 | AliceHopTuple 0 ).
Proof.
rewrite alice_trace_tupleE (centropy_RV_cancel trace_of_trace_tupleK).
rewrite alice_hop_tuple_rand_traceE
        (centropy_RV_cancel hop_tuple_of_rand_traceK).
by rewrite (centropy_RV_drop_indep combine_rand_trace_indep).
Qed.

(* The two abbreviations pin the parameters of the view ladder, as the
   abbreviations this section opens with do. *)
Local Notation AliceView :=
  (AliceView (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation alice_view_of_hop_tupleE :=
  (alice_view_of_hop_tupleE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).

(* The hopping tuple is the first component of Alice's view.
   Naming: [_of_] names the source the conversion reads, after
   [hop_tuple_of_rand_trace]. *)
Lemma alice_hop_tuple_of_view :
  AliceHopTuple 0 = (fun q => q.1.1.1) `o AliceView.
Proof. by []. Qed.

(* Conditioning on Alice's view leaves the same uncertainty about Bob's input
   as conditioning on her hopping tuple. *)
Corollary centropy_AliceView_AliceHopTuple :
  `H( V2 | AliceView ) = `H( V2 | AliceHopTuple 0 ).
Proof.
(* Each of the two is a deterministic function of the other, so the
   contraction of entropy.v applies in both directions. *)
transitivity (`H( V2 | [% AliceView, AliceHopTuple 0] )).
  by rewrite [in RHS]alice_hop_tuple_of_view centropy_RV_contraction.
rewrite centropy_RV_fdistA.
by rewrite [in LHS]alice_view_of_hop_tupleE centropy_RV_contraction.
Qed.

End dsdp_alice_trace_centropy.

Section dsdp_alice_trace_ideal_test_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Each abbreviation pins, under the name it abbreviates, the parameters
   discharged by the sections above, as Section dsdp_alice_trace_centropy
   does. *)
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) card_renc rand_of_renc v1 u1 u2 u3
     dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation dsdp_alice_trace_simulator :=
  (dsdp_alice_trace_simulator (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation alice_trace_ideal_joint :=
  (alice_trace_ideal_joint (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation dsdp_trace_of_hop_tuple :=
  (dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).

(* The Boolean ideal trace experiment: sample the honest inputs, run the
   trace simulator on their leaked output, and apply the test.
   Naming: after [alice_trace_ideal_joint], with [test] marking the Boolean
   experiment a distinguisher plays against that law. *)
Definition alice_trace_ideal_test
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
    R.-fdist bool :=
  `p_ [% V2, V3] >>= (fun vv =>
    dsdp_alice_trace_simulator (dsdp_output v1 u1 u2 u3 vv.1 vv.2)
      >>= (fun tr => fdist1 (D (vv.1, vv.2, tr)))).

(* The experiment is the pushforward of the ideal joint law along the
   test.
   Naming: the [E] suffix marks the equation, after [alice_trace_tupleE]. *)
Lemma alice_trace_ideal_testE
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  alice_trace_ideal_test D = fdistmap D alice_trace_ideal_joint.
Proof.
rewrite /alice_trace_ideal_test /alice_trace_ideal_joint fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => vv.
by rewrite fdistmap_comp.
Qed.

(* The simulator-advantage bound with its ideal side written through the
   named experiment.
   Naming: extends [dsdp_alice_trace_sim_advantage_fdist_le] with the [test]
   variant token before [le]; kept long to preserve the family grouping. *)
Corollary dsdp_alice_trace_sim_advantage_fdist_test_le
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr (alice_trace_ideal_test D) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_dk Bob)
       (hop0_reduction
         (fun x => D (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2)))
     + indcpa_fdist_epsilon (pkey_of_dk Charlie)
       (hop1_reduction
         (fun x => D (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2))).
Proof.
rewrite alice_trace_ideal_testE.
exact: (dsdp_alice_trace_sim_advantage_fdist_le card_renc rand_of_renc
          v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2 D).
Qed.

End dsdp_alice_trace_ideal_test_sec.

Section dsdp_alice_trace_public_setup.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (pk_a pk_b pk_c : pub_key AHE).
Variable w_rc2 : Renc.

(* Alice's encoded executed trace read off a value of her hopping tuple,
   with the reconstruction key passed as Alice's public key.
   Naming: after [dsdp_trace_of_hop_tuple], with [pub] marking the
   public-key setup, as in [dsdp_alice_simulator_pub]. *)
Definition dsdp_trace_of_hop_tuple_pub
    (v : dsdp_alice_hop_tupleT AHE Renc) :
    15.-bseq (dsdp_trace_dataT AHE) :=
  [bseq inl (inl (inl v.1.1.2));
        inl (inl (inr
          (enc pk_a
               (v.1.1.2 - u1 * v1 + v.1.1.1.1.1 + v.1.1.1.1.2)
               (rand_of_renc w_rc2))));
        inl (inl (inr v.2));
        inl (inl (inr v.1.2));
        inl (inl (inl v.1.1.1.1.2));
        inl (inl (inl v.1.1.1.1.1));
        inl (inl (inl u3)); inl (inl (inl u2));
        inl (inl (inl u1)); inl (inl (inl v1));
        inl (inr tt)].

(* The trace simulator with its cryptographic setup passed as the three
   public keys it reads: Alice's for the reconstructed ciphertext, Bob's and
   Charlie's for the two zero encryptions.
   Naming: after [dsdp_alice_trace_simulator], with [pub] as above. *)
Definition dsdp_alice_trace_simulator_pub (s : plain AHE) :
    R.-fdist (15.-bseq (dsdp_trace_dataT AHE)) :=
  fdistmap dsdp_trace_of_hop_tuple_pub
           (dsdp_alice_simulator_pub card_renc rand_of_renc pk_b pk_c s).

End dsdp_alice_trace_public_setup.

Section dsdp_alice_trace_public_compat.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variable w_rc2 : Renc.

(* Instantiating Alice's public key from her private key yields the
   existing encoder.
   Naming: the [E] suffix marks the instantiation equation. *)
Lemma dsdp_trace_of_hop_tuple_pubE :
  dsdp_trace_of_hop_tuple_pub rand_of_renc v1 u1 u2 u3
    (pub_of_priv dk_a) w_rc2
  = dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rc2.
Proof. by []. Qed.

(* Instantiating the three public keys from the private keys yields the
   existing trace simulator.
   Naming: the [E] suffix marks the instantiation equation. *)
Lemma dsdp_alice_trace_simulator_pubE (s : plain AHE) :
  dsdp_alice_trace_simulator_pub (R:=R) card_renc rand_of_renc v1 u1 u2 u3
    (pub_of_priv dk_a) (pub_of_priv dk_b) (pub_of_priv dk_c) w_rc2 s
  = dsdp_alice_trace_simulator card_renc rand_of_renc v1 u1 u2 u3
      dk_a dk_b dk_c w_rc2 s.
Proof. by []. Qed.

End dsdp_alice_trace_public_compat.

Section dsdp_alice_trace_avg_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variable w_rb2 : Renc.

(* Each parameterized abbreviation pins everything but the re-encryption
   coin, which this section samples. *)
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceTraceW w :=
  (AliceTrace (R:=R) card_renc rand_of_renc v1 u1 u2 u3
     dk_a dk_b dk_c w_rb2 w).
Local Notation alice_trace_ideal_joint_at w :=
  (alice_trace_ideal_joint (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w).
Local Notation dsdp_trace_of_hop_tuple_at w :=
  (dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).

(* The real executed-trace joint law with a uniformly sampled re-encryption
   coin.
   Naming: after the per-coin joint law of
   [dsdp_alice_trace_sim_advantage_fdist_le], with [avg] marking the
   sampled coin. *)
Definition alice_trace_real_joint_avg :
    R.-fdist (plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT) :=
  fdist_uniform card_renc >>= (fun w => `p_ [% V2, V3, AliceTraceW w]).

(* The ideal trace joint law with a uniformly sampled re-encryption coin.
   Naming: after [alice_trace_ideal_joint], with [avg] as above. *)
Definition alice_trace_ideal_joint_avg :
    R.-fdist (plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT) :=
  fdist_uniform card_renc >>= (fun w => alice_trace_ideal_joint_at w).

(* The averaged real-versus-ideal gap is at most the average of the two
   per-coin hop advantages.
   Naming: extends [dsdp_alice_trace_sim_advantage_fdist_le] with the [avg]
   variant token before [le]; kept long to preserve the family grouping. *)
Theorem dsdp_alice_trace_sim_advantage_fdist_avg_le
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr alice_trace_real_joint_avg [set x | D x]
     - Pr (fdistmap D alice_trace_ideal_joint_avg) [set true] |
  <= \sum_(w in Renc) (fdist_uniform card_renc : R.-fdist Renc) w
       * (indcpa_fdist_epsilon (pkey_of_dk Bob)
            (hop0_reduction
              (fun x => D (x.1.1, x.1.2, dsdp_trace_of_hop_tuple_at w x.2)))
          + indcpa_fdist_epsilon (pkey_of_dk Charlie)
            (hop1_reduction
              (fun x => D (x.1.1, x.1.2, dsdp_trace_of_hop_tuple_at w x.2)))).
Proof.
rewrite Pr_fdistmap_bool.
apply: fdist_mixture_advantage_le => w.
rewrite -[X in `|_ - X| <= _]Pr_fdistmap_bool.
exact: (dsdp_alice_trace_sim_advantage_fdist_le card_renc rand_of_renc
          v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w D).
Qed.

End dsdp_alice_trace_avg_sec.

Section dsdp_alice_trace_unpredictability_ereal_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Hypothesis u3_unit : u3 \is a GRing.unit.
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Extended-real statements are written with the constructors and the order
   constant explicitly (EFin, EPInf, Order.le): ahe_monoid.v delimits
   emul_scope with %E, shadowing constructive_ereal's delimiter in every
   file that imports the HE stack. *)
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) card_renc rand_of_renc v1 u1 u2 u3
     dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation dsdp_trace_of_hop_tuple :=
  (dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation alice_trace_predictor_unpredictability :=
  (alice_trace_predictor_unpredictability (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* The success probability of a trace predictor, the quantity the zero-safe
   unpredictability reads. *)
Let trace_guess_pr (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  Pr (alice_sample_fdist (R:=R) AHE card_renc)
     [set t | (g `o AliceTrace) t == V2 t].

(* The advantage against Bob's key of the hop-0 reduction of the
   distinguisher associated with a trace predictor composed with
   dsdp_trace_of_hop_tuple. *)
Let trace_eps0 (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_dk Bob)
    (hop0_reduction
       (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple))).

(* The advantage against Charlie's key of the hop-1 reduction of the
   distinguisher associated with a trace predictor composed with
   dsdp_trace_of_hop_tuple. *)
Let trace_eps1 (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_dk Charlie)
    (hop1_reduction
       (distinguisher_of_guess (g \o dsdp_trace_of_hop_tuple))).

(* The zero-safe unpredictability of Bob's input at Alice's encoded trace:
   infinite at zero predictor success, the negative logarithm otherwise.
   Naming: the [_ereal] token marks the extended-real carrier, after
   [conv_erealE] of probability/convex.v. *)
Definition alice_trace_predictor_unpredictability_ereal
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) : \bar R :=
  if trace_guess_pr g == 0 then @EPInf R
  else EFin (alice_trace_predictor_unpredictability g).

(* Zero success is infinite unpredictability.
   Naming: the [E] suffix marks the branch equation. *)
Lemma alice_trace_predictor_unpredictability_ereal_zeroE g :
  trace_guess_pr g = 0 ->
  alice_trace_predictor_unpredictability_ereal g = @EPInf R.
Proof.
by move=> H; rewrite /alice_trace_predictor_unpredictability_ereal H eqxx.
Qed.

(* Positive success is the finite negative logarithm.
   Naming: [_gt0] spells the positivity premise, after MathComp; the [E]
   suffix marks the branch equation. *)
Lemma alice_trace_predictor_unpredictability_ereal_gt0E g :
  0 < trace_guess_pr g ->
  alice_trace_predictor_unpredictability_ereal g
  = EFin (- log (trace_guess_pr g)).
Proof.
move=> H.
by rewrite /alice_trace_predictor_unpredictability_ereal gt_eqF.
Qed.

(* The real-valued definition is the finite branch.
   Naming: [_fin] marks the finite branch; the [E] suffix marks the branch
   equation. *)
Lemma alice_trace_predictor_unpredictability_ereal_finE g :
  0 < trace_guess_pr g ->
  alice_trace_predictor_unpredictability_ereal g
  = EFin (alice_trace_predictor_unpredictability g).
Proof.
move=> H.
by rewrite /alice_trace_predictor_unpredictability_ereal gt_eqF.
Qed.

(* The existing lower bound, lifted to the zero-safe order with no
   positivity premise: the zero branch is infinite, and the positive branch
   consumes the guessing bound through
   [dsdp_alice_trace_predictor_unpredictability_fdist_ge].
   Naming: extends that theorem name with the [ereal] variant token before
   [ge]; kept long to preserve the family grouping. *)
Theorem dsdp_alice_trace_predictor_unpredictability_fdist_ereal_ge g :
  Order.le
    (EFin (log (#|plain AHE|%:R)
           - log (1 + #|plain AHE|%:R * (trace_eps0 g + trace_eps1 g))))
    (alice_trace_predictor_unpredictability_ereal g).
Proof.
rewrite /alice_trace_predictor_unpredictability_ereal.
case: (eqVneq (trace_guess_pr g) 0) => [_|Hneq]; first exact: leey.
have Hpos : 0 < trace_guess_pr g by rewrite lt0r Hneq /=; exact: Pr_ge0.
rewrite lee_fin.
exact: (dsdp_alice_trace_predictor_unpredictability_fdist_ge u3_unit Hpos).
Qed.

End dsdp_alice_trace_unpredictability_ereal_sec.

Section dsdp_alice_raw_trace_sec.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) card_renc rand_of_renc v1 u1 u2 u3
     dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation alice_trace_ideal_joint :=
  (alice_trace_ideal_joint (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation dsdp_trace_of_hop_tuple :=
  (dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).

(* The fixed-key decoding of one encoded trace datum: plaintexts and
   ciphertexts restored as themselves, the private-key mark restored as dk,
   the public-key mark as pk.  There is no global inverse: the encoding
   erases which key value each mark carried.
   Naming: the [_of_] connective names the source the conversion reads,
   after [trace_data_of_di_data], in the opposite direction. *)
Definition di_data_of_trace_data (dk : priv_key AHE) (pk : pub_key AHE)
    (x : dsdp_trace_dataT) : di_data DI :=
  match x with
  | inl (inl (inl m)) => di_data_of_plain DI m
  | inl (inl (inr c)) => di_data_of_cipher DI c
  | inl (inr _) => di_data_of_priv_key DI dk
  | inr _ => di_data_of_pub_key DI pk
  end.

(* Alice's raw interpreter trace at one sample.  A plain function: di_data
   DI is not a finType and no distribution on it is ever formed. *)
Definition alice_raw_trace (s : dsdp_alice_sampleT AHE Renc) :
    seq (di_data DI) :=
  nth [::]
      (run_interp 15 (dsdp_procs_of_sample (R:=R) card_renc rand_of_renc
                        v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2 s)).2 0.

(* The round trip on Alice's actual generated trace: decoding with her
   private key restores the raw interpreter trace.  The public key pk is
   universally quantified because her trace contains no public-key mark.
   Naming: the [E] suffix marks the round-trip equation. *)
Lemma alice_raw_trace_decodeE (pk : pub_key AHE)
    (s : dsdp_alice_sampleT AHE Renc) :
  map (di_data_of_trace_data dk_a pk) (AliceTrace s) = alice_raw_trace s.
Proof.
have -> : map (di_data_of_trace_data dk_a pk) (AliceTrace s)
        = map (di_data_of_trace_data dk_a pk
               \o @trace_data_of_di_data AHE)
              (nth [::]
                 (run_interp 15 (dsdp_procs_of_sample (R:=R) card_renc
                    rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2 s)).2
                 0).
  by rewrite map_comp.
rewrite /alice_raw_trace /dsdp_procs_of_sample.
by rewrite dsdp_run_traces_ok.
Qed.

(* The simulator-advantage bound for a Boolean test reading the raw
   interpreter trace, via composition with the fixed-key decoder.
   Naming: extends [dsdp_alice_trace_sim_advantage_fdist_le] with [raw]
   marking the observation read; kept long to preserve the family
   grouping. *)
Corollary dsdp_alice_raw_trace_sim_advantage_fdist_le
    (D_raw : plain AHE * plain AHE * seq (di_data DI) -> bool) :
  `| Pr (alice_sample_fdist (R:=R) AHE card_renc)
        [set t | D_raw (V2 t, V3 t, alice_raw_trace t)]
     - Pr (fdistmap
             (fun x : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT =>
                D_raw (x.1.1, x.1.2,
                       map (di_data_of_trace_data dk_a (pub_of_priv dk_a))
                           x.2))
             alice_trace_ideal_joint) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_dk Bob)
       (hop0_reduction
         (fun x => D_raw (x.1.1, x.1.2,
            map (di_data_of_trace_data dk_a (pub_of_priv dk_a))
                (dsdp_trace_of_hop_tuple x.2))))
     + indcpa_fdist_epsilon (pkey_of_dk Charlie)
       (hop1_reduction
         (fun x => D_raw (x.1.1, x.1.2,
            map (di_data_of_trace_data dk_a (pub_of_priv dk_a))
                (dsdp_trace_of_hop_tuple x.2)))).
Proof.
set D := fun x : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT =>
  D_raw (x.1.1, x.1.2,
         map (di_data_of_trace_data dk_a (pub_of_priv dk_a)) x.2).
have HrealE : Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
            = Pr (alice_sample_fdist (R:=R) AHE card_renc)
                 [set t | D_raw (V2 t, V3 t, alice_raw_trace t)].
  rewrite /dist_of_RV Pr_fdistmap_preim; apply: eq_bigl => t.
  rewrite !inE.
  by rewrite -(alice_raw_trace_decodeE (pub_of_priv dk_a)).
rewrite -HrealE.
exact: (dsdp_alice_trace_sim_advantage_fdist_le card_renc rand_of_renc
          v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2 D).
Qed.

End dsdp_alice_raw_trace_sec.
