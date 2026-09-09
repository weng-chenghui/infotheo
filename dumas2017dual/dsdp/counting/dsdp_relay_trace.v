From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba jfdist_cond entropy graphoid.
Require Import spp_proba extra_proba extra_entropy extra_algebra statdist.
Require Import homomorphic_encryption idealized_ahe.
Require Import smc_interpreter smc_session_types pismc.
Require Import dsdp_interface dsdp_session_types dsdp_pismc.
Require Import dsdp_random_inputs dsdp_relay_secrecy.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* Corrupted-relay secrecy read at the trace the piSMC interpreter produces.  *)
(* A relay's view is no longer a tuple standing for what it observes: it is   *)
(* the sequence the interpreter writes for that party while it executes the   *)
(* DSDP programs, and the two objects are shown to be the same observation.   *)
(*                                                                            *)
(* One value of dsdp_random_inputs is the first object of the flow, and the   *)
(* whole file runs at that one sample space and that one law.  The three      *)
(* piSMC programs of dsdp_pismc.v enter through Standard_DSDP_Interface at    *)
(* the idealized scheme, which instantiates their ciphertexts, coins and      *)
(* keys, and through run_interp, which executes them on seed streams read off *)
(* the record's six coin coordinates.  dsdp_run_traces_idealE is what the run *)
(* produces: thirteen entries for Alice, six for Bob, five for Charlie.       *)
(*                                                                            *)
(* Two observation changes carry the four bounds of dsdp_relay_secrecy.v      *)
(* from the view to the trace, and neither costs anything.                    *)
(* dsdp_run_traces_idealE makes a relay's trace a deterministic image of its  *)
(* view, and bob_trace_of_viewK (with its Charlie sibling) inverts that       *)
(* image, so can_centropy_eq equates the two conditional entropies.  The      *)
(* four privacy theorems of dsdp_relay_secrecy.v are then the terminal        *)
(* evaluations, re-read at the trace with the same value log m.               *)
(*                                                                            *)
(* Every statement here is at the idealized scheme, where a ciphertext is its *)
(* plaintext and no ciphertext depends on a coin, so the coins a relay        *)
(* records are inert components of its view rather than the randomness any    *)
(* ciphertext in that view was built with.  The bounds are counting-axis and  *)
(* unconditional, as the view bounds they re-read are.                        *)
(*                                                                            *)
(* Alice's trace is stated by dsdp_run_traces_idealE and no theorem is read   *)
(* at it: her axis is the hopping one, at the real scheme, where              *)
(* dsdp_alice_trace_link.v states the matching identity.                      *)
(*                                                                            *)
(* dsdp_procs_ideal, dsdp_seeds_ideal : the three DSDP programs at one        *)
(*   sample's inputs and the six coin coordinates that seed them.             *)
(* dsdp_run_traces_idealE : the three traces of the eighteen-round run.       *)
(* ideal_trace_size : eighteen rounds bound every party's trace.              *)
(* ideal_trace_of_run : the trace party i sees in the run, as a random        *)
(*   variable.                                                                *)
(* BobTrace, CharlieTrace : each relay's trace as a random observation.       *)
(* bob_trace_of_viewE, charlie_trace_of_viewE : the trace is a deterministic  *)
(*   image of the view; bob_trace_of_viewK and its sibling invert it.         *)
(* centropy_V1_bob_traceE and its three siblings : trace and view leave the   *)
(*   same uncertainty about the secret.                                       *)
(* bob_trace_privacy_V1, bob_trace_privacy_V3, charlie_trace_privacy_V1,      *)
(*   charlie_trace_privacy_V2 : H(secret | trace) = log m and it is positive. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope proc_scope.
Local Open Scope sproc_scope.

Section dsdp_relay_trace.
(* Each relay's interpreter trace is a reversible recoding of the view
   dsdp_relay_secrecy.v bounds, so every bound there is a bound on what the
   executed protocol hands that relay. *)
Context {R : realType}.
Variables (p q : nat).
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.
Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.

(* One 3-party run at this modulus, on the counting side: the sample space,
   the law, the eleven random inputs and the six coins the run draws. *)
Variable I : dsdp_random_inputs R p_gt1 q_gt1.

Local Notation T := (sampleT I).
Local Notation P := (sample_fdist I).
Local Notation V1 := (V1 I).
Local Notation V2 := (V2 I).
Local Notation V3 := (V3 I).
Local Notation U1 := (U1 I).
Local Notation U2 := (U2 I).
Local Notation U3 := (U3 I).
Local Notation R2 := (R2 I).
Local Notation R3 := (R3 I).
Local Notation Dk_a := (Dk_a I).
Local Notation Dk_b := (Dk_b I).
Local Notation Dk_c := (Dk_c I).

(* The six coins the run draws, two per party.  The interpreter takes them as
   seed streams and writes them back into the traces. *)
Local Notation coin_ra1 := (coin_ra1 I).
Local Notation coin_ra2 := (coin_ra2 I).
Local Notation coin_rb1 := (coin_rb1 I).
Local Notation coin_rb2 := (coin_rb2 I).
Local Notation coin_rc1 := (coin_rc1 I).
Local Notation coin_rc2 := (coin_rc2 I).

(* The two relay views of dsdp_relay_secrecy.v at this run, the objects the
   four bounds re-read below are stated at. *)
Local Notation BobView := (BobView (I:=I)).
Local Notation CharlieView := (CharlieView (I:=I)).

(* ========================================================================== *)
(* The idealized scheme the run executes at                                   *)
(* ========================================================================== *)

(* The idealized homomorphic scheme on the plaintext ring, where plaintext,
   randomness, ciphertext and both keys are the ring itself, encryption
   returns its plaintext and decryption returns its ciphertext. *)
Local Definition Idealized_EncDec_instance := @Idealized_isEncDec msg.
Local Definition Idealized_AHEnc_instance := @Idealized_isAHEnc msg.
Local Definition Idealized_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      Idealized_EncDec_instance Idealized_AHEnc_instance).

Let AHE : AHEncType := Idealized_AHEnc_local.

(* The interface the three programs run at: the canonical one of
   dsdp_interface.v, carried by the idealized scheme. *)
Let DI := Standard_DSDP_Interface AHE.

(* The carrier of a trace entry, finite because every one of the scheme's five
   carriers is the plaintext ring. *)
Local Notation ideal_datum := (std_data AHE : finType).

(* The four injections into that carrier. *)
Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let k := di_data_of_priv_key DI.
Let rd := di_data_of_rand DI.

(* The scheme's own decryption, which the programs receive as their decoder. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

(* Every party's public key, at the ring's zero: the idealized encryption
   ignores the key it is given. *)
Let ek : party_id -> pub_key AHE := fun _ => 0.

(* The three programs are qualified by their module: dsdp_program.v declares
   the same three names, so the qualification fixes which pair the run uses. *)

(* Alice's program at the idealized scheme. *)
Let palice_ideal := @dsdp_pismc.palice DI decode ek.

(* Bob's program at the same scheme. *)
Let pbob_ideal := @dsdp_pismc.pbob DI decode ek.

(* Charlie's program at the same scheme. *)
Let pcharlie_ideal := @dsdp_pismc.pcharlie DI decode ek.

(* The three programs at the inputs one sample gives them, in the party order
   the interpreter indexes by. *)
Definition dsdp_procs_ideal (t : T) : seq (proc (di_data DI)) :=
  erase_aprocs
    [aprocs palice_ideal (party_key_v (Dk_a t))
              (V1 t) (U1 t) (U2 t) (U3 t) (R2 t) (R3 t) ;
            pbob_ideal (party_key_v (Dk_b t)) (V2 t) ;
            pcharlie_ideal (party_key_v (Dk_c t)) (V3 t)].

(* The seed stream each party consumes, its two coin coordinates at that
   sample, in the order its program draws them. *)
Definition dsdp_seeds_ideal (t : T) : seq (seq (di_data DI)) :=
  [:: [:: rd (coin_ra1 t); rd (coin_ra2 t)];
      [:: rd (coin_rb1 t); rd (coin_rb2 t)];
      [:: rd (coin_rc1 t); rd (coin_rc2 t)]].

(* What the eighteen-round run writes for the three parties, newest entry
   first.  Thirteen entries for Alice, six for Bob, five for Charlie. *)
Lemma dsdp_run_traces_idealE (t : T) :
  (run_interp 18 (dsdp_procs_ideal t) (dsdp_seeds_ideal t)).1.2 =
  [:: [:: d (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t)
           - R2 t - R3 t + U1 t * V1 t);
          e (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t));
          rd (coin_ra2 t); rd (coin_ra1 t);
          e (V3 t); e (V2 t);
          d (R3 t); d (R2 t); d (U3 t); d (U2 t); d (U1 t); d (V1 t);
          k (party_key_v (Dk_a t))];
      [:: rd (coin_rb2 t);
          e (V3 t * U3 t + R3 t);
          e (V2 t * U2 t + R2 t);
          rd (coin_rb1 t); d (V2 t);
          k (party_key_v (Dk_b t))];
      [:: rd (coin_rc2 t);
          e (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t));
          rd (coin_rc1 t); d (V3 t);
          k (party_key_v (Dk_c t))]].
Proof. reflexivity. Qed.

(* Eighteen rounds bound every party's trace of the run.  The bound packages
   a trace as a bounded sequence. *)
Lemma ideal_trace_size (i : party_id) (t : T) :
  (size (nth [::] (run_interp 18 (dsdp_procs_ideal t)
                     (dsdp_seeds_ideal t)).1.2 n( i )) <= 18)%N.
Proof. exact: size_traces_nth. Qed.

(* The trace party i sees in the run, as a random variable.  The
   corrupted-relay bounds are re-read at this observation. *)
Definition ideal_trace_of_run (i : party_id) :
    {RV P -> 18.-bseq ideal_datum} :=
  fun t => Bseq (ideal_trace_size i t).

(* Bob's trace, as a random observation.  It is the object the executed
   protocol hands a corrupted Bob. *)
Definition BobTrace := ideal_trace_of_run Bob.

(* Charlie's trace as a random observation. *)
Definition CharlieTrace := ideal_trace_of_run Charlie.

(* The plaintext-ring zero, the coin the readers below return on the branch
   no trace of the run reaches. *)
Let coin0 : msg := 0.

(* The value type BobView takes, which the two readers below encode and
   decode. *)
Local Notation bob_viewT :=
  (Bob.-key Dec msg * msg * Charlie.-enc msg * Bob.-enc msg *
   msg * msg)%type.

(* The value type CharlieView takes, one ciphertext shorter than Bob's. *)
Local Notation charlie_viewT :=
  (Charlie.-key Dec msg * msg * Charlie.-enc msg * msg * msg)%type.

(* Bob's six trace entries built from his view, newest first: second coin, the
   two received ciphertexts, first coin, input, key.  A ciphertext is its
   plaintext here, so the party tag his view carries is dropped and restored
   by the reader. *)
Definition bob_trace_of_view (w : bob_viewT) : 18.-bseq ideal_datum :=
  [bseq rd w.2;
        e (enc_for_v w.1.1.1.2);
        e (enc_for_v w.1.1.2);
        rd w.1.2;
        d w.1.1.1.1.2;
        k (party_key_v w.1.1.1.1.1)].

(* Bob's view read back off a trace of that shape, which is what makes the
   recoding lose nothing. *)
Definition bob_view_of_trace (s : 18.-bseq ideal_datum) : bob_viewT :=
  match val s with
  | [:: inr (inr c2); inl (inl (inr x)); inl (inl (inr y));
        inr (inr c1); inl (inl (inl v)); inl (inr key)] =>
      (KeyOf Bob Dec key, v, E' Charlie x, E' Bob y, c1, c2)
  | _ => (KeyOf Bob Dec 0, 0, E' Charlie 0, E' Bob 0, coin0, coin0)
  end.

(* The encoding of Bob's view into his trace is left-invertible, so the two
   observations carry the same information. *)
Lemma bob_trace_of_viewK : cancel bob_trace_of_view bob_view_of_trace.
Proof.
(* The key and the two ciphertexts are one-constructor Variants, so the
   reader's match stays stuck until they are opened. *)
by case=> [[[[[[key] v2] [x]] [y]] c1] c2].
Qed.

(* The trace the interpreter produces for Bob is a deterministic image of the
   view dsdp_relay_secrecy.v bounds. *)
Lemma bob_trace_of_viewE : BobTrace = bob_trace_of_view `o BobView.
Proof.
apply: funext => t; apply/val_inj; rewrite /BobTrace /ideal_trace_of_run.
by move: (ideal_trace_size Bob t); rewrite dsdp_run_traces_idealE.
Qed.

(* Bob's trace and his view leave the same uncertainty about Alice's input. *)
Lemma centropy_V1_bob_traceE : `H(V1 | BobTrace) = `H(V1 | BobView).
Proof.
by rewrite bob_trace_of_viewE; exact: (can_centropy_eq bob_trace_of_viewK).
Qed.

(* Bob's trace and his view leave the same uncertainty about Charlie's
   input. *)
Lemma centropy_V3_bob_traceE : `H(V3 | BobTrace) = `H(V3 | BobView).
Proof.
by rewrite bob_trace_of_viewE; exact: (can_centropy_eq bob_trace_of_viewK).
Qed.

(* Charlie's five trace entries built from his view, newest first.  Second
   coin, the received ciphertext, first coin, input, key. *)
Definition charlie_trace_of_view (w : charlie_viewT) :
    18.-bseq ideal_datum :=
  [bseq rd w.2;
        e (enc_for_v w.1.1.2);
        rd w.1.2;
        d w.1.1.1.2;
        k (party_key_v w.1.1.1.1)].

(* Charlie's view read back off a trace of that shape. *)
Definition charlie_view_of_trace (s : 18.-bseq ideal_datum) :
    charlie_viewT :=
  match val s with
  | [:: inr (inr c2); inl (inl (inr x)); inr (inr c1);
        inl (inl (inl v)); inl (inr key)] =>
      (KeyOf Charlie Dec key, v, E' Charlie x, c1, c2)
  | _ => (KeyOf Charlie Dec 0, 0, E' Charlie 0, coin0, coin0)
  end.

(* The encoding of Charlie's view into his trace is left-invertible. *)
Lemma charlie_trace_of_viewK :
  cancel charlie_trace_of_view charlie_view_of_trace.
Proof. by case=> [[[[[key] v3] [x]] c1] c2]. Qed.

(* The trace the interpreter produces for Charlie is a deterministic image of
   the view dsdp_relay_secrecy.v bounds. *)
Lemma charlie_trace_of_viewE :
  CharlieTrace = charlie_trace_of_view `o CharlieView.
Proof.
apply: funext => t; apply/val_inj.
rewrite /CharlieTrace /ideal_trace_of_run.
by move: (ideal_trace_size Charlie t); rewrite dsdp_run_traces_idealE.
Qed.

(* Charlie's trace and his view leave the same uncertainty about Alice's
   input. *)
Lemma centropy_V1_charlie_traceE : `H(V1 | CharlieTrace) = `H(V1 | CharlieView).
Proof.
by rewrite charlie_trace_of_viewE;
   exact: (can_centropy_eq charlie_trace_of_viewK).
Qed.

(* Charlie's trace and his view leave the same uncertainty about Bob's
   input. *)
Lemma centropy_V2_charlie_traceE : `H(V2 | CharlieTrace) = `H(V2 | CharlieView).
Proof.
by rewrite charlie_trace_of_viewE;
   exact: (can_centropy_eq charlie_trace_of_viewK).
Qed.

(* Given the trace the interpreter hands a corrupted Bob, Alice's input keeps
   log m bits of uncertainty. *)
Theorem bob_trace_privacy_V1 :
  `H(V1 | BobTrace) = log (m%:R : R) /\ `H(V1 | BobTrace) > 0.
Proof. rewrite centropy_V1_bob_traceE; exact: bob_privacy_V1. Qed.

(* Given that same trace, Charlie's input keeps log m bits of uncertainty, by
   Alice's mask R3, which Bob never sees. *)
Theorem bob_trace_privacy_V3 :
  `H(V3 | BobTrace) = log (m%:R : R) /\ `H(V3 | BobTrace) > 0.
Proof. rewrite centropy_V3_bob_traceE; exact: bob_privacy_V3. Qed.

(* Given the trace the interpreter hands a corrupted Charlie, Alice's input
   keeps log m bits of uncertainty. *)
Theorem charlie_trace_privacy_V1 :
  `H(V1 | CharlieTrace) = log (m%:R : R) /\ `H(V1 | CharlieTrace) > 0.
Proof. rewrite centropy_V1_charlie_traceE; exact: charlie_privacy_V1. Qed.

(* Given that same trace, Bob's input keeps log m bits of uncertainty, by
   Alice's mask R2, which Charlie never sees. *)
Theorem charlie_trace_privacy_V2 :
  `H(V2 | CharlieTrace) = log (m%:R : R) /\ `H(V2 | CharlieTrace) > 0.
Proof. rewrite centropy_V2_charlie_traceE; exact: charlie_privacy_V2. Qed.

End dsdp_relay_trace.
