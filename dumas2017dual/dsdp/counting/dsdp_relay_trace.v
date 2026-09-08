From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba jfdist_cond entropy graphoid.
Require Import spp_proba extra_proba extra_entropy extra_algebra statdist.
Require Import homomorphic_encryption.
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
(* piSMC programs of dsdp_pismc.v enter through Symbolic_DSDP_Interface,      *)
(* which instantiates their abstract ciphertexts, coins and keys, and through *)
(* run_interp, which executes them on seed streams read off the record's six  *)
(* coin coordinates.  dsdp_run_traces_symbolicE is what the run produces:     *)
(* thirteen entries for Alice, six for Bob, five for Charlie.                 *)
(*                                                                            *)
(* Two observation changes carry the four bounds of dsdp_relay_secrecy.v      *)
(* from the view to the trace, and neither costs anything.                    *)
(* dsdp_run_traces_symbolicE makes a relay's trace a deterministic image of   *)
(* its view, and bob_trace_of_viewK (with its Charlie sibling) inverts that   *)
(* image, so can_centropy_eq equates the two conditional entropies.  The      *)
(* four privacy theorems of dsdp_relay_secrecy.v are then the terminal        *)
(* evaluations, re-read at the trace with the same value log m.               *)
(*                                                                            *)
(* Every statement here is at the symbolic cipher model: a ciphertext is its  *)
(* plaintext under a party label, and no ciphertext depends on a coin, so the *)
(* coins a relay records are inert components of its view rather than the     *)
(* randomness any ciphertext in that view was built with.  The bounds are     *)
(* counting-axis and unconditional, as the view bounds they re-read are.      *)
(*                                                                            *)
(* Alice's symbolic trace is stated by dsdp_run_traces_symbolicE and no       *)
(* theorem is read at it: her axis is the hopping one, at the real scheme,    *)
(* where dsdp_alice_trace_link.v states the matching identity.                *)
(*                                                                            *)
(* dsdp_procs_symbolic, dsdp_seeds_symbolic : the three DSDP programs at one  *)
(*   sample's inputs and the six coin coordinates that seed them.             *)
(* dsdp_run_traces_symbolicE : the three traces of the eighteen-round run.    *)
(* symbolic_trace_size : eighteen rounds bound every party's trace.           *)
(* symbolic_trace_of_run : the trace party i sees in the run, as a random     *)
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

(* The interface the three programs run at: ciphertexts are party-labeled
   plaintexts and coins are the record's own coin space. *)
Let symbolic_DI := Symbolic_DSDP_Interface msg (coinT I).

(* The carrier of a symbolic trace entry, finite because both the plaintext
   ring and the coin space are. *)
Local Notation symbolic_datum := (symbolic_data msg (coinT I) : finType).

(* The four injections into that carrier, and the party-labeled encryption
   read as a trace entry. *)
Let datum_plain := di_data_of_plain symbolic_DI.
Let datum_cipher := di_data_of_cipher symbolic_DI.
Let datum_priv_key := di_data_of_priv_key symbolic_DI.
Let datum_coin := di_data_of_rand symbolic_DI.
Let datum_enc (i : party_id) (x : msg) := datum_cipher (party_E i x).

(* The three programs are qualified by their module: dsdp_program.v declares
   the same three names, and the unqualified ones resolve there.  [party_D] is
   applied to [@ _ _] because its two implicits precede the decoder's own
   arguments, so nothing else fixes them at a partial application. *)

(* Alice's program at the symbolic interface, decrypting with party_D and
   taking each party's own label as its public key. *)
Let palice_symbolic := @dsdp_pismc.palice symbolic_DI (@party_D _ _) id.

(* Bob's program at the same interface. *)
Let pbob_symbolic := @dsdp_pismc.pbob symbolic_DI (@party_D _ _) id.

(* Charlie's program at the same interface. *)
Let pcharlie_symbolic := @dsdp_pismc.pcharlie symbolic_DI (@party_D _ _) id.

(* The three programs at the inputs one sample gives them, in the party order
   the interpreter indexes by. *)
Definition dsdp_procs_symbolic (t : T) : seq (proc (di_data symbolic_DI)) :=
  erase_aprocs
    [aprocs palice_symbolic (Dk_a t : party_id * key_type * msg)
              (V1 t) (U1 t) (U2 t) (U3 t) (R2 t) (R3 t) ;
            pbob_symbolic (Dk_b t : party_id * key_type * msg) (V2 t) ;
            pcharlie_symbolic (Dk_c t : party_id * key_type * msg) (V3 t)].

(* The seed stream each party consumes, its two coin coordinates at that
   sample, in the order its program draws them. *)
Definition dsdp_seeds_symbolic (t : T) : seq (seq (di_data symbolic_DI)) :=
  [:: [:: datum_coin (coin_ra1 t); datum_coin (coin_ra2 t)];
      [:: datum_coin (coin_rb1 t); datum_coin (coin_rb2 t)];
      [:: datum_coin (coin_rc1 t); datum_coin (coin_rc2 t)]].

(* What the eighteen-round run writes for the three parties, newest entry
   first.  Thirteen entries for Alice, six for Bob, five for Charlie. *)
Lemma dsdp_run_traces_symbolicE (t : T) :
  (run_interp 18 (dsdp_procs_symbolic t) (dsdp_seeds_symbolic t)).1.2 =
  [:: [:: datum_plain (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t)
                       - R2 t - R3 t + U1 t * V1 t);
          datum_enc Alice (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t));
          datum_coin (coin_ra2 t); datum_coin (coin_ra1 t);
          datum_enc Charlie (V3 t); datum_enc Bob (V2 t);
          datum_plain (R3 t); datum_plain (R2 t); datum_plain (U3 t);
          datum_plain (U2 t); datum_plain (U1 t); datum_plain (V1 t);
          datum_priv_key (Dk_a t : party_id * key_type * msg)];
      [:: datum_coin (coin_rb2 t);
          datum_enc Charlie (V3 t * U3 t + R3 t);
          datum_enc Bob (V2 t * U2 t + R2 t);
          datum_coin (coin_rb1 t); datum_plain (V2 t);
          datum_priv_key (Dk_b t : party_id * key_type * msg)];
      [:: datum_coin (coin_rc2 t);
          datum_enc Charlie (V3 t * U3 t + R3 t + (V2 t * U2 t + R2 t));
          datum_coin (coin_rc1 t); datum_plain (V3 t);
          datum_priv_key (Dk_c t : party_id * key_type * msg)]].
Proof.
(* [reflexivity] alone fails: a private key reaches [party_D] through the
   [tuple_of_party_key] coercion, a match on a one-constructor Variant that
   stays stuck until the key is opened, and that blocks the decryptions. *)
rewrite /dsdp_procs_symbolic /dsdp_seeds_symbolic
        /palice_symbolic /pbob_symbolic /pcharlie_symbolic.
by case: (Dk_a t) => ka; case: (Dk_b t) => kb; case: (Dk_c t) => kc.
Qed.

(* Eighteen rounds bound every party's trace of the symbolic run.  The bound
   packages a trace as a bounded sequence. *)
Lemma symbolic_trace_size (i : party_id) (t : T) :
  (size (nth [::] (run_interp 18 (dsdp_procs_symbolic t)
                     (dsdp_seeds_symbolic t)).1.2 n( i )) <= 18)%N.
Proof. exact: size_traces_nth. Qed.

(* The trace party i sees in the symbolic run, as a random variable.  The
   corrupted-relay bounds are re-read at this observation. *)
Definition symbolic_trace_of_run (i : party_id) :
    {RV P -> 18.-bseq symbolic_datum} :=
  fun t => Bseq (symbolic_trace_size i t).

(* Bob's trace at the symbolic cipher model, as a random observation.  It is
   the object the executed protocol hands a corrupted Bob. *)
Definition BobTrace := symbolic_trace_of_run Bob.

(* Charlie's trace at the symbolic cipher model as a random observation. *)
Definition CharlieTrace := symbolic_trace_of_run Charlie.

(* A coin drawn at one sample of the space.  The readers below return it on
   the branch no trace of the run reaches. *)
Let coin0 : coinT I := coin_rb1 (enum_val (Ordinal (fdist_card_neq0 P))).

(* The value type BobView takes, which the two readers below encode and
   decode. *)
Local Notation bob_viewT :=
  (Bob.-key Dec msg * msg * Charlie.-enc msg * Bob.-enc msg *
   coinT I * coinT I)%type.

(* The value type CharlieView takes, one ciphertext shorter than Bob's. *)
Local Notation charlie_viewT :=
  (Charlie.-key Dec msg * msg * Charlie.-enc msg *
   coinT I * coinT I)%type.

(* Bob's six trace entries built from his view, newest first.  Second coin,
   the two received ciphertexts, first coin, input, key. *)
Definition bob_trace_of_view (w : bob_viewT) : 18.-bseq symbolic_datum :=
  [bseq datum_coin w.2;
        datum_cipher (w.1.1.1.2 : party_id * msg);
        datum_cipher (w.1.1.2 : party_id * msg);
        datum_coin w.1.2;
        datum_plain w.1.1.1.1.2;
        datum_priv_key (w.1.1.1.1.1 : party_id * key_type * msg)].

(* Bob's view read back off a trace of that shape, which is what makes the
   recoding lose nothing. *)
Definition bob_view_of_trace (s : 18.-bseq symbolic_datum) : bob_viewT :=
  match val s with
  | [:: inr (inr c2); inl (inl (inr (_, x))); inl (inl (inr (_, y)));
        inr (inr c1); inl (inl (inl v)); inl (inr (_, _, k))] =>
      (KeyOf Bob Dec k, v, E' Charlie x, E' Bob y, c1, c2)
  | _ => (KeyOf Bob Dec 0, 0, E' Charlie 0, E' Bob 0, coin0, coin0)
  end.

(* The encoding of Bob's view into his trace is left-invertible, so the two
   observations carry the same information. *)
Lemma bob_trace_of_viewK : cancel bob_trace_of_view bob_view_of_trace.
Proof.
(* The key and the two ciphertexts are one-constructor Variants, so the
   reader's match stays stuck until they are opened. *)
by case=> [[[[[[k] v2] [x]] [y]] c1] c2].
Qed.

(* The trace the interpreter produces for Bob is a deterministic image of the
   view dsdp_relay_secrecy.v bounds. *)
Lemma bob_trace_of_viewE : BobTrace = bob_trace_of_view `o BobView.
Proof.
apply: funext => t; apply/val_inj; rewrite /BobTrace /symbolic_trace_of_run.
by move: (symbolic_trace_size Bob t); rewrite dsdp_run_traces_symbolicE.
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
    18.-bseq symbolic_datum :=
  [bseq datum_coin w.2;
        datum_cipher (w.1.1.2 : party_id * msg);
        datum_coin w.1.2;
        datum_plain w.1.1.1.2;
        datum_priv_key (w.1.1.1.1 : party_id * key_type * msg)].

(* Charlie's view read back off a trace of that shape. *)
Definition charlie_view_of_trace (s : 18.-bseq symbolic_datum) :
    charlie_viewT :=
  match val s with
  | [:: inr (inr c2); inl (inl (inr (_, x))); inr (inr c1);
        inl (inl (inl v)); inl (inr (_, _, k))] =>
      (KeyOf Charlie Dec k, v, E' Charlie x, c1, c2)
  | _ => (KeyOf Charlie Dec 0, 0, E' Charlie 0, coin0, coin0)
  end.

(* The encoding of Charlie's view into his trace is left-invertible. *)
Lemma charlie_trace_of_viewK :
  cancel charlie_trace_of_view charlie_view_of_trace.
Proof. by case=> [[[[[k] v3] [x]] c1] c2]. Qed.

(* The trace the interpreter produces for Charlie is a deterministic image of
   the view dsdp_relay_secrecy.v bounds. *)
Lemma charlie_trace_of_viewE :
  CharlieTrace = charlie_trace_of_view `o CharlieView.
Proof.
apply: funext => t; apply/val_inj.
rewrite /CharlieTrace /symbolic_trace_of_run.
by move: (symbolic_trace_size Charlie t); rewrite dsdp_run_traces_symbolicE.
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
