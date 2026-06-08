(* dsdp_symbolic.v — symbolic instance of the standalone DSDP_Interface, and
   the DERIVED homomorphic-combine terms of corrupted Alice.

   Phase-2b of the symbolic-to-game observer derivation (design doc:
   dumas2017dual/notes/20260604-symbolic-to-game-derivation-design.md).

   This file RUNS the DI-parameterized protocol procs [palice] of dsdp_pismc.v
   at a NON-cryptographic symbolic instance of [DSDP_Interface] whose
   message/cipher carriers are the deep-embedded [he_term] algebra of
   dsdp_game_code.v, and reads off the homomorphic-assembly [he_term]s that
   corrupted Alice sends back.  These DERIVED terms ([dsdp_observed_combines])
   are what dsdp_game_symbolic.v feeds to its [AO_combine] observation steps,
   replacing the hand-written terms.

   The [he_term] algebra is the REAL one from dsdp_game_code.v (imported), so
   the symbolic sends and dsdp_game_symbolic.dsdp_alice_obs share one type;
   downstream [game_of_trace]/[denote_he] lower these terms to the SSProve game
   with no translation. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_pismc.
Require Import dsdp_game_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Symbolic data carrier and Recv combinators.                                *)
(* ========================================================================== *)

(* symbolic_data — the unified data carrier the symbolic interface uses for
   [di_data]; mirrors the standard sum-carrier's four injection slots, but
   payloads are [he_term]s (plain/cipher) and nat key ids (priv/pub). *)
Inductive symbolic_data :=
| SD_plain (_ : he_term) | SD_cipher (_ : he_term)
| SD_priv_key (_ : nat)  | SD_pub_key (_ : nat).

(* symbolic_get_cipher — recover the ciphertext he_term from a data carrier;
   None on the non-cipher injections (matches std_get_cipher's shape). *)
Definition symbolic_get_cipher (d : symbolic_data) : option he_term :=
  if d is SD_cipher c then Some c else None.

(* symbolic_Recv_enc — recv-for-HE: extract the ciphertext he_term and continue
   with it (the symbolic image of std_Recv_enc). *)
Definition symbolic_Recv_enc (frm : nat) (f : he_term -> proc symbolic_data)
  : proc symbolic_data :=
  Recv frm (fun d => match symbolic_get_cipher d with
                     | Some c => f c | None => Fail end).

(* symbolic_Recv_dec — recv-and-decrypt: extract the ciphertext he_term and
   continue with its symbolic decryption [HE_dec sk c] (the symbolic image of
   std_Recv_dec, where the scheme [dec] becomes the syntactic HE_dec node). *)
Definition symbolic_Recv_dec (frm : nat) (sk : nat)
    (f : he_term -> proc symbolic_data) : proc symbolic_data :=
  Recv frm (fun d => match symbolic_get_cipher d with
                     | Some c => f (HE_dec sk c) | None => Fail end).

(* Symbolic_DSDP_Interface — the parameter-free symbolic instance of the
   standalone DSDP_Interface. Carriers: messages and ciphertexts are [he_term],
   randomness/keys are nat ids. Operations are the syntactic he_term
   constructors; the Recv combinators are the symbolic_Recv_* above. *)
Definition Symbolic_DSDP_Interface : DSDP_Interface :=
  {| di_msgT := he_term ; di_cipherT := he_term ; di_randT := nat ;
     di_priv_keyT := nat ; di_pub_keyT := nat ; di_data := symbolic_data ;
     di_data_of_plain := SD_plain ; di_data_of_cipher := SD_cipher ;
     di_data_of_priv_key := SD_priv_key ; di_data_of_pub_key := SD_pub_key ;
     di_get_cipher := symbolic_get_cipher ;
     di_encrypt := (fun pk m r => HE_enc pk m r) ;
     di_emul := HE_emul ; di_epow := HE_epow ;
     di_add := HE_add ; di_sub := HE_sub ; di_mul := HE_mul ;
     di_Recv_dec := symbolic_Recv_dec ; di_Recv_enc := symbolic_Recv_enc |}.

(* ========================================================================== *)
(* Symbolic decoder and key map fed to the DI-parameterized procs.            *)
(* ========================================================================== *)

(* decode_sym — the per-instance recv-decoder [palice] takes alongside [DI];
   the standard instance supplies the scheme [dec], the symbolic one wraps the
   ciphertext in a syntactic [HE_dec sk c]. Never reached on Alice's send path
   (her only [Recv_dec] is the final g, after both sends). *)
Definition decode_sym (sk : nat) (c : he_term) : option he_term :=
  Some (HE_dec sk c).

(* ek_sym — the symbolic public-key map: a party maps to its nat id (Alice 0,
   Bob 1, Charlie 2). Composed with the procs' [nat_to_party_id] coercion this
   round-trips the literal party tag (party_id_to_nat (nat_to_party_id 1) = 1),
   so the HE_enc party tags in the sends are 1 (Bob) and 2 (Charlie), matching
   dsdp_game_symbolic.dsdp_alice_obs. *)
Definition ek_sym (p : party_id) : nat := party_id_to_nat p.

(* ========================================================================== *)
(* Sent-payload projection (local copy of dsdp_trace_bridge.sent_payloads).    *)
(* ========================================================================== *)

(* sent_payloads — deterministic "what does this process send on the wire?"
   Six-arm match over [proc]: Init/Ret/Finish/Fail contribute nothing; Send
   prepends its payload; Recv consumes one response from [resp] (received data,
   head-first in call order) and recurses. This MIRRORS dsdp_trace_bridge.v's
   [sent_payloads] verbatim; it is copied here (rather than imported) because
   dsdp_trace_bridge.v drags in the full SSProve stack, which this light
   derivation file does not need. *)
Fixpoint sent_payloads {dT} (p : @smc_interpreter.proc dT)
    (resp : seq dT) : seq dT :=
  match p with
  | smc_interpreter.Init _ k => sent_payloads k resp
  | smc_interpreter.Send _ d k => d :: sent_payloads k resp
  | smc_interpreter.Recv _ f =>
      match resp with
      | [::] => [::]
      | r :: rs => sent_payloads (f r) rs
      end
  | smc_interpreter.Ret _ => [::]
  | smc_interpreter.Finish => [::]
  | smc_interpreter.Fail => [::]
  end.

(* ========================================================================== *)
(* The symbolic run of corrupted Alice and her DERIVED combine terms.         *)
(* ========================================================================== *)

(* palice_sym — Alice's DI-parameterized program instantiated at the symbolic
   interface and erased to a plain [proc]. Inputs (names follow
   dsdp_game_symbolic.dsdp_alice_obs's canonical map): dk = key id 0; the two
   inputs Alice does not leak (v1 u1) get unused names 16/17; her four leaked
   scalars u2 u3 r2 r3 = HE_var 12..15; the two mask randomness slots ra1 ra2 =
   20, 21.  Running this is the DERIVATION: the combine terms below come out of
   it, they are not hand-written. *)
Definition palice_sym : proc symbolic_data :=
  smc_session_types.erase
    (@palice Symbolic_DSDP_Interface decode_sym ek_sym
       0 (HE_var 16) (HE_var 17) (HE_var 12) (HE_var 13) (HE_var 14) (HE_var 15)
       20 21).

(* dsdp_recv_responses — the response stream Alice receives, in call order, as
   NAMED PLACEHOLDERS: the ciphertext from Bob is the opaque name [HE_var 30]
   (c2), Charlie's is [HE_var 31] (c3), and the final value Charlie returns is
   [HE_var 50] (consumed by Alice's last Recv_dec, never re-sent).  Feeding the
   received ciphertexts as names (rather than their actual Enc terms) is what
   makes Alice's computed [Send] payloads reference c2/c3 BY NAME 30/31, exactly
   as dsdp_game_symbolic.dsdp_alice_obs does after its AO_recv_hop steps bind
   the received ciphertexts to 30/31. *)
Definition dsdp_recv_responses : seq symbolic_data :=
  [:: SD_cipher (HE_var 30) ; SD_cipher (HE_var 31) ; SD_cipher (HE_var 50) ].

(* dsdp_observed_combines — the homomorphic-assembly [he_term]s corrupted Alice
   sends back to Bob, DERIVED by symbolically running [palice] against the
   named-placeholder recv stream and projecting the ciphertext payloads.  By
   [dsdp_observed_combines_eq] this computes to
     [:: HE_emul (HE_epow (HE_var 30) (HE_var 12)) (HE_enc 1 (HE_var 14) 20)
       ; HE_emul (HE_epow (HE_var 31) (HE_var 13)) (HE_enc 2 (HE_var 15) 21) ]
   i.e. a1 = Emul (Epow c2 u2) (Enc_Bob r2 ra1), a2 = Emul (Epow c3 u3)
   (Enc_Charlie r3 ra2) — the very terms dsdp_alice_obs feeds to its two
   AO_combine steps, now obtained from the program rather than hand-written. *)
Definition dsdp_observed_combines : seq he_term :=
  pmap symbolic_get_cipher (sent_payloads palice_sym dsdp_recv_responses).

(* a1_observed / a2_observed — the two expected homomorphic assemblies, named
   for use as the validation target of the derivation. *)
Definition a1_observed : he_term :=
  HE_emul (HE_epow (HE_var 30) (HE_var 12)) (HE_enc 1 (HE_var 14) 20).
Definition a2_observed : he_term :=
  HE_emul (HE_epow (HE_var 31) (HE_var 13)) (HE_enc 2 (HE_var 15) 21).

(* dsdp_observed_combines_eq — THE DERIVATION RESULT. The Send payloads Alice's
   [palice] program emits at the symbolic interface ARE exactly a1, a2, by full
   computation ([erase] + [sent_payloads] + [pmap] reduce on the closed he_terms
   and the symbolic ops). This is genuinely derived: a1/a2 fall out of running
   [palice], they are not a hand-written constant on the right-hand side feeding
   itself. *)
Lemma dsdp_observed_combines_eq :
  dsdp_observed_combines = [:: a1_observed ; a2_observed ].
Proof. by []. Qed.

(* ========================================================================== *)
(* The senders whose first sends are the ciphertexts Alice receives.          *)
(* ========================================================================== *)

(* pbob_sym — Bob's DI-parameterized program instantiated at the symbolic
   interface and erased to a plain [proc]. Its head send is the structured
   secret-bearing ciphertext corrupted Alice receives as her first hop: it
   encrypts Bob's secret [HE_var 10] (= v2). The randomness slots 22/23 sit
   inside the hop ciphertext and are never read by the hop, so they take unused
   names. *)
Definition pbob_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pbob Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 10) 22 23).

(* pcharlie_sym — Charlie's program at the symbolic interface, erased to a plain
   [proc] (the sibling of [pbob_sym]). Its head send encrypts Charlie's secret
   [HE_var 11] (= v3), corrupted Alice's second hop; randomness slots 24/25 sit
   inside the ciphertext and take unused names. *)
Definition pcharlie_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pcharlie Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 11) 24 25).

(* first_send — read a party's head [Send] payload, walking past [Init]; None
   if the program reaches a Recv/Ret/Finish/Fail before sending. The sender
   programs above emit their hop ciphertext as their first send. *)
Fixpoint first_send (p : proc symbolic_data) : option symbolic_data :=
  match p with
  | smc_interpreter.Init _ k => first_send k
  | smc_interpreter.Send _ d _ => Some d
  | _ => None
  end.

(* dsdp_received_hop_ciphertexts — the hop-reception stream fed to the
   corrupted-view walk: the head sends of Bob and Charlie, in call order. This
   is DERIVED from the sender programs (via [first_send]), not hand-written; by
   [dsdp_received_hop_ciphertexts_eq] it computes to the two structured Enc
   ciphertexts Alice receives. *)
Definition dsdp_received_hop_ciphertexts : seq symbolic_data :=
  pmap first_send [:: pbob_sym ; pcharlie_sym].

(* dsdp_received_hop_ciphertexts_eq — THE DERIVATION RESULT for the hop stream.
   The head [Send] payloads Bob's and Charlie's programs emit at the symbolic
   interface ARE exactly the structured secret-bearing ciphertexts
   [HE_enc 1 (HE_var 10) 22] (Bob) and [HE_enc 2 (HE_var 11) 24] (Charlie), by
   full computation. The party tags 1/2 come from [ek_sym] round-tripping the
   party ids; the secrets [HE_var 10]/[HE_var 11] are v2/v3.
   Naming: the [_eq] suffix renders MathComp's equation [E] suffix in this file's
   all-snake_case style, matching the sibling [dsdp_observed_combines_eq]. *)
Lemma dsdp_received_hop_ciphertexts_eq :
  dsdp_received_hop_ciphertexts
  = [:: SD_cipher (HE_enc 1 (HE_var 10) 22)
      ; SD_cipher (HE_enc 2 (HE_var 11) 24) ].
Proof. by []. Qed.
