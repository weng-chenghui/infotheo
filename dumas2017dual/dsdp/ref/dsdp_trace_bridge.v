(** dsdp_trace_bridge.v — Tier-1 concrete piSMC<->SSProve trace bridge for
    DSDP-Alice.

    Per the dated memo
    [dumas2017dual/notes/20260526-pismc-ssprove-trace-bridge-plan.md] §6, this
    file makes the operational faithfulness statement of the
    piSMC-to-SSProve translator (smc/pismc_to_ssprove.v) concrete on the DSDP
    side, at the idealized AHE instance where [enc pk m r = m].  Two trace
    derivations are forced to compute through reflexivity:

    1. SSProve-side: [Run sampler (code_link (dsdp_palice_code …)
       (pack dsdp_recv_oracle_preloaded)) seed] reduces by [Run_aux] to the
       Some-wrapped list of ciphertexts Alice sends.

    2. piSMC-side:  [sent_payloads (erase (palice …)) recvs] computes to the
       same list (after the [data -> cipher] extractor).

    Together they realize §6's "minimum rigorous bridge" — operational
    faithfulness in the sense of "the SSProve code Alice runs emits exactly
    the ciphertexts the piSMC interpreter says she sends".  This DOES NOT
    discharge [Hypothesis game_real_eq_pismc] at
    [dsdp_security_indcpa_pismc.v:472], which lives in the denotational
    [Pr]/[≈₀] world and is independent of the [Run] tape interpreter.  See
    the memo §3 for the two-tier framing.

    Scope.  This file deliberately stays Tier 1 concrete: no [≈₀], no
    [eq_rel_perf_ind_eq], no [pkg_advantage].  Just [Run] equalities by
    [reflexivity], the exact pattern of SSProve's
    [examples/Executor.v:255-260] (interpretation_test1) and of
    [du2002/spp_proof.v:106,120] (smc_scalar_product_ok).
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition pkg_interpreter.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import ssr_ext smc_interpreter smc_session_types pismc_to_ssprove.
Require Import homomorphic_encryption idealized_ahe enc_dec ahe_enc.
Require Import dsdp_interface dsdp_session_types dsdp_pismc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

(******************************************************************************)
(** * Concrete idealized-AHE instantiation for the bridge                     *)
(******************************************************************************)

(* Pick a tiny concrete modulus so the [Run] interpreter can reduce.  Any
   nonzero [p : nat] would do; we pick [p = 5] because ['F_5] is small enough
   for [Eval compute] yet not [0] (which would trigger the [chFin 0] sampler
   guard in pkg_interpreter.v:161-164).  Primality is NOT required by
   MathComp's ['F_p] (it routes through [pdiv]), so [p = 5] is just a
   convenient inhabitant. *)
Local Notation p := 5.

(** msgT — the underlying message carrier for the idealized AHE.  ['F_5]
    inherits [finComNzRingType] from MathComp unconditionally, which is
    exactly what [Idealized_HETypes] needs.  Used as both the plaintext
    and ciphertext type at the idealized instance. *)
Definition msgT : finComNzRingType := [the finComNzRingType of 'F_p].

(** AHE — the concrete idealized AHEnc scheme.  Mirrors
    [dsdp_security_indcpa_concrete.v:556] but pinned to the literal modulus
    [5] so all carriers are first-order ['F_5] values. *)
Definition AHE : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msgT)
    (@AHEnc.Class (Idealized_HETypes msgT)
      (@Idealized_isEncDec msgT)
      (@Idealized_isAHEnc msgT)).

(** t_cipher — SSProve [choice_type] carrier for the ciphertext type.
    Set to ['fin #|msgT|] so the [chFin]-handled [ch_nat]/[nat_ch] round
    trip applies (pkg_interpreter.v:60-109).  Mirrors the [Module Concrete]
    pattern at [dsdp_security_indcpa_concrete.v:168] specialised at the
    idealized AHE. *)
Definition t_cipher : choice_type := chFin #|msgT|.

(* Carrier coherence: [cipher AHE] reduces to [msgT] for the idealized
   scheme (Idealized_HETypes sets cipher := msgT).  This makes
   [enum_rank] / [enum_val] well-typed at both ends. *)
Lemma cipher_AHE_eq : cipher AHE = msgT.
Proof. by []. Qed.

(** chcipher_of_cipher — embed an AHE ciphertext into the SSProve
    choice_type layer so it can round-trip through a package oracle. *)
Definition chcipher_of_cipher (c : cipher AHE) : t_cipher :=
  enum_rank (c : msgT).

(** cipher_of_chcipher — inverse of [chcipher_of_cipher].  Uses [enum_val]
    to project the ordinal index back to an element of [msgT]. *)
Definition cipher_of_chcipher (i : t_cipher) : cipher AHE :=
  enum_val i.

Lemma chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher.
Proof. by move=> c; rewrite /chcipher_of_cipher /cipher_of_chcipher enum_rankK. Qed.

(******************************************************************************)
(** * piSMC-side input wiring                                                  *)
(******************************************************************************)

(* Pick a single inhabitant on the key side so the [Init #dk] action in
   [palice] is fed a concrete value.  At the idealized AHE all key types
   reduce to ['F_5], so [0%R : 'F_5] is canonical. *)
Definition dk_witness : priv_key AHE := 0%R.

(* Same convention as [dsdp_security_indcpa_pismc.v:238] for the public-key
   per party — the idealized AHE makes [pkey_of_party] free of cryptographic
   meaning; both [Bob] and [Charlie] map to [0%R]. *)
Definition pkey_of_party (_ : party_id) : pub_key AHE := 0%R.

(* Small literal plaintext / randomness inputs.  Pinned so [Run] reduces
   under [Eval compute] / [reflexivity].  Same convention as
   [du2002/spp_proof.v:106,120]. *)
Definition v1_in : plain AHE := 1%R.
Definition u1_in : plain AHE := 0%R.
Definition u2_in : plain AHE := 1%R.
Definition u3_in : plain AHE := 1%R.
Definition r2_in : plain AHE := 0%R.
Definition r3_in : plain AHE := 0%R.
Definition ra1_in : rand AHE := 1%R.
Definition ra2_in : rand AHE := 1%R.

(* Bob's and Charlie's first ciphertexts.  In the idealized AHE
   [enc pk m r = m] so [c2 = v2] and [c3 = v3].  We pick the same literal
   shape Alice would receive from Bob/Charlie heads in the W2 chain. *)
Definition v2_recv : plain AHE := 2%R.
Definition v3_recv : plain AHE := 3%R.

Definition c2_in : cipher AHE := enc (pkey_of_party Bob) v2_recv 0%R.
Definition c3_in : cipher AHE := enc (pkey_of_party Charlie) v3_recv 0%R.

(******************************************************************************)
(** * T1A.1: piSMC-side sent-payload projection                                *)
(******************************************************************************)

(** sent_payloads — the deterministic Gallina shadow of "what does this
    process send on the wire?".  Six-arm match over [proc]:
    [Init] / [Ret] / [Finish] / [Fail] contribute nothing; [Send] prepends
    its payload; [Recv] consumes one response from [resp] (a stream of
    received [data] values, head-first in call order) and recurses on the
    continuation.

    Why: the SSProve translator [code_of_proc] produces a [chList t_cipher]
    that head-firstly accumulates Send payloads (Design Commitment 3 of
    [pismc_to_ssprove.v]).  The corresponding Gallina projection at the
    piSMC level is what we compare against. *)
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

(******************************************************************************)
(** * T1A.2: preloaded recv oracle (no [get], no [#put])                       *)
(******************************************************************************)

(* Oracle identifiers.  Match the ids used by [dsdp_palice_code]'s
   translation (see [dsdp_security_indcpa_pismc.v:110-111]) so we can
   directly [code_link] against [palice] translated under the same ids. *)
Definition id_recv_enc_pismc : nat := 3%N.
Definition id_recv_dec_pismc : nat := 4%N.

(* The [code_of_proc] translation only ever issues [code_of_recv_enc]
   calls (the [DRecv_dec] case folds its decoder into the continuation
   before [erase], so the resulting [proc] sees only [Recv]).  This is
   verified in [pismc_to_ssprove.v:235-252]: the [Recv] arm uniformly
   dispatches to [code_of_recv_enc].

   Hence we only need to serve [id_recv_enc_pismc].  We give
   [id_recv_dec_pismc] a benign fallback so the oracle still exports
   [recv_iface] verbatim. *)

(* The piSMC data carrier matches the wrap [std_e] uses (see
   [dsdp_interface.v:126-128]). *)
Definition data_dsdp : Type := di_data (Standard_DSDP_Interface AHE).

Definition dsdp_data_to_cipher (d : data_dsdp) : t_cipher :=
  match d with
  | inl (inl (inr c)) => chcipher_of_cipher c
  | _ => chcipher_of_cipher (0%R : cipher AHE)
  end.

Definition dsdp_cipher_to_data (c : t_cipher) : data_dsdp :=
  inl (inl (inr (cipher_of_chcipher c))).

(* Pre-encoded ciphertexts the oracle will hand out, in [t_cipher]
   representation. *)
Definition c2_chc : t_cipher := chcipher_of_cipher c2_in.
Definition c3_chc : t_cipher := chcipher_of_cipher c3_in.

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).

(** dsdp_recv_oracle_preloaded — stateless recv oracle for the trace
    bridge: Bob's and Charlie's ciphertexts are baked in as constants
    rather than loaded from heap cells.  This sidesteps the default-heap
    obstruction that prevents [Run_aux] from reading values written by a
    game body's [#put] steps, making the [Run] computation in
    [alice_run_trace_concrete] reduce unconditionally by [cbn].  Routes
    by source index: [n == bob_idx] returns [c2_chc], otherwise [c3_chc]. *)
Definition dsdp_recv_oracle_preloaded :
  package [interface]
    (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc) :=
  [package emptym ;
    #def #[ id_recv_enc_pismc ] (n : 'nat) : cipher_t
    {
      @ret t_cipher (if n == bob_idx then c2_chc else c3_chc)
    } ;
    #def #[ id_recv_dec_pismc ] (_ : 'nat) : cipher_t
    {
      @ret t_cipher c2_chc
    }
  ].

(******************************************************************************)
(** * T1A.3: SSProve-side Run trace through code_link                          *)
(******************************************************************************)

(** dsdp_palice_code — Alice's piSMC program translated to SSProve [code]
    at the idealized concrete carriers.  Mirrors
    [dsdp_security_indcpa_pismc.v:215] but specialised to our concrete
    instance ([msgT = 'F_5]) so the resulting [code] is closed and
    computes. *)
Definition dsdp_palice_code
    (dk : priv_key AHE)
    (v1 u1 u2 u3 r2 r3 : plain AHE)
    (ra1 ra2 : rand AHE) :
  code emptym
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    emptym
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@palice AHE pkey_of_party dk v1 u1 u2 u3 r2 r3 ra1 ra2).

(* The two ciphertexts Alice actually sends, computed concretely.  These
   are the literal SSProve-side targets the [Run]-trace lemma equals. *)
Definition a1_send : cipher AHE :=
  Emul (Epow c2_in u2_in) (enc (pkey_of_party Bob) r2_in ra1_in).
Definition a2_send : cipher AHE :=
  Emul (Epow c3_in u3_in) (enc (pkey_of_party Charlie) r3_in ra2_in).

(** alice_run_trace_concrete — operational faithfulness witness on the
    SSProve side: for any tape [seed], the [Run] interpreter applied to
    Alice's translated code (linked against the preloaded oracle) returns
    exactly the two ciphertexts Alice emits.  Together with
    [alice_pismc_sends_concrete] it closes the piSMC-to-SSProve trace
    bridge. *)
Lemma alice_run_trace_concrete (seed : nat) :
  Run sampler
      (code_link (dsdp_palice_code dk_witness
                                   v1_in u1_in u2_in u3_in r2_in r3_in
                                   ra1_in ra2_in).(prog)
                 (pack dsdp_recv_oracle_preloaded))
      seed
  = Some [:: chcipher_of_cipher a1_send;
             chcipher_of_cipher a2_send].
Proof.
(* The [unlock] step is required because [coerce_kleisli] is wrapped in
   a lock; the [setm] dispatch ordering depends on
   [id_recv_enc_pismc < id_recv_dec_pismc] reducing to numerals first. *)
by cbn; unfold resolve, coerce_kleisli, coerce_code; unlock;
   rewrite /= !coerceE /= !chcipher_of_cipherK.
Qed.

(******************************************************************************)
(** * T1A.4: piSMC-side sent-payload trace                                     *)
(******************************************************************************)

(* The corresponding piSMC-side input: the recv response stream, in call
   order (Bob first, Charlie second).  These are wrapped via [std_e]
   exactly as [dsdp_cipher_to_data] inverts. *)
Definition recvs_piSMC : seq data_dsdp :=
  [:: dsdp_cipher_to_data c2_chc;
      dsdp_cipher_to_data c3_chc].

(* The two payloads Alice's piSMC program emits, in [data_dsdp] form
   (wrapped via [std_e] of the AHE ciphertext). *)
Definition a1_send_pi : data_dsdp := inl (inl (inr a1_send)).
Definition a2_send_pi : data_dsdp := inl (inl (inr a2_send)).

(** alice_pismc_sends_concrete — operational faithfulness witness on the
    piSMC side: the deterministic [sent_payloads] projection of the erased
    [palice] process, fed Bob's and Charlie's ciphertext responses in call
    order, returns the two-element list of [data_dsdp] values Alice emits
    on the wire.  Counterpart to [alice_run_trace_concrete]; together they
    pin down the trace-level equivalence through [dsdp_data_to_cipher]. *)
Lemma alice_pismc_sends_concrete :
  sent_payloads (smc_session_types.erase
                   (@palice AHE pkey_of_party
                            dk_witness v1_in u1_in u2_in u3_in
                            r2_in r3_in ra1_in ra2_in))
                recvs_piSMC
  = [:: a1_send_pi; a2_send_pi].
Proof.
(* [palice] is a six-action [sproc] over the [DSDP_Interface] sum type;
   [erase] strips the session/fuel indices, leaving a six-arm [proc] over
   [data_dsdp].  [sent_payloads] consumes that tree with the [recvs_piSMC]
   stream and emits the two [std_e]-wrapped ciphertexts.  Modulo
   [chcipher_of_cipherK] (the [data -> cipher] extractor round-trip) and
   the [idealized_*] op definitions, the result is definitionally equal
   to [[:: a1_send_pi; a2_send_pi]]. *)
by rewrite /= !chcipher_of_cipherK.
Qed.

(******************************************************************************)
(** * T1A.5: Tier-1 corollary — the two traces agree under the extractor      *)
(******************************************************************************)

(** alice_trace_eq_concrete — Tier-1 corollary.  The SSProve-side [Run]
    trace equals the piSMC-side [sent_payloads] trace mapped element-wise
    through the [data -> cipher] extractor [dsdp_data_to_cipher].  Closes
    the operational-faithfulness statement of the memo §6. *)
Corollary alice_trace_eq_concrete (seed : nat) :
  Run sampler
      (code_link (dsdp_palice_code dk_witness
                                   v1_in u1_in u2_in u3_in r2_in r3_in
                                   ra1_in ra2_in).(prog)
                 (pack dsdp_recv_oracle_preloaded))
      seed
  = Some (map dsdp_data_to_cipher
              (sent_payloads (smc_session_types.erase
                                (@palice AHE pkey_of_party
                                         dk_witness v1_in u1_in u2_in u3_in
                                         r2_in r3_in ra1_in ra2_in))
                             recvs_piSMC)).
Proof.
by rewrite alice_pismc_sends_concrete alice_run_trace_concrete.
Qed.

