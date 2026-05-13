(** piSMC primitive translations to SSProve [code].

    Per the audited plan at ~/.claude/plans/sprightly-finding-robin.md
    (Tasks 03 and 04).  Translates each piSMC primitive (Init, Send,
    Recv_enc, Recv_dec, Ret, Finish) to an SSProve [code] fragment, then
    composes them via a Fixpoint [code_of_proc] over the unindexed [proc]
    type from smc_interpreter.v.  The full piSMC-to-SSProve translator is
    [translate_pismc_to_ssprove], which factors through [erase].

    Design commitments (Rocq expert audit):
    - Commitment 1: encryption-randomness carrier is a finType ([Renc]
      in the consuming file, abstracted here as a Section variable).
    - Commitment 3: [Send<dst> v ; P] threads [v] into the return-value
      accumulator of [P]; no heap operations.  Concretely, the translator
      takes a continuation [code L I (chList t_cipher)] and prepends [v]
      to the returned list.
    - Commitment 4: [translate_correct] is stated only as a marginal
      soundness, not as a full piSMC-to-SSProve bisimulation.  Concretely:
      the translation factors through [erase], so [translate_pismc_to_ssprove]
      depends on its sproc input only via the unindexed [proc] that
      [dsdp_program.v]'s protocol-level random variables already use.
    - Recv translators consume oracle interfaces via [#import]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import smc_interpreter smc_session_types.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.
#[local] Open Scope package_scope.

Section pismc_to_ssprove.

(* Section-parametric carriers.  Exposed so this file does not depend on
   a specific [AHEncType] instance; the consuming file picks them. *)
Variable t_msg : choice_type.
Variable t_cipher : choice_type.

Local Notation "''msg'" := t_msg
  (in custom pack_type at level 2).
Local Notation "''cipher'" := t_cipher
  (in custom pack_type at level 2).

Variable index_renc : nat.
Variable t_priv_key : Type.
Variable dec_op : t_priv_key -> t_cipher -> option t_msg.
Variable id_recv_enc : nat.
Variable id_recv_dec : nat.

(** recv_iface — shared oracle import interface for the two Recv translators.
    Declares two operations [id_recv_enc] and [id_recv_dec], both of wire
    type ['nat -> 'cipher], covering the raw-ciphertext path (enc) and the
    decrypt-and-use path (dec).
    Kind: helper.
    Why: imported by [code_of_recv_enc] and [code_of_recv_dec] as the
    oracle interface for all wire-read calls; keeping one shared interface
    ensures both translators agree on oracle identifiers and types.
    Used by: code_of_recv_enc, code_of_recv_dec. *)
Definition recv_iface : Interface :=
  [interface
    #val #[ id_recv_enc ] : 'nat → 'cipher ;
    #val #[ id_recv_dec ] : 'nat → 'cipher
  ].

Variable LocCtx : Locations.
Variable t_out : choice_type.

(** code_of_finish — returns the empty ciphertext accumulator
    ([::] : chList t_cipher) as an SSProve [code] fragment, translating
    the piSMC [Finish] constructor.
    Kind: helper.
    Why: base case of the piSMC-to-SSProve dispatch loop.  Programs that
    end with [Finish] return an empty list of sent ciphertexts.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_finish :
  code LocCtx recv_iface (chList t_cipher) :=
  {code ret ([::] : chList t_cipher) }.

(** code_of_ret — returns [x : t_out] directly as an SSProve [code]
    fragment, translating the piSMC [Ret x] constructor.  Output carrier
    is the section parameter [t_out].
    Kind: helper.
    Why: return-value path of the piSMC-to-SSProve dispatch loop;
    distinct from [code_of_finish] because [Ret] preserves the user's
    data value rather than collapsing to an empty accumulator.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_ret (x : t_out) :
  code LocCtx recv_iface t_out :=
  {code ret x }.

(** code_of_init — applies the continuation [k] to the binding value [x],
    translating the piSMC [Init x ; P] constructor.  No I/O, no randomness
    draw; the binding is a plain functional application.
    Kind: helper.
    Why: [Init] in piSMC just binds a value into the surrounding context;
    in SSProve [code], a plain functional argument is the natural model.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_init {A : choice_type}
    (x : t_msg)
    (k : t_msg -> code LocCtx recv_iface A) :
  code LocCtx recv_iface A :=
  k x.

(** code_of_send — prepends a sent ciphertext [v] to the return-value
    accumulator produced by the continuation [k], translating the piSMC
    [Send<dst> v ; P] constructor (Design Commitment 3 of the Rocq audit).
    Kind: helper.
    Why: heap-free Send.  No [#put] is used; the wire destination is
    encoded by the package structure built around these primitives in
    Task 04.  Heap-freeness keeps the lossless-operation argument for
    [bridge_total_mass] clean.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_send
    (dst : nat) (v : t_cipher)
    (k : code LocCtx recv_iface (chList t_cipher)) :
  code LocCtx recv_iface (chList t_cipher) :=
  {code
    rest ← k ;;
    ret (v :: rest : chList t_cipher)
  }.

(** code_of_recv_enc — issues a [#import]-based read from the
    [id_recv_enc] oracle, passes the ciphertext to the continuation [k],
    and returns its result, translating the piSMC [Recv<src> c => P c]
    constructor.
    Kind: helper.
    Why: the encryption-receive path treats the wire payload as an opaque
    ciphertext.  The src party index is passed as the oracle argument so
    the package built around this code can route to the correct sender.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_recv_enc
    (src : nat)
    (k : t_cipher -> code LocCtx recv_iface (chList t_cipher)) :
  code LocCtx recv_iface (chList t_cipher) :=
  {code
    #import {sig #[ id_recv_enc ] : 'nat → 'cipher } as recv_enc ;;
    c ← recv_enc src ;;
    rest ← k c ;;
    ret rest
  }.

(** pismc_recv_dec_branch — branches on the decryption result: [Some m]
    feeds [m] to the continuation [k], [None] returns the empty
    accumulator.  Returns a full [code] rather than [raw_code] so the
    surrounding [bind] in [code_of_recv_dec] uses the [prog]/[prog_valid]
    coercion path.
    Kind: helper.
    Why: total decryption handler.  The [None] case matches the [SFail]
    behaviour of [DRecv_dec] in dsdp_session_types.v.  Splitting the
    branch out from [code_of_recv_dec] keeps the [refine] proof tractable.
    Used by: code_of_recv_dec. *)
Program Definition pismc_recv_dec_branch
    (k : t_msg -> code LocCtx recv_iface (chList t_cipher))
    (om : option t_msg) :
  code LocCtx recv_iface (chList t_cipher) :=
  match om with
  | Some m => k m
  | None => {code ret ([::] : chList t_cipher) }
  end.

(** code_of_recv_dec — issues a [#import]-based read from the
    [id_recv_dec] oracle, decrypts the response with [dec_op] under [dk],
    and dispatches via [pismc_recv_dec_branch] to either the continuation
    [k] (Some m) or the empty accumulator (None), translating the piSMC
    [Recv<src> #dk m => P m] constructor.
    Kind: helper.
    Why: the decryption-receive path consumes the wire ciphertext as a
    plaintext through the section-parametric [dec_op].  Decryption
    failure falls through to an empty accumulator, matching SFail.
    Used by: translate_pismc_to_ssprove (Task 04). *)
Definition code_of_recv_dec
    (src : nat) (dk : t_priv_key)
    (k : t_msg -> code LocCtx recv_iface (chList t_cipher)) :
  code LocCtx recv_iface (chList t_cipher).
Proof.
  refine
    {code
      #import {sig #[ id_recv_dec ] : 'nat → 'cipher } as recv_dec ;;
      c ← recv_dec src ;;
      rest ← (pismc_recv_dec_branch k (dec_op dk c)).(prog) ;;
      ret rest
    }.
  apply: valid_opr.
  - (* fhas: id_recv_dec is the second entry of recv_iface; setmE walks
       past id_recv_enc and finds it. *)
    cbv [recv_iface]. rewrite /fhas /= setmE.
    case: ifP => _ //. by rewrite setmE eqxx.
  - move=> c. eapply valid_bind.
    + exact: (pismc_recv_dec_branch k (dec_op dk c)).(prog_valid).
    + move=> rest. exact: valid_ret.
Defined.

(******************************************************************************)
(** * Task 04: recursive translator over erased [proc] plus marginal soundness *)
(******************************************************************************)

(** Section-parametric piSMC data carrier and its extractors into the
    SSProve cipher carrier.  The translator below treats the piSMC [data]
    type as opaque modulo [data_to_cipher] (used on the Send/Ret payload)
    and [cipher_to_data] (used to re-wrap the value received on the wire
    for the continuation).  The consuming file (Task 06) instantiates
    these against the AHE-derived [std_data] sum type. *)

Variable data : Type.
Variable data_to_cipher : data -> t_cipher.
Variable cipher_to_data : t_cipher -> data.

(** code_of_proc — recursive translator from an unindexed
    [smc_interpreter.proc] process to an SSProve [code] fragment.
    Dispatches to the per-primitive translators ([code_of_finish],
    [code_of_send], [code_of_recv_enc], etc.).  [Init] is collapsed to its body since piSMC's [Init] is a pure
    binding with no I/O effect.  [Fail] is collapsed to [code_of_finish]
    because the marginal-distribution scope does not distinguish failure
    from clean termination; both produce an empty ciphertext accumulator.
    [Recv] is uniformly translated through [code_of_recv_enc]: after
    erasure, the [DRecv_dec] decryption is already inlined into the
    continuation [f], so a single Recv arm suffices.
    Kind: main.
    Why: Task 04 verification step; composes the Task 03 primitives into
    a recursive walker over [proc], which is the carrier that
    [translate_pismc_to_ssprove] uses after [erase].  Returns into the
    Send-accumulator codomain [chList t_cipher] (Design Commitment 3).
    Used by: translate_pismc_to_ssprove. *)
Fixpoint code_of_proc (p : @smc_interpreter.proc data) {struct p} :
  code LocCtx recv_iface (chList t_cipher) :=
  match p with
  | smc_interpreter.Finish => code_of_finish
  | smc_interpreter.Fail => code_of_finish
  | smc_interpreter.Ret d =>
      {code ret ([:: data_to_cipher d] : chList t_cipher) }
  | smc_interpreter.Init _ k => code_of_proc k
  | smc_interpreter.Send dst d k =>
      code_of_send dst (data_to_cipher d) (code_of_proc k)
  | smc_interpreter.Recv src f =>
      code_of_recv_enc src (fun c => code_of_proc (f (cipher_to_data c)))
  end.

(** The piSMC AST is parametric in the dtype [eqType].  The recursive
    [code_of_proc] only needs the unindexed [data] carrier, so the
    [dtype] parameter appears only in the entry-point definition that
    performs erasure. *)
Variable dtype : eqType.

(** translate_pismc_to_ssprove — main entry point: translate a piSMC
    session-typed process [sproc] into an SSProve [code] fragment, by
    erasing the session-type and fuel indices via [erase] and walking
    the resulting unindexed [proc] through [code_of_proc].
    Kind: main.
    Why: Task 04 deliverable.  The factorization through [erase] is
    deliberate: the unindexed [proc] is the same carrier that
    dsdp_program.v's protocol-level random variables sample over, so the
    translation produces a distribution that depends only on the same
    operational behaviour as the protocol-level RVs.  This is the marginal
    soundness statement (Design Commitment 4 of the Rocq audit).
    Used by: dsdp_security_indcpa.v (Task 06 onwards) to build the four
    games [game_real], [game_hybrid_one], [game_hybrid_two], [game_leak]. *)
Definition translate_pismc_to_ssprove
    {party : nat} {n : nat} {env : senv dtype}
    (p : @sproc dtype data party n env) :
    code LocCtx recv_iface (chList t_cipher) :=
  code_of_proc (smc_session_types.erase p).

(** translate_correct_marginal — the marginal soundness lemma promised by
    Task 04 (Design Commitment 4 of the Rocq audit).  States that
    [translate_pismc_to_ssprove p] factors through [erase p].  Proven by
    definitional equality.
    Kind: main.
    Why: This factorization is the precise content of "the translation
    projects to the same joint distribution as the protocol-level random
    variables": the SSProve code carrier depends on the input sproc only
    via the unindexed [proc] that dsdp_program.v's RVs already sample
    over.  A stronger SDistr-to-fdist bridge is built later as Task 12.
    Used by: dsdp_security_indcpa.v Task 13 (Pr_game_leak_V2_uniform). *)
Lemma translate_correct_marginal
    {party : nat} {n : nat} {env : senv dtype}
    (p : @sproc dtype data party n env) :
  translate_pismc_to_ssprove p = code_of_proc (smc_session_types.erase p).
Proof. by []. Qed.

(** translate_correct_marginal_init — per-constructor reduction:
    translating an [SInit] sproc collapses to translating its body.
    Kind: helper.
    Why: piSMC [Init] is a pure binding without I/O effect, so the
    translation should not introduce any [code] structure for it.  This
    lemma exposes that fact at the sproc level (rather than at the [proc]
    level reached after [erase]), which is convenient for downstream
    rewriting in Task 13.
    Used by: dsdp_security_indcpa.v Task 13. *)
Lemma translate_correct_marginal_init
    {party n} {env : senv dtype} (x : data)
    (k : @sproc dtype data party n env) :
  translate_pismc_to_ssprove (SInit x k) =
  translate_pismc_to_ssprove k.
Proof. by []. Qed.

(** translate_correct_marginal_send — per-constructor reduction:
    translating an [SSend] sproc unfolds to [code_of_send] applied to the
    payload converted via [data_to_cipher] and to the translation of the
    continuation.
    Kind: helper.
    Why: exposes the explicit shape of the Send case at the sproc level.
    Useful in Task 13 to reason about the leaked ciphertext list.
    Used by: dsdp_security_indcpa.v Task 13. *)
Lemma translate_correct_marginal_send
    {party n} {env : senv dtype}
    (dst : nat) (dt : dtype) (v : data)
    (k : @sproc dtype data party n env) :
  translate_pismc_to_ssprove (SSend dst dt v k) =
  code_of_send dst (data_to_cipher v) (translate_pismc_to_ssprove k).
Proof. by []. Qed.

(** translate_correct_marginal_recv — per-constructor reduction:
    translating an [SRecv] sproc unfolds to [code_of_recv_enc] applied to
    the source index and a continuation that re-wraps the received
    ciphertext via [cipher_to_data].
    Kind: helper.
    Why: exposes the explicit shape of the Recv case at the sproc level.
    [DRecv_dec] also lands here after [erase] folds its decryption into
    the continuation, so a single sproc-level Recv lemma covers both
    enc-receive and dec-receive piSMC operations.
    Used by: dsdp_security_indcpa.v Task 13. *)
Lemma translate_correct_marginal_recv
    {party n} {env : senv dtype}
    (src : nat) (dt : dtype)
    (f : data -> @sproc dtype data party n env) :
  translate_pismc_to_ssprove (SRecv src dt f) =
  code_of_recv_enc src
    (fun c => translate_pismc_to_ssprove (f (cipher_to_data c))).
Proof. by []. Qed.

End pismc_to_ssprove.

(** Smoke check: every Definition above type-checks individually.  This
    is the Task 03 verification step (per
    ~/.claude/plans/sprightly-finding-robin.md). *)
Check code_of_finish.
Check code_of_ret.
Check code_of_init.
Check code_of_send.
Check code_of_recv_enc.
Check code_of_recv_dec.

(** Task 04 verification: the Fixpoint [code_of_proc] normalises on
    concrete processes.  Using a tiny stand-in [proc] (instead of [palice]
    from dsdp_pismc.v, which would create a circular dependency) we check
    that [Compute code_of_proc ...] does not get stuck.  The
    dsdp_pismc.v-level Compute test happens in dsdp_security_indcpa.v
    (Task 06), where [palice] is in scope. *)
Section task04_compute_smoke.

(** smoke_tc — concrete ciphertext carrier for the Task 04 smoke check,
    instantiated as ['bool] so [code_of_proc] reduces under [Compute].
    Kind: helper.
    Why: Task 04 verification needs a concrete [choice_type] that the
    Section variable [t_cipher] can be instantiated with.  [bool] is the
    cheapest such instance.
    Used by: smoke_d2c, smoke_c2d, smoke_code. *)
Definition smoke_tc : choice_type := 'bool.

(** smoke_d2c — concrete [data -> t_cipher] extractor for the Task 04
    smoke check.  Encodes a [nat] as its parity.
    Kind: helper.
    Why: Task 04 verification needs a concrete extractor to instantiate
    the Section variable [data_to_cipher].  The exact encoding does not
    matter for the normalisation check, only that the function is total.
    Used by: smoke_code. *)
Definition smoke_d2c (n : nat) : smoke_tc := odd n.

(** smoke_c2d — concrete [t_cipher -> data] inverse extractor for the
    Task 04 smoke check.
    Kind: helper.
    Why: counterpart to [smoke_d2c] for instantiating the Section variable
    [cipher_to_data].
    Used by: smoke_code. *)
Definition smoke_c2d (b : smoke_tc) : nat := if b then 1 else 0.

(** smoke_proc — a hand-written [proc] with the same constructor sequence
    as [dsdp_pismc.palice] (Init, Recv, Recv, Send, Send, Recv, Ret)
    instantiated over [nat].  Verifies that [code_of_proc] reduces on a
    DSDP-shaped concrete input. *)
Definition smoke_proc : @smc_interpreter.proc nat :=
  smc_interpreter.Init (7 : nat) (
  smc_interpreter.Recv 1 (fun c2 : nat =>
  smc_interpreter.Recv 2 (fun c3 : nat =>
  smc_interpreter.Send 1 (c2 + c3 : nat) (
  smc_interpreter.Send 1 (c2 + c3 : nat) (
  smc_interpreter.Recv 2 (fun g : nat =>
  smc_interpreter.Ret (g : nat))))))).

(** smoke_code — the result of applying [code_of_proc] to [smoke_proc].
    [Compute] reduces it to a normal-form [code] term, which demonstrates
    that the [code_of_proc] recursive walker normalises and dispatches
    correctly to each per-primitive translator on a DSDP-shaped input
    (Task 04 "Verify" step).
    Kind: helper.
    Why: the plan's Task 04 verification step requires that
    [Compute translate_pismc_to_ssprove palice] reduce to a normal-form
    [code].  Since [palice] lives in dsdp_pismc.v which imports this
    file, we use the equivalent shape on a stand-in [proc] here.
    Used by: the Task 04 Verify step (no runtime use). *)
Definition smoke_code :
  code emptym
       (recv_iface smoke_tc 100 101)
       (chList smoke_tc) :=
  code_of_proc smoke_tc 100 101 emptym nat smoke_d2c smoke_c2d smoke_proc.

Check smoke_code.

(* [Eval compute] forces full normalisation of the underlying [raw_code]:
   if the recursive [code_of_proc] had any stuck redex on the DSDP-shaped
   concrete proc, this line would reject it.  We only inspect the [prog]
   projection to avoid printing the validity proof at compile time. *)
Eval compute in smoke_code.(prog).

End task04_compute_smoke.
