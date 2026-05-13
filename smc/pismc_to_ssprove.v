(** piSMC primitive translations to SSProve [code].

    Per the audited plan at ~/.claude/plans/sprightly-finding-robin.md
    (Task 03).  Translates each piSMC primitive (Init, Send, Recv_enc,
    Recv_dec, Ret, Finish) to an SSProve [code] fragment.

    Design commitments (Rocq expert audit):
    - Commitment 1: encryption-randomness carrier is a finType ([Renc]
      in the consuming file, abstracted here as a Section variable).
    - Commitment 3: [Send<dst> v ; P] threads [v] into the return-value
      accumulator of [P]; no heap operations.  Concretely, the translator
      takes a continuation [code L I (chList t_cipher)] and prepends [v]
      to the returned list.
    - Recv translators consume oracle interfaces via [#import].

    The Fixpoint that walks the piSMC AST and dispatches to these
    primitives lives in Task 04 ([translate_pismc_to_ssprove]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

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
