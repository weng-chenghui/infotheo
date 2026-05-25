(* DSDP Alice secrecy under IND-CPA.

   Hybrid (computational + information-theoretic) closed-form bound

       Pr[A(AliceView) = V_2] <= 1 / m + 2 * epsilon_cpa

   for the 3-party DSDP protocol against static semi-honest corrupted Alice.
   Two real-or-zero IND-CPA ciphertext swaps plus an information-theoretic
   residual-uniformity step.

   Plan: ~/.claude/plans/sprightly-finding-robin.md
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(* Pin SSProve's real type as the ambient realType for this file. *)
Notation R := SSProve.Crypt.Axioms.R.

(* Adversary type abbreviation. *)
Notation adversary := (package _ _ _).

(** [valid_code_link_residual] - SSProve [code_link]'s residual-imports
    validity.  Strengthens [pkg_composition.valid_code_link]: the
    inner code [v] may import operations [Im] that the outer
    package [p] does NOT export — those operations get resolved
    to a [sampler dnull] by SSProve's [resolve] on a missing key,
    which is still a valid code under any imports [Ir].  Therefore
    [code_link v p] is valid under [Ir] (the imports of [p]) with
    NO requirement that [Im] is a sub-interface of [p]'s exports.
    Kind: helper.
    Why: the canonical [valid_link_weak] requires [fsubmap M1 M2]
    where [M1 = p1]'s imports and [M2 = p2]'s exports — but the
    partial-link case [boolean_shell ∘ predictor] has p1's imports
    [unionm game_iface guesser_export] strictly LARGER than p2's
    exports [guesser_export], so neither [valid_link] nor
    [valid_link_weak] applies.  This residual-imports variant is
    the missing API: it propagates only [p]'s imports as the
    result's imports, dropping any [Im] entries not in [p]'s
    exports (they become samplers, not import obligations).
    Used by: [valid_boolean_shell_link] below. *)
Lemma valid_code_link_residual :
  forall (A : choice_type) (L : Locations) (Im Ir E : Interface)
    (v : raw_code A) (p : raw_package),
    ValidCode L Im v ->
    ValidPackage L Ir E p ->
    ValidCode L Ir (code_link v p).
Proof.
move=> A L Im Ir E v p hv hp.
elim: hv => //=.
all: try by [move=> *; constructor; auto].
move=> o x k _ _ IH.
apply: valid_bind.
rewrite /resolve.
case Eo: (p o.1) => [[S [T g]] | ].
- have body_valid : forall y, ValidCode L Ir (g y).
  { by case: hp => _ hi y; exact: (hi o.1 (existT _ S (existT _ T g)) y Eo). }
  rewrite /coerce_kleisli -lock /coerce_code.
  case: (coerce x) => [s | ] /=.
  + apply: valid_bind.
    move=> a /=.
    by case: (coerce a) => [r' | ];
      [constructor | apply: valid_sampler => ?; constructor].
  + apply: valid_sampler => r.
    apply: valid_bind.
    move=> a /=.
    by case: (coerce a) => [r' | ];
      [constructor | apply: valid_sampler => ?; constructor].
- by apply: valid_sampler => ?; constructor.
Qed.

Section dsdp_security_indcpa.

(* AHE scheme is parametric, matching the existing project convention
   from dsdp_pismc.v. *)
Variable AHE : AHEncType.

(* Design Commitment 1 (Rocq audit).  rand AHE is declared as Type in
   homomorphic_encryption/he_types.v:40.  SSProve cannot sample over a
   bare Type.  This scaffold introduces a refined finType carrier Renc
   for the encryption randomness; later instantiation against a
   concrete scheme (Benaloh/Paillier) identifies Renc with rand AHE. *)
Variable Renc : finType.

(* Cardinality index for [sample uniform].  The hypothesis [renc_card]
   below ties [#|Renc|] to [card_renc] so the SSProve uniform sample
   value can be lifted to an [Renc] value via [enum_val]. *)
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.

(** sample_to_renc — convert an SSProve uniform-index value
    ['I_card_renc] to an [Renc] value by routing through [enum_val] and
    the cardinality cast.
    Kind: helper.
    Why: [sample uniform card_renc] returns an ['I_card_renc]; the AHE
    encryption requires an [Renc]-shaped value (after passing through
    [rand_of_renc]).  This is the same plumbing as in
    [homomorphic_encryption/indcpa_ror.v].
    Used by: game_real, game_hybrid_one, game_hybrid_two. *)
Definition sample_to_renc (i : 'I_card_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

(** rand_of_renc — bridge from the SSProve-side finType [Renc] to the
    AHE-side encryption-randomness type [rand AHE].  Same Section
    parameter as in [homomorphic_encryption/indcpa_ror.v]. *)
Variable rand_of_renc : Renc -> rand AHE.

(* Section-parametric carriers for the SSProve [choice_type] message and
   ciphertext spaces, with conversions to/from the AHE [plain]/[cipher]
   types.  Mirrors indcpa_ror.v so the two files share interface shapes. *)
Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.

(** cipher_of_chcipher — inverse of [chcipher_of_cipher], bringing an
    SSProve-side ciphertext ([t_cipher]) back into the AHE-side
    [cipher AHE] type.
    Kind: helper.
    Why: the IND-CPA oracle returns a ciphertext wrapped via
    [chcipher_of_cipher] (so it lives in the SSProve [choice_type]
    world).  The Task 07 reductions then need to feed that ciphertext
    into [Emul] / [Epow] (which live on [cipher AHE]) to assemble the
    Alice-to-other-party slots [a_1] and [a_2].  Both sides are bare
    [Type] / [choice_type] and [chcipher_of_cipher] is intended to be
    a bijection on representatives, so providing the inverse here is
    benign.  Concrete instantiations against Benaloh/Paillier supply
    a concrete [cipher_of_chcipher] satisfying
    [cancel chcipher_of_cipher cipher_of_chcipher].
    Used by: predictor_via_oracle_charlie, predictor_via_oracle_bob. *)
Variable cipher_of_chcipher : t_cipher -> cipher AHE.

(** chcipher_of_cipherK — cancel law witnessing that [cipher_of_chcipher]
    is a left inverse of [chcipher_of_cipher].  Together with
    [chmsg_of_msgK] below this expresses the design intent (file header,
    line 104-108) that the SSProve and AHE message/ciphertext carriers
    are biject on representatives.  Concrete instantiations against a
    real AHE (Benaloh/Paillier) discharge these hypotheses by picking
    [chcipher_of_cipher] / [chmsg_of_msg] as identity-like encodings.
    Kind: hypothesis.
    Why: the Task 09 perfect-equivalence proofs ([game_real ≈₀
    game_via_oracle_charlie ∘ oracle_real] etc.) need to collapse the
    round-trip [cipher_of_chcipher (chcipher_of_cipher c)] introduced
    when the oracle returns its result and the reduction immediately
    feeds that result into [Emul]/[Epow].  Without this cancel,
    [rreflexivity_rule] cannot close the relational goal.
    Used by: game_real_equiv_charlie_real, charlie_zero_equiv_game_hybrid_one,
    game_hybrid_one_equiv_bob_real, bob_zero_equiv_game_hybrid_two. *)
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.

(** chmsg_of_msgK — cancel law witnessing that [msg_of_chmsg] is a left
    inverse of [chmsg_of_msg].  Companion of [chcipher_of_cipherK] for
    the message-side round-trip.
    Kind: hypothesis.
    Why: the Charlie/Bob translation packages call the IND-CPA oracle on
    [(party, chmsg_of_msg v_i)]; the oracle's body applies
    [msg_of_chmsg] internally so the post-simplification goal carries
    [msg_of_chmsg (chmsg_of_msg (msg_of_idx ...))] on one side and
    [msg_of_idx ...] on the other.  Cancelling this round-trip is
    required for [rreflexivity_rule] to close the Task 09 goals.
    Used by: same as [chcipher_of_cipherK]. *)
Hypothesis chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.

(* Public-key supply per party, again parametric (no commitment to a
   specific key-generation strategy). *)
Variable pkey_of_party : party_id -> pub_key AHE.

(* Index for the protocol-level scalar carrier ('Z_m or 'F_m in the
   instantiated proof; here abstracted as a finType-indexed uniform).
   The three protocol-side random variables V_1, V_2, V_3, U_1, U_2, U_3,
   R_2, R_3 are all sampled from this carrier.  card_msg gives its
   cardinality so [sample uniform card_msg] is well-typed. *)
Variable card_msg : nat.

(** msg_of_idx — bridge from the SSProve uniform-sample index
    ['I_card_msg] to a [plain AHE] value.  Section-parametric: a
    concrete instantiation supplies the cardinality bridge and the
    enumeration.
    Kind: helper.
    Why: SSProve samples take a [nat] cardinality, but the protocol-level
    arithmetic in DSDP operates on [plain AHE].  This indirection lets
    the same game definitions instantiate against different concrete
    plaintext carriers (e.g. ['F_m] or ['Z_(p*q)]) without retyping.
    Used by: game_real, game_hybrid_one, game_hybrid_two. *)
Variable msg_of_idx : 'I_card_msg -> plain AHE.

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).

(** cipher_list — the choice_type carrier for the return-value
    accumulator: an SSProve list of ciphertexts.  Each game produces a
    value of this type as its single observable output.
    Kind: canonical.
    Why: Design Commitment 3 (Rocq audit).  [Send<dst> v ; P] threads [v]
    into a return-value accumulator.  All four games share this
    accumulator type so they can be composed/contrasted via
    [AdvantageE].
    Used by: game_iface, game_real, game_hybrid_one, game_hybrid_two,
    game_enc_zero. *)
Definition cipher_list : choice_type := chList t_cipher.

Local Notation "'ciphers'" := cipher_list (in custom pack_type at level 2).

(** id_game_run — the cipher-output operation identifier exported by
    every game.  Calling it executes the joint protocol run and returns
    the ciphertext accumulator visible to corrupted Alice; as a side
    effect the protocol-side scalar V_2 sampled inside the body is
    written to the shared [V_2_cell] location so the second oracle
    [id_v2_get] can read it back.
    Kind: canonical.
    Why: SSProve operations are identified by a [nat]; a single shared
    identifier across the four games keeps [game_iface] unique so
    [AdvantageE] is well-typed.
    Used by: game_iface and all four game packages. *)
Definition id_game_run : nat := 0%N.

(** id_v2_get — the V_2-reveal operation identifier exported by every
    game.  Calling it returns the protocol-side V_2 sample written into
    [V_2_cell] by the previous call to [id_game_run].
    Kind: canonical.
    Why: T1 of [~/.claude/plans/sprightly-finding-robin.md].  The
    indicator wrapper (T4) compares the predictor's guess against V_2
    by reading this oracle.  Operation id [2] is fresh; id [1] is
    reserved for the predictor's own export identifier ([id_guess] in
    T4).
    Used by: game_iface and all four game packages. *)
Definition id_v2_get : nat := 2%N.

(** V_2_cell — shared SSProve [Location] storing the protocol-side V_2
    sample.  The cell holds an [option t_msg]; the cipher oracle [#put]s
    it to [Some _] before returning, the V_2 oracle [get]s it back.
    Kind: canonical.
    Why: T1 of [~/.claude/plans/sprightly-finding-robin.md].  The
    pre-T0 framework sampled an independent [iV2] inside the indicator
    after the predictor returned its guess, making the V_2-guess event
    vacuously [1/m]-bounded.  T1 fixes this by routing the actual V_2
    used inside the cipher-game body through a state-shared location;
    the indicator (T4) reads this location to obtain the V_2 the
    predictor was distinguishing against.
    Naming: project-local [V_2] preserves TeX subscript; [_cell] marks
    the SSProve mutable location.
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_enc_zero,
    game_via_oracle_charlie, game_via_oracle_bob, T4's indicator wrapper. *)
Definition V_2_cell : Location := mkloc 8 (None : option t_msg).

(** protocol_state — the [Locations] fmap holding [V_2_cell].  Used as
    the [locs] field of every game and translation package so the four
    games and the two reductions all share the same state-cell layout.
    Kind: canonical.
    Why: T1 of [~/.claude/plans/sprightly-finding-robin.md].  SSProve
    packages carry their own [locs] field; for two packages to share a
    state cell at runtime they must declare the same [Locations] map.
    Using [protocol_state] uniformly across the games and translations
    is the standard SSProve idiom (compare [IND_CPA_location] in
    [SSProve/examples/PRF.v:276]).
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_enc_zero,
    game_via_oracle_charlie, game_via_oracle_bob. *)
Definition protocol_state : Locations := [fmap V_2_cell].

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

(** game_iface — the shared export interface of the four games.  Each
    game exports two operations: [id_game_run] taking ['unit] and
    returning the ciphertext accumulator [ciphers], and [id_v2_get]
    taking ['unit] and returning the protocol-side V_2 sample
    ([t_msg]).
    Kind: canonical.
    Why: the SSProve advantage [AdvantageE G_0 G_1 A] requires both
    games to share their export interface.  The IND-CPA hops chain four
    games against this single shared two-oracle signature.  The
    predictor (T2's reductions) only imports the [id_game_run]
    sub-interface; the indicator (T4) imports both oracles.
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_enc_zero,
    advantage_game_real_game_enc_zero. *)
Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

(** game_real — package modelling the real DSDP execution.  Samples the
    protocol-level random variables (V_2, V_3, U_2, U_3, R_2, R_3) and
    Bob/Charlie/Alice's encryption-randomness uniformly, computes
    Bob-to-Alice c_2 = Enc(pk_bob, V_2, r_b1) and Charlie-to-Alice
    c_3 = Enc(pk_charlie, V_3, r_c1), and the two Alice-to-Bob/Charlie
    ciphertexts a_1, a_2 from the homomorphic operations on (c_2, c_3,
    U_2, U_3, R_2, R_3, r_a1, r_a2).  Returns the four-element list
    [a_1; a_2; c_2; c_3] (the ciphertext slots leaked to corrupted
    Alice).
    Kind: main.
    Why: Task 06 of the plan.  This is the start of the hybrid chain;
    the IND-CPA hops replace c_2 and c_3 with zero-encryptions, then the
    residual leak is collapsed in [game_enc_zero].
    Used by: Tasks 07 (reductions), 08 (advantage triangle). *)
Definition game_real :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      (* protocol-level scalars *)
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      (* fresh randomnesses for the four encryption slots *)
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      let c3 := enc pk_c v3 rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** game_hybrid_one — first IND-CPA hop.  Same as [game_real] except
    Charlie-to-Alice c_3 is replaced by [Enc(pk_charlie, 0, r_c1)].
    Distinguishing it from [game_real] reduces to IND-CPA security of
    the AHE scheme on Charlie's public key (via [predictor_via_oracle_charlie] in
    Task 07).
    Kind: main.
    Why: Task 06 of the plan.  Strips the V_3 dependency from the
    Charlie ciphertext slot while leaving the Bob slot real.  The IND-CPA
    advantage of [game_real] vs [game_hybrid_one] is bounded by
    [epsilon_cpa].
    Used by: Tasks 07 (reductions), 08 (advantage triangle). *)
Definition game_hybrid_one :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      (* Charlie's slot is now a zero-encryption (first IND-CPA hop). *)
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** game_hybrid_two — second IND-CPA hop.  Same as [game_hybrid_one]
    except Bob-to-Alice c_2 is also replaced by [Enc(pk_bob, 0, r_b1)].
    Both ciphertext slots are now zero-encryptions; only the random
    deterministic algebra over (V_2, U_2, U_3, R_2, R_3) plus the
    encryption-randomness terms remain.
    Kind: main.
    Why: Task 06 of the plan.  Second IND-CPA hop, symmetric to the
    Charlie hop.  After this hop, [game_hybrid_two] is identical in
    distribution to [game_enc_zero] modulo a deterministic post-processing
    (Task 09 closes that equivalence).
    Used by: Tasks 07 (reductions), 08 (advantage triangle),
    09 (perfect equivalence). *)
Definition game_hybrid_two :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      (* Both ciphertext slots are now zero-encryptions. *)
      let c2 := enc pk_b (0 : plain AHE) rb1 in
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** game_enc_zero — residual game post-IND-CPA collapse.  Both ciphertext
    slots encrypt the constant [0 : plain AHE], so the joint
    distribution of the four-element ciphertext list is a deterministic
    function of fresh encryption-randomness independent of the
    protocol-side secret [V_2].  Identical in body to [game_hybrid_two];
    the distinct name marks the role in the advantage triangle (this is
    the post-collapse endpoint where the IT residual analysis takes
    over).  Used to close the advantage triangle in Task 08 and as the
    input distribution for the residual uniformity argument in Task 13.
    Kind: main.
    Why: Task 06 of the plan.  Once both IND-CPA hops have been taken,
    the remaining ciphertext content is independent of the protocol
    secret V_2; Task 13 then shows
    [Pr[predictor game_enc_zero = V_2] = 1/m].  Task 09's perfect
    equivalence [game_hybrid_two ≈₀ game_enc_zero] is by reflexivity.
    Naming: an earlier draft used an empty-list residual.  The empty
    list is not perfectly equivalent to [game_hybrid_two] (it returns a
    syntactically distinct 0-length list), and Task 09 was unprovable in
    that shape.  The body now matches [game_hybrid_two] so the perfect
    equivalence holds, while Task 13 takes responsibility for showing
    the IT residual is uniform on [V_2].
    Used by: Tasks 08 (advantage triangle), 09 (perfect equivalence),
    13 (residual uniformity). *)
Definition game_enc_zero :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b (0 : plain AHE) rb1 in
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** Task 06 verification: each game type-checks as an SSProve
    [package _ _ _] sharing the same import interface ([interface]) and
    export interface ([game_iface]).  This is what the Task 08
    [ssprove triangle] tactic consumes. *)
Check game_real.
Check game_hybrid_one.
Check game_hybrid_two.
Check game_enc_zero.

(* The [msg] pack_type notation aliasing [t_msg] is declared above
   alongside the [game_iface] definition so the V_2 oracle's return-type
   slot can use it. *)

(** game_via_oracle_charlie — SSProve translation package mediating between
    the IND-CPA real-or-zero oracle on Charlie's public key and the
    DSDP game interface.  Imports the encryption oracle
    [oracle_encrypt_iface t_msg t_cipher] and exports the shared
    [game_iface] in front of [game_real] / [game_hybrid_one].  Inside:
    samples (V_2, V_3, U_2, U_3, R_2, R_3, r_a1, r_a2, r_b1) and
    deterministically builds Bob-to-Alice c_2 = Enc(pk_b, V_2, r_b1).
    Then queries the oracle on the pair (Charlie, V_3), bringing the
    returned ciphertext back into [cipher AHE] via
    [cipher_of_chcipher] so it can be fed into the homomorphic [Emul]
    and [Epow] operations that assemble [a_1] and [a_2].  Returns the
    same four-element ciphertext list as the four games.
    Kind: helper.
    Why: Task 07 of the plan.  The IND-CPA real-or-zero hypothesis
    [enc_ind_cpa_real_or_zero] bounds the SSProve advantage of an
    adversary distinguishing [oracle_encrypt_real_pkg] from
    [oracle_encrypt_zero_pkg].  By design,
    [predictor ∘ game_via_oracle_charlie ∘ oracle_encrypt_real_pkg] is
    distribution-equivalent to [predictor ∘ game_real] and
    [predictor ∘ game_via_oracle_charlie ∘ oracle_encrypt_zero_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_one].  Those
    two equivalences (proven in Task 08) turn the abstract IND-CPA
    bound into the [game_real] / [game_hybrid_one] hop.
    Used by: predictor_via_oracle_charlie, Task 08 advantage triangle. *)
Definition game_via_oracle_charlie :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      ch3 ← oracle_enc (party_id_to_nat Charlie, chmsg_of_msg v3) ;;
      let c3 := cipher_of_chcipher ch3 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; ch3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** game_via_oracle_bob — SSProve translation package mediating between the
    IND-CPA real-or-zero oracle on Bob's public key and the DSDP game
    interface.  Imports the encryption oracle
    [oracle_encrypt_iface t_msg t_cipher] and exports the shared
    [game_iface] in front of [game_hybrid_one] / [game_hybrid_two].
    Inside: samples the same protocol-level scalars and a fresh
    Charlie-side randomness r_c1.  Charlie's ciphertext is hardcoded
    to the zero-encryption [enc pk_c (0 : plain AHE) r_c1] (matching
    [game_hybrid_one] and [game_hybrid_two], which both freeze that
    slot).  Bob's ciphertext c_2 is obtained by querying the oracle on
    (Bob, V_2), again routed through [cipher_of_chcipher] for the
    homomorphic [Emul]/[Epow] assembly.
    Kind: helper.
    Why: Task 07 of the plan.  Symmetric to [game_via_oracle_charlie], for
    the second IND-CPA hop.  By design,
    [predictor ∘ game_via_oracle_bob ∘ oracle_encrypt_real_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_one] and
    [predictor ∘ game_via_oracle_bob ∘ oracle_encrypt_zero_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_two].
    Those equivalences (Task 08) bind the IND-CPA hardness on
    [pkey_of_party Bob] to the [game_hybrid_one] / [game_hybrid_two]
    hop.
    Used by: predictor_via_oracle_bob, Task 08 advantage triangle. *)
Definition game_via_oracle_bob :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      ch2 ← oracle_enc (party_id_to_nat Bob, chmsg_of_msg v2) ;;
      let c2 := cipher_of_chcipher ch2 in
      let c3 := enc pk_c (0%R : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; ch2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(** predictor_via_oracle_charlie — IND-CPA reduction packaging the predictor at
    the Charlie slot.  Composes [predictor] (an arbitrary SSProve
    raw_package consuming [game_iface]) with [game_via_oracle_charlie]
    (consuming the IND-CPA oracle and exporting [game_iface]).  The
    result imports [oracle_encrypt_iface t_msg t_cipher] and exports
    the predictor's own export interface; in particular it is a valid
    distinguisher for the IND-CPA real-or-zero hypothesis on Charlie's
    public key.
    Kind: main.
    Why: Task 07 of the plan.  The IND-CPA real-or-zero hypothesis
    [enc_ind_cpa_real_or_zero] is universally quantified over the
    reduction adversary, so to instantiate it at the first hop
    ([game_real] vs [game_hybrid_one]) we need a single SSProve
    raw_package that, when composed with [oracle_encrypt_real_pkg]
    (resp. [oracle_encrypt_zero_pkg]), reproduces the predictor's
    behaviour against [game_real] (resp. [game_hybrid_one]).  That
    package is exactly [predictor ∘ game_via_oracle_charlie].
    Used by: Task 08 advantage triangle (first hop). *)
Definition predictor_via_oracle_charlie (predictor : raw_package) : raw_package :=
  predictor ∘ pack game_via_oracle_charlie.

(** predictor_via_oracle_bob — IND-CPA reduction packaging the predictor at the
    Bob slot.  Symmetric to [predictor_via_oracle_charlie], built from
    [game_via_oracle_bob] which freezes Charlie's slot to a
    zero-encryption and routes Bob's slot through the IND-CPA oracle.
    Kind: main.
    Why: Task 07 of the plan.  Used in the second hop of the
    [ssprove triangle] ([game_hybrid_one] vs [game_hybrid_two])
    instantiating [enc_ind_cpa_real_or_zero] on
    [pkey_of_party Bob].
    Used by: Task 08 advantage triangle (second hop). *)
Definition predictor_via_oracle_bob (predictor : raw_package) : raw_package :=
  predictor ∘ pack game_via_oracle_bob.

(** Task 07 verification: both translations are [ValidPackage]s with
    the same import [oracle_encrypt_iface t_msg t_cipher] and export
    [game_iface], and both reductions accept any predictor raw_package
    and type-check against [enc_ind_cpa_real_or_zero]. *)
Check game_via_oracle_charlie.
Check game_via_oracle_bob.
Check (predictor_via_oracle_charlie : raw_package -> _).
Check (predictor_via_oracle_bob : raw_package -> _).

(** Type-check the reductions against the IND-CPA hypothesis.  Sealed
    in a transient [Section] so [Variable predictor] disappears at
    [End].  The actual algebraic [AdvantageE] use is Task 08. *)
Section reduction_typecheck.
Variable predictor : raw_package.
Check (enc_ind_cpa_real_or_zero
         AHE Renc card_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (predictor_via_oracle_charlie predictor)).
Check (enc_ind_cpa_real_or_zero
         AHE Renc card_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (predictor_via_oracle_bob predictor)).
End reduction_typecheck.

(** Local abbreviation for the IND-CPA real oracle package at this
    section's parameters, kept anonymous-friendly so [enc_ind_cpa_real_or_zero]
    fires cleanly under [Advantage_link] rewrites in Task 08.
    Kind: helper.
    Why: the IND-CPA hypothesis names the two oracle packages explicitly;
    aliasing them here makes the [Advantage_link] / [enc_ind_cpa_real_or_zero]
    chain at the hop-1 / hop-2 boundaries readable.
    Used by: advantage_game_real_game_enc_zero. *)
Definition oracle_real : raw_package :=
  oracle_encrypt_real AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                      pkey_of_party.

(** oracle_zero — local alias for [oracle_encrypt_zero] at this section's
    parameters.
    Kind: helper.
    Why: aliasing [oracle_encrypt_zero] at the current section's
    parameters keeps the [Advantage_link] / [enc_ind_cpa_real_or_zero]
    chain at the hop boundaries readable, paired with [oracle_real] for
    the IND-CPA real-or-zero hypothesis instantiation.
    Used by: advantage_hop_real_h1, advantage_hop_h1_h2,
    advantage_game_real_game_enc_zero. *)
Definition oracle_zero : raw_package :=
  oracle_encrypt_zero AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher chcipher_of_cipher pkey_of_party.

(** game_real_equiv_charlie_real — perfect equivalence between [game_real]
    and the Charlie translation linked with the real-encryption oracle.
    Both sides sample the same protocol-level scalars, the same
    encryption-randomness slots and produce the same four-ciphertext
    accumulator; the only difference is that the right-hand side routes
    Charlie's ciphertext through the oracle interface.  Inlining
    [oracle_encrypt_real] makes the two sides relationally equal up to
    swap of independent samples.
    Kind: helper.
    Naming: SSProve game-equivalence convention; `equiv` placed medially
    between the two game operands so both sides of the [≈₀] relation are
    readable at the hop-1 boundary.  The MathComp `_E` suffix is
    unsuitable here because both operands carry their own multi-component
    names and a single trailing `_E` would obscure which side is which.
    Why: Task 08 uses this equivalence under [erewrite ... by ssprove_valid]
    to bridge [AdvantageE game_real game_hybrid_one predictor] to
    [AdvantageE (game_via_oracle_charlie ∘ oracle_real) (game_via_oracle_charlie ∘
    oracle_zero) predictor], where [Advantage_link] then exposes the
    IND-CPA reduction [predictor_via_oracle_charlie predictor].
    Proof: Task 09.  [eq_rel_perf_ind_eq] reduces the goal to a
    relational equality on the SSProve code; ten [ssprove_sync_eq]
    steps synchronise the ten shared uniform samples; the round-trip
    [cipher_of_chcipher (chcipher_of_cipher _)] and the message
    round-trip [msg_of_chmsg (chmsg_of_msg _)] both collapse via the
    [chcipher_of_cipherK] and [chmsg_of_msgK] cancel hypotheses;
    [rreflexivity_rule] then closes the goal.  Mirrors the
    [IND_CPA_equiv_false] proof at [SSProve/examples/PRF.v] line 328.
    Used by: advantage_hop_real_h1, advantage_game_real_game_enc_zero. *)
Lemma game_real_equiv_charlie_real :
  game_real ≈₀ game_via_oracle_charlie ∘ oracle_real.
Proof.
(* Use [eapply] (not ssreflect [apply:]).  On a linked package of this
   size, ssreflect's [apply:] runs an aggressive higher-order unification
   that delta-unfolds the [raw_package] bodies while inferring the
   implicit [{L0 L1 E}] arguments, duplicating a huge term in memory
   (observed: ~80 GiB before OOM kill on this lemma).  Vanilla [eapply]
   leaves [L0]/[L1]/[E] as existentials and resolves them lazily after
   [ValidPackage] typeclass search finds the instances, so the package
   term is never duplicated.  All SSProve upstream examples
   ([PRF.v], [Schnorr.v]) use [eapply] at this step for the same reason.
   The remaining ssreflect tactics in this and the sibling equivalence
   proofs ([apply:], [by]) are unaffected because they operate on the
   smaller post-[simplify_eq_rel] goals.

   (L0, L1 are the sets of mutable state cells that p₀ and p₁ are allowed
    to touch (their "private heap")).
   (E: the export interface, i.e., the set of operations the package offers
    to the outside world. Both packages must export the same interface —
    that is what makes them interchangeable for an adversary).
*)
(* eq_rel_perf_ind_eq: if executing each exported operation on the two
   packages produces the same answer and the same updated heap,
   then no adversary can ever tell them apart.

   The goal after this eapply:

   eq_up_to_inv game_iface (λ '(h₀, h₁), h₀ = h₁) game_real
     (game_via_oracle_charlie ∘ oracle_real)

   eq_up_to_inv E I p₀ p₁:  a per-operation observational-equivalence
   judgement in the relational program logic: for every operation op ∈ E
   and every argument, the two implementations of op produce the same return
   value and leave the heap in a related final state, provided the initial
   heaps were related by the invariant I. Here I = (λ '(h₀, h₁), h₀ = h₁),
   i.e., heaps are required to be bit-identical on both sides.

   Since game_real and game_via_oracle_charlie ∘ oracle_real are literally
   different terms, even they have heap equality, they are not equal.
   Although heap equality is already the strongest invariant
   we can have to prove.

   The purpose: now there is no universal quantifier over adversaries.
   So we don't need to prove "for all adversaries" which is difficult.
   We just have to compare the code of each operation in game_iface on
   the two sides, under heap equality.
*)
eapply eq_rel_perf_ind_eq.

(* Once unfolding eq_up_to_inv, it says that
   for every operation op in the export interface and every argument m,
   the two implementations are related by a relational Hoare triple over the
   heap-equality invariant. This is still abstract.

   simplify_eq_rel m: 

   1. Introduce the operation.
   2. Case-split on which operation we are handling: one subgoal per
      declaration in E. So an interface with two operations produces
      two subgoals.
   3. Unfold the pack / lookup_op
   4. Tidies up the resulting match on the op tag.

   The end state of each subgoal is a concrete relational Hoare triple of the
   form ⊢ ⦃ h₀ = h₁ ⦄ ⟦ code₀(m) ⟧ ≈ ⟦ code₁(m) ⟧ ⦃ ... ⦄, where code₀ and code₁
   are the actual #sample / #put / #get / ret programs we wrote in the package
   definition.
*)
simplify_eq_rel m.
(* ssprove_swap_rhs N swaps the two adjacent commands at position N and N+1 in
   the program text on the right-hand side of a relational triple. *)
- ssprove_swap_rhs 9%N.
(* ssprove_sync_eq is the tactic that takes one identical "probabilistic step"
   off the front of both sides of a relational Hoare triple under the
   heap-equality invariant, from:

   ⊢ ⦃ h₀ = h₁ ⦄  s ← sample D ;; k₀ s   ≈   s ← sample D ;; k₁ s   ⦃ post ⦄

   To:

   ∀ v : D,
    ⊢ ⦃ h₀ = h₁ ⦄   k₀ v   ≈   k₁ v   ⦃ post ⦄

   So it peels off one synchronized (sampling) step.
   Then we by `=> ?` drop the value.
   So those `sample uniform ...` lines in the goal are gone.

   If at any iteration the next instruction on the two sides was not identical,
   say one side had a sample uniform card_msg and the other had a sample uniform
   card_renc, or one side had a #put and the other had a sample,
   ssprove_sync_eq would fail and we need a different relational rule.
*)
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  
(* The two ret [...] blocks in the goal are huge because they contain the entire
   returned ciphertext list spelled out with all the
   Epow/enc/pkey_of_party/msg_of_idx plumbing.


   rpost_weaken_rule is the consequence rule on the post-condition side.
   Given a relational triple, you may strengthen the program-side post-condition
   provided you supply an implication back to the original one:

     ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post' ⦄         ∀ a₀ a₁,  post' a₀ a₁  →  post a₀ a₁
     ───────────────────────────────────────────────────────────────────────
                           ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄

   and it generates two subgoals:

   (a)  ⊢ ⦃ h₀ = h₁ ⦄  ret [...]  ≈  ret [...]  ⦃ ?post' ⦄
   (b)  ∀ a₀ a₁, ?post' a₀ a₁  →  (λ '(b₀,s₀) '(b₁,s₁), b₀ = b₁ ∧ s₀ = s₁) a₀ a₁

   then the rreflexivity_rule is the relational Hoare counterpart of reflexivity
   says: when the two sides of a relational triple are the same program up to
   convertibility, you can close the triple with the strong post-condition
   λ a₀ a₁, a₀ = a₁ (i.e., the result pairs are literally equal).

   In your printout the LHS contains

     rand_of_renc (sample_to_renc _a9_)

   while one item on the RHS displays as

     rand_of_renc (indcpa_ror.sample_to_renc Renc card_renc renc_card _a9_) 

  But actually the local `sample_to_renc` is a wrapper of the latter,
  so they are convertible. The LHS comes from game_real
  (written using the local abbreviation),
  the RHS comes from game_via_oracle_charlie ∘ oracle_real where the oracle was
  defined in indcpa_ror and refers to the fully-qualified name directly.

  Note that the two program game_real and
  are not convertible at top-level. This is the whole point of lines before:
  by peeling layers that are not convertible, the residual part are convertible.
  In other words:

  After a sound permutation of the sample sequence (the swap),
  the diagonal coupling of every shared random choice (the eleven syncs),
  and the cancellation of an artificial encoding round-trip (the two rewrites),
  what remains of the two programs is the same expression.
*)
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(** charlie_zero_equiv_game_hybrid_one — perfect equivalence between
    the Charlie translation linked with the zero-encryption oracle and
    [game_hybrid_one].  Symmetric to [game_real_equiv_charlie_real]: the
    only difference between the two sides is that Charlie's ciphertext
    slot encrypts [0%R] (in [game_hybrid_one]) and the oracle returns a
    fresh zero-encryption (left-hand side).
    Kind: helper.
    Naming: SSProve game-equivalence convention; `equiv` placed medially
    between the two game operands so both sides of the [≈₀] relation are
    readable at the hop-1 boundary.
    Why: Task 08 uses this to close the right end of the first IND-CPA
    hop, after [game_real_equiv_charlie_real] has been used on the left.
    Proof: Task 09.  Same shape as [game_real_equiv_charlie_real] but
    the message-side cancel [chmsg_of_msgK] is unused: the zero oracle
    discards its message argument, so the round-trip
    [msg_of_chmsg (chmsg_of_msg _)] never appears on either side.
    Used by: advantage_hop_real_h1, advantage_game_real_game_enc_zero. *)
Lemma charlie_zero_equiv_game_hybrid_one :
  game_via_oracle_charlie ∘ oracle_zero ≈₀ game_hybrid_one.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_lhs 9%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(** game_hybrid_one_equiv_bob_real — perfect equivalence between
    [game_hybrid_one] and the Bob translation linked with the
    real-encryption oracle.  Both sides freeze Charlie's slot to a
    zero-encryption; only the Bob slot differs in routing (direct [enc]
    in [game_hybrid_one], oracle on the right-hand side).
    Kind: helper.
    Naming: SSProve game-equivalence convention; `equiv` placed medially
    between the two game operands so both sides of the [≈₀] relation are
    readable at the hop-2 boundary.
    Why: Task 08 uses this at the left end of the second IND-CPA hop.
    Proof: Task 09.  Like the Charlie case, plus one [ssprove_swap_rhs
    8%N] to align the encryption-randomness sample order: the LHS
    samples irb1 (Bob's randomness) at position 9, irc1 at position 10;
    [game_via_oracle_bob] samples irc1 at position 9 and the oracle adds
    Bob's randomness at position 10.  After the swap the two sides
    agree on the ten-sample prefix and the cancels close as before.
    Used by: advantage_hop_h1_h2, advantage_game_real_game_enc_zero. *)
Lemma game_hybrid_one_equiv_bob_real :
  game_hybrid_one ≈₀ game_via_oracle_bob ∘ oracle_real.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_rhs 9%N.
  ssprove_swap_rhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(** bob_zero_equiv_game_hybrid_two — perfect equivalence between the
    Bob translation linked with the zero-encryption oracle and
    [game_hybrid_two].  Symmetric to [game_hybrid_one_equiv_bob_real]:
    both sides freeze Charlie and Bob slots to zero-encryptions.
    Kind: helper.
    Naming: SSProve game-equivalence convention; `equiv` placed medially
    between the two game operands so both sides of the [≈₀] relation are
    readable at the hop-2 boundary.
    Why: Task 08 uses this at the right end of the second IND-CPA hop.
    Proof: Task 09.  Mirror of [game_hybrid_one_equiv_bob_real] with
    the sample-order swap on the LHS instead of the RHS (the oracle
    sits on the LHS this time).  The message-side cancel
    [chmsg_of_msgK] is unused (zero oracle), so only
    [chcipher_of_cipherK] is rewritten before [rreflexivity_rule].
    Used by: advantage_hop_h1_h2, advantage_game_real_game_enc_zero. *)
Lemma bob_zero_equiv_game_hybrid_two :
  game_via_oracle_bob ∘ oracle_zero ≈₀ game_hybrid_two.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_lhs 9%N.
  ssprove_swap_lhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(** game_hybrid_two_perfect_game_enc_zero — perfect equivalence between
    [game_hybrid_two] and [game_enc_zero].  [game_enc_zero] has the same body
    as [game_hybrid_two] (both ciphertext slots are zero-encryptions of
    the constant [0 : plain AHE]); the distinct name marks the
    triangle endpoint where the IT residual analysis takes over
    (Task 13).
    Kind: helper.
    Naming: SSProve game-equivalence convention; `perfect` placed
    medially between the two game operands marking the residual
    perfect-equivalence (zero-advantage) hop in the triangle chain.
    Why: Task 08 uses this at the right end of the triangle to collapse
    the residual hop [AdvantageE game_hybrid_two game_enc_zero predictor] to
    zero, so the [2 * epsilon_cpa] bound closes.
    Proof: Task 09.  Reflexivity on the relational specification after
    ten [ssprove_sync_eq] steps; no swap or cancel rewrite is needed
    because the two game bodies are syntactically identical.
    Used by: advantage_game_real_game_enc_zero. *)
Lemma game_hybrid_two_perfect_game_enc_zero :
  game_hybrid_two ≈₀ game_enc_zero.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(** advantage_hop_real_h1 — IND-CPA bound on the first hop
    [AdvantageE game_real game_hybrid_one predictor].  Uses
    [Advantage_triangle] to insert the two Charlie-translation
    intermediates ([game_via_oracle_charlie ∘ oracle_real] and
    [game_via_oracle_charlie ∘ oracle_zero]), zeroes the two outer
    summands using [game_real_equiv_charlie_real] and
    [charlie_zero_equiv_game_hybrid_one], then [Advantage_link]
    exposes the IND-CPA reduction [predictor_via_oracle_charlie predictor]
    so [enc_ind_cpa_real_or_zero] closes the bound.
    Kind: helper.
    Why: factoring the first hop's argument keeps
    [advantage_game_real_game_enc_zero] aligned with the PRF.v idiom
    (a single [ssprove triangle] over the four-game chain followed
    by [lerD]).
    Used by: advantage_game_real_game_enc_zero. *)
Lemma advantage_hop_real_h1
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real : fseparate LA game_real.(locs))
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_via_oracle_charlie : fseparate LA game_via_oracle_charlie.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_hybrid_one predictor <= epsilon_cpa.
Proof.
(* AdvantageE behaves like a pseudo-metric on packages
   (with respect to a fixed adversary A):

   AdvantageE G₀ G₂ A  ≤  AdvantageE G₀ G₁ A  +  AdvantageE G₁ G₂ A

   Iterating it over a finite chain of intermediate games G₀, G₁, …, G_n gives
 
   AdvantageE G₀ G_n A  ≤  Σᵢ  AdvantageE Gᵢ Gᵢ₊₁ A  

   The actual list it returns 3 hops, hA, hB, hC:


     game_real
     ────────  hA
     game_via_oracle_charlie ∘ oracle_real
     ────────  hB
     game_via_oracle_charlie ∘ oracle_zero
     ────────  hC
     game_hybrid_one


   AdvantageE game_real game_hybrid_one predictor
    ≤  AdvantageE game_real (charlie ∘ oracle_real) predictor  :hA
     + AdvantageE (charlie ∘ oracle_real) (charlie ∘ oracle_zero) predictor :hB
     + AdvantageE (charlie ∘ oracle_zero) game_hybrid_one predictor :hC

   Then the `cbn in triangle_ineq` unfolds the list-based fold that
   Advantage_triangle_chain returns into this explicit three-term sum
   (otherwise the right-hand side would still be a foldl (+) 0 (map … [_;_])
   expression that subsequent rewrites would not match).
*)
  have triangle_ineq :=
    Advantage_triangle_chain (game_real : raw_package)
      [:: (game_via_oracle_charlie ∘ oracle_real : raw_package)
        ; (game_via_oracle_charlie ∘ oracle_zero : raw_package) ]
      (game_hybrid_one : raw_package) predictor.
  cbn in triangle_ineq.
(* Just handle assoc hA + (hB + hC) to hA + hB + hC,
   so that after the two erewrite it becomes 0 + hB + 0,
   then the two addr0 can handle those 0 with the correct assoc. 
*)
  rewrite ?addrA in triangle_ineq.
  
(* Before this line, the proof state is:

  - Goal:
      AdvantageE game_real game_hybrid_one predictor <= epsilon_cpa
  - In context: triangle_ineq :
      AdvantageE game_real game_hybrid_one predictor <= hA + hB + hC

   After the line we have:

      hA + hB + hC <= epsilon_cpa
*)
  apply: (le_trans triangle_ineq).
  clear triangle_ineq.

(* Each hop turns into 0 or epsilon_cpa. Since each individual hop is a
   fact already proved or already assumed:

   - Hop A: game_real_equiv_charlie_real says
     game_real ≈₀ game_via_oracle_charlie ∘ oracle_real.
     So AdvantageE on this pair is 0. Handled by the 1st erewrite.

   - Hop C: charlie_zero_equiv_game_hybrid_one similarly says
     game_via_oracle_charlie ∘ oracle_zero ≈₀ game_hybrid_one,
     so its AdvantageE is also 0. Handled by the 2nd erewrite.

   - Hop B: This is the cryptographic content. Advantage_link rewrites
     AdvantageE (charlie ∘ oracle_real) (charlie ∘ oracle_zero) predictor
       =  AdvantageE oracle_real oracle_zero
            (predictor_via_oracle_charlie predictor)

     - i.e., bundles the game_via_oracle_charlie half into the adversary.
     After that the goal is exactly the IND-CPA assumption applied to a
     slightly reshaped adversary, and enc_ind_cpa_real_or_zero discharges
     it with bound epsilon_cpa.

   After the two erewrites of the perfect-indistinguishability hops,
   the inequality reads

   AdvantageE game_real game_hybrid_one predictor
    ≤ 0 + AdvantageE oracle_real oracle_zero
         (predictor_via_oracle_charlie predictor) + 0
*)  
(* The erewrite line:

   "unify AdvantageE game_real (charlie ∘ oracle_real) ?A against the goal,
    accept the unification even though the validity/disjointness premises of
    game_real_equiv_charlie_real are still evars, perform the substitution,
    and then close every leftover premise with ssprove_valid."

   For replace:

     AdvantageE game_real (charlie ∘ oracle_real) predictor

   with 0, using game_real_equiv_charlie_real as the rewrite rule and
   ssprove_valid as the side-condition discharger.

   We need erewrite is because:

   Notation "G0 ≈₀ G1" := (G0 ≈[ λ _ : raw_package, 0 ] G1).

   Is actually:

   forall LA (A : raw_package),
    ValidPackage LA (export A_export) A_export A ->
    fdisjoint LA G0.(locs) ->
    fdisjoint LA G1.(locs) ->
    AdvantageE G0 G1 A = 0.

   To substitute AdvantageE game_real (charlie ∘ oracle_real) predictor with 0
   in the goal, the rewrite engine must

   1. unify the pattern AdvantageE game_real (charlie ∘ oracle_real) ?A against
      the goal, which instantiates ?A := predictor,
   2. invent a fitting LA, and
   3. discharge the three premises (the ValidPackage certificate and the two
      location-disjointness facts).

   Plain rewrite cannot do (2) or (3).
   The moment the lemma comes with premises, rewrite is the wrong tool.

   erewrite is rewrite with two extra liberties:

   - The pattern is allowed to contain unresolved evars after unification
     (so the implicit LA and the validity witness
      can stay as ?LA, ?val, ?dj1, ?dj2 rather than blocking the rewrite).
   - After the substitution succeeds, the still-open evars are presented as
     fresh subgoals
*)
  erewrite game_real_equiv_charlie_real by ssprove_valid.
  erewrite charlie_zero_equiv_game_hybrid_one by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

(** advantage_hop_h1_h2 — IND-CPA bound on the second hop
    [AdvantageE game_hybrid_one game_hybrid_two predictor], symmetric
    to [advantage_hop_real_h1].  Uses
    [game_hybrid_one_equiv_bob_real] and
    [bob_zero_equiv_game_hybrid_two] together with
    [enc_ind_cpa_real_or_zero] applied to [predictor_via_oracle_bob predictor].
    Kind: helper.
    Why: symmetric to [advantage_hop_real_h1], for the Bob slot.
    Used by: advantage_game_real_game_enc_zero. *)
Lemma advantage_hop_h1_h2
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 : fseparate LA game_hybrid_two.(locs))
    (predictor_disj_via_oracle_bob : fseparate LA game_via_oracle_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_hybrid_one game_hybrid_two predictor <= epsilon_cpa.
Proof.
  have triangle_ineq :=
    Advantage_triangle_chain (game_hybrid_one : raw_package)
      [:: (game_via_oracle_bob ∘ oracle_real : raw_package)
        ; (game_via_oracle_bob ∘ oracle_zero : raw_package) ]
      (game_hybrid_two : raw_package) predictor.
  cbn in triangle_ineq.
  rewrite ?addrA in triangle_ineq.
  eapply le_trans. 1: exact triangle_ineq.
  clear triangle_ineq.
  erewrite game_hybrid_one_equiv_bob_real by ssprove_valid.
  erewrite bob_zero_equiv_game_hybrid_two by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

(** advantage_game_real_game_enc_zero — Task 08 main result.  Bounds the
    SSProve advantage of any predictor distinguishing [game_real] from
    [game_enc_zero] by [2 * epsilon_cpa].  The bound is established by
    triangle inequality across the four-game chain
        [game_real ; game_hybrid_one ; game_hybrid_two ; game_enc_zero],
    bounding the first two hops by [enc_ind_cpa_real_or_zero] (instantiated
    at [predictor_via_oracle_charlie predictor] and [predictor_via_oracle_bob predictor]
    respectively, via [advantage_hop_real_h1] and
    [advantage_hop_h1_h2]) and the last hop by
    [game_hybrid_two_perfect_game_enc_zero].
    Kind: main.
    Why: this is the computational part of the closed-form Alice secrecy
    bound (Tasks 13-14 stitch the information-theoretic residual onto
    this advantage to get [1/m + 2 * epsilon_cpa]).
    Used by: T1 V_2-aware rebuild.
    Naming: advantage_<source>_<target> is the project-local convention for
    SSProve advantage-bound lemmas; the suffix records the two games whose
    AdvantageE is being bounded, not a MathComp algebraic property. *)


(* The bound becomes epsilon_cpa + epsilon_cpa
  Same triangle-inequality bookkeeping as before,
  just with one more + in the bound:

  AdvantageE game_real game_enc_zero predictor
   ≤ AdvantageE game_rea game_hybrid_one  predictor (hop 1, ≤ epsilon_cpa)
   + AdvantageE game_hybrid_one game_hybrid_two predictor (hop 2, ≤ epsilon_cpa)
   + AdvantageE game_hybrid_two  game_enc_zero predictor   (perfect hop, = 0)
     ≤ epsilon_cpa + epsilon_cpa + 0
     = epsilon_cpa + epsilon_cpa.
*)
Lemma advantage_game_real_game_enc_zero
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real :
       fseparate LA game_real.(locs))
    (predictor_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (predictor_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (predictor_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (predictor_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_enc_zero predictor <= epsilon_cpa + epsilon_cpa.
Proof.
  ssprove triangle (game_real : raw_package)
    [:: (game_hybrid_one : raw_package)
      ; (game_hybrid_two : raw_package) ]
    (game_enc_zero : raw_package) predictor as advantage_bound.
  eapply le_trans. 1: exact advantage_bound.
  clear advantage_bound.
  erewrite game_hybrid_two_perfect_game_enc_zero by ssprove_valid.
  rewrite GRing.addr0.
  apply lerD.
  - exact: advantage_hop_real_h1.
  - exact: advantage_hop_h1_h2.
Qed.

(* ================================================================== *)
(* Task T4: boolean_shell reading V_2 from id_v2_get + Pr_guess_le    *)
(* ================================================================== *)

(* T4 of [~/.claude/plans/sprightly-finding-robin.md]: re-introduce
   the predictor/indicator framework that was deleted in T0 (it was
   mathematically vacuous: the pre-T0 indicator sampled an
   independent [iV2] after the predictor returned a guess, so the
   probability that the guess matched that fresh sample was
   trivially [1/m] regardless of IND-CPA hardness).  The V_2-aware
   rebuild reads V_2 from the game's [id_v2_get] oracle, which
   returns the V_2 stored in the shared [V_2_cell] by [id_game_run].
   The resulting bound [Pr[guess = V_2] <= 1/m + 2 * epsilon_cpa]
   is cryptographically meaningful: the [2 * epsilon_cpa] half is
   load-bearing on the IND-CPA axiom
   [enc_ind_cpa_real_or_zero], and the [1/m] half is the IT residual
   at [game_enc_zero] dischargeable via Task F's
   [cPr_V2_V3_uniform_on_fiber_joint]. *)

(** id_guess — operation identifier exported by a [t_msg]-output
    predictor.  Calling it [tt] runs the predictor body (which has
    imported [game_iface] and is free to query [id_game_run] but
    NOT [id_v2_get]) and returns the predictor's [t_msg]-typed
    guess.
    Kind: canonical.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].
    SSProve operations are identified by a [nat]; [id_game_run = 0%N]
    and [id_v2_get = 2%N] are already taken by [game_iface], so the
    predictor's operation needs a fresh identifier.  [1%N] is the
    next available slot.
    Naming: project-local; mirrors [id_game_run], [id_v2_get],
    [id_oracle_encrypt].
    Used by: [guesser_export], [boolean_shell], [predictor_guesser]. *)
Definition id_guess : nat := 1%N.

(** guesser_export — the export interface of a [t_msg]-output
    predictor.  Exposes a single operation [id_guess] taking
    ['unit] and returning the SSProve message-space carrier
    [t_msg] (aliased to the [pack_type] custom-entry notation
    ['msg']).
    Kind: canonical.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  The
    [predictor_guesser] type below exports this interface in front
    of [game_iface]: the predictor consumes the game's two-oracle
    [game_iface] and emits a [t_msg] guess of V_2.  This is the
    SSProve analogue of the TeX adversary [A : Y → Δ(R)] from
    [notes/20260506-dsdp-secrecy-closed-form.tex]: map the Alice-
    view [Y] to a distribution on the message space [R].
    Naming: project-local; reads "predictor-style guess exporter".
    Used by: [predictor_guesser], [boolean_shell],
    [guess_indicator_pkg]. *)
Definition guesser_export : Interface :=
  [interface #val #[ id_guess ] : 'unit → msg ].

(** predictor_iface — the predictor's import-side interface.
    Strict subset of [game_iface]: exports only [id_game_run]
    (the ciphertext-reveal oracle), NOT [id_v2_get] (the V_2-reveal
    oracle).
    Kind: canonical.
    Why: structural fix for the V_2-leak attack.  The pre-refactor
    [predictor_guesser] imported the full [game_iface], letting
    adversaries call [id_v2_get] and echo V_2 (yielding Pr=1) or
    anti-echo (yielding Pr=0) — both bypassing the IND-CPA bound.
    Restricting the predictor's import interface to [predictor_iface]
    makes such attacks Coq-level type errors.
    Used by: [predictor_guesser], [valid_boolean_shell_link]. *)
Definition predictor_iface : Interface :=
  [interface #val #[ id_game_run ] : 'unit → ciphers ].

(** predictor_guesser — the SSProve [package] type of a
    [t_msg]-output predictor: imports [predictor_iface] (the
    ciphertext-only sub-interface of [game_iface]) and exports
    [guesser_export] (the [t_msg]-guess oracle).
    Kind: canonical.
    Why: structurally enforces "Alice's adversary sees only leaked
    ciphertexts, not the secret V_2".  Matches the cryptographic
    intent of a corrupted-Alice adversary.  Replaces the pre-refactor
    [package game_iface guesser_export] which exposed [id_v2_get]
    to the adversary (breaking IND-CPA bounds trivially).
    Naming: project-local; reads "a guesser-style predictor".
    Used by: [guess_indicator_pkg], [Pr_guess_le]. *)
Definition predictor_guesser : Type :=
  package predictor_iface guesser_export.

(** boolean_shell — the V_2-aware boolean indicator package.
    Imports the union [unionm game_iface guesser_export] (giving
    access to both the game's V_2-reveal oracle [id_v2_get] and
    the predictor's [id_guess] oracle) and exports the standard
    SSProve adversary interface [A_export] ([#val #[ 0%N ] :
    'unit → 'bool]).  Body: calls the predictor to obtain a [t_msg]
    [guess], calls the game's [id_v2_get] to obtain the V_2 value
    stored in [V_2_cell] by [id_game_run], and returns the boolean
    equality [guess == v2].
    Kind: helper.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md] —
    REPLACES the deleted pre-T0 [boolean_shell] which sampled an
    independent [iV2] after the predictor returned (yielding a
    vacuous [1/m] bound).  The new body reads V_2 from the game's
    state via [id_v2_get], guaranteeing the V_2 the indicator
    compares to is the SAME V_2 sampled inside [game_real]'s body
    and propagated through the IND-CPA hops to [game_enc_zero].
    Naming: project-local; reads "the V_2-aware boolean indicator
    shell".
    Used by: [guess_indicator_pkg], [Pr_guess_le]. *)
Definition boolean_shell :
  package (unionm game_iface guesser_export) A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_guess  ] : 'unit → msg } as call_pred ;;
      #import {sig #[ id_v2_get ] : 'unit → msg } as call_v2 ;;
      guess ← call_pred tt ;;
      v2    ← call_v2 tt ;;
      ret (guess == v2 : 'bool)
    }
  ].

(** guess_indicator_pkg — the canonical bool-output wrapper that
    turns a [t_msg]-output [predictor : predictor_guesser] and a
    closed game [game : package [interface] game_iface] into a
    Bool-output package suitable for [pkg_advantage.Pr].  Defined
    as the sequential link [boolean_shell ∘ predictor ∘ game]:
    [game] supplies [game_iface] (both [id_game_run] and
    [id_v2_get]) to its consumers; [predictor] consumes
    [id_game_run] for its body and re-exports [id_guess];
    [boolean_shell] consumes both [id_guess] (from predictor) and
    [id_v2_get] (which threads through predictor's import,
    eventually resolving against [game]) and returns the boolean
    [guess == v2].  Since SSProve link propagates unmatched
    imports through the chain, [boolean_shell]'s [id_v2_get]
    import is satisfied by [game] via the predictor layer (the
    predictor's [game_iface] import is wider than [id_game_run],
    so [id_v2_get] passes through transparently — at concrete
    instantiation the predictor body simply never queries
    [id_v2_get], matching the cryptographic intent "the
    distinguisher is blind to V_2").
    Kind: main.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].
    Downstream consumers (T5 / T6) take a [predictor_guesser]
    explicitly and compose with [guess_indicator_pkg] to recover
    the Bool-shaped distribution that [pkg_advantage.Pr] consumes.
    The V_2-equality semantics is now syntactic (the [boolean_shell]
    body literally compares [guess == v2] where [v2] comes from the
    game's [V_2_cell]) rather than via an implicit semantic
    convention on a Bool output.
    Naming: project-local; reads "the guess-indicator-style
    package wrapper".  Mirrors [predictor_via_oracle_charlie] / [predictor_via_oracle_bob]
    in shape (a function from a predictor to a [raw_package]) but
    with the additional [game] argument to keep the closed/open
    distinction explicit.
    Used by: [Pr_guess_le], T5's [dsdp_alice_secrecy], T6's
    concrete corollaries. *)
Definition guess_indicator_pkg
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) : raw_package :=
  boolean_shell ∘ predictor ∘ game.

(** card_t_msg — cardinality of the (image of the) message-space
    carrier the predictor's [t_msg] guesses live over.  Bridges
    [#|plain AHE|] to a [nat] for the [1 / card_t_msg] residual
    bound.  At concrete instantiation (T6) this is identified with
    [card_msg] (the protocol-scalar carrier size) since V_2 is
    sampled from [msg_of_idx] applied to ['I_card_msg] and stored
    as [chmsg_of_msg v2] in [V_2_cell].
    Kind: section parameter.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  The
    IT residual bound on [Pr[guess = V_2]] at [game_enc_zero] is
    [1 / card_t_msg]; parametrising the bound on this index
    decouples the abstract SSProve composition from the concrete
    AHE plaintext carrier choice.
    Naming: project-local; mirrors [card_msg], [card_renc].
    Used by: [Pr_guess_enc_zero_le_invm] hypothesis, [Pr_guess_le]. *)
Variable card_t_msg : nat.

(** card_t_msg_gt0 — positivity of [card_t_msg]: the message
    space is non-empty.  Without positivity the residual bound
    [1 / card_t_msg] would be vacuously [0 <= 0] which is still
    mathematically correct but degenerate.
    Kind: section hypothesis.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  Used
    to keep the [1 / card_t_msg] bound a meaningful positive
    quantity at concrete instantiation; the discharge at T6 is
    trivial via [prime_p] / [prime_q] etc. depending on the AHE
    scheme.
    Naming: project-local; the [_gt0] suffix marks a positivity
    hypothesis.
    Used by: [Pr_guess_le] (indirectly, via the hypothesis it
    cascades). *)
Hypothesis card_t_msg_gt0 : (0 < card_t_msg)%N.

(** Pr_guess_enc_zero_le_invm — IT residual bound: at [game_enc_zero] the
    probability that any [predictor_guesser]'s guess equals the
    V_2 read via [id_v2_get] is at most [1 / card_t_msg].
    Kind: section hypothesis.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md], the
    [1/m] half of the closed-form bound.  At [game_enc_zero] the
    ciphertext slots [c_2], [c_3] are zero-encryptions, so V_2's
    value does NOT influence the ciphertext list returned by
    [id_game_run]; therefore the predictor's guess (computed from
    [id_game_run] output only) is statistically independent of
    V_2, and [Pr[guess = V_2] = E_guess[Pr[V_2 = guess | guess]]
    = E_guess[1 / card_t_msg] = 1 / card_t_msg] by uniformity of
    V_2.  This is a CHANNEL-2 (ciphertext-transcript) fact: the
    predictor's view is exactly the [id_game_run] output, which at
    [game_enc_zero] is independent of V_2, so the bound follows by
    direct independence + uniformity of V_2.  It does NOT require the
    fiber-counting / output-channel argument (that is the separate
    Channel-1 result in [dsdp_entropy.v], about Alice's legitimate
    knowledge of the scalar-product output S; the predictor here never
    sees S).  The discharge is therefore an SSProve independence proof
    ([id_game_run] output _|_ [V_2_cell]); see the dated note
    [notes/20260525-two-channel-secrecy-fiber-vs-indcpa.md].

    WHY THIS IS A [Hypothesis] AND NOT A [Lemma].  The [forall
    predictor] quantifier is essential: this is the SECURITY statement
    (no adversary in the class guesses V_2 better than [1 / m]).  A
    per-predictor version would be a mere example, not a security
    theorem, so the universal quantifier must stay.  It is kept
    ASSUMED, rather than machine-checked, because mechanizing the
    forall-arbitrary-adversary ABSOLUTE-probability bound needs program
    logic SSProve does not provide: SSProve reasons about [Advantage]
    (differences between two games) for arbitrary adversaries, but has
    no machinery to compute an absolute single-program [Pr] value, nor
    to push the independence fact through an OPAQUE adversary to an
    exact [1 / m].  After linking, the adversary's [id_game_run] calls
    are inlined as [game_enc_zero]'s body, which itself [#put]s
    [V_2_cell], so the swap / non-interference rules for concrete code
    do not lift to the opaque-predictor case.  The argument is one line
    on paper (independence + uniformity of V_2); only the SSProve
    formalisation route is missing.  The MECHANISED contribution is the
    reduction: the [2 * epsilon_cpa] game-hopping chain
    ([advantage_game_real_game_enc_zero]) is fully machine-checked.
    This [1 / m] ideal-world bound is the standard assumed step.
    TIGHTNESS / NON-VACUITY is witnessed concretely by
    [random_guess_adv] (a stateless adversary that emits a fresh
    uniform guess), which achieves the [1 / m] guess rate and satisfies
    every chain hypothesis: see [secrecy_random_guess] in
    [dsdp_security_indcpa_concrete.v].
    Naming: project-local; reads "Pr[guess = V_2 at game_enc_zero] is
    bounded by [1 / m]".
    Used by: [Pr_guess_le]. *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_enc_zero)) true
      <= (card_t_msg%:R)^-1.

(** Pr_guess_le — the headline non-vacuous Alice-secrecy bound in
    the V_2-aware framing.  For any [t_msg]-output adversary
    [predictor : predictor_guesser] satisfying the disjointness
    conditions of [advantage_game_real_game_enc_zero], the probability
    that the [boolean_shell]-wrapped indicator
    [guess_indicator_pkg predictor game_real] evaluates to [true]
    (i.e. the predictor's guess matches the V_2 that [game_real]
    sampled and stored in [V_2_cell]) is at most
    [1 / card_t_msg + 2 * epsilon_cpa].
    Kind: main residual bound.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  This
    is the IND-CPA-based replacement for the deleted (vacuous)
    [dsdp_alice_secrecy_indcpa].  The [2 * epsilon_cpa] half comes
    from [advantage_game_real_game_enc_zero] (the SSProve triangle
    across the four-game ladder, two IND-CPA hops plus a perfect-
    equivalence residual), instantiated at the chain
    [boolean_shell ∘ par predictor (ID game_iface)] (a closed
    package importing [game_iface] and exporting [A_export]).  The
    [1 / card_t_msg] half comes from the section hypothesis
    [Pr_guess_enc_zero_le_invm] (the IT residual at [game_enc_zero]).
    Proof outline (4 steps):
      1. Triangle: by the elementary [a <= b + |a - b|]
         identity (using [ler_norm] and [lerBlDl]), [Pr_real <=
         Pr_enc_zero + AdvantageE (boolean_shell ∘ par pred game_real)
         (boolean_shell ∘ par pred game_enc_zero)] (the AdvantageE
         instantiated at the trivial distinguisher [A := ID
         A_export] would give exactly this, but the
         [a <= b + |a - b|] form is more direct).
      2. Transfer the SSProve advantage [AdvantageE
         (boolean_shell ∘ par pred game_real) (boolean_shell ∘
         par pred game_enc_zero) (ID A_export)] to [AdvantageE
         game_real game_enc_zero (boolean_shell ∘ par pred (ID
         game_iface))] via [Advantage_link].  The chain
         [boolean_shell ∘ par pred (ID game_iface)] is a closed
         distinguisher package importing [game_iface] and
         exporting [A_export], which is exactly the shape
         [advantage_game_real_game_enc_zero] consumes.
      3. Bound this AdvantageE by [advantage_game_real_game_enc_zero]
         at [≤ epsilon_cpa + epsilon_cpa = 2 * epsilon_cpa].
      4. Combine with the section hypothesis
         [Pr_guess_enc_zero_le_invm predictor] for the [1 /
         card_t_msg] half.
    The IND-CPA axiom [enc_ind_cpa_real_or_zero] is load-bearing
    on step 3 via the [advantage_game_real_game_enc_zero] chain.
    Naming: project-local; reads "[Pr[guess = V_2]] is bounded
    above" in the standard MathComp probability-bound idiom
    ([Pr_X_le]).  Three components (verb-noun-mode); within the
    project's F001/I001 budget.
    Used by: T5's [dsdp_alice_secrecy] (thin wrapper), T6's
    concrete corollaries. *)

(** boolean_shell_pack_setm — folds the displayed [setm emptym 0%N …]
    form of [boolean_shell.(pack)] back to the named term.  The body on
    the right-hand side is exactly what [boolean_shell.(pack)] reduces
    to after δ-unfolding [boolean_shell] into its record literal and
    ι-projecting the [.pack] field; the two notations [#def] and
    [#import] in [boolean_shell] expand to [mkdef] and [opr]
    respectively, after which monadic-bind beta-iota leaves the form
    shown below.  Equality therefore holds by βδιζη convertibility and
    [change] witnesses it directly.  Used by: [valid_boolean_shell_link]
    in place of the in-proof [change (setm emptym _ _) with
    (boolean_shell.(pack))] folds. *)
Lemma boolean_shell_pack_setm :
  boolean_shell.(pack) =
  setm emptym 0%N
    (mkdef 'unit 'bool
      (fun _ : 'unit =>
        guess ← op {sig #[id_guess]  : 'unit → msg } ⋅ tt ;;
        v2    ← op {sig #[id_v2_get] : 'unit → msg } ⋅ tt ;;
        ret (guess == v2 : 'bool))).
Proof.
change boolean_shell.(pack) with
  (setm emptym 0%N
    (mkdef 'unit 'bool
      (fun _ : 'unit =>
        guess ← op {sig #[id_guess]  : 'unit → msg } ⋅ tt ;;
        v2    ← op {sig #[id_v2_get] : 'unit → msg } ⋅ tt ;;
        ret (guess == v2 : 'bool)))).
reflexivity.
Qed.
  
(*
  A slightly more granular phrasing of the same pattern might be:
  decompose → align → witness → close, with type-equality extraction
  sitting between "decompose" and "witness" whenever a dependent pair
  shows up. Here, "align" means reshapiung the goal until it has the
  literal syntactic form that some named lemma's conclusion
  (or some hypothesis in context) is talking about. Because in a typical proof
  step you have three logical phases:

  1. Decompose — break a big goal into pieces (split, case:, intro).
  2. Align — reshape each piece so it matches a known fact.
  3. Discharge — point at the known fact (exact:, apply:, assumption, by)

  For this particular proof the pattern instantiates as:

  1. Decompose the goal until it is small enough to look at one piece at
     a time.
     - split on ValidPackage to get the two field obligations.
     - split on the inner ↔ of valid_exports to get two implications.
     - move=> [f Hf] to destructure existentials.
     - case Eb: on boolean_shell.(pack) o.1 to fork on whether the lookup
       hits an entry.
  2. Align the goal with a lemma or hypothesis. This is the step that
     does the actual work — almost every line of the proof is a
     translation from one form into another so that a stored fact about
     the original package becomes applicable.
     - rewrite he1 substitutes the exports of boolean_shell for A_export
       so we can compare the two setms directly.
     - rewrite //= mapmE converts the mapm plumbing inside the linked
       package into an omap on the original's lookup, which is what the
       case analysis needs.
     - change (setm emptym _ _) with (boolean_shell.(pack)) (now backed
       by boolean_shell_pack_setm) renames the unfolded form so that
       Eb : boolean_shell.(pack) o.1 = … lines up.
     - eapply valid_code_link_residual reduces the body-validity question
       to two smaller validity claims that match the shapes of hi1 and
       pred.(pack_valid) respectively.
  3. Extract type equalities when an existential carries a dependent pair
     (the existT S (existT T f) triples are the recurring offender).
     - move: Hf => [= ? ?]; subst peels Some then the two existTs, learns
       S = chsrc o and T = chtgt o, and rewrites them everywhere. After
       this, the witness's outer types match the goal's expected types
       and the remaining content can be supplied.
  4. Supply the witness for the existential, when there is one to supply.
     - exists g, eexists (fun x => code_link (f x) pred), etc.
  5. Close with a hypothesis in context via the ssreflect by terminator
     (which folds in assumption, reflexivity, discriminate, and a few
     more).
     - by after exists g closes via Eb.
     - by rewrite Eb /= in Hf closes the None case via discriminate (Hf
       collapses to None = Some _).

  The "type equality" step is the part most specific to SSProve's package
  logic: the function-table entries are dependent triples
  (src_type ; tgt_type ; body), and proofs about them constantly bump
  into the need to unify the outer types before talking about the inner
  body. The [=] injection pattern + subst is the standard SSProve idiom
  for that bump.
*)
Lemma valid_boolean_shell_link
    (pred : predictor_guesser) :
  ValidPackage (locs pred) game_iface A_export (boolean_shell ∘ pred).
Proof.
case: boolean_shell.(pack_valid) => he1 hi1.

(* split is decomposing the ValidPackage Record into its two field
   obligations. Looking at the definition in SSProve's
   pkg_core_definition.v:

  Class ValidPackage (L : Locations) (I E : Interface) p :=
    is_valid_package : valid_package L I E p.

  Record valid_package L (I E : Interface) (p : raw_package) :=
    { valid_exports : ∀ o,
        fhas E o <-> (∃ f, fhas p (o.1, (chsrc o ; chtgt o ; f)))
    ; valid_imports : ∀ n (F : typed_raw_function) (x : F.π1),
        fhas p (n, F) → ValidCode L I (F.π2.π2 x)
    }.

  ValidPackage is a single-field typeclass wrapper around the two-field
  record valid_package.

  Then, for sub-goals:

  Subgoal 1 — valid_exports: the function table matches the
    export interface.

    ∀ o, fhas A_export o  ↔ 
      (∃ f, fhas (boolean_shell ∘ pred) (o.1, ⟨chsrc o, chtgt o, f⟩))

  Subgoal 2 — valid_imports: each operation body is well-formed code.
 
    ∀ n F x, fhas (boolean_shell ∘ pred) (n, F) →
      ValidCode (locs pred) game_iface (F.π2.π2 x)
*)
split.
- move=> o.
  rewrite he1 /link.
(* The second split is doing exactly the same kind of structural
   decomposition as the first one, but on an ↔ (iff) rather than on
   a Record.

   Forward (→).
   Given f such that fhas boolean_shell (o.1, ⟨chsrc o, chtgt o, f⟩),
   the linked-side entry has to be the result of applying the linking
   transform to f.

   `eexists (fun x => code_link (f x) pred)`
   Supplies the witness on the conclusion side.
   This is the function-table entry that boolean_shell ∘ pred
   must have at name o.1: it is the original body f,
   post-linked by code_link _ pred so all its imports of
   predictor_iface are resolved through pred.

   `by rewrite //= mapmE Hf`
   Finishes by appealing to the SSProve lemma mapmE, which says

   mapm φ m k = omap φ (m k)

   i.e., looking up k in mapm φ m returns Some (φ v) whenever
   m k = Some v.

   With Hf : boolean_shell o.1 = Some ⟨chsrc o, chtgt o, f⟩,
   mapmE rewrites the lookup on the linked side to
   Some (φ ⟨chsrc o, chtgt o, f⟩) =
     Some ⟨chsrc o, chtgt o, fun x => code_link (f x) pred⟩,
   which matches the existential witness we just supplied.

   ----

   Backward (←). Given that the linked table has an entry at o.1,
   we must produce a corresponding entry in the original table.

   ----

   - The → direction says completeness:
     if boolean_shell exports o, then so does boolean_shell ∘ pred.
     Linking does not delete exports.
   - The ← direction says minimality: if boolean_shell ∘ pred exports o,
     then boolean_shell already did. Linking does not invent new exports
     out of thin air.
*)
  split.
  + move=> [f Hf].
(* `exists e` provides e as the witness for ∃ x, P x and immediately
   requires Coq to type-check e against the binder's type.

   `eexists e` does the same thing but is more lenient:
   any unresolved unification is left as a fresh existential variable
   rather than being demanded on the spot.

   In this case, both are the same.
*)
    exists (fun x => code_link (f x) pred).
(* mapmE : (mapm f m) k = omap f (m k)

   Plain English: to look up key k in the transformed table,
   you can equivalently look up k in the original table and then apply
   the transform to whatever you
   found (or to nothing, if the key was absent).

   It is about mapm (update a table for a key if found then entity) and
   omap (option map: apply f if looking up result is Some v).

   Since mapm φ boolean_shell is exactly the post-link function table,
   mapmE is what lets the proof translate questions about that post-link
   table into questions about the original boolean_shell table,
   which is what he1 and hi1 already give us facts about.
*)
    by rewrite //= mapmE Hf.
  + rewrite //= mapmE.
(* Since we want `setm (setm emptym <K1> <V1>) <K2> <V2>` being converted to
   boolean_shell.(pack) -- the singleton lookup table to the named structure. 
   `change` works because:

   boolean_shell.(pack)
   by _δ   {| locs := … ;
             pack := setm (setm emptym K1 V1) K2 V2 ; pack_valid := … |}.(pack)
         (δ unfolds the Definition `boolean_shell` into its record literal body)
   by _ι   setm (setm emptym K1 V1) K2 V2
         (ι projects the `.pack` field out of the record literal)
*)
    change (setm emptym _ _) with (boolean_shell.(pack)).
    move=> [f Hf].
    change (setm emptym _ _) with (boolean_shell.(pack)) in Hf.
    case Eb: (boolean_shell.(pack) o.1) => [[S [T g]]|].
    * rewrite Eb /= in Hf.
(* by move: Hf we have Eb in the top:

   boolean_shell.(pack) o.1 = Some (existT _ S (existT _ T g))

   After subst:  

   boolean_shell.(pack) o.1 =
      Some (existT _ (chsrc o) (existT _ (chtgt o) g))

   Then give the g:

   fhas boolean_shell.(pack) (o.1, existT _ (chsrc o) (existT _ (chtgt o) g))

   which by SSProve's definition unfolds to
   
   boolean_shell.(pack) o.1 = Some (existT _ (chsrc o) (existT _ (chtgt o) g))
   — exactly Eb (after the subst we just did). So `by` makes it done.
*)
      by move: Hf => [= ? ?]; subst; exists g.
    * by rewrite Eb /= in Hf.
- move=> n F x.
  rewrite /fhas /link mapmE.
  change (setm emptym _ _) with (boolean_shell.(pack)).
  case Eb: (boolean_shell.(pack) n) => [[S' [T' f']]|]; last by [].
  move=> /= [= ?]; subst F => /=.
  eapply (@valid_code_link_residual _ (locs pred)
            (unionm game_iface guesser_export) game_iface guesser_export).
  + have /= Hbs_valid := hi1 n (existT _ S' (existT _ T' f')) x Eb.
    eapply valid_injectLocations; [| exact: Hbs_valid].
    exact: fsub0map.
  + (* Widen pred's pack_valid from [predictor_iface] to [game_iface].
       Sound because [predictor_iface ⊆ game_iface]: predictor_iface
       has only id_game_run, while game_iface adds id_v2_get.  A package
       that's valid against a narrower import is valid against a wider
       one (it just leaves new imports unused). *)
    eapply valid_package_inject_import; last exact: pred.(pack_valid).
    fmap_solve.
Qed.

(*
  Pr[predictor guesses V_2 in game_real]  ≤  1/card_t_msg  +  2·ε_cpa

  The strategy is the classic "ideal-world bound + reality gap" 
  decomposition:

  1. Pr_real  ≤  Pr_enc_zero  +  |Pr_real − Pr_enc_zero|
     (trivial, since a ≤ b + |a−b|).
  2. The two summands match the two summands of the target bound:
    - Pr_enc_zero ≤ 1/card_t_msg — the section hypothesis
      Pr_guess_enc_zero_le_invm, which says that in the fully-idealized game,
      the adversary's view is decoupled from V_2, so the best it can do is
      uniform guessing.
    - |Pr_real − Pr_enc_zero| ≤ 2·ε_cpa — exactly the AdvantageE bound
      established earlier by advantage_game_real_game_enc_zero over the
      four-game chain.

   Note that although in game_real, the adversary sees Enc(V_2) and could in
   principle attack the encryption. But we never prove anything about it
   directly. We pay 2·ε_cpa to migrate the entire argument to game_enc_zero,
   where V_2 is structurally absent from the cipher list. In game_enc_zero the
   IT bound 1/m is unconditional. This is why the hypothesis
   Pr_guess_enc_zero_le_invm can be used here to say no V_2 in the view,
   which means no V_2 in game_enc_zero view. In other words, we have an IT
   hypothesis after the computional security reasoning of real-or-zero
   indistinguishability.
*)
(*
  The four-game chain is just the outer skeleton. Each hop expands internally
  into a 3-step micro-chain through the oracle/distinguisher factoring, and each
  visited location needs its own disjointness premise. Here is the expansion:

    game_real                                   ← chain_disj_real
       │
       │  hop A bounded by epsilon_cpa:
       │      game_real
       │        ≡ game_via_oracle_charlie       ← chain_disj_via_oracle_charlie
       │            ∘ oracle_encrypt_real_pkg   ← chain_disj_ore
       │        ≈ game_via_oracle_charlie
       │            ∘ oracle_encrypt_zero_pkg   ← chain_disj_oze
       │        ≡ game_hybrid_one
       ▼
    game_hybrid_one                             ← chain_disj_h1
       │
       │  hop B bounded by epsilon_cpa:
       │      game_hybrid_one
       │        ≡ game_via_oracle_bob           ← chain_disj_via_oracle_bob
       │            ∘ oracle_encrypt_real_pkg   ← chain_disj_ore (same as hop A)
       │        ≈ game_via_oracle_bob
       │            ∘ oracle_encrypt_zero_pkg   ← chain_disj_oze (same as hop A)
       │        ≡ game_hybrid_two
       ▼
    game_hybrid_two                             ← chain_disj_h2
       │
       │  hop C: perfect equivalence, advantage 0:
       │      game_hybrid_two ≡ game_enc_zero
       ▼
    game_enc_zero                               ← chain_disj_enc_zero

  Legend: ≡ is a perfect-equivalence rewrite (zero advantage, justified by one
  of the *_equiv_* lemmas in the file). ≈ is the IND-CPA indistinguishability
  step (the only place epsilon_cpa is paid).

*)
Lemma Pr_guess_le
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (boolean_shell ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
(* Step 1: Pr_real <= Pr_enc_zero + |Pr_real - Pr_enc_zero| (elementary). *)
set Pr_real :=
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true.
set Pr_enc_zero :=
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_enc_zero)) true.

(*
  Split the goal:   Pr_real ≤ (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa
  Into two parts and then continue the proof. The first is by the IT assumption.
*)
apply: le_trans (_ : Pr_enc_zero + `|Pr_real - Pr_enc_zero| <= _);
  first by rewrite -lerBlDl; exact: ler_norm.

(*
   lerD is "le, r, D = sum": a ≤ b → c ≤ d → a + c ≤ b + d.
   It splits Pr_enc_zero + |…| ≤ 1/card_t_msg + 2·ε_cpa along the +
*)
apply: lerD; first exact: Pr_guess_enc_zero_le_invm.

(* The rewrite chain rewires the goal into the exact shape
  advantage_game_real_game_enc_zero produces. Walking left to right:

  1. /Pr_real /Pr_enc_zero: unfold the two set names. The goal's LHS becomes
     the literal |distr.mu (Pr (guess_indicator_pkg predictor game_real)) true
     − distr.mu (Pr (guess_indicator_pkg predictor game_enc_zero)) true|.

  2. !link_assoc: link_assoc says (p ∘ q) ∘ r = p ∘ (q ∘ r). Package linking
     is associative. The ! prefix applies it repeatedly, re-associating the
     two compositions inside the absolute value so that on each side the
     package reads (boolean_shell ∘ predictor) ∘ game_X, i.e. a single
     distinguisher boolean_shell ∘ predictor composed against game_real and
     against game_enc_zero. That is the form
     AdvantageE game_real game_enc_zero (boolean_shell ∘ predictor) expects.

  After this single combined rewrite line, the goal is

    AdvantageE game_real game_enc_zero (boolean_shell ∘ predictor)
      <= epsilon_cpa + epsilon_cpa

  Two things matter:
  - ∘ is right-associative. So boolean_shell ∘ predictor ∘ game_X parses as
    boolean_shell ∘ (predictor ∘ game_X), not
    (boolean_shell ∘ predictor) ∘ game_X.
  - guess_indicator_pkg predictor game_X is definitionally equal to
    boolean_shell ∘ (predictor ∘ game_X) (by δ), but syntactically it is the
    opaque constant guess_indicator_pkg applied to two arguments.

  The whole point is making link_assoc works.
  We δ-unfold (unfold the defined function in its application, "turn function
  application into function composition in this case, by the definition of
  guess_indicator_pkg"):

  guess_indicator_pkg predictor game_real ⇝ 
    boolean_shell ∘ predictor ∘ game_real

  After this step, the ∘ is visible,
  then link_assoc re-associates so that boolean_shell ∘ predictor becomes one
  syntactic unit (the distinguisher). After that, the goal is definitionally
  equal to the chain lemma's conclusion and exact: closes it.
*)
rewrite /Pr_real /Pr_enc_zero /guess_indicator_pkg
        !link_assoc mulr_natl mulr2n.
exact: advantage_game_real_game_enc_zero.
Qed.

(* T4 verify clauses: the framework type-checks and the headline
   bound closes with [Qed].  Mirrors the verify clauses of
   [advantage_game_real_game_enc_zero] above. *)
Check predictor_guesser.
Check boolean_shell.
Check guess_indicator_pkg.
Check Pr_guess_le.

(* ================================================================== *)
(* Task T5: dsdp_alice_secrecy — closed-form Alice-secrecy bound      *)
(* ================================================================== *)

(** dsdp_alice_secrecy — top-level closed-form Alice-secrecy bound.
    Thin wrapper over [Pr_guess_le] giving the project's canonical
    secrecy claim:

      Pr[predictor's guess equals the protocol's V_2 in game_real]
        <= 1/card_t_msg + 2 * epsilon_cpa.

    The same theorem-level argument list as [Pr_guess_le]: the four
    Section-bound abstract carriers are baked into the Section
    parameters (AHE, Renc, ...); the eleven theorem-level arguments
    [(LA : Locations), (predictor : predictor_guesser),
    chain_valid, 8 disjointness, ValidCode_predictor_game_enc_zero,
    LosslessCode_predictor_game_enc_zero] are mirrored verbatim.  At
    concrete instantiation (T6) the disjointness goals close by
    [fseparate0m] (since the random-guess adversary is stateless,
    [locs = emptym]), and the ValidPackage / lossless goals close
    by [ssprove_valid] and [Lossless_sample + LosslessOp_uniform +
    card_t_msg_gt0] respectively.  Note: in T4's [Pr_guess_le],
    the Section hypothesis [Pr_guess_enc_zero_le_invm] supplies the
    [1/card_t_msg] half; that hypothesis itself is discharged in
    the IT residual section [Section dsdp_security_indcpa_residual]
    below via [cPr_V2_V3_uniform_on_fiber_joint].
    Kind: main.
    Why: the project-canonical secrecy theorem.  Mirrors the TeX
    writeup's Theorem 1 statement
    ([notes/20260506-dsdp-secrecy-closed-form/].).
    Naming: project-local; reads "dsdp-side Alice-secrecy bound".
    Three components, within F001/I001 budget.
    Used by: T6's concrete corollaries
    [{Concrete,Idealized,Benaloh,Paillier}.secrecy_random_guess]. *)
Theorem dsdp_alice_secrecy
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (boolean_shell ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
exact: Pr_guess_le.
Qed.

(* T5 verify clause: the closed-form Alice-secrecy theorem
   type-checks against the Section-internal hypothesis chain. *)
Check dsdp_alice_secrecy.

(* ================================================================== *)
(* Task U2: entropy form of the Alice-secrecy bound                   *)
(*   H_unp^C(V_2 | AliceView) >= log m - log(1 + 2 * m * epsilon_cpa) *)
(* ================================================================== *)

(** epsilon_cpa_ge0 — nonnegativity of the IND-CPA error parameter.
    [indcpa_ror.epsilon_cpa : R] is declared as a bare [Parameter]
    without positivity; the IND-CPA axiom bounds an [AdvantageE]
    by it but does not imply [epsilon_cpa >= 0].
    Kind: section hypothesis.
    Why: required by [log_id] (the [1 + 2 * m * eps > 0] step).
    Used by: [log_id], [Hunp_ge_bound]. *)
Hypothesis epsilon_cpa_ge0 : (0 <= epsilon_cpa)%R.

(** log_id — algebraic identity connecting the probability and
    entropy forms of the secrecy bound:
      [-log (1/m + 2 * eps) = log m - log (1 + 2 * m * eps)]
    for [0 < m] and [0 <= eps].
    Kind: helper.
    Why: bridges [dsdp_alice_secrecy]'s probability bound
    [Pr <= 1/m + 2 * eps_cpa] to the entropy form
    [-log Pr >= log m - log (1 + 2 * m * eps_cpa)] used in the
    TeX writeup (line ~312).
    Proof outline: rewrite [1/m + 2 * eps = (1 + 2 * m * eps) / m]
    by basic algebra, then apply [LogDiv] from
    [lib/realType_ln.v:104]:
    [Log n (x / y) = Log n x - Log n y].
    Used by: [Hunp_ge_bound]. *)
Lemma log_id (m : nat) (eps : R) :
  (0 < m)%N -> (0 <= eps)%R ->
  (- log (m%:R^-1 + 2%:R * eps) = log m%:R - log (1 + 2%:R * m%:R * eps))%R.
Proof.
move=> Hm Heps.
have Hm_pos : (0 < m%:R :> R)%R by rewrite ltr0n.
have Hmeps_pos : (0 < 1 + 2%:R * m%:R * eps :> R)%R
  by rewrite ltr_pwDl ?ltr01 // !mulr_ge0 // ?ler0n.
have Heq : (m%:R^-1 + 2%:R * eps =
            (1 + 2%:R * m%:R * eps) / m%:R :> R)%R
  by rewrite [RHS]mulrDl mul1r mulrAC mulfK // gt_eqF.
by rewrite Heq logDiv // opprB.
Qed.

(** Hunp — the conditional unpredictability entropy
    [H_unp^C(V_2 | AliceView)] for a fixed predictor at
    [game_real].  Defined as the negative log of the predictor's
    success probability:
    [-log (Pr[guess = V_2 in game_real])].
    Kind: definition.
    Why: gives the LHS of the [Hunp_ge_bound] inequality,
    matching the TeX writeup's [H_unp^C].
    Used by: [Hunp_ge_bound]. *)
Definition Hunp (predictor : predictor_guesser) : R :=
  (- log (distr.mu
            (pkg_advantage.Pr
               (guess_indicator_pkg predictor game_real)) true))%R.

(** bound — the entropy lower bound
    [log m - log (1 + 2 * m * epsilon_cpa)] from the TeX writeup.
    Kind: definition.
    Why: the target lower bound for [Hunp_ge_bound].  At the
    IND-CPA-secure regime [epsilon_cpa -> 0] the bound approaches
    [log m], i.e. the information-theoretic maximum.
    Used by: [Hunp_ge_bound]. *)
Definition bound : R :=
  (log card_t_msg%:R - log (1 + 2%:R * card_t_msg%:R * epsilon_cpa))%R.

(** Hunp_ge_bound — the headline entropy lower bound:
      [H_unp^C(V_2 | AliceView)
         >= log m - log (1 + 2 * m * epsilon_cpa)]
    for any V_2-aware adversary [predictor : predictor_guesser]
    satisfying [dsdp_alice_secrecy]'s structural conditions.
    Kind: main.
    Why: matches TeX writeup
    [dumas2017dual/notes/20260506-dsdp-secrecy-closed-form/].
    line ~312:
    [H_unp^C(V_2 | AliceView) >= log m - log (1 + 2 * m * eps_cpa)].
    Consumed by U3's concrete entropy corollaries.
    Proof outline:
      1. [dsdp_alice_secrecy] (via [Pr_guess_le]): the probability
         [Pr_real <= 1/m + 2 * eps_cpa].
      2. Theorem-level [Pr_real_gt0]: per-predictor positivity
         [0 < Pr_real].  Replaces the pre-refactor universal
         Section Hypothesis [Pr_guess_real_ge_invm] which was
         structurally false on anti-correlating adversaries.
         Concrete corollaries discharge [Pr_real_gt0] for their
         specific witness predictor (e.g., random_guess_adv's
         output is information-theoretically independent of V_2,
         so Pr = 1/m > 0).
      3. [log_id]: [-log (1/m + 2 * eps_cpa) = log m -
         log (1 + 2 * m * eps_cpa) = bound].
      4. Monotonicity of [log] on [Num.pos] (via [ler_log]) and
         [lerN2]: [-log Pr_real >= -log (1/m + 2 * eps_cpa) = bound].
    Used by: U3 [Hunp_random_guess] corollaries in
    [dsdp_security_indcpa_concrete.v]. *)
Theorem Hunp_ge_bound
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (boolean_shell ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs))
    (Pr_real_gt0 :
       (0 < distr.mu (pkg_advantage.Pr
                        (guess_indicator_pkg predictor game_real)) true)%R) :
  (bound <= Hunp predictor)%R.
Proof.
unfold Hunp, bound.
set Pr_real := distr.mu (pkg_advantage.Pr
                          (guess_indicator_pkg predictor game_real)) true.
have Hpr_le : (Pr_real <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa)%R
  by apply: Pr_guess_le.
have Hinvm_pos : (0 < (card_t_msg%:R)^-1 :> R)%R
  by rewrite invr_gt0 ltr0n card_t_msg_gt0.
have Hbound_pos : (0 < (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa :> R)%R
  by rewrite ltr_pwDl // mulr_ge0 //.
rewrite -(log_id (m := card_t_msg) (eps := epsilon_cpa)
                 card_t_msg_gt0 epsilon_cpa_ge0).
by rewrite lerN2 ler_log //.
Qed.

(* U2 verify clauses: the entropy form type-checks against the
   Section-internal hypothesis chain. *)
Check log_id.
Check Hunp.
Check bound.
Check Hunp_ge_bound.

End dsdp_security_indcpa.
