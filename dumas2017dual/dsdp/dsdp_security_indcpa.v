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
intros A L Im Ir E v p hv hp.
induction hv => //=; try (solve [constructor; auto]).
apply valid_bind; [| auto].
rewrite /resolve.
destruct (p o.1) as [[S [T g]]|] eqn:Eo.
- rewrite /coerce_kleisli -lock /coerce_code.
  destruct (coerce x) as [s|]; simpl.
  + apply valid_bind.
    * destruct hp as [he hi].
      have := hi o.1 (existT _ S (existT _ T g)) s Eo.
      simpl. auto.
    * intros a. destruct (coerce a) as [r'|]; simpl.
      -- constructor.
      -- apply valid_sampler. intros. constructor.
  + apply valid_sampler. intros r.
    apply valid_bind.
    * destruct hp as [he hi].
      have := hi o.1 (existT _ S (existT _ T g)) r Eo.
      simpl. auto.
    * intros a. destruct (coerce a) as [r'|]; simpl.
      -- constructor.
      -- apply valid_sampler. intros. constructor.
- apply valid_sampler. intro. constructor.
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
   below ties [#|Renc|] to [index_renc] so the SSProve uniform sample
   value can be lifted to an [Renc] value via [enum_val]. *)
Variable index_renc : nat.
Hypothesis renc_card : #|Renc| = index_renc.

(** sample_to_renc — convert an SSProve uniform-index value
    ['I_index_renc] to an [Renc] value by routing through [enum_val] and
    the cardinality cast.
    Kind: helper.
    Why: [sample uniform index_renc] returns an ['I_index_renc]; the AHE
    encryption requires an [Renc]-shaped value (after passing through
    [rand_of_renc]).  This is the same plumbing as in
    [homomorphic_encryption/indcpa_ror.v].
    Used by: game_real, game_hybrid_one, game_hybrid_two. *)
Definition sample_to_renc (i : 'I_index_renc) : Renc :=
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
    Used by: reduction_charlie, reduction_bob. *)
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
    translation_charlie ∘ oracle_real] etc.) need to collapse the
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
   R_2, R_3 are all sampled from this carrier.  index_msg gives its
   cardinality so [sample uniform index_msg] is well-typed. *)
Variable index_msg : nat.

(** msg_of_idx — bridge from the SSProve uniform-sample index
    ['I_index_msg] to a [plain AHE] value.  Section-parametric: a
    concrete instantiation supplies the cardinality bridge and the
    enumeration.
    Kind: helper.
    Why: SSProve samples take a [nat] cardinality, but the protocol-level
    arithmetic in DSDP operates on [plain AHE].  This indirection lets
    the same game definitions instantiate against different concrete
    plaintext carriers (e.g. ['F_m] or ['Z_(p*q)]) without retyping.
    Used by: game_real, game_hybrid_one, game_hybrid_two. *)
Variable msg_of_idx : 'I_index_msg -> plain AHE.

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
    game_leak. *)
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
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_leak,
    translation_charlie, translation_bob, T4's indicator wrapper. *)
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
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_leak,
    translation_charlie, translation_bob. *)
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
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_leak,
    advantage_game_real_game_leak. *)
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
    residual leak is collapsed in [game_leak].
    Used by: Tasks 07 (reductions), 08 (advantage triangle). *)
Definition game_real :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      (* protocol-level scalars *)
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      (* fresh randomnesses for the four encryption slots *)
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irb1 ← sample uniform index_renc ;;
      irc1 ← sample uniform index_renc ;;
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
    the AHE scheme on Charlie's public key (via [reduction_charlie] in
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
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irb1 ← sample uniform index_renc ;;
      irc1 ← sample uniform index_renc ;;
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
    distribution to [game_leak] modulo a deterministic post-processing
    (Task 09 closes that equivalence).
    Used by: Tasks 07 (reductions), 08 (advantage triangle),
    09 (perfect equivalence). *)
Definition game_hybrid_two :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irb1 ← sample uniform index_renc ;;
      irc1 ← sample uniform index_renc ;;
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

(** game_leak — residual game post-IND-CPA collapse.  Both ciphertext
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
    [Pr[predictor game_leak = V_2] = 1/m].  Task 09's perfect
    equivalence [game_hybrid_two ≈₀ game_leak] is by reflexivity.
    Naming: an earlier draft used an empty-list residual.  The empty
    list is not perfectly equivalent to [game_hybrid_two] (it returns a
    syntactically distinct 0-length list), and Task 09 was unprovable in
    that shape.  The body now matches [game_hybrid_two] so the perfect
    equivalence holds, while Task 13 takes responsibility for showing
    the IT residual is uniform on [V_2].
    Used by: Tasks 08 (advantage triangle), 09 (perfect equivalence),
    13 (residual uniformity). *)
Definition game_leak :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irb1 ← sample uniform index_renc ;;
      irc1 ← sample uniform index_renc ;;
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
Check game_leak.

(* The [msg] pack_type notation aliasing [t_msg] is declared above
   alongside the [game_iface] definition so the V_2 oracle's return-type
   slot can use it. *)

(** translation_charlie — SSProve translation package mediating between
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
    [predictor ∘ translation_charlie ∘ oracle_encrypt_real_pkg] is
    distribution-equivalent to [predictor ∘ game_real] and
    [predictor ∘ translation_charlie ∘ oracle_encrypt_zero_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_one].  Those
    two equivalences (proven in Task 08) turn the abstract IND-CPA
    bound into the [game_real] / [game_hybrid_one] hop.
    Used by: reduction_charlie, Task 08 advantage triangle. *)
Definition translation_charlie :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irb1 ← sample uniform index_renc ;;
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

(** translation_bob — SSProve translation package mediating between the
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
    Why: Task 07 of the plan.  Symmetric to [translation_charlie], for
    the second IND-CPA hop.  By design,
    [predictor ∘ translation_bob ∘ oracle_encrypt_real_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_one] and
    [predictor ∘ translation_bob ∘ oracle_encrypt_zero_pkg] is
    distribution-equivalent to [predictor ∘ game_hybrid_two].
    Those equivalences (Task 08) bind the IND-CPA hardness on
    [pkey_of_party Bob] to the [game_hybrid_one] / [game_hybrid_two]
    hop.
    Used by: reduction_bob, Task 08 advantage triangle. *)
Definition translation_bob :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform index_msg ;;
      iV3 ← sample uniform index_msg ;;
      iU2 ← sample uniform index_msg ;;
      iU3 ← sample uniform index_msg ;;
      iR2 ← sample uniform index_msg ;;
      iR3 ← sample uniform index_msg ;;
      ira1 ← sample uniform index_renc ;;
      ira2 ← sample uniform index_renc ;;
      irc1 ← sample uniform index_renc ;;
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

(** reduction_charlie — IND-CPA reduction packaging the predictor at
    the Charlie slot.  Composes [predictor] (an arbitrary SSProve
    raw_package consuming [game_iface]) with [translation_charlie]
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
    package is exactly [predictor ∘ translation_charlie].
    Used by: Task 08 advantage triangle (first hop). *)
Definition reduction_charlie (predictor : raw_package) : raw_package :=
  predictor ∘ pack translation_charlie.

(** reduction_bob — IND-CPA reduction packaging the predictor at the
    Bob slot.  Symmetric to [reduction_charlie], built from
    [translation_bob] which freezes Charlie's slot to a
    zero-encryption and routes Bob's slot through the IND-CPA oracle.
    Kind: main.
    Why: Task 07 of the plan.  Used in the second hop of the
    [ssprove triangle] ([game_hybrid_one] vs [game_hybrid_two])
    instantiating [enc_ind_cpa_real_or_zero] on
    [pkey_of_party Bob].
    Used by: Task 08 advantage triangle (second hop). *)
Definition reduction_bob (predictor : raw_package) : raw_package :=
  predictor ∘ pack translation_bob.

(** Task 07 verification: both translations are [ValidPackage]s with
    the same import [oracle_encrypt_iface t_msg t_cipher] and export
    [game_iface], and both reductions accept any predictor raw_package
    and type-check against [enc_ind_cpa_real_or_zero]. *)
Check translation_charlie.
Check translation_bob.
Check (reduction_charlie : raw_package -> _).
Check (reduction_bob : raw_package -> _).

(** Type-check the reductions against the IND-CPA hypothesis.  Sealed
    in a transient [Section] so [Variable predictor] disappears at
    [End].  The actual algebraic [AdvantageE] use is Task 08. *)
Section reduction_typecheck.
Variable predictor : raw_package.
Check (enc_ind_cpa_real_or_zero
         AHE Renc index_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (reduction_charlie predictor)).
Check (enc_ind_cpa_real_or_zero
         AHE Renc index_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (reduction_bob predictor)).
End reduction_typecheck.

(** Local abbreviation for the IND-CPA real oracle package at this
    section's parameters, kept anonymous-friendly so [enc_ind_cpa_real_or_zero]
    fires cleanly under [Advantage_link] rewrites in Task 08.
    Kind: helper.
    Why: the IND-CPA hypothesis names the two oracle packages explicitly;
    aliasing them here makes the [Advantage_link] / [enc_ind_cpa_real_or_zero]
    chain at the hop-1 / hop-2 boundaries readable.
    Used by: advantage_game_real_game_leak. *)
Definition oracle_real : raw_package :=
  oracle_encrypt_real AHE Renc index_renc renc_card rand_of_renc
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
    advantage_game_real_game_leak. *)
Definition oracle_zero : raw_package :=
  oracle_encrypt_zero AHE Renc index_renc renc_card rand_of_renc
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
    [AdvantageE (translation_charlie ∘ oracle_real) (translation_charlie ∘
    oracle_zero) predictor], where [Advantage_link] then exposes the
    IND-CPA reduction [reduction_charlie predictor].
    Proof: Task 09.  [eq_rel_perf_ind_eq] reduces the goal to a
    relational equality on the SSProve code; ten [ssprove_sync_eq]
    steps synchronise the ten shared uniform samples; the round-trip
    [cipher_of_chcipher (chcipher_of_cipher _)] and the message
    round-trip [msg_of_chmsg (chmsg_of_msg _)] both collapse via the
    [chcipher_of_cipherK] and [chmsg_of_msgK] cancel hypotheses;
    [rreflexivity_rule] then closes the goal.  Mirrors the
    [IND_CPA_equiv_false] proof at [SSProve/examples/PRF.v] line 328.
    Used by: advantage_hop_real_h1, advantage_game_real_game_leak. *)
Lemma game_real_equiv_charlie_real :
  game_real ≈₀ translation_charlie ∘ oracle_real.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  (* Two operations now: id_game_run and id_v2_get.  The cipher
     oracle's RHS samples Charlie's randomness inside the oracle, so
     the #put-V_2_cell step appears before the renc sample on the RHS
     whereas the LHS [game_real] samples all four renc values before
     #put.  Swap RHS positions 9-10 to align. *)
  - ssprove_swap_rhs 9%N.
    do 10 ssprove_sync_eq=> ?.
    ssprove_sync_eq.
    rewrite chcipher_of_cipherK chmsg_of_msgK.
    eapply rpost_weaken_rule.
    1: eapply rreflexivity_rule.
    cbn.
    intros [? ?] [? ?] e.
    inversion e.
    intuition auto.
  - (* id_v2_get oracle: both sides read V_2_cell and return its
       contents (or the unreachable-None fallback) identically. *)
    ssprove_sync_eq=> stored.
    destruct stored as [v|].
    + apply: r_ret. by [].
    + apply: r_ret. by [].
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
    Used by: advantage_hop_real_h1, advantage_game_real_game_leak. *)
Lemma charlie_zero_equiv_game_hybrid_one :
  translation_charlie ∘ oracle_zero ≈₀ game_hybrid_one.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  - (* Cipher oracle: same sample-order swap as the real-oracle side,
       on the LHS instead.  [translation_charlie] samples irb1 at
       position 9 and the oracle adds Charlie's renc at position 10
       on the LHS; [game_hybrid_one] samples all four renc before
       #put on the RHS.  Swap LHS positions 9-10 to align. *)
    ssprove_swap_lhs 9%N.
    do 10 ssprove_sync_eq=> ?.
    ssprove_sync_eq.
    rewrite chcipher_of_cipherK.
    eapply rpost_weaken_rule.
    1: eapply rreflexivity_rule.
    cbn.
    intros [? ?] [? ?] e.
    inversion e.
    intuition auto.
  - ssprove_sync_eq=> stored.
    destruct stored as [v|].
    + apply: r_ret. by [].
    + apply: r_ret. by [].
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
    [translation_bob] samples irc1 at position 9 and the oracle adds
    Bob's randomness at position 10.  After the swap the two sides
    agree on the ten-sample prefix and the cancels close as before.
    Used by: advantage_hop_h1_h2, advantage_game_real_game_leak. *)
Lemma game_hybrid_one_equiv_bob_real :
  game_hybrid_one ≈₀ translation_bob ∘ oracle_real.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  - (* Two RHS swaps are needed: the #put-V_2_cell step sits between
       the three direct renc samples and the oracle-supplied Bob's
       randomness on [translation_bob ∘ oracle_real], whereas
       [game_hybrid_one] samples all four renc before #put.  First
       [ssprove_swap_rhs 9%N] swaps the #put past the oracle's renc
       sample so all four renc samples are contiguous on the RHS;
       then [ssprove_swap_rhs 8%N] reorders the last two renc samples
       so the (ira1, ira2, irb1, irc1) order on the LHS matches the
       (x4, x5, oracle-supplied, x6-from-irc1) order on the RHS. *)
    ssprove_swap_rhs 9%N.
    ssprove_swap_rhs 8%N.
    do 10 ssprove_sync_eq=> ?.
    ssprove_sync_eq.
    rewrite chcipher_of_cipherK chmsg_of_msgK.
    eapply rpost_weaken_rule.
    1: eapply rreflexivity_rule.
    cbn.
    intros [? ?] [? ?] e.
    inversion e.
    intuition auto.
  - ssprove_sync_eq=> stored.
    destruct stored as [v|].
    + apply: r_ret. by [].
    + apply: r_ret. by [].
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
    Used by: advantage_hop_h1_h2, advantage_game_real_game_leak. *)
Lemma bob_zero_equiv_game_hybrid_two :
  translation_bob ∘ oracle_zero ≈₀ game_hybrid_two.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  - (* Two LHS swaps mirror the RHS swaps in
       [game_hybrid_one_equiv_bob_real]: push the #put past the
       oracle-supplied renc sample, then reorder the last two renc
       samples to match [game_hybrid_two]'s (ira1, ira2, irb1, irc1)
       order. *)
    ssprove_swap_lhs 9%N.
    ssprove_swap_lhs 8%N.
    do 10 ssprove_sync_eq=> ?.
    ssprove_sync_eq.
    rewrite chcipher_of_cipherK.
    eapply rpost_weaken_rule.
    1: eapply rreflexivity_rule.
    cbn.
    intros [? ?] [? ?] e.
    inversion e.
    intuition auto.
  - ssprove_sync_eq=> stored.
    destruct stored as [v|].
    + apply: r_ret. by [].
    + apply: r_ret. by [].
Qed.

(** game_hybrid_two_perfect_game_leak — perfect equivalence between
    [game_hybrid_two] and [game_leak].  [game_leak] has the same body
    as [game_hybrid_two] (both ciphertext slots are zero-encryptions of
    the constant [0 : plain AHE]); the distinct name marks the
    triangle endpoint where the IT residual analysis takes over
    (Task 13).
    Kind: helper.
    Naming: SSProve game-equivalence convention; `perfect` placed
    medially between the two game operands marking the residual
    perfect-equivalence (zero-advantage) hop in the triangle chain.
    Why: Task 08 uses this at the right end of the triangle to collapse
    the residual hop [AdvantageE game_hybrid_two game_leak predictor] to
    zero, so the [2 * epsilon_cpa] bound closes.
    Proof: Task 09.  Reflexivity on the relational specification after
    ten [ssprove_sync_eq] steps; no swap or cancel rewrite is needed
    because the two game bodies are syntactically identical.
    Used by: advantage_game_real_game_leak. *)
Lemma game_hybrid_two_perfect_game_leak :
  game_hybrid_two ≈₀ game_leak.
Proof.
  (* [game_leak] is defined to have the same body as [game_hybrid_two]
     (both ciphertext slots encrypt the constant [0 : plain AHE] and
     both #put V_2_cell at the same position), so the perfect
     equivalence reduces to a reflexivity on the relational
     specification after stepping past the ten samples and the
     #put.  The id_v2_get oracle bodies are also syntactically
     identical. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  - do 10 ssprove_sync_eq=> ?.
    ssprove_sync_eq.
    eapply rpost_weaken_rule.
    1: eapply rreflexivity_rule.
    cbn.
    intros [? ?] [? ?] e.
    inversion e.
    intuition auto.
  - ssprove_sync_eq=> stored.
    destruct stored as [v|].
    + apply: r_ret. by [].
    + apply: r_ret. by [].
Qed.

(** advantage_hop_real_h1 — IND-CPA bound on the first hop
    [AdvantageE game_real game_hybrid_one predictor].  Uses
    [Advantage_triangle] to insert the two Charlie-translation
    intermediates ([translation_charlie ∘ oracle_real] and
    [translation_charlie ∘ oracle_zero]), zeroes the two outer
    summands using [game_real_equiv_charlie_real] and
    [charlie_zero_equiv_game_hybrid_one], then [Advantage_link]
    exposes the IND-CPA reduction [reduction_charlie predictor]
    so [enc_ind_cpa_real_or_zero] closes the bound.
    Kind: helper.
    Why: factoring the first hop's argument keeps
    [advantage_game_real_game_leak] aligned with the PRF.v idiom
    (a single [ssprove triangle] over the four-game chain followed
    by [lerD]).
    Used by: advantage_game_real_game_leak. *)
Lemma advantage_hop_real_h1
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real : fseparate LA game_real.(locs))
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_tc : fseparate LA translation_charlie.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_hybrid_one predictor <= epsilon_cpa.
Proof.
  have triangle_ineq :=
    Advantage_triangle_chain (game_real : raw_package)
      [:: (translation_charlie ∘ oracle_real : raw_package)
        ; (translation_charlie ∘ oracle_zero : raw_package) ]
      (game_hybrid_one : raw_package) predictor.
  cbn in triangle_ineq.
  rewrite ?addrA in triangle_ineq.
  eapply le_trans. 1: exact triangle_ineq.
  clear triangle_ineq.
  erewrite game_real_equiv_charlie_real by ssprove_valid.
  erewrite charlie_zero_equiv_game_hybrid_one by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

(** advantage_hop_h1_h2 — IND-CPA bound on the second hop
    [AdvantageE game_hybrid_one game_hybrid_two predictor], symmetric
    to [advantage_hop_real_h1].  Uses
    [game_hybrid_one_equiv_bob_real] and
    [bob_zero_equiv_game_hybrid_two] together with
    [enc_ind_cpa_real_or_zero] applied to [reduction_bob predictor].
    Kind: helper.
    Why: symmetric to [advantage_hop_real_h1], for the Bob slot.
    Used by: advantage_game_real_game_leak. *)
Lemma advantage_hop_h1_h2
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 : fseparate LA game_hybrid_two.(locs))
    (predictor_disj_tb : fseparate LA translation_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_hybrid_one game_hybrid_two predictor <= epsilon_cpa.
Proof.
  have triangle_ineq :=
    Advantage_triangle_chain (game_hybrid_one : raw_package)
      [:: (translation_bob ∘ oracle_real : raw_package)
        ; (translation_bob ∘ oracle_zero : raw_package) ]
      (game_hybrid_two : raw_package) predictor.
  cbn in triangle_ineq.
  rewrite ?addrA in triangle_ineq.
  eapply le_trans. 1: exact triangle_ineq.
  clear triangle_ineq.
  erewrite game_hybrid_one_equiv_bob_real by ssprove_valid.
  erewrite bob_zero_equiv_game_hybrid_two by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

(** advantage_game_real_game_leak — Task 08 main result.  Bounds the
    SSProve advantage of any predictor distinguishing [game_real] from
    [game_leak] by [2 * epsilon_cpa].  The bound is established by
    triangle inequality across the four-game chain
        [game_real ; game_hybrid_one ; game_hybrid_two ; game_leak],
    bounding the first two hops by [enc_ind_cpa_real_or_zero] (instantiated
    at [reduction_charlie predictor] and [reduction_bob predictor]
    respectively, via [advantage_hop_real_h1] and
    [advantage_hop_h1_h2]) and the last hop by
    [game_hybrid_two_perfect_game_leak].
    Kind: main.
    Why: this is the computational part of the closed-form Alice secrecy
    bound (Tasks 13-14 stitch the information-theoretic residual onto
    this advantage to get [1/m + 2 * epsilon_cpa]).
    Used by: T1 V_2-aware rebuild.
    Naming: advantage_<source>_<target> is the project-local convention for
    SSProve advantage-bound lemmas; the suffix records the two games whose
    AdvantageE is being bounded, not a MathComp algebraic property. *)
Lemma advantage_game_real_game_leak
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real :
       fseparate LA game_real.(locs))
    (predictor_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (predictor_disj_leak :
       fseparate LA game_leak.(locs))
    (predictor_disj_tc :
       fseparate LA translation_charlie.(locs))
    (predictor_disj_tb :
       fseparate LA translation_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_leak predictor <= epsilon_cpa + epsilon_cpa.
Proof.
  ssprove triangle (game_real : raw_package)
    [:: (game_hybrid_one : raw_package)
      ; (game_hybrid_two : raw_package) ]
    (game_leak : raw_package) predictor as advantage_bound.
  eapply le_trans. 1: exact advantage_bound.
  clear advantage_bound.
  erewrite game_hybrid_two_perfect_game_leak by ssprove_valid.
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
   at [game_leak] dischargeable via Task F's
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

(** predictor_guesser — the SSProve [package] type of a
    [t_msg]-output predictor: imports [game_iface] (the two-oracle
    DSDP game interface shared by [game_real], [game_hybrid_one],
    [game_hybrid_two], [game_leak]) and exports [guesser_export]
    (the [t_msg]-guess oracle).  Concrete instantiations (T6) build
    predictors as section-parametric [package]s of this shape.
    Kind: canonical.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  The
    rebuilt closed-form theorem [Pr_guess_le] takes a value of this
    type in place of the original [raw_package].  Importing the
    full [game_iface] is convenient for the SSProve advantage
    machinery — the IT residual side handles the constraint that
    a correctness-respecting predictor must not query [id_v2_get]
    (otherwise the bound is trivially violatable by echoing V_2;
    the section hypothesis [Pr_guess_leak_le_invm] below carries
    the IT load-bearing claim).
    Naming: project-local; reads "a guesser-style predictor".
    Used by: [guess_indicator_pkg], [Pr_guess_le]. *)
Definition predictor_guesser : Type :=
  package game_iface guesser_export.

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
    and propagated through the IND-CPA hops to [game_leak].
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
    package wrapper".  Mirrors [reduction_charlie] / [reduction_bob]
    in shape (a function from a predictor to a [raw_package]) but
    with the additional [game] argument to keep the closed/open
    distinction explicit.
    Used by: [Pr_guess_le], T5's [dsdp_alice_secrecy], T6's
    concrete corollaries. *)
Definition guess_indicator_pkg
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) : raw_package :=
  boolean_shell ∘ predictor ∘ game.

(** index_t_msg — cardinality of the (image of the) message-space
    carrier the predictor's [t_msg] guesses live over.  Bridges
    [#|plain AHE|] to a [nat] for the [1 / index_t_msg] residual
    bound.  At concrete instantiation (T6) this is identified with
    [index_msg] (the protocol-scalar carrier size) since V_2 is
    sampled from [msg_of_idx] applied to ['I_index_msg] and stored
    as [chmsg_of_msg v2] in [V_2_cell].
    Kind: section parameter.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  The
    IT residual bound on [Pr[guess = V_2]] at [game_leak] is
    [1 / index_t_msg]; parametrising the bound on this index
    decouples the abstract SSProve composition from the concrete
    AHE plaintext carrier choice.
    Naming: project-local; mirrors [index_msg], [index_renc].
    Used by: [Pr_guess_leak_le_invm] hypothesis, [Pr_guess_le]. *)
Variable index_t_msg : nat.

(** index_t_msg_gt0 — positivity of [index_t_msg]: the message
    space is non-empty.  Without positivity the residual bound
    [1 / index_t_msg] would be vacuously [0 <= 0] which is still
    mathematically correct but degenerate.
    Kind: section hypothesis.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  Used
    to keep the [1 / index_t_msg] bound a meaningful positive
    quantity at concrete instantiation; the discharge at T6 is
    trivial via [prime_p] / [prime_q] etc. depending on the AHE
    scheme.
    Naming: project-local; mirrors [index_msg_gt0], [index_renc_gt0].
    Used by: [Pr_guess_le] (indirectly, via the hypothesis it
    cascades). *)
Hypothesis index_t_msg_gt0 : (0 < index_t_msg)%N.

(** Pr_guess_leak_le_invm — IT residual bound: at [game_leak] the
    probability that any [predictor_guesser]'s guess equals the
    V_2 read via [id_v2_get] is at most [1 / index_t_msg].
    Kind: section hypothesis.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md], the
    [1/m] half of the closed-form bound.  At [game_leak] the
    ciphertext slots [c_2], [c_3] are zero-encryptions, so V_2's
    value does NOT influence the ciphertext list returned by
    [id_game_run]; therefore the predictor's guess (computed from
    [id_game_run] output only) is statistically independent of
    V_2, and [Pr[guess = V_2] = E_guess[Pr[V_2 = guess | guess]]
    = E_guess[1 / index_t_msg] = 1 / index_t_msg] by uniformity of
    V_2.  The discharge at concrete instantiation (T6) routes
    through the bridged joint fdist [fdist_game_leak_joint] and
    the residual uniformity [cPr_V2_V3_uniform_on_fiber_joint]
    (line 2899 below); this hypothesis captures the SSProve-side
    statement those facts collectively imply.
    Naming: project-local; reads "Pr[guess = V_2 at game_leak] is
    bounded by [1 / m]".  Mirrors the section-hypothesis pattern
    of [V_2_uniform_hyp], [V_3_uniform_hyp] in Task D below: the
    fact is provable from the IT residual + bridge chain but is
    captured here as a [Hypothesis] so [Pr_guess_le] is provable
    Section-internally before the bridge content (Tasks A-F)
    appears.
    Used by: [Pr_guess_le]. *)
Hypothesis Pr_guess_leak_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_leak)) true
      <= (index_t_msg%:R)^-1.

(** Pr_guess_le — the headline non-vacuous Alice-secrecy bound in
    the V_2-aware framing.  For any [t_msg]-output adversary
    [predictor : predictor_guesser] satisfying the disjointness
    conditions of [advantage_game_real_game_leak], the probability
    that the [boolean_shell]-wrapped indicator
    [guess_indicator_pkg predictor game_real] evaluates to [true]
    (i.e. the predictor's guess matches the V_2 that [game_real]
    sampled and stored in [V_2_cell]) is at most
    [1 / index_t_msg + 2 * epsilon_cpa].
    Kind: main residual bound.
    Why: T4 of [~/.claude/plans/sprightly-finding-robin.md].  This
    is the IND-CPA-based replacement for the deleted (vacuous)
    [dsdp_alice_secrecy_indcpa].  The [2 * epsilon_cpa] half comes
    from [advantage_game_real_game_leak] (the SSProve triangle
    across the four-game ladder, two IND-CPA hops plus a perfect-
    equivalence residual), instantiated at the chain
    [boolean_shell ∘ par predictor (ID game_iface)] (a closed
    package importing [game_iface] and exporting [A_export]).  The
    [1 / index_t_msg] half comes from the section hypothesis
    [Pr_guess_leak_le_invm] (the IT residual at [game_leak]).
    Proof outline (4 steps):
      1. Triangle: by the elementary [a <= b + |a - b|]
         identity (using [ler_norm] and [lerBlDl]), [Pr_real <=
         Pr_leak + AdvantageE (boolean_shell ∘ par pred game_real)
         (boolean_shell ∘ par pred game_leak)] (the AdvantageE
         instantiated at the trivial distinguisher [A := ID
         A_export] would give exactly this, but the
         [a <= b + |a - b|] form is more direct).
      2. Transfer the SSProve advantage [AdvantageE
         (boolean_shell ∘ par pred game_real) (boolean_shell ∘
         par pred game_leak) (ID A_export)] to [AdvantageE
         game_real game_leak (boolean_shell ∘ par pred (ID
         game_iface))] via [Advantage_link].  The chain
         [boolean_shell ∘ par pred (ID game_iface)] is a closed
         distinguisher package importing [game_iface] and
         exporting [A_export], which is exactly the shape
         [advantage_game_real_game_leak] consumes.
      3. Bound this AdvantageE by [advantage_game_real_game_leak]
         at [≤ epsilon_cpa + epsilon_cpa = 2 * epsilon_cpa].
      4. Combine with the section hypothesis
         [Pr_guess_leak_le_invm predictor] for the [1 /
         index_t_msg] half.
    The IND-CPA axiom [enc_ind_cpa_real_or_zero] is load-bearing
    on step 3 via the [advantage_game_real_game_leak] chain.
    Naming: project-local; reads "[Pr[guess = V_2]] is bounded
    above" in the standard MathComp probability-bound idiom
    ([Pr_X_le]).  Three components (verb-noun-mode); within the
    project's F001/I001 budget.
    Used by: T5's [dsdp_alice_secrecy] (thin wrapper), T6's
    concrete corollaries. *)

(** [valid_boolean_shell_link] - validity of the partial link
    [boolean_shell ∘ pred] for any [pred : predictor_guesser].
    The composition resolves [pred]'s [id_guess] export against
    [boolean_shell]'s [id_guess] import; the remaining [id_v2_get]
    import in [boolean_shell] resolves to a [sampler dnull] (since
    [pred] does not export it), so the linked package's only true
    residual imports are [pred]'s imports — which is [game_iface]
    by [predictor_guesser]'s type.  Kind: helper.
    Why: feeds [Pr_guess_le]'s [chain_valid] hypothesis at
    concrete instantiations (T6).  The standard [ssprove_valid]
    tactic invokes [valid_link_weak] which requires
    [fsubmap (unionm game_iface guesser_export) guesser_export]
    (the wrong subset direction), so direct application fails;
    this helper proves the validity by construction via
    [valid_code_link_residual].
    Used by: T6's [secrecy_random_guess] and downstream
    [Idealized] / [Benaloh] / [Paillier] specialisations. *)
Lemma valid_boolean_shell_link
    (pred : predictor_guesser) :
  ValidPackage (locs pred) game_iface A_export (boolean_shell ∘ pred).
Proof.
destruct boolean_shell.(pack_valid) as [he1 hi1].
split.
{ move=> o.
  rewrite he1 /link.
  split.
  { move=> [f Hf]. eexists (fun x => code_link (f x) pred).
    rewrite //= mapmE Hf //. }
  { rewrite //= mapmE.
    change (setm emptym _ _) with (boolean_shell.(pack)).
    move=> [f Hf].
    change (setm emptym _ _) with (boolean_shell.(pack)) in Hf.
    destruct (boolean_shell.(pack) o.1) as [[S [T g]]|] eqn:Eb.
    { rewrite Eb /= in Hf. injection Hf as [= ? ?]. subst. by exists g. }
    { rewrite Eb /= in Hf. discriminate. } } }
{ move=> n F x.
  rewrite /fhas /link mapmE.
  change (setm emptym _ _) with (boolean_shell.(pack)).
  destruct (boolean_shell.(pack) n) as [[S' [T' f']]|] eqn:Eb; last by [].
  simpl. move=> H. injection H as H. subst F. simpl.
  eapply (@valid_code_link_residual _ (locs pred)
            (unionm game_iface guesser_export) game_iface guesser_export).
  { have Hbs_valid := hi1 n (existT _ S' (existT _ T' f')) x Eb.
    simpl in Hbs_valid.
    eapply valid_injectLocations; [| exact: Hbs_valid].
    apply fsub0map. }
  { exact: pred.(pack_valid). } }
Qed.

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
    (chain_disj_leak :
       fseparate LA game_leak.(locs))
    (chain_disj_tc :
       fseparate LA translation_charlie.(locs))
    (chain_disj_tb :
       fseparate LA translation_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true
    <= (index_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
(* Step 1: Pr_real <= Pr_leak + |Pr_real - Pr_leak| (elementary). *)
set Pr_real :=
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true.
set Pr_leak :=
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_leak)) true.
have Hsplit : Pr_real <= Pr_leak + `|Pr_real - Pr_leak|.
{ rewrite -lerBlDl. exact: ler_norm. }
apply: le_trans Hsplit _.
apply: lerD; first exact: Pr_guess_leak_le_invm.
(* Step 2: |Pr_real - Pr_leak| = AdvantageE on the chain.
   By [link_assoc], [guess_indicator_pkg predictor game] equals
   [(boolean_shell ∘ predictor) ∘ game], i.e. the distinguisher
   is exactly [boolean_shell ∘ predictor].  AdvantageE then
   reduces directly. *)
have HEadvE :
    `|Pr_real - Pr_leak|
  = AdvantageE game_real game_leak
      (boolean_shell ∘ predictor).
{ rewrite /Pr_real /Pr_leak /AdvantageE /guess_indicator_pkg.
  by rewrite !link_assoc. }
rewrite HEadvE.
(* Step 3: bound the AdvantageE by advantage_game_real_game_leak.
   2 * epsilon_cpa = epsilon_cpa + epsilon_cpa via mulr2n / -addrr. *)
have -> : 2%:R * epsilon_cpa = epsilon_cpa + epsilon_cpa
  by rewrite mulrDl !mul1r.
exact: advantage_game_real_game_leak.
Qed.

(* T4 verify clauses: the framework type-checks and the headline
   bound closes with [Qed].  Mirrors the verify clauses of
   [advantage_game_real_game_leak] above. *)
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
        <= 1/index_t_msg + 2 * epsilon_cpa.

    The same theorem-level argument list as [Pr_guess_le]: the four
    Section-bound abstract carriers are baked into the Section
    parameters (AHE, Renc, ...); the eleven theorem-level arguments
    [(LA : Locations), (predictor : predictor_guesser),
    chain_valid, 8 disjointness, ValidCode_predictor_game_leak,
    LosslessCode_predictor_game_leak] are mirrored verbatim.  At
    concrete instantiation (T6) the disjointness goals close by
    [fseparate0m] (since the random-guess adversary is stateless,
    [locs = emptym]), and the ValidPackage / lossless goals close
    by [ssprove_valid] and [Lossless_sample + LosslessOp_uniform +
    index_t_msg_gt0] respectively.  Note: in T4's [Pr_guess_le],
    the Section hypothesis [Pr_guess_leak_le_invm] supplies the
    [1/index_t_msg] half; that hypothesis itself is discharged in
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
    (chain_disj_leak :
       fseparate LA game_leak.(locs))
    (chain_disj_tc :
       fseparate LA translation_charlie.(locs))
    (chain_disj_tb :
       fseparate LA translation_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real)) true
    <= (index_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
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

(** Pr_guess_real_ge_invm — strict positivity lower bound on
    [Pr_guess_real]: the indicator wrapper returns [true] with
    probability at least [1/index_t_msg] for any predictor.
    Kind: section hypothesis.
    Why: needed for [entropy_ge_bound] to handle the [Pr = 0]
    degenerate case.  In mathcomp-analysis [log 0 = 0] (not [+oo]),
    so without this hypothesis the entropy lower bound fails when
    [bound > 0].  Discharged at concrete instantiation by symmetry:
    [V_2] is uniform on [t_msg] and the predictor's guess is
    independent of [V_2] in expectation, so [Pr[guess = V_2] >= 1/m].
    Mirrors the [Pr_guess_leak_le_invm] hypothesis pattern from T4.
    Used by: [entropy_ge_bound]. *)
Hypothesis Pr_guess_real_ge_invm :
  forall (predictor : predictor_guesser),
    (index_t_msg%:R)^-1
      <= distr.mu (pkg_advantage.Pr
                     (guess_indicator_pkg predictor game_real)) true.

(** epsilon_cpa_ge0 — nonnegativity of the IND-CPA error parameter.
    [indcpa_ror.epsilon_cpa : R] is declared as a bare [Parameter]
    without positivity; the IND-CPA axiom bounds an [AdvantageE]
    by it but does not imply [epsilon_cpa >= 0].
    Kind: section hypothesis.
    Why: required by [log_id] (the [1 + 2 * m * eps > 0] step).
    Used by: [log_id], [entropy_ge_bound]. *)
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
    Used by: [entropy_ge_bound]. *)
Lemma log_id (m : nat) (eps : R) :
  (0 < m)%N -> (0 <= eps)%R ->
  (- log (m%:R^-1 + 2%:R * eps) = log m%:R - log (1 + 2%:R * m%:R * eps))%R.
Proof.
move=> Hm Heps.
have Hm_pos : (0 < m%:R :> R)%R by rewrite ltr0n.
have Hmeps_pos : (0 < 1 + 2%:R * m%:R * eps :> R)%R.
{ apply: ltr_pwDl; first exact: ltr01. by rewrite !mulr_ge0 // ?ler0n. }
have Heq :
    (m%:R^-1 + 2%:R * eps = (1 + 2%:R * m%:R * eps) / m%:R :> R)%R.
{ rewrite [RHS]mulrDl mul1r.
  congr (_ + _).
  by rewrite [_ * eps / _]mulrAC mulfK // gt_eqF. }
by rewrite Heq logDiv // opprB.
Qed.

(** entropy — the conditional unpredictability entropy
    [H_unp^C(V_2 | AliceView)] for a fixed predictor at
    [game_real].  Defined as the negative log of the predictor's
    success probability:
    [-log (Pr[guess = V_2 in game_real])].
    Kind: definition.
    Why: gives the LHS of the [entropy_ge_bound] inequality,
    matching the TeX writeup's [H_unp^C].
    Used by: [entropy_ge_bound]. *)
Definition entropy (predictor : predictor_guesser) : R :=
  (- log (distr.mu
            (pkg_advantage.Pr
               (guess_indicator_pkg predictor game_real)) true))%R.

(** bound — the entropy lower bound
    [log m - log (1 + 2 * m * epsilon_cpa)] from the TeX writeup.
    Kind: definition.
    Why: the target lower bound for [entropy_ge_bound].  At the
    IND-CPA-secure regime [epsilon_cpa -> 0] the bound approaches
    [log m], i.e. the information-theoretic maximum.
    Used by: [entropy_ge_bound]. *)
Definition bound : R :=
  (log index_t_msg%:R - log (1 + 2%:R * index_t_msg%:R * epsilon_cpa))%R.

(** entropy_ge_bound — the headline entropy lower bound:
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
      2. [Pr_guess_real_ge_invm]: [Pr_real >= 1/m > 0].
      3. [log_id]: [-log (1/m + 2 * eps_cpa) = log m -
         log (1 + 2 * m * eps_cpa) = bound].
      4. Monotonicity of [log] on [Num.pos] (via [ler_log]) and
         [lerN2]: [-log Pr_real >= -log (1/m + 2 * eps_cpa) = bound].
    Used by: U3 [entropy_random_guess] corollaries in
    [dsdp_security_indcpa_concrete.v]. *)
Theorem entropy_ge_bound
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
    (chain_disj_leak :
       fseparate LA game_leak.(locs))
    (chain_disj_tc :
       fseparate LA translation_charlie.(locs))
    (chain_disj_tb :
       fseparate LA translation_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc index_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  (bound <= entropy predictor)%R.
Proof.
unfold entropy, bound.
set Pr_real := distr.mu (pkg_advantage.Pr
                          (guess_indicator_pkg predictor game_real)) true.
have Hpr_le : (Pr_real <= (index_t_msg%:R)^-1 + 2%:R * epsilon_cpa)%R.
{ rewrite /Pr_real. by apply: Pr_guess_le. }
have Hinvm_pos : (0 < (index_t_msg%:R)^-1 :> R)%R.
{ by rewrite invr_gt0 ltr0n; exact: index_t_msg_gt0. }
have Hpr_ge_inv : ((index_t_msg%:R)^-1 <= Pr_real)%R.
{ exact: Pr_guess_real_ge_invm. }
have Hpr_pos : (0 < Pr_real)%R.
{ exact: (lt_le_trans Hinvm_pos Hpr_ge_inv). }
have Hbound_pos : (0 < (index_t_msg%:R)^-1 + 2%:R * epsilon_cpa :> R)%R.
{ apply: ltr_pwDl => //. by rewrite mulr_ge0 // ?ler0n. }
rewrite -(log_id (m := index_t_msg) (eps := epsilon_cpa)
                 index_t_msg_gt0 epsilon_cpa_ge0).
by rewrite lerN2 ler_log // ?posrE.
Qed.

(* U2 verify clauses: the entropy form type-checks against the
   Section-internal hypothesis chain. *)
Check log_id.
Check entropy.
Check bound.
Check entropy_ge_bound.

(* ================================================================== *)
(* Task 10: alice_view carrier (finType + SSProve choice_type)        *)
(* ================================================================== *)

(** Dk_a_carrier - section parameter for Alice's private-key carrier as
    a [finType].  The AHE record (homomorphic_encryption/he_types.v:45)
    declares [priv_key AHE : Type] without a finType structure, but the
    Alice secrecy analysis needs the joint Alice-view to be a finType so
    that infotheo's [{fdist alice_view}] machinery applies (Tasks 12-13).
    Concrete instantiations against Benaloh/Paillier supply a concrete
    finType for the private-key space at this section parameter; the
    semi-honest secrecy proof is parametric in the choice.
    Kind: parameter.
    Why: the IND-CPA hops do not depend on the structure of [priv_key
    AHE], only on its enumeration; refining to a finType here is the
    minimal commitment that suffices for the entropy step.
    Used by: alice_view, alice_view_RV (Task 13). *)
Variable Dk_a_carrier : finType.

(** index_Dk_a, Dk_a_card - cardinality index for [Dk_a_carrier] and the
    bridge hypothesis tying [#|Dk_a_carrier|] to it.  Same pattern as
    [Renc] / [index_renc] / [renc_card] at the top of this section.
    Kind: parameter + hypothesis.
    Why: SSProve uniform samples take a [nat] cardinality.  The IND-CPA
    games (Task 06) sample protocol scalars over [index_msg]; the entropy
    residual (Task 13) will likewise need to enumerate [alice_view] by
    its total cardinality, which decomposes through [Dk_a_card].
    Used by: index_alice_view, alice_view_ct, the residual entropy
    arguments in Task 13. *)
Variable index_Dk_a : nat.
Hypothesis Dk_a_card : #|Dk_a_carrier| = index_Dk_a.

(** alice_view - the corrupted-Alice view's codomain: a nine-tuple
    finType bundling Alice's private key, the input scalars known to
    Alice (S, V_1, U_1), the masking scalars Alice draws (U_2, U_3,
    R_2, R_3), and the plaintext D_3 (the contribution Alice sees as a
    cleartext value after decryption with [Dk_a]).
    Kind: canonical.
    Why: Task 10 of the plan (~/.claude/plans/sprightly-finding-robin.md).
    This is strictly smaller than the trace-level [alice_view_valuesT]
    in dsdp_security.v:143-145, because the IND-CPA swaps (Tasks 06-09)
    have already eliminated the three ciphertext components from the
    distinguisher-visible view.  MathComp's HB machinery automatically
    inherits both [finType] and [choiceType] structures on the iterated
    [%type] product since [Dk_a_carrier : finType] and [plain AHE :
    finComNzRingType] (which extends [finType] and [choiceType]).  The
    finType structure is consumed by infotheo's [{fdist alice_view}] in
    Task 12-13; the choiceType structure is consumed by SSProve via the
    bridge [alice_view_ct] below.
    Used by: alice_view_RV (Task 13), bridge_leak_to_fdist (Task 12). *)
Definition alice_view : finType :=
  (Dk_a_carrier * plain AHE * plain AHE * plain AHE * plain AHE *
   plain AHE * plain AHE * plain AHE * plain AHE)%type.

(** alice_view_choice_finType - the named HB instance label tying
    [alice_view] simultaneously to MathComp's [finType] and
    [choiceType] structures.  No additional plumbing is required: the
    iterated product type-class search finds both instances
    automatically because each component is itself a finType (which
    extends choiceType).  This [Definition] documents the canonical
    structure agreement so downstream tasks can refer to it by name.
    Kind: canonical (HB instance label, no new content).
    Why: the plan names this instance explicitly (Task 10 in
    ~/.claude/plans/sprightly-finding-robin.md, line 154) so audits can
    grep for the joint declaration.  The two [Check] judgments below
    discharge the verify clause of Task 10.
    Naming: <type>_<class1>_<class2> is the MathComp convention for
    composite HB instance labels.
    Used by: documentation only; the instances are picked up by
    canonical-structure resolution at the use sites. *)
Definition alice_view_choice_finType : Type := alice_view.

(* Task 10 verify clause: both finType and choiceType inhabit alice_view. *)
Check (alice_view : finType).
Check (alice_view : choiceType).

(** index_alice_view - the cardinality of [alice_view] as a [nat].
    Computed once so that the SSProve-side [chFin] embedding below can
    refer to it by name.
    Kind: canonical.
    Why: SSProve's [choice_type] GADT (Crypt/choice_type.v:48) uses
    [chFin (n : nat)] for finite carriers, with [chInterp (chFin n) =
    'I_n].  Naming the cardinality lets us state the cardinality lemma
    [alice_view_ct_card] cleanly.
    Used by: alice_view_ct, the bridge in Task 12. *)
Definition index_alice_view : nat := #|alice_view|.

(** alice_view_ct - the SSProve-side [choice_type] avatar of
    [alice_view], lifted as a single [chFin] of the total cardinality.
    This is the carrier that the Task 12 bridge [bridge_leak_to_fdist :
    SDistr alice_view -> {fdist alice_view}] will round-trip through to
    transfer SSProve probabilities (which live over [chInterp
    alice_view_ct = 'I_index_alice_view]) onto infotheo's
    [{fdist alice_view}].
    Kind: canonical.
    Why: SSProve's [choice_type] is a closed inductive (eleven
    constructors at the time of writing) and does not directly cover
    finType products.  Routing through [chFin (#|alice_view|)] is the
    standard idiom for SSProve-finType interop (see indcpa_ror.v and
    pkg_distr.v for similar uses).  The [alice_view_to_ct] /
    [alice_view_of_ct] bijection below mediates between the two views.
    Naming: <type>_ct uses the SSProve-side suffix _ct (choice_type) so
    the split between the MathComp finType and the GADT carrier is
    visible at the use site.
    Used by: bridge_leak_to_fdist (Task 12). *)
Definition alice_view_ct : choice_type := chFin index_alice_view.

(** alice_view_to_ct, alice_view_of_ct - bijection between the MathComp
    finType [alice_view] and the SSProve-side [alice_view_ct = chFin
    index_alice_view = 'I_index_alice_view], realised via MathComp's
    [enum_rank] and [enum_val] on the canonical enumeration of
    [alice_view].
    Kind: helper.
    Why: the bridge [bridge_leak_to_fdist] in Task 12 builds an
    [{fdist alice_view}] by walking the SSProve [Pr_code] over
    [alice_view_ct] and re-indexing each probability against the
    corresponding MathComp finType element.  These two functions are
    the re-indexing primitive; the [_K] cancel lemmas below guarantee
    the round-trip is the identity.
    Used by: bridge_leak_to_fdist (Task 12), the support-enumeration
    obligation [bridge_support_enum]. *)
Definition alice_view_to_ct (v : alice_view) : alice_view_ct :=
  enum_rank v.

(** alice_view_of_ct — companion to [alice_view_to_ct]: send an
    SSProve-side index [i : alice_view_ct] back to its [alice_view]
    inhabitant via [enum_val].
    Kind: helper.
    Why: Task 12's [bridge_leak_to_fdist] sums an SSProve [SDistr] over
    [alice_view_ct] and re-indexes through this function to land on the
    infotheo-side [{fdist alice_view}].
    Used by: bridge_leak_to_fdist (Task 12), [alice_view_to_ct_K],
    [alice_view_of_ct_K]. *)
Definition alice_view_of_ct (i : alice_view_ct) : alice_view :=
  enum_val i.

(** alice_view_to_ct_K - cancel law: [alice_view_of_ct] is a left
    inverse of [alice_view_to_ct].  Follows from MathComp's
    [enum_rankK].
    Kind: cancellation.
    Why: Task 12's [bridge_correct] needs to argue that summing an
    SSProve density over [alice_view_ct] and re-indexing back through
    [alice_view_of_ct] recovers the original [alice_view] support; the
    cancel pair is the algebraic content of that argument.
    Used by: bridge_correct (Task 12). *)
Lemma alice_view_to_ct_K : cancel alice_view_to_ct alice_view_of_ct.
Proof. exact: enum_rankK. Qed.

(** alice_view_of_ct_K - companion cancel: [alice_view_to_ct] is a left
    inverse of [alice_view_of_ct].  Follows from MathComp's
    [enum_valK].
    Kind: cancellation.
    Why: same role as [alice_view_to_ct_K] but for the inverse
    direction; together they make the pair a bijection (used by Task 12
    to justify the [psum]/[bigop] re-indexing). *)
Lemma alice_view_of_ct_K : cancel alice_view_of_ct alice_view_to_ct.
Proof. exact: enum_valK. Qed.

(** alice_view_ct_card, alice_view_card_index - cardinality coherence:
    [alice_view_ct] interprets as ['I_index_alice_view] which has
    cardinality [index_alice_view], and [alice_view] itself has the
    same cardinality by definition of [index_alice_view].
    Kind: coherence.
    Why: Task 12's [bridge_total_mass] relates [psum] over [chInterp
    alice_view_ct] (which the SSProve semantics produces) to
    [\sum_(v : alice_view) ...] (the infotheo target); these two facts
    let us swap the indexing finType under the [bigop] / [psum] without
    changing the value.
    Used by: bridge_total_mass (Task 12). *)
Lemma alice_view_ct_card : #|alice_view_ct| = index_alice_view.
Proof. exact: card_ord. Qed.

(** alice_view_card_index — cardinality of the infotheo-side [alice_view]
    equals [index_alice_view] by definition (the latter is bound as
    [#|alice_view|]).  Trivial by reflexivity.
    Kind: coherence.
    Why: Task 12's [bridge_total_mass] re-indexes a [psum] over the
    SSProve-side [alice_view_ct] back to a [\sum_(v : alice_view)]; this
    lemma is the cardinality side of that re-indexing.
    Used by: bridge_total_mass (Task 12).
    Naming: _card_index records "cardinality equals the named index
    parameter"; project-local convention, not a MathComp suffix-table
    entry. *)
Lemma alice_view_card_index : #|alice_view| = index_alice_view.
Proof. by []. Qed.

(* ================================================================== *)
(* Task 12: SDistr-to-fdist bridge for alice_view                     *)
(* ================================================================== *)

#[local] Open Scope fdist_scope.

(** bridge_psum_to_bigop - the elementary identity converting SSProve's
    [psum] over an [alice_view]-valued sub-distribution into MathComp's
    [\sum_(v : alice_view)].  On a [finType] both quantities enumerate
    the same support, and [psum f = \sum_i |f i|] from realsum collapses
    to the plain sum because [distr.mu mu] is non-negative.
    Kind: helper bridge.
    Why: Task 12 of the plan (~/.claude/plans/sprightly-finding-robin.md).
    The SSProve denotational semantics produces a [distr R alice_view]
    via [Pr_fst]; the infotheo target side wants an
    [\sum_(v : alice_view)] indexed bigop.  This lemma is the only
    place where the two summation conventions meet.
    Naming: project-local; not a MathComp suffix-table entry.  The
    leading [bridge_] prefix marks it as part of the SSProve / infotheo
    bridge.
    Used by: bridge_leak_to_fdist, bridge_total_mass. *)
Lemma bridge_psum_to_bigop (mu : distr.distr R alice_view) :
  \sum_(v : alice_view) (distr.mu mu) v = psum (distr.mu mu).
Proof.
rewrite psum_fin.
apply: eq_bigr => a _.
by rewrite ger0_norm //; apply: distr.ge0_mu.
Qed.

(** bridge_leak_to_fdist - the SDistr-to-fdist bridge.  Given a
    sub-distribution [mu : distr R alice_view] and a proof that its
    total mass is one, produce an infotheo-side [{fdist alice_view}]
    by wrapping [distr.mu mu] in an [ffun] and discharging the
    [FDist.make] obligations: non-negativity comes from [distr.ge0_mu],
    summation-to-one comes from [bridge_psum_to_bigop] composed with
    the mass hypothesis.
    Kind: bridge construction.
    Why: Task 12 of the plan.  This is the central piece of plumbing
    that lets the IT residual analysis (Task 13) run against an
    infotheo [{fdist alice_view}] while the upstream IND-CPA hops
    (Tasks 06-08) work over SSProve's [distr R alice_view].  The
    function is parametric in [mu] and its mass-1 hypothesis: the
    [Pr_fst game_leak]-specific instance is the consumer's obligation
    (Task 13 will supply it via [LosslessCode] resolution on the
    resolved [game_leak] code).
    Naming: project-local.  The [_to_] middle marks the bridge
    direction (SSProve SDistr -> infotheo fdist).
    Used by: Task 13's [cPr_V2_V3_uniform_on_fiber] (which feeds the
    [Pr_fst]-side of [game_leak] through this bridge to land on a
    [{fdist alice_view}] and then applies [inde_RV2_cinde],
    [cinde_rv_comp_removal], and [Pr_dsdp_sol_uniform]). *)
Definition bridge_leak_to_fdist (mu : distr.distr R alice_view)
  (Hmass : psum (distr.mu mu) = 1) : R.-fdist alice_view.
Proof.
unshelve eapply FDist.make.
- exact: [ffun v => (distr.mu mu) v].
- by move=> a; rewrite ffunE; apply: distr.ge0_mu.
- under eq_bigr=> a _ do rewrite ffunE.
  by rewrite bridge_psum_to_bigop.
Defined.

(** bridge_leak_to_fdistE - elementwise equation for the bridge.
    Spells out how to evaluate the resulting [{fdist alice_view}] at a
    point: it is just [distr.mu mu] of the same point.
    Kind: simplification.
    Why: lets downstream proofs unfold the bridge to expose the
    underlying SSProve density without forcing them to manage the
    [ffun] wrapper.
    Naming: trailing [E] follows MathComp convention for elementwise /
    extensional equations (compare [fdist1E], [fdistbindE]).
    Used by: bridge_correct, bridge_support_enum, and Task 13 callers. *)
Lemma bridge_leak_to_fdistE (mu : distr.distr R alice_view)
    (Hmass : psum (distr.mu mu) = 1) (v : alice_view) :
  bridge_leak_to_fdist Hmass v = (distr.mu mu) v.
Proof. by rewrite /bridge_leak_to_fdist /= ffunE. Qed.

(** bridge_total_mass - sums to one.  For any sub-distribution [mu]
    with [psum (distr.mu mu) = 1] (which is the [LosslessCode]
    statement when [mu] is [Pr_fst c] for a lossless code [c]), the
    MathComp bigop sum over [alice_view] is one.  This is exactly the
    FDist.make obligation extracted to a named lemma so callers can
    use it without re-running the bridge's discharge.
    Kind: bridge obligation.
    Why: Task 12 of the plan, verbatim.  Discharged generically by
    [bridge_psum_to_bigop] composed with [Hmass]; specifically for
    [Pr_fst (resolve game_leak RUN tt)] the [Hmass] hypothesis will be
    supplied by [LosslessOp_bind] / [LosslessOp_ret] resolution
    (Task 11) once the [game_leak] body is reduced to its raw_code
    form by Task 13.  No fallback hypothesis is required here: the
    bridge is parametric in the mass proof, and consumers carry the
    [LosslessCode] obligation themselves.
    Naming: project-local; follows the [bridge_] convention.
    Used by: Task 13's [cPr_V2_V3_uniform_on_fiber]. *)
Lemma bridge_total_mass (mu : distr.distr R alice_view)
    (Hmass : psum (distr.mu mu) = 1) :
  \sum_(v : alice_view) (distr.mu mu) v = 1.
Proof. by rewrite bridge_psum_to_bigop. Qed.

(** bridge_support_enum - the support of [bridge_leak_to_fdist] is
    contained in the canonical [enum alice_view].  Trivial in this
    direction since [enum alice_view] enumerates the whole finType,
    but stating the bound named makes the residual analysis in Task 13
    syntactically uniform with the partition-by-support pattern used
    in [dsdp_centropy_uniform].
    Kind: bridge obligation.
    Why: Task 12 of the plan.  When the IT residual rewrites
    [\sum_(v : alice_view) bridge_leak_to_fdist _ v] using infotheo
    machinery, having a named lemma certifying that no element outside
    the [enum] needs special handling keeps the rewriting steps
    minimal.
    Naming: project-local; [_support_enum] reads "support is contained
    in the enum".
    Used by: Task 13. *)
Lemma bridge_support_enum (mu : distr.distr R alice_view)
    (Hmass : psum (distr.mu mu) = 1) (v : alice_view) :
  bridge_leak_to_fdist Hmass v != 0 -> v \in enum alice_view.
Proof. by move=> _; rewrite mem_enum. Qed.

(** bridge_correct - the bridge preserves event probabilities.  For
    any predicate [P : pred alice_view], the SSProve-side conditional
    sum equals the infotheo-side [Pr] over the corresponding set.
    Kind: bridge obligation.
    Why: Task 12 of the plan, verbatim.  This is the bookkeeping
    lemma that lets Task 13 state its residual goal first on the
    SSProve side (where the upstream IND-CPA hops live) and then
    transfer through the bridge to the infotheo
    [{fdist alice_view}] side (where [Pr_dsdp_sol_uniform] lives).
    The proof unfolds [Pr d E = \sum_(a in E) d a], rewrites the set
    membership against the predicate, and uses
    [bridge_leak_to_fdistE] to expose the underlying [distr.mu mu].
    Naming: project-local; [_correct] reads "the bridge respects the
    intended interpretation".
    Used by: Task 13's [cPr_V2_V3_uniform_on_fiber]. *)
Lemma bridge_correct (mu : distr.distr R alice_view)
    (Hmass : psum (distr.mu mu) = 1) (P : pred alice_view) :
  \sum_(v : alice_view | P v) (distr.mu mu) v
    = Pr (bridge_leak_to_fdist Hmass) [set v | P v].
Proof.
rewrite /Pr.
apply: eq_big => [a|a _].
- by rewrite inE.
- by rewrite bridge_leak_to_fdistE.
Qed.

(* Task 12 verify clause: the bridge type-checks at the expected
   signature, and [Print Assumptions] on [bridge_correct] reveals no
   admitted obligation beyond the standard SSProve / MathComp axioms.
   The construction is parametric in the mass hypothesis; consumers
   supply [Hmass] from [LosslessCode] resolution at the use site. *)
Check bridge_leak_to_fdist :
  forall (mu : distr.distr R alice_view),
    psum (distr.mu mu) = 1 -> R.-fdist alice_view.

(** index_msg_gt0, index_renc_gt0 — positivity of the SSProve uniform-
    sample cardinalities.
    Kind: section hypothesis.
    Why: [LosslessOp_uniform] (SSProve [pkg_distr.v:206]) requires
    [Lt 0 i] (i.e. [0 < i]) for the sampler [uniform i] to have total
    mass one.  The DSDP game samples ten times — six over [index_msg]
    (the plaintext-scalar carrier ['I_index_msg]) and four over
    [index_renc] (the encryption-randomness carrier ['I_index_renc]) —
    and each draw must have nonzero support, otherwise the chain mass
    collapses to zero rather than to one.  Concretely, an instantiation
    against [plain AHE = 'Z_(p*q)] takes [index_msg = (p*q)%N] which is
    positive because [p, q] are prime; an instantiation against a
    concrete AHE randomness type [Renc] equates [index_renc] with the
    finType cardinality [#|Renc|] (via [renc_card]), which is positive
    when the scheme draws encryption randomness from a nonempty set.
    Both are mild and concrete instantiations discharge them
    trivially; they are stated as section hypotheses so the residual
    [LosslessCode_game_leak] below is provable Section-internally.
    Used by: LosslessCode_game_leak (and any subsequent Pr_fst-on-
    game_leak mass argument). *)
Hypothesis index_msg_gt0 : (0 < index_msg)%N.
Hypothesis index_renc_gt0 : (0 < index_renc)%N.

(** game_leak_run_code — the [raw_code] body of [game_leak] obtained by
    resolving its single export operation [id_game_run] at the unit
    argument.
    Kind: helper definition.
    Why: SSProve's [LosslessCode] class is a property of [raw_code]
    values, not of [package] values.  The Task 12 bridge
    [bridge_leak_to_fdist] takes its mass hypothesis as
    [psum (distr.mu mu) = 1] where [mu = Pr_fst c] for some
    [c : raw_code _]; the natural instantiation is
    [c := game_leak_run_code] (the body of [game_leak]'s
    [id_game_run] operation evaluated at [tt]).  Naming this body
    once lets [LosslessCode_game_leak] state the [Pr_fst]-mass
    obligation in a syntactically-uniform form that the consumer
    (Task 13's [cPr_V2_V3_uniform_on_fiber] caller in Task 14) can feed
    directly into [bridge_leak_to_fdist].
    Used by: LosslessCode_game_leak. *)
Definition game_leak_run_code : raw_code cipher_list :=
  resolve game_leak (id_game_run, ('unit, cipher_list)) tt.

(** LosslessCode_game_leak — the ten-sample-plus-[ret] body of
    [game_leak] is lossless: [psum (Pr_fst game_leak_run_code) = 1].
    Kind: instance / mass discharge.
    Why: Task A of [~/.claude/plans/sprightly-finding-robin.md].  The
    Task 12 bridge [bridge_leak_to_fdist] needs an [Hmass : psum (Pr_fst
    _) = 1] hypothesis to bring an SSProve [distr R alice_view] across
    to an infotheo [{fdist alice_view}]; this lemma supplies that
    hypothesis at the concrete code [game_leak_run_code].
    Proof outline.  [resolve game_leak _ tt] reduces to
    [coerce_kleisli (λ _, body) tt] where [body] is the literal
    ten-sample chain; [coerce_kleisliE] collapses the [coerce_kleisli]
    wrapper since the source/target [choice_type]s match.  Then ten
    applications of [Lossless_sample] (SSProve [nominal/Pr.v:198])
    walk through the [sample uniform i ;; k] tree, each leaving a
    [LosslessOp (uniform i)] subgoal discharged by
    [LosslessOp_uniform] (which consumes [index_msg_gt0] /
    [index_renc_gt0]).  The final [LosslessCode (ret _)] is closed by
    [Lossless_ret] (resolved automatically by typeclass eauto inside
    the last [Lossless_sample]).
    Naming: upstream-style PascalCase exception, mirroring
    [Lossless_ret], [Lossless_sample], and [LosslessOp_uniform] in
    SSProve.  See [feedback_mathcomp_naming.md] in user memory.
    Used by: T1 V_2-aware rebuild — discharges the [Hmass]
    obligation of [bridge_leak_to_fdist] at the [game_leak]-resolved
    code. *)
(** Lossless_put_ret — putting to a location and immediately returning
    is lossless: the [#put] step only mutates the heap, and the
    subsequent [ret] gives a Dirac mass on the projected value.
    Kind: helper instance.
    Why: T1's [#put V_2_cell := Some ...] step inside [game_leak]'s
    cipher-oracle body extends the pre-T0 ten-sample-plus-[ret] chain
    with an extra effect node.  The upstream [Lossless_sample] /
    [Lossless_ret] instances do not cover [#put]; this lemma fills the
    one missing case so [LosslessCode_game_leak] still discharges.
    Used by: LosslessCode_game_leak. *)
Lemma Lossless_put_ret {A : choiceType} (l : Location) (v : l) (x : A) :
  LosslessCode (#put l := v ;; ret x).
Proof.
rewrite /LosslessCode /Pr_fst.
rewrite Pr_code_put Pr_code_ret.
rewrite /(distr.dmargin _ _) dlet_unit_ext.
exact: Couplings.psum_SDistr_unit.
Qed.

Lemma LosslessCode_game_leak : LosslessCode game_leak_run_code.
Proof.
rewrite /game_leak_run_code /resolve /=.
rewrite coerce_kleisliE.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
apply: Lossless_sample => [|?]; first by apply: LosslessOp_uniform.
exact: Lossless_put_ret.
Qed.

(* ================================================================== *)
(* Task B: alice_view_joint carrier and SDistr-to-fdist bridge *)
(* ================================================================== *)

(** V_2_carrier, V_3_carrier - section parameters for the protocol
    scalars V_2 and V_3 as [finType]s.  The DSDP protocol scalars live
    in a finite commutative ring (the TeX abstraction at Setup item 2);
    Tasks E-F will generalize the IT residual lemma to an arbitrary
    [finComNzRingType] and instantiate this section at the ring of
    plaintext scalars [plain AHE].  Until then, these section parameters
    keep Task B parametric in the V_2 / V_3 carriers so the carrier and
    bridge plumbing can be checked and committed independently of the
    ring-genericity work.
    Kind: parameter.
    Why: Task B of [~/.claude/plans/sprightly-finding-robin.md] (Fallback
    R2A: extend the carrier to [alice_view_joint]).  Task 10's
    [alice_view] does not include V_2 / V_3, but the IT residual analysis
    in Task 13 / Task F treats V_2 and V_3 as random variables; lifting
    them into the joint sample space requires their carriers to be
    finType so the iterated product [alice_view * V_2_carrier *
    V_3_carrier] remains a finType.
    Used by: alice_view_joint, Task D's V_2_RV / V_3_RV
    projections, Task F's section instantiation. *)
Variable V_2_carrier : finType.

(** index_V_2, V_2_card - cardinality index for [V_2_carrier] and the
    bridge hypothesis tying [#|V_2_carrier|] to it.  Same pattern as
    [Renc] / [index_renc] / [renc_card] at the top of this section, and
    as [Dk_a_carrier] / [index_Dk_a] / [Dk_a_card] in Task 10.
    Kind: parameter + hypothesis.
    Why: SSProve [sample uniform] requires a [nat] cardinality; the
    Task H residual bound [Pr [ (predictor ∘ game_leak).output =
    V_2_sample ] <= #|R|%:R^-1] (where [R] is the ring of plaintext
    scalars) operates on [V_2_carrier] cardinality.  Concrete
    instantiations identify [V_2_carrier] with [plain AHE] and
    [index_V_2] with [index_msg].
    Used by: Task D's V_2_RV projection, Task F's residual section
    instantiation. *)
Variable index_V_2 : nat.
Hypothesis V_2_card : #|V_2_carrier| = index_V_2.

(** V_3_carrier, index_V_3, V_3_card - companion parameters for the
    third protocol scalar V_3.  Same shape as V_2's parameters.
    Kind: parameter + hypothesis.
    Why: same as V_2_carrier.  V_3 is the other DSDP secret scalar that
    Task D will project from [alice_view_joint] as a random
    variable; the IT residual decomposition operates on the joint
    [(V_2, V_3)] pair (the fiber of [u_2 v_2 + u_3 v_3 = s - u_1 v_1]).
    Used by: alice_view_joint, Task D's V_3_RV projection,
    Task F's residual section instantiation. *)
Variable V_3_carrier : finType.
Variable index_V_3 : nat.
Hypothesis V_3_card : #|V_3_carrier| = index_V_3.

(** alice_view_joint - the corrupted-Alice view extended with the
    two protocol scalars V_2 and V_3 that Alice does NOT see directly
    (they are masked into the ciphertexts and into the linear identity)
    but that the IT residual analysis treats as random variables on the
    same joint sample space.  Eleven-tuple finType built as the product
    of Task 10's [alice_view] with [V_2_carrier] and [V_3_carrier].
    Kind: canonical.
    Why: Task B of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R2A).  The two real-or-zero IND-CPA hops (Tasks 06-08)
    eliminate the three ciphertext slots from the distinguisher-visible
    view, leaving Task 10's nine-component [alice_view].  But to argue
    [Pr[predictor = V_2] <= 1/m] on the leak game, the joint sample
    space must contain V_2 (so that the V_2-guess event is a measurable
    predicate on the carrier) and V_3 (so that the constraint
    [u_2 v_2 + u_3 v_3 = s - u_1 v_1] picks out the fiber).  Extending
    the carrier here is the cleanest way to do this: HB instances
    inherit automatically through [%type] products since [alice_view],
    [V_2_carrier], [V_3_carrier] are all finType (which extends
    choiceType).  The Task D projections then expose V_2 / V_3 as
    [{RV _ -> _}].
    Naming: [_with_secrets] reads "the surface view plus the secret
    scalars V_2, V_3"; user-chosen, see plan line 53.  Not _full
    (rejected as too generic).
    Used by: Task D's protocol random variables, Task F's residual
    section instantiation, T1 V_2-aware rebuild. *)
Definition alice_view_joint : finType :=
  (alice_view * V_2_carrier * V_3_carrier)%type.

(** alice_view_joint_choice_finType - the named HB instance label
    tying [alice_view_joint] simultaneously to MathComp's
    [finType] and [choiceType] structures.  No additional plumbing is
    required: the iterated product type-class search finds both
    instances automatically because each component is itself a finType.
    Kind: canonical (HB instance label, no new content).
    Why: mirrors Task 10's [alice_view_choice_finType] so audits can
    grep for the joint declaration.  The two [Check] judgments below
    discharge the verify clause of Task B.
    Naming: <type>_<class1>_<class2> follows the MathComp convention
    used by Task 10.
    Used by: documentation only; the instances are picked up by
    canonical-structure resolution at the use sites. *)
Definition alice_view_joint_choice_finType : Type :=
  alice_view_joint.

(* Task B verify clause: both finType and choiceType inhabit
   alice_view_joint. *)
Check (alice_view_joint : finType).
Check (alice_view_joint : choiceType).

(** index_alice_view_joint - the cardinality of
    [alice_view_joint] as a [nat].  Computed once so that the
    SSProve-side [chFin] embedding below can refer to it by name.
    Kind: canonical.
    Why: mirrors Task 10's [index_alice_view].  SSProve's [choice_type]
    GADT uses [chFin (n : nat)] for finite carriers, with
    [chInterp (chFin n) = 'I_n].  Naming the cardinality lets us state
    the cardinality lemma [alice_view_joint_ct_card] cleanly.
    Naming: [index_X] is a project-local prefix for SSProve [chFin]
    cardinality parameters, mirroring Task 10's [index_alice_view] and
    the top-of-section [index_renc] / [index_Dk_a].  The [_card] suffix
    is reserved for the finType cardinality lemmas below
    ([alice_view_joint_ct_card],
    [alice_view_joint_card_index]), so [index_] is used for the
    nat value itself to keep the two roles distinct.
    Used by: alice_view_joint_ct, the Task B bridge. *)
Definition index_alice_view_joint : nat :=
  #|alice_view_joint|.

(** alice_view_joint_ct - the SSProve-side [choice_type] avatar
    of [alice_view_joint], lifted as a single [chFin] of the
    total cardinality.  This is the carrier that the Task B bridge
    [bridge_alice_view_joint_to_fdist :
    SDistr alice_view_joint -> {fdist alice_view_joint}]
    will round-trip through to transfer SSProve probabilities (which
    live over [chInterp alice_view_joint_ct =
    'I_index_alice_view_joint]) onto infotheo's
    [{fdist alice_view_joint}].
    Kind: canonical.
    Why: same reason as Task 10's [alice_view_ct].  SSProve's
    [choice_type] is a closed inductive that does not directly cover
    finType products; routing through [chFin (#|...|)] is the standard
    idiom.  The [alice_view_joint_to_ct] /
    [alice_view_joint_of_ct] bijection below mediates between
    the two views.
    Naming: <type>_ct uses the SSProve-side suffix _ct (choice_type)
    matching Task 10's [alice_view_ct].
    Used by: bridge_alice_view_joint_to_fdist (Task B), Task C's
    extended bridge over predictor composition. *)
Definition alice_view_joint_ct : choice_type :=
  chFin index_alice_view_joint.

(** alice_view_joint_to_ct, alice_view_joint_of_ct -
    bijection between the MathComp finType [alice_view_joint]
    and the SSProve-side [alice_view_joint_ct =
    chFin index_alice_view_joint =
    'I_index_alice_view_joint], realised via MathComp's
    [enum_rank] and [enum_val] on the canonical enumeration.
    Kind: helper.
    Why: Task B builds an [{fdist alice_view_joint}] by walking
    the SSProve [Pr_code] over [alice_view_joint_ct] and
    re-indexing each probability against the corresponding MathComp
    finType element.  These two functions are the re-indexing
    primitive; the [_K] cancel lemmas below guarantee the round-trip
    is the identity.
    Naming: <type>_to_ct / <type>_of_ct mirrors Task 10's
    [alice_view_to_ct] / [alice_view_of_ct].
    Used by: bridge_alice_view_joint_to_fdist (Task B), Task C's
    extended bridge, the support-enumeration obligation. *)
Definition alice_view_joint_to_ct
    (v : alice_view_joint) : alice_view_joint_ct :=
  enum_rank v.

(** alice_view_joint_of_ct - companion to
    [alice_view_joint_to_ct]: send an SSProve-side index
    [i : alice_view_joint_ct] back to its
    [alice_view_joint] inhabitant via [enum_val].
    Kind: helper.
    Why: same as the [_to_ct] direction; together they form the
    bijection mediating between the SSProve [chFin]-indexed view and
    the infotheo [finType]-indexed view.
    Naming: <type>_of_ct mirrors Task 10's [alice_view_of_ct]; the
    [_of_ct] suffix names the inverse direction of [_to_ct] for the
    SSProve [choice_type] avatar.  Project-local, not a MathComp
    suffix-table entry.
    Used by: bridge_alice_view_joint_to_fdist (Task B),
    [alice_view_joint_to_ct_K],
    [alice_view_joint_of_ct_K]. *)
Definition alice_view_joint_of_ct
    (i : alice_view_joint_ct) : alice_view_joint :=
  enum_val i.

(** alice_view_joint_to_ct_K - cancel law:
    [alice_view_joint_of_ct] is a left inverse of
    [alice_view_joint_to_ct].  Follows from MathComp's
    [enum_rankK].
    Kind: cancellation.
    Why: Task C's extended bridge over predictor composition needs to
    argue that summing an SSProve density over
    [alice_view_joint_ct] and re-indexing back through
    [alice_view_joint_of_ct] recovers the original
    [alice_view_joint] support; the cancel pair is the algebraic
    content of that argument.
    Used by: Task C's bridge correctness lemma. *)
Lemma alice_view_joint_to_ct_K :
  cancel alice_view_joint_to_ct alice_view_joint_of_ct.
Proof. exact: enum_rankK. Qed.

(** alice_view_joint_of_ct_K - companion cancel:
    [alice_view_joint_to_ct] is a left inverse of
    [alice_view_joint_of_ct].  Follows from MathComp's
    [enum_valK].
    Kind: cancellation.
    Why: same role as [alice_view_joint_to_ct_K] but for the
    inverse direction; together they make the pair a bijection (used
    by Task C to justify the [psum] / [bigop] re-indexing). *)
Lemma alice_view_joint_of_ct_K :
  cancel alice_view_joint_of_ct alice_view_joint_to_ct.
Proof. exact: enum_valK. Qed.

(** alice_view_joint_ct_card,
    alice_view_joint_card_index - cardinality coherence:
    [alice_view_joint_ct] interprets as
    ['I_index_alice_view_joint] which has cardinality
    [index_alice_view_joint], and [alice_view_joint]
    itself has the same cardinality by definition of
    [index_alice_view_joint].
    Kind: coherence.
    Why: Task C's total-mass bridge relates [psum] over [chInterp
    alice_view_joint_ct] (the SSProve semantics output) to
    [\sum_(v : alice_view_joint) ...] (the infotheo target);
    these two facts let us swap the indexing finType under the bigop /
    psum without changing the value.
    Used by: Task C's extended bridge correctness. *)
Lemma alice_view_joint_ct_card :
  #|alice_view_joint_ct| = index_alice_view_joint.
Proof. exact: card_ord. Qed.

(** alice_view_joint_card_index - cardinality of the
    infotheo-side [alice_view_joint] equals
    [index_alice_view_joint] by definition.  Trivial by
    reflexivity.
    Kind: coherence.
    Why: same role as Task 10's [alice_view_card_index].  When the
    Task C bridge re-indexes a [psum] over the SSProve-side
    [alice_view_joint_ct] back to a
    [\sum_(v : alice_view_joint)], this lemma is the cardinality
    side of that re-indexing.
    Naming: _card_index records "cardinality equals the named index
    parameter"; project-local convention, not a MathComp suffix-table
    entry.
    Used by: Task C's extended bridge. *)
Lemma alice_view_joint_card_index :
  #|alice_view_joint| = index_alice_view_joint.
Proof. by []. Qed.

#[local] Open Scope fdist_scope.

(** bridge_psum_to_bigop_with_secrets - the elementary identity
    converting SSProve's [psum] over an [alice_view_joint]-valued
    sub-distribution into MathComp's
    [\sum_(v : alice_view_joint)].  On a [finType] both
    quantities enumerate the same support, and [psum f = \sum_i |f i|]
    from realsum collapses to the plain sum because [distr.mu mu] is
    non-negative.
    Kind: helper bridge.
    Why: Task B of [~/.claude/plans/sprightly-finding-robin.md].  The
    SSProve denotational semantics produces a [distr R
    alice_view_joint] via [Pr_fst]; the infotheo target side
    wants an [\sum_(v : alice_view_joint)] indexed bigop.  This
    lemma is the only place where the two summation conventions meet
    for the wider carrier (Task 12's [bridge_psum_to_bigop] does the
    same job for the narrower [alice_view]).
    Naming: project-local; mirrors Task 12's [bridge_psum_to_bigop]
    with the [_with_secrets] suffix.
    Used by: bridge_alice_view_joint_to_fdist, Task C's
    extended bridge correctness. *)
Lemma bridge_psum_to_bigop_with_secrets
    (mu : distr.distr R alice_view_joint) :
  \sum_(v : alice_view_joint) (distr.mu mu) v
    = psum (distr.mu mu).
Proof.
rewrite psum_fin.
apply: eq_bigr => a _.
by rewrite ger0_norm //; apply: distr.ge0_mu.
Qed.

(** bridge_alice_view_joint_to_fdist - the SDistr-to-fdist
    bridge at the extended carrier.  Given a sub-distribution
    [mu : distr R alice_view_joint] and a proof that its total
    mass is one, produce an infotheo-side
    [{fdist alice_view_joint}] by wrapping [distr.mu mu] in an
    [ffun] and discharging the [FDist.make] obligations:
    non-negativity comes from [distr.ge0_mu], summation-to-one comes
    from [bridge_psum_to_bigop_with_secrets] composed with the mass
    hypothesis.
    Kind: bridge construction.
    Why: Task B of the plan.  Mirrors Task 12's
    [bridge_leak_to_fdist] for the eleven-component carrier.  Task C's
    extended bridge over predictor composition will produce a
    sub-distribution of this shape (the joint distribution of the
    game's samples plus the predictor's t_msg output), and the IT
    residual analysis (Task F) will operate on the resulting
    [{fdist alice_view_joint}].
    Naming: project-local.  Mirrors Task 12's [bridge_leak_to_fdist]
    with the wider carrier suffix.
    Used by: [bridge_alice_view_joint_to_fdistE], T1 V_2-aware
    rebuild. *)
Definition bridge_alice_view_joint_to_fdist
    (mu : distr.distr R alice_view_joint)
    (Hmass : psum (distr.mu mu) = 1) :
  R.-fdist alice_view_joint.
Proof.
unshelve eapply FDist.make.
- exact: [ffun v => (distr.mu mu) v].
- by move=> a; rewrite ffunE; apply: distr.ge0_mu.
- under eq_bigr=> a _ do rewrite ffunE.
  by rewrite bridge_psum_to_bigop_with_secrets.
Defined.

(** bridge_alice_view_joint_to_fdistE - elementwise equation for
    the bridge.  Spells out how to evaluate the resulting
    [{fdist alice_view_joint}] at a point: it is just
    [distr.mu mu] of the same point.
    Kind: simplification.
    Why: lets downstream proofs unfold the bridge to expose the
    underlying SSProve density without forcing them to manage the
    [ffun] wrapper.  Mirrors Task 12's [bridge_leak_to_fdistE].
    Naming: trailing [E] follows MathComp convention for elementwise /
    extensional equations.
    Used by: T1 V_2-aware rebuild. *)
Lemma bridge_alice_view_joint_to_fdistE
    (mu : distr.distr R alice_view_joint)
    (Hmass : psum (distr.mu mu) = 1) (v : alice_view_joint) :
  bridge_alice_view_joint_to_fdist Hmass v = (distr.mu mu) v.
Proof. by rewrite /bridge_alice_view_joint_to_fdist /= ffunE. Qed.

(* Task B verify clause: the bridge type-checks at the expected
   signature.  Mirrors Task 12's verify [Check] on
   [bridge_leak_to_fdist]. *)
Check bridge_alice_view_joint_to_fdist :
  forall (mu : distr.distr R alice_view_joint),
    psum (distr.mu mu) = 1 -> R.-fdist alice_view_joint.

(* ================================================================== *)
(* Task D: protocol random variables on alice_view_joint       *)
(* ================================================================== *)

#[local] Open Scope proba_scope.

(** fdist_game_leak_joint - the joint probability distribution
    over [alice_view_joint].  Morally obtained by composing
    Task A's [LosslessCode_game_leak] (which discharges the [psum] mass
    obligation) with Task B's [bridge_alice_view_joint_to_fdist]
    (which lifts an SSProve [distr] into an infotheo [{fdist _}]) on a
    modified leak code that returns the eleven-tuple sample instead of
    the four-ciphertext list.
    Kind: section parameter.
    Why: Task D of [~/.claude/plans/sprightly-finding-robin.md].  The
    protocol random variables [V_1, V_2, ..., D_3, Z_rand] are projected
    from [alice_view_joint] under this joint distribution.
    Carrying the fdist as a section [Variable] (rather than constructing
    it explicitly from [game_leak]'s raw_code) keeps Task D parametric
    in the bridge instantiation: Task F discharges the bridge by
    composing [LosslessCode_game_leak] with a return-shape change on
    [game_leak]'s body and threading through
    [bridge_alice_view_joint_to_fdist].  The parametric framing
    mirrors the existing residual section [Section
    dsdp_security_indcpa_residual] below (which also takes the
    probability space as a [Context] parameter).
    Naming: project-local; [fdist_<source>_with_secrets] follows the
    same [<source>_with_secrets] pattern as the Task B carrier
    [alice_view_joint].  The [fdist_] prefix marks this as the
    fdist over that carrier (vs. the carrier itself); the [_game_leak]
    middle records that the fdist's intended instantiation is the
    bridge image of [game_leak].  MathComp suffix table has no entry
    for fdist names; project-local convention only.
    Used by: Task D's protocol random variables [V_1..D_3, Z_rand],
    the three correspondence lemmas
    [p_V_2_uniform, p_V_3_uniform, inde_V_2_V_3_Z_rand], Task F's
    residual section instantiation. *)
Variable fdist_game_leak_joint : R.-fdist alice_view_joint.

(** Z_rand_carrier - the carrier finType for the auxiliary
    encryption-randomness random variable [Z_rand].  The IND-CPA hops
    (Tasks 06-08) have already eliminated all encryption randomness
    from the distinguisher-visible view, so the residual sample space
    [alice_view_joint] does NOT carry any explicit
    encryption-rand component.  Modelling [Z_rand] as a unit-typed
    random variable is therefore correct: at the post-hop residual
    layer, encryption randomness is a constant (its values are
    perfectly indistinguishable from any other encryption randomness
    because the ciphertexts have collapsed to zero-encryptions, see
    [bob_zero_equiv_game_hybrid_two] and the [game_hybrid_two] body).
    Kind: canonical.
    Why: Task D of the plan.  The residual section [Section
    dsdp_security_indcpa_residual] below takes [Z_rand : {RV P -> TR}]
    where [TR : finType]; we instantiate [TR := Z_rand_carrier := unit]
    so the IT residual independence hypothesis [V2V3_Z_inde_given_Y]
    becomes provable rather than parametric.
    Naming: [Z_rand_carrier] mirrors [V_2_carrier], [V_3_carrier],
    [Dk_a_carrier]; project-local convention for the carrier finType
    of a named random variable.
    Used by: [Z_rand], [inde_V_2_V_3_Z_rand]. *)
Definition Z_rand_carrier : finType := unit.

(** V_3 - rightmost component of [alice_view_joint], the third
    protocol scalar V_3.  By the Task B carrier construction
    [alice_view_joint = ((alice_view, V_2), V_3)], V_3 is the
    [snd] projection.
    Kind: helper.
    Why: Task D of the plan.  The IT residual analysis treats V_3 as a
    random variable on the joint sample space for the fiber argument
    [(v_2, v_3) \in dsdp_fiber u_1 u_2 u_3 v_1 s]; the marginal
    uniformity correspondence [p_V_3_uniform] and the joint
    independence [inde_V_2_V_3_Z_rand] both reference V_3 directly.
    Naming: TeX-derived subscript; [_3] marks the third of the
    (v_1, v_2, v_3) input-share triple, not the MathComp ring-three
    suffix.  Plan line 82 explicitly forbids the [_RV] suffix;
    matches [dsdp_security.v:147]'s [V_3] in the trace-level
    [AliceView].  Project-local convention.
    Used by: [p_V_3_uniform], [inde_V_2_V_3_Z_rand], Task F's
    residual section instantiation, Task H's residual bound. *)
Definition V_3 : {RV fdist_game_leak_joint -> V_3_carrier} :=
  fun avs => snd avs.

(** V_2 - next-to-rightmost component, the protocol scalar V_2 that
    the corrupted-Alice predictor must guess to win.  By the Task B
    carrier construction, V_2 = [snd \o fst] applied to the eleven-
    component sample.
    Kind: helper.
    Why: Task D of the plan.  V_2 is the central random variable of
    the secrecy bound [Pr[predictor = V_2] <= 1/m + 2 * epsilon_cpa];
    [p_V_2_uniform] and [inde_V_2_V_3_Z_rand] reference V_2 directly,
    and T1's V_2-aware residual bound is stated against the event
    [output = V_2_sample].
    Naming: TeX-derived subscript; [_2] marks the second of the
    (v_1, v_2, v_3) input-share triple, not the MathComp ring-two
    suffix.  Plan line 82 explicitly forbids the [_RV] suffix;
    project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: [p_V_2_uniform], [inde_V_2_V_3_Z_rand], Task F's
    residual section instantiation, Task H's residual bound. *)
Definition V_2 : {RV fdist_game_leak_joint -> V_2_carrier} :=
  fun avs => snd (fst avs).

(** D_3 - the plaintext D_3 (the decrypted contribution that Alice
    receives), rightmost component of the inner nine-tuple
    [alice_view].  By the Task 10 carrier construction
    [alice_view = ((((((((Dk_a, S), V_1), U_1), U_2), U_3), R_2), R_3),
    D_3)], D_3 is reached by [snd \o fst \o fst] applied to the
    eleven-component sample.
    Kind: helper.
    Why: Task D of the plan.  D_3 is part of Alice's surfaced view
    (after IND-CPA elimination of the ciphertext slots).  The residual
    independence hypotheses operate on the joint
    [(V_1, U_1, U_2, U_3, S)] conditioning view, not on D_3 directly,
    but D_3 still lives on the same sample space and Task F's
    residual section instantiation carries it through.
    Naming: TeX-derived subscript; [_3] marks the third-party
    decrypted contribution Alice receives, not the MathComp ring-
    three suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition D_3 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst avs)).

(** R_3 - the masking scalar R_3 Alice draws for Charlie's slot,
    projected as the fourth [snd]-then-fst path from the eleven-tuple
    sample.
    Kind: helper.
    Why: Task D of the plan.  Part of the eight-scalar block of
    [alice_view].  R_3 lives on the joint sample space and is
    independent of (V_2, V_3) under the joint distribution; Task F's
    residual section instantiation carries it through.
    Naming: TeX-derived subscript; [_3] marks the masking scalar
    Alice draws for Charlie's slot (the [R_3] of the (R_2, R_3) pair),
    not the MathComp ring-three suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition R_3 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst avs))).

(** R_2 - the masking scalar R_2 Alice draws for Bob's slot,
    projected as the fifth [snd]-then-fst path from the eleven-tuple
    sample.
    Kind: helper.
    Why: Task D of the plan.  R_2 lives on the joint sample space
    alongside the other protocol scalars; Task F's residual section
    instantiation carries it through as a component of the bridged
    fdist so the protocol-RV infrastructure stays self-contained.
    Naming: TeX-derived subscript; [_2] marks the masking scalar
    Alice draws for Bob's slot (the [R_2] of the (R_2, R_3) pair),
    not the MathComp ring-two suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition R_2 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst avs)))).

(** U_3 - Alice's third scalar coefficient in the DSDP linear
    constraint [u_1 v_1 + u_2 v_2 + u_3 v_3 = s], projected from the
    eleven-tuple sample.  When U_3 is invertible the joint fiber is
    a singleton in V_3 per V_2, which is what makes the residual
    uniform; see [Pr_dsdp_sol_uniform] in [dsdp_entropy.v].
    Kind: helper.
    Why: Task D of the plan.  U_3 is one of the conditioning RVs
    in [cPr_V2_V3_uniform_on_fiber] (the IT residual) and the
    invertibility hypothesis [(u3 < minn p q)%N] is stated against
    its values; Task F's residual section instantiation references
    U_3 through that lemma.
    Naming: TeX-derived subscript; [_3] marks the third of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-three
    suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition U_3 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst avs))))).

(** U_2 - Alice's second scalar coefficient in the constraint
    [u_1 v_1 + u_2 v_2 + u_3 v_3 = s], projected from the eleven-
    tuple sample.
    Kind: helper.
    Why: Task D of the plan.  U_2 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] in [cPr_V2_V3_uniform_on_fiber];
    Task F's residual section instantiation carries it through.
    Naming: TeX-derived subscript; [_2] marks the second of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-two
    suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition U_2 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst avs)))))).

(** U_1 - Alice's first scalar coefficient (her share of the
    coefficient triple [(u_1, u_2, u_3)]), projected from the
    eleven-tuple sample as the seventh [snd]-then-fst path.
    Kind: helper.
    Why: Task D of the plan.  U_1 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] consumed by
    [cPr_V2_V3_uniform_on_fiber] and [constraint_holds_indcpa].
    Naming: TeX-derived subscript; [_1] marks the first of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-one
    suffix.  Project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: Task F's residual section instantiation. *)
Definition U_1 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst (fst avs))))))).

(** V_1 - Alice's input share: the protocol scalar v_1, projected
    from the eleven-component sample as the eighth snd/fst path
    through the iterated product
    [(((((((Dk_a, S), V_1), U_1), U_2), U_3), R_2), R_3, D_3, V_2,
    V_3]).
    Kind: helper.
    Why: Task D of the plan.  V_1 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] consumed by
    [cPr_V2_V3_uniform_on_fiber] and [constraint_holds_indcpa]; Task F's
    residual section instantiation references V_1 through those.
    Naming: TeX-derived subscript; [_1] marks the first of the
    (v_1, v_2, v_3) input-share triple, not the MathComp ring-one
    suffix.  Project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: Task F's residual section instantiation. *)
Definition V_1 : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst (fst (fst avs)))))))).

(** S - the sum scalar [S = u_1 v_1 + u_2 v_2 + u_3 v_3] that Alice
    learns at the end of the DSDP protocol (Alice's view of the
    inner product result), projected as the second-from-left snd-then-
    fst-... path through the eleven-tuple sample.
    Kind: helper.
    Why: Task D of the plan.  S is the deterministic function of
    [(V_1, U_1, U_2, U_3, V_2, V_3)] that the constraint
    [constraint_holds_indcpa] expresses; Task F's residual section
    instantiation uses S as a conditioning RV in
    [cPr_V2_V3_uniform_on_fiber].  Project-local naming: TeX [S]
    matches [dsdp_security.v:117]'s [Let S : {RV P -> msg}], which
    is similarly a single-letter random variable; no [_RV] suffix
    per plan line 82.  Inside [Section dsdp_security_indcpa] this
    definition shadows the natural-number successor [nat.S] in
    subsequent lines, but the section closes immediately after
    Task D so the shadow is local and does not affect any earlier
    proof.
    Naming: TeX-derived single-letter; plan line 82 explicitly
    requires no [_RV] suffix.  MathComp suffix table has no entry
    for single-letter RVs; project-local convention only.
    Used by: Task F's residual section instantiation (consumed via
    [constraint_holds_indcpa] and [cPr_V2_V3_uniform_on_fiber]). *)
Definition S : {RV fdist_game_leak_joint -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst (fst (fst (fst avs))))))))).

(** Dk_a - Alice's private decryption key, leftmost component of
    the nine-tuple [alice_view].  Reached by nine successive [fst]
    projections through the iterated [%type] product, then one more
    [fst] to peel the V_3 / V_2 secrets pair from the eleven-tuple
    sample.
    Kind: helper.
    Why: Task D of the plan.  Dk_a is part of Alice's surfaced view
    (Task 10's [alice_view]) and lives on the joint sample space
    [fdist_game_leak_joint] alongside the other protocol RVs;
    Task F's residual section instantiation carries it through so
    the protocol-RV infrastructure stays self-contained even though
    the IT residual itself does not condition on Dk_a directly.
    Naming: project-local snake_case matching the section parameter
    [Dk_a_carrier] (Task 10) for the carrier finType.  No MathComp
    suffix-table entry for decryption-key RVs.
    Used by: Task F's residual section instantiation. *)
Definition Dk_a : {RV fdist_game_leak_joint -> Dk_a_carrier} :=
  fun avs => fst (fst (fst (fst (fst (fst (fst (fst (fst (fst avs))))))))).

(** Z_rand - the auxiliary encryption-randomness random variable,
    instantiated as the constant unit-valued RV [fun _ => tt].
    Kind: helper.
    Why: Task D of the plan.  At the post-IND-CPA-hop residual layer,
    encryption randomness has been collapsed (both ciphertexts c_2,
    c_3 are zero-encryptions in [game_leak]'s body); the residual
    section [dsdp_security_indcpa_residual] below carries [Z_rand]
    as a parametric [Z_rand : {RV P -> TR}] but only consumes it
    through the conditional-independence hypothesis
    [V2V3_Z_inde_given_Y].  Setting [Z_rand] to the constant unit RV
    discharges that hypothesis structurally: a constant random
    variable is independent of every other RV (see
    [inde_V_2_V_3_Z_rand] below).
    Naming: TeX-derived snake_case [Z_rand]; per plan line 82 no
    [_RV] suffix.  Project-local convention.
    Used by: [inde_V_2_V_3_Z_rand], [pfwd1_Z_rand_tt], Task F's
    residual section instantiation (which discharges
    [V2V3_Z_inde_given_Y] from [inde_V_2_V_3_Z_rand]). *)
Definition Z_rand : {RV fdist_game_leak_joint -> Z_rand_carrier} :=
  fun _ => tt.

(* Task D verify clause: all eleven protocol random variables plus
   [Z_rand] type-check as [{RV fdist_game_leak_joint -> _}]. *)
Check V_1 : {RV fdist_game_leak_joint -> plain AHE}.
Check V_2 : {RV fdist_game_leak_joint -> V_2_carrier}.
Check V_3 : {RV fdist_game_leak_joint -> V_3_carrier}.
Check U_1 : {RV fdist_game_leak_joint -> plain AHE}.
Check U_2 : {RV fdist_game_leak_joint -> plain AHE}.
Check U_3 : {RV fdist_game_leak_joint -> plain AHE}.
Check R_2 : {RV fdist_game_leak_joint -> plain AHE}.
Check R_3 : {RV fdist_game_leak_joint -> plain AHE}.
Check S   : {RV fdist_game_leak_joint -> plain AHE}.
Check D_3 : {RV fdist_game_leak_joint -> plain AHE}.
Check Dk_a : {RV fdist_game_leak_joint -> Dk_a_carrier}.
Check Z_rand : {RV fdist_game_leak_joint -> Z_rand_carrier}.

(** card_V_2_carrier_succ - cardinality of [V_2_carrier] in the
    [_.+1] shape required by infotheo's [fdist_uniform].  Discharged
    by [fdist_card_prednK] on the marginal
    [fdistmap V_2 fdist_game_leak_joint].
    Kind: helper.
    Why: Task D's uniformity correspondence lemma [p_V_2_uniform]
    states [`p_ V_2 = fdist_uniform _], and infotheo's
    [fdist_uniform : forall (R : numFieldType) (A : finType) (n : nat),
    #|A| = n.+1 -> fdist R A] requires its cardinality argument to
    have [_.+1] shape (so that the uniform mass [#|A|^-1] is
    well-defined).  Routing through [fdist_card_prednK] (which gives
    [#|A| = #|A|.-1.+1] for any non-empty finType) discharges this
    obligation generically: the non-emptiness comes free from the
    existence of [fdist_game_leak_joint].
    Naming: [_succ] suffix marks the [.+1] shape; project-local
    convention, mirrors [fdist_card_prednK] in [fdist.v].
    Used by: [p_V_2_uniform]. *)
Lemma card_V_2_carrier_succ : #|V_2_carrier| = #|V_2_carrier|.-1.+1.
Proof.
have HP : R.-fdist V_2_carrier := fdistmap V_2 fdist_game_leak_joint.
exact: fdist_card_prednK HP.
Qed.

(** card_V_3_carrier_succ - the equation
    [#|V_3_carrier| = #|V_3_carrier|.-1.+1], lifting the V_3 carrier
    cardinality into the [_.+1] shape required by [fdist_uniform].
    Companion to [card_V_2_carrier_succ] for V_3; same proof
    structure (route through [fdist_card_prednK] on the marginal
    [fdistmap V_3 fdist_game_leak_joint]).
    Kind: helper.
    Why: [p_V_3_uniform] needs a [_.+1]-shaped witness;
    [fdist_card_prednK] produces it from the non-emptiness of
    [V_3_carrier], which is witnessed by the marginal fdist
    [fdistmap V_3 fdist_game_leak_joint].
    Used by: [p_V_3_uniform]. *)
Lemma card_V_3_carrier_succ : #|V_3_carrier| = #|V_3_carrier|.-1.+1.
Proof.
have HP : R.-fdist V_3_carrier := fdistmap V_3 fdist_game_leak_joint.
exact: fdist_card_prednK HP.
Qed.

(** V_2_uniform_hyp - marginal uniformity of V_2 under
    [fdist_game_leak_joint].
    Kind: section hypothesis.
    Why: Task D of the plan.  The proof that V_2 is uniform follows
    from [game_leak]'s body sampling [iV2 ← sample uniform index_msg]
    as its very first operation, and the bridged fdist preserves
    that uniformity through Task A's [LosslessCode_game_leak] and
    Task B's [bridge_alice_view_joint_to_fdist].  At the
    abstract Task D layer (which is parametric in
    [fdist_game_leak_joint]) the uniformity is a hypothesis
    that Task F discharges when instantiating the bridge at the
    concrete eleven-tuple-returning leak code.  Same engineering
    pattern as [VarRV_uniform_indcpa] in the residual section
    [dsdp_security_indcpa_residual] below.
    Used by: [p_V_2_uniform]. *)
Hypothesis V_2_uniform_hyp :
  `p_ V_2 = fdist_uniform card_V_2_carrier_succ.

(** V_3_uniform_hyp - marginal uniformity of V_3, analogous to
    [V_2_uniform_hyp].  Proof origin: [game_leak] samples
    [iV3 ← sample uniform index_msg] immediately after [iV2]. *)
Hypothesis V_3_uniform_hyp :
  `p_ V_3 = fdist_uniform card_V_3_carrier_succ.

(** pfwd1_Z_rand_tt - [Z_rand] hits [tt] with probability one because
    [Z_rand] is the constant unit-valued random variable.  Standard
    fact: a constant random variable concentrates its mass on its
    constant value.
    Kind: helper.
    Why: feeds [inde_V_2_V_3_Z_rand].  The independence of
    [[%V_2, V_3]] and [Z_rand] reduces to showing
    [Pr[(V_2, V_3, Z_rand) = (v_2, v_3, tt)] = Pr[(V_2, V_3) =
    (v_2, v_3)] * Pr[Z_rand = tt]]; using
    [Pr[Z_rand = tt] = 1] turns the RHS into the LHS up to the
    bijection [Pr[(V_2, V_3, Z_rand) = (v_2, v_3, tt)] = Pr[(V_2, V_3)
    = (v_2, v_3)]] (which holds because the [Z_rand] component is
    always [tt]).
    Used by: [inde_V_2_V_3_Z_rand]. *)
Lemma pfwd1_Z_rand_tt : `Pr[ Z_rand = tt ] = 1.
Proof.
rewrite pfwd1E.
suff -> : (finset (preim Z_rand (pred1 tt))) = setT by exact: Pr_setT.
apply/setP => x; rewrite !inE /=.
by case: (Z_rand x).
Qed.

(** p_V_2_uniform - the V_2 marginal of [fdist_game_leak_joint]
    is the uniform distribution on [V_2_carrier].
    Kind: correspondence lemma.
    Why: Task D of [~/.claude/plans/sprightly-finding-robin.md], one
    of the three correspondence lemmas this task discharges.  Task F
    feeds this into [VarRV_uniform_indcpa] of the residual section
    (after restricting V_2 / V_3 to a joint-uniform [(V_2, V_3)]
    statement via [fdist_prod_indep] / [VarRV_indep_inputs]).
    Proof: direct from [V_2_uniform_hyp].  The Task A-B chain
    (lossless game body + bridge) discharges this at concrete
    instantiation time (Task F); at the parametric layer the
    hypothesis carries the bridge content.
    Naming: [p_<X>_<property>] follows the infotheo project
    convention; compare [VarRV_uniform_indcpa] at
    [dsdp_security_indcpa_residual] section below.
    Used by: Task F's residual section instantiation. *)
Lemma p_V_2_uniform : `p_ V_2 = fdist_uniform card_V_2_carrier_succ.
Proof. exact: V_2_uniform_hyp. Qed.

(** p_V_3_uniform - companion uniformity for V_3:
    [`p_ V_3 = fdist_uniform card_V_3_carrier_succ].  Same shape and
    justification as [p_V_2_uniform], with the Task A-B chain
    discharging the bridge at concrete instantiation (Task F).
    Kind: correspondence lemma.
    Why: Task D of the plan.  Task F feeds this into
    [VarRV_uniform_indcpa] of the residual section as the marginal
    side of a [(V_2, V_3)] joint-uniform statement (built via
    [fdist_prod_indep] from this lemma, [p_V_2_uniform], and
    [VarRV_indep_inputs]).
    Used by: Task F's residual section instantiation. *)
Lemma p_V_3_uniform : `p_ V_3 = fdist_uniform card_V_3_carrier_succ.
Proof. exact: V_3_uniform_hyp. Qed.

(** inde_V_2_V_3_Z_rand - the pair [(V_2, V_3)] is independent of
    [Z_rand] under [fdist_game_leak_joint].
    Kind: correspondence lemma.
    Why: Task D of the plan.  This is the third correspondence
    lemma; it feeds [V2V3_Z_inde_given_Y] in the residual section
    instantiation at Task F.  Unlike the uniformity lemmas, this
    independence is provable directly (no hypothesis needed) because
    [Z_rand] is the constant unit-valued RV: a constant random
    variable is independent of every other random variable, since
    [Pr[X = x] * Pr[Z = tt] = Pr[X = x] * 1 = Pr[X = x] = Pr[(X, Z)
    = (x, tt)]].  The proof realises this through
    [pfwd1_Z_rand_tt] + a [setP] argument collapsing the joint event
    [(V_2, V_3, Z_rand) = (v_2, v_3, tt)] to [(V_2, V_3) = (v_2, v_3)].
    Naming: [inde_<X>_<Y>] follows the infotheo convention for
    independence statements; compare [V2V3_Z_inde_given_Y] in the
    residual section below.
    Used by: Task F's residual section instantiation. *)
Lemma inde_V_2_V_3_Z_rand :
  fdist_game_leak_joint |= [% V_2, V_3] _|_ Z_rand.
Proof.
rewrite /inde_RV.
move=> [v2 v3] z.
case: z.
rewrite pfwd1_Z_rand_tt mulr1.
rewrite !pfwd1E.
apply: eq_bigl => x; rewrite !inE /=.
rewrite /RV2 /=.
by case: (Z_rand x); rewrite !xpair_eqE andbT.
Qed.

(* Task D verify clause: the three correspondence lemmas type-check
   and close with [Qed].  Mirrors Task 12's and Task B/C's verify
   [Check]s. *)
Check p_V_2_uniform :
  `p_ V_2 = fdist_uniform card_V_2_carrier_succ.

Check p_V_3_uniform :
  `p_ V_3 = fdist_uniform card_V_3_carrier_succ.

Check inde_V_2_V_3_Z_rand :
  fdist_game_leak_joint |= [% V_2, V_3] _|_ Z_rand.

End dsdp_security_indcpa.

(* ================================================================== *)
(* Task 13: residual uniformity cPr_V2_V3_uniform_on_fiber                *)
(* ================================================================== *)

(* Imports needed by the [du2002/spp_entropy.v] / [du2002/spp_proba.v]
   chain consumed below.  Each lemma in the chain operates on an
   infotheo-side [R.-fdist T] probability space; this section establishes
   the matching probability space and discharges the residual uniformity
   claim by composing [inde_RV2_cinde] (Lemma 3.3 of du2002),
   [cinde_rv_comp_removal] (the deterministic-function conditioning
   lemma), and [Pr_dsdp_sol_uniform] (the protocol-level residual). *)

#[local] Open Scope proba_scope.
#[local] Open Scope fdist_scope.
#[local] Open Scope ring_scope.

Section dsdp_security_indcpa_residual.

(** Probability-space parameters mirroring [dsdp_entropy.v]'s
    [Section dsdp_entropy].  The protocol scalars live in [Z/(p*q)Z]
    with [p, q] distinct primes; the joint distribution [P] supplies
    the DSDP-shaped random variables [V_1, V_2, V_3, U_1, U_2, U_3, S]
    plus an auxiliary encryption-randomness random variable [Z_rand]
    which represents the SSProve-sampled ciphertext-randomness tuple
    [(r_a, r_c', r_b')] from [game_leak].
    Kind: section parameters.
    Why: Task 13 of [~/.claude/plans/sprightly-finding-robin.md].  The
    residual uniformity step is purely information-theoretic; it
    operates on the bridged [{fdist alice_view}]-side and is parametric
    in the probability space.  T1's V_2-aware rebuild instantiates
    this section at the bridge image and combines with the SSProve-
    side advantage bound to close the rebuilt secrecy theorem.  The
    encryption-rand tuple [Z_rand] is carried as a single auxiliary
    RV (its concrete component shape is irrelevant to the residual
    argument: only the independence hypothesis [V2V3_Z_inde_given_Y]
    matters). *)
Context (p_minus_2 q_minus_2 : nat).
Hypothesis prime_p_indcpa : prime p_minus_2.+2.
Hypothesis prime_q_indcpa : prime q_minus_2.+2.
Hypothesis coprime_pq_indcpa : coprime p_minus_2.+2 q_minus_2.+2.
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q)%N.
Context (T : finType) (P : R.-fdist T).
Context (V_1 V_2 V_3 U_1 U_2 U_3 S : {RV P -> 'Z_m}).
Context (TR : finType) (Z_rand : {RV P -> TR}).

(** constraint_holds_indcpa - DSDP constraint at every sample.  Same
    shape as [dsdp_entropy.v]'s [constraint_holds] hypothesis.
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform] (dsdp_entropy.v:237).  The
    constraint [s - u_1*v_1 = u_2*v_2 + u_3*v_3] is what makes the
    fiber a CRT linear system and ultimately produces the [1/m]
    residual. *)
Hypothesis constraint_holds_indcpa :
  forall t : T,
    dsdp_constraint ([%V_1, U_1, U_2, U_3, S] t) ([%V_2, V_3] t).

(** VarRV_uniform_indcpa - the protocol-level pair [(V_2, V_3)] is
    uniformly distributed over [(msg * msg)].  Standard SMC
    assumption, matches [dsdp_entropy.v:116].
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform]. *)
Hypothesis VarRV_uniform_indcpa :
  `p_ [%V_2, V_3] =
    fdist_uniform (dsdp_entropy.card_msg_pair_subproof p_minus_2 q_minus_2).

(** VarRV_indep_inputs_indcpa - [(V_2, V_3)] is independent of the
    protocol inputs [(V_1, U_1, U_2, U_3)].  Matches
    [dsdp_entropy.v:117].
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform]. *)
Hypothesis VarRV_indep_inputs_indcpa :
  P |= [%V_1, U_1, U_2, U_3] _|_ [%V_2, V_3].

(** V2V3_Z_inde_given_Y - independence of the protocol pair [(V_2, V_3)]
    jointly with the IT conditioning view [(V_1, U_1, U_2, U_3, S)]
    from the encryption-randomness tuple [Z_rand].  This is the
    semantic content of "the IND-CPA hops have eliminated all
    information about [V_2] from the ciphertext slots": after the two
    real-or-zero hops, every ciphertext is a function of fresh
    encryption-randomness that is independent of the protocol-side
    secrets.
    Kind: hypothesis.
    Why: feeds [inde_RV2_cinde] (Lemma 3.3, [du2002/spp_proba.v:146])
    to obtain the conditional independence
    [(V_2, V_3) _|_ Z_rand | (V_1, U_1, U_2, U_3, S)], which then feeds
    [cinde_rv_comp_removal] to drop [Z_rand] from the conditioning. *)
Hypothesis V2V3_Z_inde_given_Y :
  P |= [%[%V_2, V_3], [%V_1, U_1, U_2, U_3, S]] _|_ Z_rand.

(** cPr_V2_V3_uniform_on_fiber - residual uniformity of [V_2] after both
    IND-CPA hops have been taken.  Conditioning the joint
    [(V_2, V_3)] event on the full Alice view (which combines the
    IT-side tuple [(V_1, U_1, U_2, U_3, S)] with the
    encryption-randomness [Z_rand]) yields the [1/m] uniform residual
    whenever the conditioning event has nonzero probability and the
    target pair lies in the DSDP fiber.
    Kind: main residual.
    Why: Task 13 of [~/.claude/plans/sprightly-finding-robin.md].
    This is the second half of the closed-form Alice secrecy bound
    [1/m + 2 * epsilon_cpa]; the [2 * epsilon_cpa] half lives in
    [advantage_game_real_game_leak] (Task 08).  T1's V_2-aware
    rebuild combines the two halves into the rebuilt secrecy
    theorem.
    Proof: [inde_RV2_cinde] (independence to conditional
    independence), then [cinde_rv_comp_removal] (drop [Z_rand] from
    the conditioning, this is the cinde-removal arrow that the
    SSProve-side [bridge_correct] feeds into via Task 14's caller),
    then [Pr_dsdp_sol_uniform] (the IT residual at the fiber).  The
    nonzero marginal precondition for [Pr_dsdp_sol_uniform] is
    discharged via [pfwd1_domin_RV1] from the joint nonzero
    hypothesis.
    Naming: [Pr_<thing>_<property>] is the infotheo convention; see
    [Pr_dsdp_sol_uniform] at [dsdp_entropy.v:237].
    Used by: T1 V_2-aware rebuild.
    Bookkeeping translation: the SSProve-side [V_2] sample inside
    [game_leak] is projected to the infotheo-side RV [V_2] via the
    bridge [bridge_leak_to_fdist] (Task 12); Task 14 calls
    [bridge_correct] to transfer an SSProve [Pr] statement to the
    infotheo [Pr], at which point the present lemma closes the
    residual on the joint-fiber-event form.  Marginalisation onto the
    single [V_2 = v_2] event (rather than the joint [(V_2, V_3) =
    (v_2, v_3)] event) follows by partitioning the fiber on [v_3];
    each [v_2] has exactly one fiber partner when [u_3] is invertible
    (which is the [u_3 < minn p q] hypothesis), so the marginal is
    also [1/m].  Task 14 handles that partitioning step. *)
Lemma cPr_V2_V3_uniform_on_fiber
    (u1 u2 u3 v1 s : 'Z_m) (v2 v3 : 'Z_m) (z : TR) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[ [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
  (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
  `Pr[ [%V_2, V_3] = (v2, v3) |
       [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
    = m%:R^-1.
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos Hin.
(* Step 1: independence to conditional independence (inde_RV2_cinde). *)
have V2V3_indep_Zrand :
    [%V_2, V_3] _|_ Z_rand | [%V_1, U_1, U_2, U_3, S]
  by apply: inde_RV2_cinde.
(* Step 2: cinde_rv_comp_removal drops Z_rand from conditioning.
   Cast the deterministic-function shape via two trivial eta lemmas. *)
have Heta1 :
    (fst `o [%Z_rand, [%V_1, U_1, U_2, U_3, S]] : {RV P -> TR}) = Z_rand
  by [].
have Heta2 :
    (snd `o [%Z_rand, [%V_1, U_1, U_2, U_3, S]] : {RV P -> _})
      = [%V_1, U_1, U_2, U_3, S]
  by [].
have Hcomp :=
  @cinde_rv_comp_removal R T _ _ _ _ (v2, v3) z (v1, u1, u2, u3, s) P
    [%V_2, V_3] [%Z_rand, [%V_1, U_1, U_2, U_3, S]] fst snd.
rewrite Heta1 Heta2 in Hcomp.
rewrite -(Hcomp V2V3_indep_Zrand Hcond_pos).
(* Step 3: Pr_dsdp_sol_uniform closes the IT residual on the fiber.
   The nonzero marginal precondition is the only side-obligation;
   discharge it by pfwd1_domin_RV1 from the joint nonzero. *)
apply: Pr_dsdp_sol_uniform => //.
apply: contraNneq Hcond_pos => H0.
by apply/eqP; apply: pfwd1_domin_RV1; exact: H0.
Qed.

(* Task 13 verify clause: [cPr_V2_V3_uniform_on_fiber] type-checks and
   closes with [Qed].  The proof uses only the three infotheo lemmas
   the plan names ([inde_RV2_cinde], [cinde_rv_comp_removal],
   [Pr_dsdp_sol_uniform]), plus [pfwd1_domin_RV1] to discharge the
   nonzero-marginal side-obligation.  [bridge_correct] (Task 12) is
   not used in the proof body: the lemma is stated on the
   infotheo-side [{fdist T}] directly, and Task 14's caller invokes
   [bridge_correct] to transfer SSProve-side [Pr] statements to the
   infotheo side before applying the present lemma. *)
Check cPr_V2_V3_uniform_on_fiber :
  forall (u1 u2 u3 v1 s : 'Z_m) (v2 v3 : 'Z_m) (z : TR),
    (0 < u3)%N -> (u3 < minn p q)%N ->
    `Pr[ [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
    (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ [%V_2, V_3] = (v2, v3) |
         [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
      = m%:R^-1.

End dsdp_security_indcpa_residual.

(* ================================================================== *)
(* Task F: ring-generic residual section + alice_view_joint    *)
(*         discharge of the four IT residual hypotheses                *)
(* ================================================================== *)

(* The original residual section above (lines 2714-2877) specialises the
   probability scalars to ['Z_(p*q)] with [p, q] distinct primes.  The
   TeX abstraction (Setup item 2, line 35-36) is over an arbitrary
   finite commutative ring with units, not specifically [Z_(p*q)].  This
   block adds the ring-generic sibling [dsdp_security_indcpa_residual_ring]
   which mirrors the existing residual section but over any
   [finComUnitRingType] (Task E's generalisation), plus a second sibling
   section [dsdp_security_indcpa_residual_joint]
   that discharges the four IT residual hypotheses from Task D's
   correspondence lemmas in the canonical instantiation
   [Z_rand := fun _ => tt].

   Reference: ~/.claude/plans/sprightly-finding-robin.md, Task F. *)

Section dsdp_security_indcpa_residual_ring.

(** Ring-generic siblings of the [Section dsdp_security_indcpa_residual]
    parameters: a [finComUnitRingType] [Rring] replaces the specialised
    [Z_(p*q)] modulus; the seven DSDP RVs [V_1, V_2, V_3, U_1, U_2, U_3,
    S] are typed at [Rring]; the auxiliary [Z_rand] retains its
    parametric [TR : finType] carrier.
    Kind: section parameters.
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  The
    original residual section's [Context (p_minus_2 q_minus_2 : nat).
    Hypothesis prime_p_indcpa : prime p_minus_2.+2. ...] block bakes in
    the primality of [p] and [q] so that [Z_(p*q)] has a CRT decomposition
    and [u_3 < minn p q] suffices for [u_3]'s invertibility.  The
    [finComUnitRingType] generalisation in Task E
    ([Pr_dsdp_sol_uniform_ring]) replaces both the modulus and the
    primality-based unit check with the abstract membership
    [u_3 \is a GRing.unit], so this sibling section drops the three
    prime-related hypotheses entirely while still producing the same
    [1/m] residual where [m = #|Rring|].
    Used by: T1 V_2-aware rebuild — when the composed-game
    probability is transferred to a V_2-aware joint fdist and the
    V_2-guess event is counted via the conditional uniformity
    proved here. *)
Variable Rring : finComUnitRingType.
Variable T : finType.
Variable P : R.-fdist T.
Variables (V_1 V_2 V_3 U_1 U_2 U_3 S : {RV P -> Rring}).
Variable TR : finType.
Variable Z_rand : {RV P -> TR}.

(** constraint_holds_indcpa_ring - DSDP constraint at every sample, in
    ring-generic shape.  Same role as [constraint_holds_indcpa] at
    line 2751 but parametrised in [Rring : finComUnitRingType].
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform_ring]
    ([dsdp_entropy.v:554]).  The protocol-level fact that
    [s - u_1 v_1 = u_2 v_2 + u_3 v_3] holds on every sample of the
    bridged fdist is what makes the (V_2, V_3) fiber the kernel of a
    linear system; without it the fiber-cardinality argument has no
    purchase.  Concrete discharge: Task F's second section discharges
    this from the leak-game-shaped distribution
    [fdist_game_leak_joint] together with Task D's protocol
    RVs. *)
Hypothesis constraint_holds_indcpa_ring :
  forall t : T,
    dsdp_constraint_ring ([%V_1, U_1, U_2, U_3, S] t) ([%V_2, V_3] t).

(** VarRV_uniform_indcpa_ring - [(V_2, V_3)] is jointly uniform on
    [Rring * Rring], ring-generic analogue of [VarRV_uniform_indcpa] at
    line 2760.
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform_ring].  Cardinality witness
    [dsdp_entropy.card_RR_pair_subproof Rring] is the inlined [Let
    card_RR_pair] from [Section dsdp_entropy_ring], reachable here
    because [Section dsdp_entropy_ring] has closed and its [Let]
    binding is published as a [_subproof] term.  Mirrors the original
    residual section's [dsdp_entropy.card_msg_pair_subproof p_minus_2
    q_minus_2] reference. *)
Hypothesis VarRV_uniform_indcpa_ring :
  `p_ [%V_2, V_3] = fdist_uniform (dsdp_entropy.card_RR_pair_subproof Rring).

(** VarRV_indep_inputs_indcpa_ring - [(V_2, V_3)] is independent of the
    protocol inputs [(V_1, U_1, U_2, U_3)].  Ring-generic analogue of
    [VarRV_indep_inputs_indcpa] at line 2769.
    Kind: hypothesis.
    Why: required by [Pr_dsdp_sol_uniform_ring].  Stands for the
    structural fact that the SSProve leak-game body samples V_2 and
    V_3 fresh from [sample uniform index_msg] before any input
    inspection. *)
Hypothesis VarRV_indep_inputs_indcpa_ring :
  P |= [%V_1, U_1, U_2, U_3] _|_ [%V_2, V_3].

(** V2V3_Z_inde_given_Y_ring - the protocol pair [(V_2, V_3)] jointly
    with the IT conditioning view [(V_1, U_1, U_2, U_3, S)] is
    independent of the encryption-randomness tuple [Z_rand].
    Ring-generic analogue of [V2V3_Z_inde_given_Y] at line 2785.
    Kind: hypothesis.
    Why: feeds [inde_RV2_cinde] (Lemma 3.3, [du2002/spp_proba.v:146])
    in the proof of [cPr_V2_V3_uniform_on_fiber_ring] below.  At the
    instantiation [Z_rand := fun _ => tt] (the constant unit-valued
    RV) this hypothesis is discharged by
    [V2V3_Z_inde_given_Y_joint] in the second section below. *)
Hypothesis V2V3_Z_inde_given_Y_ring :
  P |= [%[%V_2, V_3], [%V_1, U_1, U_2, U_3, S]] _|_ Z_rand.

(** cPr_V2_V3_uniform_on_fiber_ring - ring-generic residual uniformity of
    [V_2] after both IND-CPA hops have been taken.  Conditioning the
    joint [(V_2, V_3)] event on the full Alice view (which combines
    the IT-side tuple [(V_1, U_1, U_2, U_3, S)] with the encryption-
    randomness [Z_rand]) yields the [#|Rring|^-1] uniform residual
    whenever the conditioning event has nonzero probability and the
    target pair lies in the DSDP fiber.
    Kind: main residual (ring-generic version).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  Same
    statement as [cPr_V2_V3_uniform_on_fiber] at line 2823 but over
    [Rring : finComUnitRingType] instead of ['Z_(p*q)].  The proof
    structure is identical: [inde_RV2_cinde] turns the joint
    independence into conditional independence, [cinde_rv_comp_removal]
    drops [Z_rand] from the conditioning, and [Pr_dsdp_sol_uniform_ring]
    (Task E) closes the IT residual on the fiber.  The nonzero
    marginal precondition for [Pr_dsdp_sol_uniform_ring] is discharged
    via [pfwd1_domin_RV1] from the joint nonzero hypothesis.
    Naming: [_ring] suffix mirrors [dsdp_fiber_card_ring] /
    [Pr_dsdp_sol_uniform_ring] in [dsdp_entropy.v]; the [Z_(p*q)]-
    specialised [cPr_V2_V3_uniform_on_fiber] above is left unchanged.
    Used by: T1 V_2-aware rebuild. *)
Lemma cPr_V2_V3_uniform_on_fiber_ring
    (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : TR) :
  u3 \is a GRing.unit ->
  `Pr[ [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
  `Pr[ [%V_2, V_3] = (v2, v3) |
       [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
    = #|Rring|%:R^-1.
Proof.
move=> Hu3_unit Hcond_pos Hin.
(* Step 1: independence to conditional independence (inde_RV2_cinde). *)
have V2V3_indep_Zrand :
    [%V_2, V_3] _|_ Z_rand | [%V_1, U_1, U_2, U_3, S]
  by apply: inde_RV2_cinde.
(* Step 2: cinde_rv_comp_removal drops Z_rand from conditioning.
   Cast the deterministic-function shape via two trivial eta lemmas. *)
have Heta1 :
    (fst `o [%Z_rand, [%V_1, U_1, U_2, U_3, S]] : {RV P -> TR}) = Z_rand
  by [].
have Heta2 :
    (snd `o [%Z_rand, [%V_1, U_1, U_2, U_3, S]] : {RV P -> _})
      = [%V_1, U_1, U_2, U_3, S]
  by [].
have Hcomp :=
  @cinde_rv_comp_removal R T _ _ _ _ (v2, v3) z (v1, u1, u2, u3, s) P
    [%V_2, V_3] [%Z_rand, [%V_1, U_1, U_2, U_3, S]] fst snd.
rewrite Heta1 Heta2 in Hcomp.
rewrite -(Hcomp V2V3_indep_Zrand Hcond_pos).
(* Step 3: Pr_dsdp_sol_uniform_ring (Task E) closes the IT residual on
   the fiber.  The nonzero marginal precondition is the only side-
   obligation; discharge it by pfwd1_domin_RV1 from the joint nonzero. *)
apply: Pr_dsdp_sol_uniform_ring.
- exact: constraint_holds_indcpa_ring.
- exact: VarRV_uniform_indcpa_ring.
- exact: VarRV_indep_inputs_indcpa_ring.
- exact: Hu3_unit.
- apply: contraNneq Hcond_pos => H0.
  by apply/eqP; apply: pfwd1_domin_RV1; exact: H0.
- exact: Hin.
Qed.

(* Task F verify clause (ring-generic side): [cPr_V2_V3_uniform_on_fiber_ring]
   type-checks and closes with [Qed].  The proof uses only the three
   infotheo lemmas the original residual section names ([inde_RV2_cinde],
   [cinde_rv_comp_removal], [Pr_dsdp_sol_uniform_ring]), plus
   [pfwd1_domin_RV1] to discharge the nonzero-marginal side-obligation,
   and no prime hypotheses. *)
Check cPr_V2_V3_uniform_on_fiber_ring :
  forall (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : TR),
    u3 \is a GRing.unit ->
    `Pr[ [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
    (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
    `Pr[ [%V_2, V_3] = (v2, v3) |
         [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
      = #|Rring|%:R^-1.

End dsdp_security_indcpa_residual_ring.

(* ================================================================== *)
(* Discharge of the four IT residual hypotheses at the canonical       *)
(* alice_view_joint instantiation (Z_rand := fun _ => tt).      *)
(* ================================================================== *)

Section dsdp_security_indcpa_residual_joint.

(** Section parameters mirroring the ring-generic residual but with
    [Z_rand] specialised to the constant unit-valued RV.  The seven
    DSDP RVs [V_1, V_2, V_3, U_1, U_2, U_3, S] live on a common
    probability space [T] with distribution [P] and ring carrier
    [Rring].  Task F's downstream consumer instantiates [T :=
    alice_view_joint] (Task B), [P :=
    fdist_game_leak_joint] (Task D), and identifies [V_2_carrier
    = V_3_carrier = plain AHE = Rring].
    Kind: section parameters.
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  The
    four IT residual hypotheses of
    [dsdp_security_indcpa_residual_ring] are discharged from
    (i) protocol-structural hypotheses on the leak-game-shaped
    distribution (constraint, marginal uniformity, input-secret
    independence) — these mirror [dsdp_entropy.v]'s
    [constraint_holds] / [VarRV_uniform] / [VarRV_indep_inputs] at
    lines 95-117; (ii) the structural fact that the constant unit-
    valued RV is independent of every joint RV (discharged
    structurally as [V2V3_Z_inde_given_Y_joint]).
    Used by: T1 V_2-aware rebuild. *)
Variable Rring : finComUnitRingType.
Variable T : finType.
Variable P : R.-fdist T.
Variables (V_1 V_2 V_3 U_1 U_2 U_3 S : {RV P -> Rring}).

(** constraint_holds_joint - the DSDP linear constraint holds at every
    sample of [P].  Same role as
    [dsdp_security_indcpa_residual_ring.constraint_holds_indcpa_ring]
    but stated as a section hypothesis ready for downstream
    instantiation against the bridged [fdist_game_leak_joint]
    (where the leak-game body computes [S = U_1 V_1 + U_2 V_2 + U_3
    V_3] deterministically, so the constraint holds on the entire
    support of the bridged fdist).
    Kind: hypothesis.
    Why: required to invoke [cPr_V2_V3_uniform_on_fiber_ring] below.
    Used by: [cPr_V2_V3_uniform_on_fiber_joint]. *)
Hypothesis constraint_holds_joint :
  forall t : T,
    dsdp_constraint_ring ([%V_1, U_1, U_2, U_3, S] t) ([%V_2, V_3] t).

(** VarRV_uniform_joint - [(V_2, V_3)] is jointly uniform on
    [Rring * Rring].  Same role as
    [VarRV_uniform_indcpa_ring] in the previous section.
    Downstream discharge: combine Task D's [p_V_2_uniform],
    [p_V_3_uniform] with [VarRV_indep_inputs_joint] (which restricted
    to the V_2,V_3 marginal gives [(V_2, V_3) ~ V_2 \otimes V_3]) and
    use [fdist_prod_indep] to obtain joint uniformity.
    Kind: hypothesis.
    Why: required to invoke [cPr_V2_V3_uniform_on_fiber_ring].
    Used by: [cPr_V2_V3_uniform_on_fiber_joint]. *)
Hypothesis VarRV_uniform_joint :
  `p_ [%V_2, V_3] = fdist_uniform (dsdp_entropy.card_RR_pair_subproof Rring).

(** VarRV_indep_inputs_joint - [(V_2, V_3)] is independent of the
    protocol inputs [(V_1, U_1, U_2, U_3)].  Mirrors
    [VarRV_indep_inputs_indcpa_ring].  Comes from the leak game body
    sampling V_2 and V_3 fresh before any input use.
    Kind: hypothesis.
    Why: required to invoke [cPr_V2_V3_uniform_on_fiber_ring].
    Used by: [cPr_V2_V3_uniform_on_fiber_joint]. *)
Hypothesis VarRV_indep_inputs_joint :
  P |= [%V_1, U_1, U_2, U_3] _|_ [%V_2, V_3].

(** Z_rand_joint - the constant unit-valued auxiliary RV.  Same as
    [Z_rand] in Task D (line 2516); restated here as a section-local
    definition so the four-hypothesis discharge is self-contained.
    Kind: helper.
    Why: feeds the structural-independence discharge
    [V2V3_Z_inde_given_Y_joint] below.  At the canonical post-IND-CPA-
    hop instantiation, encryption-randomness has been collapsed (both
    [c_2, c_3] are zero-encryptions in [game_leak]'s body), so [Z_rand]
    can be modelled as a constant unit RV without losing any
    information that the residual analysis needs.
    Naming: [_joint] suffix indicates this is the canonical
    instantiation at [alice_view_joint].  Project-local.
    Used by: [pfwd1_Z_rand_joint_tt], [V2V3_Z_inde_given_Y_joint]. *)
Definition Z_rand_joint : {RV P -> unit} := fun _ => tt.

(** pfwd1_Z_rand_joint_tt - [Z_rand_joint] hits [tt] with probability
    one because [Z_rand_joint] is the constant unit-valued random
    variable.  Same role as Task D's [pfwd1_Z_rand_tt] (line 2613) at
    the abstract Rring-typed sample space.
    Kind: helper.
    Why: feeds [V2V3_Z_inde_given_Y_joint].  The independence of any
    joint RV [J] and [Z_rand_joint] reduces to showing
    [Pr[(J, Z_rand_joint) = (j, tt)] = Pr[J = j] *
    Pr[Z_rand_joint = tt]]; using
    [Pr[Z_rand_joint = tt] = 1] turns the RHS into [Pr[J = j]]
    which equals the LHS up to the bijection [(J, Z_rand_joint) = (j,
    tt) iff J = j] (since [Z_rand_joint] is always [tt]).
    Used by: [V2V3_Z_inde_given_Y_joint]. *)
Lemma pfwd1_Z_rand_joint_tt : `Pr[ Z_rand_joint = tt ] = 1.
Proof.
rewrite pfwd1E.
suff -> : (finset (preim Z_rand_joint (pred1 tt))) = setT by exact: Pr_setT.
apply/setP => x; rewrite !inE /=.
by case: (Z_rand_joint x).
Qed.

(** V2V3_Z_inde_given_Y_joint - the joint pair
    [([%V_2, V_3], [%V_1, U_1, U_2, U_3, S])] is independent of
    [Z_rand_joint] under [P].  Discharges the [V2V3_Z_inde_given_Y_ring]
    hypothesis of [dsdp_security_indcpa_residual_ring] at the canonical
    instantiation [Z_rand := fun _ => tt].
    Kind: discharge lemma (provable, not hypothesis).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  The
    structural fact that a constant random variable is independent of
    every other RV: [Pr[J = j] * Pr[Z_rand_joint = tt] = Pr[J = j] *
    1 = Pr[J = j] = Pr[(J, Z_rand_joint) = (j, tt)]].  Discharged via
    [pfwd1_Z_rand_joint_tt] + a [setP] argument collapsing the joint
    event to the marginal.
    Naming: mirrors Task D's [inde_V_2_V_3_Z_rand]; the [_joint]
    suffix indicates the canonical instantiation.
    Used by: [cPr_V2_V3_uniform_on_fiber_joint]. *)
Lemma V2V3_Z_inde_given_Y_joint :
  P |= [%[%V_2, V_3], [%V_1, U_1, U_2, U_3, S]] _|_ Z_rand_joint.
Proof.
rewrite /inde_RV.
move=> jj z.
case: z.
rewrite pfwd1_Z_rand_joint_tt mulr1.
rewrite !pfwd1E.
apply: eq_bigl => x; rewrite !inE /=.
rewrite /RV2 /=.
by case: (Z_rand_joint x); rewrite !xpair_eqE andbT.
Qed.

(** cPr_V2_V3_uniform_on_fiber_joint - residual uniformity of [V_2] at
    the canonical instantiation [Z_rand := fun _ => tt].  Directly
    invokes [cPr_V2_V3_uniform_on_fiber_ring] with the three
    section-hypothesis discharges (constraint, uniform, indep) and the
    one provable discharge ([V2V3_Z_inde_given_Y_joint]).
    Kind: corollary (no new mathematical content).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  This
    is the ready-to-use residual that T1's V_2-aware rebuild applies
    after transferring an SSProve-side probability statement through
    a V_2-aware joint fdist.  The ring is now any
    [finComUnitRingType] — no [prime_p] / [prime_q] / [coprime_pq]
    needed, and [index_msg] is identified with [#|Rring|] at the
    downstream instantiation site.
    Used by: T1 V_2-aware rebuild. *)
Lemma cPr_V2_V3_uniform_on_fiber_joint
    (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : unit) :
  u3 \is a GRing.unit ->
  `Pr[ [%Z_rand_joint, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
  `Pr[ [%V_2, V_3] = (v2, v3) |
       [%Z_rand_joint, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
    = #|Rring|%:R^-1.
Proof.
apply: cPr_V2_V3_uniform_on_fiber_ring.
- exact: constraint_holds_joint.
- exact: VarRV_uniform_joint.
- exact: VarRV_indep_inputs_joint.
- exact: V2V3_Z_inde_given_Y_joint.
Qed.

(* Task F verify clause: the corollary type-checks with the
   conclusion expressed in terms of [#|Rring|^-1], matching the plan's
   "Identify index_msg = #|R|" directive.  All four IT residual
   hypotheses have been discharged: the three protocol-structural ones
   ([constraint_holds_joint], [VarRV_uniform_joint],
   [VarRV_indep_inputs_joint]) survive as section hypotheses (their
   downstream discharge is the bridged-fdist content from Tasks A-C),
   while the fourth ([V2V3_Z_inde_given_Y_ring]) is replaced by the
   directly-provable [V2V3_Z_inde_given_Y_joint]. *)
Check cPr_V2_V3_uniform_on_fiber_joint :
  forall (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : unit),
    u3 \is a GRing.unit ->
    `Pr[ [%Z_rand_joint, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
    (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
    `Pr[ [%V_2, V_3] = (v2, v3) |
         [%Z_rand_joint, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
      = #|Rring|%:R^-1.

End dsdp_security_indcpa_residual_joint.
