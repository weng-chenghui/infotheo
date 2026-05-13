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
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.

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

(** id_game_run — the single operation identifier exported by every
    game.  Calling it executes the joint protocol run and returns the
    ciphertext accumulator visible to corrupted Alice.
    Kind: canonical.
    Why: SSProve operations are identified by a [nat]; a single shared
    identifier across the four games keeps [game_iface] unique so
    [AdvantageE] is well-typed.
    Used by: game_iface and all four game packages. *)
Definition id_game_run : nat := 0%N.

(** game_iface — the shared export interface of the four games.  Each
    game exports a single operation [id_game_run] taking ['unit] and
    returning the ciphertext accumulator [ciphers].
    Kind: canonical.
    Why: the SSProve advantage [AdvantageE G_0 G_1 A] requires both
    games to share their export interface.  The IND-CPA hops in Task 08
    chain four games against this single shared signature.
    Used by: game_real, game_hybrid_one, game_hybrid_two, game_leak,
    and the Task 08 advantage triangle. *)
Definition game_iface : Interface :=
  [interface #val #[ id_game_run ] : 'unit → ciphers ].

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
  [package emptym ;
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
  [package emptym ;
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
  [package emptym ;
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
      let _v2 := msg_of_idx iV2 in
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
  [package emptym ;
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
      let _v2 := msg_of_idx iV2 in
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

(** msg_pack — pack_type notation aliasing [t_msg] inside the SSProve
    interface custom-entry grammar.  Mirrors the [cipher_t] notation
    declared above so the IND-CPA oracle import signature
    [#import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t}]
    parses cleanly inside the Task 07 translation packages. *)
Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

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
  [package emptym ;
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
  [package emptym ;
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
  do 10 ssprove_sync_eq=> ?.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  eapply rpost_weaken_rule.
  1: eapply rreflexivity_rule.
  cbn.
  intros [? ?] [? ?] e.
  inversion e.
  intuition auto.
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
  do 10 ssprove_sync_eq=> ?.
  rewrite chcipher_of_cipherK.
  eapply rpost_weaken_rule.
  1: eapply rreflexivity_rule.
  cbn.
  intros [? ?] [? ?] e.
  inversion e.
  intuition auto.
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
  (* Sample-order mismatch on the encryption randomness: game_hybrid_one
     samples irb1 (position 9) before irc1 (position 10), but
     translation_bob samples irc1 (position 9) before invoking the oracle
     (which adds Bob's randomness at position 10).  Swap them on the RHS. *)
  ssprove_swap_rhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  eapply rpost_weaken_rule.
  1: eapply rreflexivity_rule.
  cbn.
  intros [? ?] [? ?] e.
  inversion e.
  intuition auto.
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
  (* Sample-order mismatch on the encryption randomness, symmetric to
     [game_hybrid_one_equiv_bob_real]: swap LHS positions 9 and 10 to
     align with [game_hybrid_two]'s irb1-before-irc1 order. *)
  ssprove_swap_lhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  rewrite chcipher_of_cipherK.
  eapply rpost_weaken_rule.
  1: eapply rreflexivity_rule.
  cbn.
  intros [? ?] [? ?] e.
  inversion e.
  intuition auto.
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
     (both ciphertext slots encrypt the constant [0 : plain AHE]), so
     the perfect equivalence reduces to a reflexivity on the relational
     specification after stepping past the ten shared samples. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  do 10 ssprove_sync_eq=> ?.
  eapply rpost_weaken_rule.
  1: eapply rreflexivity_rule.
  cbn.
  intros [? ?] [? ?] e.
  inversion e.
  intuition auto.
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
    Used by: dsdp_alice_secrecy_indcpa (Task 14).
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
    Used by: Task 13's [Pr_game_leak_V2_uniform] (which feeds the
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
    Used by: Task 13's [Pr_game_leak_V2_uniform]. *)
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
    Used by: Task 13's [Pr_game_leak_V2_uniform]. *)
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

End dsdp_security_indcpa.
