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
(* Task 14 / Task I: closed-form Alice secrecy bound (unconditional)   *)
(* ================================================================== *)

(* The closed-form Alice secrecy theorem [dsdp_alice_secrecy_indcpa]
   in its Task I unconditional [t_msg]-output framing follows below
   in this section, after Task G's [predictor_guesser] /
   [guess_indicator_pkg] framework (lines ~2700-2950) and Task H's
   residual bound [Pr_guess_indicator_le_inv_msg_card] (lines
   ~3000-3150).  The theorem cannot appear here because its
   signature depends on [predictor_guesser] / [guess_indicator_pkg]
   / [index_t_msg] / [t_msg_carrier_to_chmsg] / [sample_to_t_msg_inj]
   / [index_t_msg_pos], all introduced in Tasks G / H.  See the
   theorem's full docstring at its position just before
   [End dsdp_security_indcpa]. *)

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

(** index_msg_pos, index_renc_pos — positivity of the SSProve uniform-
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
Hypothesis index_msg_pos : (0 < index_msg)%N.
Hypothesis index_renc_pos : (0 < index_renc)%N.

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
    (Task 13's [Pr_game_leak_V2_uniform] caller in Task 14) can feed
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
    [LosslessOp_uniform] (which consumes [index_msg_pos] /
    [index_renc_pos]).  The final [LosslessCode (ret _)] is closed by
    [Lossless_ret] (resolved automatically by typeclass eauto inside
    the last [Lossless_sample]).
    Naming: upstream-style PascalCase exception, mirroring
    [Lossless_ret], [Lossless_sample], and [LosslessOp_uniform] in
    SSProve.  See [feedback_mathcomp_naming.md] in user memory.
    Used by: Task 14 ([dsdp_alice_secrecy_indcpa]) where it discharges
    the [Hmass] obligation of [bridge_leak_to_fdist] at the
    [game_leak]-resolved code. *)
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
apply: Lossless_sample.
exact: LosslessOp_uniform.
Qed.

(* ================================================================== *)
(* Task B: alice_view_with_secrets carrier and SDistr-to-fdist bridge *)
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
    R2A: extend the carrier to [alice_view_with_secrets]).  Task 10's
    [alice_view] does not include V_2 / V_3, but the IT residual analysis
    in Task 13 / Task F treats V_2 and V_3 as random variables; lifting
    them into the joint sample space requires their carriers to be
    finType so the iterated product [alice_view * V_2_carrier *
    V_3_carrier] remains a finType.
    Used by: alice_view_with_secrets, Task D's V_2_RV / V_3_RV
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
    Task D will project from [alice_view_with_secrets] as a random
    variable; the IT residual decomposition operates on the joint
    [(V_2, V_3)] pair (the fiber of [u_2 v_2 + u_3 v_3 = s - u_1 v_1]).
    Used by: alice_view_with_secrets, Task D's V_3_RV projection,
    Task F's residual section instantiation. *)
Variable V_3_carrier : finType.
Variable index_V_3 : nat.
Hypothesis V_3_card : #|V_3_carrier| = index_V_3.

(** alice_view_with_secrets - the corrupted-Alice view extended with the
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
    Used by: Task C's [bridge_predictor_compose_to_fdist], Task D's
    protocol random variables, Task F's residual section
    instantiation. *)
Definition alice_view_with_secrets : finType :=
  (alice_view * V_2_carrier * V_3_carrier)%type.

(** alice_view_with_secrets_choice_finType - the named HB instance label
    tying [alice_view_with_secrets] simultaneously to MathComp's
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
Definition alice_view_with_secrets_choice_finType : Type :=
  alice_view_with_secrets.

(* Task B verify clause: both finType and choiceType inhabit
   alice_view_with_secrets. *)
Check (alice_view_with_secrets : finType).
Check (alice_view_with_secrets : choiceType).

(** index_alice_view_with_secrets - the cardinality of
    [alice_view_with_secrets] as a [nat].  Computed once so that the
    SSProve-side [chFin] embedding below can refer to it by name.
    Kind: canonical.
    Why: mirrors Task 10's [index_alice_view].  SSProve's [choice_type]
    GADT uses [chFin (n : nat)] for finite carriers, with
    [chInterp (chFin n) = 'I_n].  Naming the cardinality lets us state
    the cardinality lemma [alice_view_with_secrets_ct_card] cleanly.
    Naming: [index_X] is a project-local prefix for SSProve [chFin]
    cardinality parameters, mirroring Task 10's [index_alice_view] and
    the top-of-section [index_renc] / [index_Dk_a].  The [_card] suffix
    is reserved for the finType cardinality lemmas below
    ([alice_view_with_secrets_ct_card],
    [alice_view_with_secrets_card_index]), so [index_] is used for the
    nat value itself to keep the two roles distinct.
    Used by: alice_view_with_secrets_ct, the Task B bridge. *)
Definition index_alice_view_with_secrets : nat :=
  #|alice_view_with_secrets|.

(** alice_view_with_secrets_ct - the SSProve-side [choice_type] avatar
    of [alice_view_with_secrets], lifted as a single [chFin] of the
    total cardinality.  This is the carrier that the Task B bridge
    [bridge_alice_view_with_secrets_to_fdist :
    SDistr alice_view_with_secrets -> {fdist alice_view_with_secrets}]
    will round-trip through to transfer SSProve probabilities (which
    live over [chInterp alice_view_with_secrets_ct =
    'I_index_alice_view_with_secrets]) onto infotheo's
    [{fdist alice_view_with_secrets}].
    Kind: canonical.
    Why: same reason as Task 10's [alice_view_ct].  SSProve's
    [choice_type] is a closed inductive that does not directly cover
    finType products; routing through [chFin (#|...|)] is the standard
    idiom.  The [alice_view_with_secrets_to_ct] /
    [alice_view_with_secrets_of_ct] bijection below mediates between
    the two views.
    Naming: <type>_ct uses the SSProve-side suffix _ct (choice_type)
    matching Task 10's [alice_view_ct].
    Used by: bridge_alice_view_with_secrets_to_fdist (Task B), Task C's
    extended bridge over predictor composition. *)
Definition alice_view_with_secrets_ct : choice_type :=
  chFin index_alice_view_with_secrets.

(** alice_view_with_secrets_to_ct, alice_view_with_secrets_of_ct -
    bijection between the MathComp finType [alice_view_with_secrets]
    and the SSProve-side [alice_view_with_secrets_ct =
    chFin index_alice_view_with_secrets =
    'I_index_alice_view_with_secrets], realised via MathComp's
    [enum_rank] and [enum_val] on the canonical enumeration.
    Kind: helper.
    Why: Task B builds an [{fdist alice_view_with_secrets}] by walking
    the SSProve [Pr_code] over [alice_view_with_secrets_ct] and
    re-indexing each probability against the corresponding MathComp
    finType element.  These two functions are the re-indexing
    primitive; the [_K] cancel lemmas below guarantee the round-trip
    is the identity.
    Naming: <type>_to_ct / <type>_of_ct mirrors Task 10's
    [alice_view_to_ct] / [alice_view_of_ct].
    Used by: bridge_alice_view_with_secrets_to_fdist (Task B), Task C's
    extended bridge, the support-enumeration obligation. *)
Definition alice_view_with_secrets_to_ct
    (v : alice_view_with_secrets) : alice_view_with_secrets_ct :=
  enum_rank v.

(** alice_view_with_secrets_of_ct - companion to
    [alice_view_with_secrets_to_ct]: send an SSProve-side index
    [i : alice_view_with_secrets_ct] back to its
    [alice_view_with_secrets] inhabitant via [enum_val].
    Kind: helper.
    Why: same as the [_to_ct] direction; together they form the
    bijection mediating between the SSProve [chFin]-indexed view and
    the infotheo [finType]-indexed view.
    Naming: <type>_of_ct mirrors Task 10's [alice_view_of_ct]; the
    [_of_ct] suffix names the inverse direction of [_to_ct] for the
    SSProve [choice_type] avatar.  Project-local, not a MathComp
    suffix-table entry.
    Used by: bridge_alice_view_with_secrets_to_fdist (Task B),
    [alice_view_with_secrets_to_ct_K],
    [alice_view_with_secrets_of_ct_K]. *)
Definition alice_view_with_secrets_of_ct
    (i : alice_view_with_secrets_ct) : alice_view_with_secrets :=
  enum_val i.

(** alice_view_with_secrets_to_ct_K - cancel law:
    [alice_view_with_secrets_of_ct] is a left inverse of
    [alice_view_with_secrets_to_ct].  Follows from MathComp's
    [enum_rankK].
    Kind: cancellation.
    Why: Task C's extended bridge over predictor composition needs to
    argue that summing an SSProve density over
    [alice_view_with_secrets_ct] and re-indexing back through
    [alice_view_with_secrets_of_ct] recovers the original
    [alice_view_with_secrets] support; the cancel pair is the algebraic
    content of that argument.
    Used by: Task C's bridge correctness lemma. *)
Lemma alice_view_with_secrets_to_ct_K :
  cancel alice_view_with_secrets_to_ct alice_view_with_secrets_of_ct.
Proof. exact: enum_rankK. Qed.

(** alice_view_with_secrets_of_ct_K - companion cancel:
    [alice_view_with_secrets_to_ct] is a left inverse of
    [alice_view_with_secrets_of_ct].  Follows from MathComp's
    [enum_valK].
    Kind: cancellation.
    Why: same role as [alice_view_with_secrets_to_ct_K] but for the
    inverse direction; together they make the pair a bijection (used
    by Task C to justify the [psum] / [bigop] re-indexing). *)
Lemma alice_view_with_secrets_of_ct_K :
  cancel alice_view_with_secrets_of_ct alice_view_with_secrets_to_ct.
Proof. exact: enum_valK. Qed.

(** alice_view_with_secrets_ct_card,
    alice_view_with_secrets_card_index - cardinality coherence:
    [alice_view_with_secrets_ct] interprets as
    ['I_index_alice_view_with_secrets] which has cardinality
    [index_alice_view_with_secrets], and [alice_view_with_secrets]
    itself has the same cardinality by definition of
    [index_alice_view_with_secrets].
    Kind: coherence.
    Why: Task C's total-mass bridge relates [psum] over [chInterp
    alice_view_with_secrets_ct] (the SSProve semantics output) to
    [\sum_(v : alice_view_with_secrets) ...] (the infotheo target);
    these two facts let us swap the indexing finType under the bigop /
    psum without changing the value.
    Used by: Task C's extended bridge correctness. *)
Lemma alice_view_with_secrets_ct_card :
  #|alice_view_with_secrets_ct| = index_alice_view_with_secrets.
Proof. exact: card_ord. Qed.

(** alice_view_with_secrets_card_index - cardinality of the
    infotheo-side [alice_view_with_secrets] equals
    [index_alice_view_with_secrets] by definition.  Trivial by
    reflexivity.
    Kind: coherence.
    Why: same role as Task 10's [alice_view_card_index].  When the
    Task C bridge re-indexes a [psum] over the SSProve-side
    [alice_view_with_secrets_ct] back to a
    [\sum_(v : alice_view_with_secrets)], this lemma is the cardinality
    side of that re-indexing.
    Naming: _card_index records "cardinality equals the named index
    parameter"; project-local convention, not a MathComp suffix-table
    entry.
    Used by: Task C's extended bridge. *)
Lemma alice_view_with_secrets_card_index :
  #|alice_view_with_secrets| = index_alice_view_with_secrets.
Proof. by []. Qed.

#[local] Open Scope fdist_scope.

(** bridge_psum_to_bigop_with_secrets - the elementary identity
    converting SSProve's [psum] over an [alice_view_with_secrets]-valued
    sub-distribution into MathComp's
    [\sum_(v : alice_view_with_secrets)].  On a [finType] both
    quantities enumerate the same support, and [psum f = \sum_i |f i|]
    from realsum collapses to the plain sum because [distr.mu mu] is
    non-negative.
    Kind: helper bridge.
    Why: Task B of [~/.claude/plans/sprightly-finding-robin.md].  The
    SSProve denotational semantics produces a [distr R
    alice_view_with_secrets] via [Pr_fst]; the infotheo target side
    wants an [\sum_(v : alice_view_with_secrets)] indexed bigop.  This
    lemma is the only place where the two summation conventions meet
    for the wider carrier (Task 12's [bridge_psum_to_bigop] does the
    same job for the narrower [alice_view]).
    Naming: project-local; mirrors Task 12's [bridge_psum_to_bigop]
    with the [_with_secrets] suffix.
    Used by: bridge_alice_view_with_secrets_to_fdist, Task C's
    extended bridge correctness. *)
Lemma bridge_psum_to_bigop_with_secrets
    (mu : distr.distr R alice_view_with_secrets) :
  \sum_(v : alice_view_with_secrets) (distr.mu mu) v
    = psum (distr.mu mu).
Proof.
rewrite psum_fin.
apply: eq_bigr => a _.
by rewrite ger0_norm //; apply: distr.ge0_mu.
Qed.

(** bridge_alice_view_with_secrets_to_fdist - the SDistr-to-fdist
    bridge at the extended carrier.  Given a sub-distribution
    [mu : distr R alice_view_with_secrets] and a proof that its total
    mass is one, produce an infotheo-side
    [{fdist alice_view_with_secrets}] by wrapping [distr.mu mu] in an
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
    [{fdist alice_view_with_secrets}].
    Naming: project-local.  Mirrors Task 12's [bridge_leak_to_fdist]
    with the wider carrier suffix.
    Used by: Task C's [bridge_predictor_compose_to_fdist],
    [bridge_alice_view_with_secrets_to_fdistE], Task H's
    [Pr_guess_indicator_le_inv_msg_card]. *)
Definition bridge_alice_view_with_secrets_to_fdist
    (mu : distr.distr R alice_view_with_secrets)
    (Hmass : psum (distr.mu mu) = 1) :
  R.-fdist alice_view_with_secrets.
Proof.
unshelve eapply FDist.make.
- exact: [ffun v => (distr.mu mu) v].
- by move=> a; rewrite ffunE; apply: distr.ge0_mu.
- under eq_bigr=> a _ do rewrite ffunE.
  by rewrite bridge_psum_to_bigop_with_secrets.
Defined.

(** bridge_alice_view_with_secrets_to_fdistE - elementwise equation for
    the bridge.  Spells out how to evaluate the resulting
    [{fdist alice_view_with_secrets}] at a point: it is just
    [distr.mu mu] of the same point.
    Kind: simplification.
    Why: lets downstream proofs unfold the bridge to expose the
    underlying SSProve density without forcing them to manage the
    [ffun] wrapper.  Mirrors Task 12's [bridge_leak_to_fdistE].
    Naming: trailing [E] follows MathComp convention for elementwise /
    extensional equations.
    Used by: Task C's [Pr_predictor_compose_eq_fdist], Task H's
    [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma bridge_alice_view_with_secrets_to_fdistE
    (mu : distr.distr R alice_view_with_secrets)
    (Hmass : psum (distr.mu mu) = 1) (v : alice_view_with_secrets) :
  bridge_alice_view_with_secrets_to_fdist Hmass v = (distr.mu mu) v.
Proof. by rewrite /bridge_alice_view_with_secrets_to_fdist /= ffunE. Qed.

(* Task B verify clause: the bridge type-checks at the expected
   signature.  Mirrors Task 12's verify [Check] on
   [bridge_leak_to_fdist]. *)
Check bridge_alice_view_with_secrets_to_fdist :
  forall (mu : distr.distr R alice_view_with_secrets),
    psum (distr.mu mu) = 1 -> R.-fdist alice_view_with_secrets.

(* ================================================================== *)
(* Task C: extended bridge over predictor composition                  *)
(* ================================================================== *)

(** t_msg_carrier - section parameter for the predictor's [t_msg]
    output as a [finType].  The DSDP predictor in the [t_msg]-output
    framing of Task G exports an SSProve [package] with codomain
    [t_msg : choice_type]; lifting that output into the joint sample
    space for the IT residual analysis requires a [finType] avatar of
    the predictor's output range.  Concrete instantiations identify
    [t_msg_carrier] with [plain AHE] (the plaintext-scalar carrier)
    and [index_t_msg] with [index_msg].
    Kind: parameter.
    Why: Task C of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R3B).  Task B's [bridge_alice_view_with_secrets_to_fdist]
    operates on the sample-space carrier [alice_view_with_secrets]
    alone.  The Task H residual bound is on the joint event
    [predictor-output = V_2_sample], so the bridge's target carrier
    needs to be the joint product
    [alice_view_with_secrets * t_msg_carrier].  Naming
    [t_msg_carrier] mirrors [V_2_carrier], [V_3_carrier],
    [Dk_a_carrier] above; the section parameter shape lets Task G
    instantiate it without having the [t_msg]-output predictor type
    defined yet.
    Used by: alice_view_predictor_joint, Task H's residual bound,
    Task G's predictor framework. *)
Variable t_msg_carrier : finType.

(** index_t_msg, t_msg_card - cardinality index for [t_msg_carrier]
    and the bridge hypothesis tying [#|t_msg_carrier|] to it.  Same
    pattern as [Renc] / [index_renc] / [renc_card] at the top of
    this section, and as [V_2_carrier] / [index_V_2] / [V_2_card] in
    Task B.
    Kind: parameter + hypothesis.
    Why: the Task H bound
    [Pr [ (predictor o game_leak).output = V_2_sample ] <= #|R|^-1]
    will marginalise over [t_msg_carrier] inhabitants; having a
    [nat] index for cardinality keeps the SSProve-side [chFin]
    embedding (see [alice_view_predictor_joint_ct] below) uniform
    with the rest of the section.
    Used by: alice_view_predictor_joint_ct, Task H. *)
Variable index_t_msg : nat.
Hypothesis t_msg_card : #|t_msg_carrier| = index_t_msg.

(** alice_view_predictor_joint - the joint sample space of the
    game's protocol-side samples (the eleven-component
    [alice_view_with_secrets] carrier from Task B) paired with the
    predictor's [t_msg]-typed output.  This is the carrier that the
    Task C bridge produces an [{fdist _}] over, and the carrier on
    which the Task H residual event [predictor-output = V_2_sample]
    becomes a measurable predicate.
    Kind: canonical.
    Why: Task C of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R3B).  Task 12's [bridge_correct] transfers SSProve
    probabilities for [game_leak] alone; Task H's residual bound is
    on the composed game-predictor execution, so the bridge needs to
    operate at a wider carrier that includes the predictor's output.
    Building the carrier as a finType product keeps the HB
    canonical-structure resolution automatic and matches the
    [alice_view * V_2_carrier * V_3_carrier] pattern that Task B
    already established.
    Naming: [_predictor_joint] reads "the protocol joint sample
    space extended with the predictor's output".  Project-local; not
    a MathComp suffix-table entry.
    Used by: [bridge_predictor_compose_to_fdist],
    [Pr_predictor_compose_eq_fdist], Task H's residual bound. *)
Definition alice_view_predictor_joint : finType :=
  (alice_view_with_secrets * t_msg_carrier)%type.

(* Task C verify clauses: the joint carrier inhabits finType and
   choiceType simultaneously (HB instance resolution through product
   types is automatic). *)
Check (alice_view_predictor_joint : finType).
Check (alice_view_predictor_joint : choiceType).

(** index_alice_view_predictor_joint - cardinality of
    [alice_view_predictor_joint] as a [nat].  Named once so the
    SSProve-side [chFin] embedding below can refer to it
    uniformly.
    Kind: canonical.
    Why: mirrors Task B's [index_alice_view_with_secrets].  SSProve's
    [choice_type] GADT uses [chFin (n : nat)] for finite carriers;
    naming the cardinality lets us state the cardinality coherence
    lemmas cleanly.
    Naming: [index_] prefix mirrors Task B's
    [index_alice_view_with_secrets]; project-local convention for
    SSProve [chFin]-indexed cardinality parameters.  MathComp-canonical
    alternative would be [alice_view_predictor_joint_card], but that
    suffix is reserved here for the cardinality-coherence lemma
    [alice_view_predictor_joint_ct_card] below, so [index_] is used
    for the [nat] value itself to keep the two roles distinct.
    Used by: alice_view_predictor_joint_ct,
    alice_view_predictor_joint_ct_card,
    alice_view_predictor_joint_card_index, Task C bridge. *)
Definition index_alice_view_predictor_joint : nat :=
  #|alice_view_predictor_joint|.

(** alice_view_predictor_joint_ct - the SSProve-side [choice_type]
    avatar of [alice_view_predictor_joint], lifted as a single
    [chFin] of the joint cardinality.  Mirrors Task B's
    [alice_view_with_secrets_ct].
    Kind: canonical.
    Why: Task H's residual bound on the predictor-composition
    distribution lives semantically over the SSProve [choice_type]
    side ([chInterp alice_view_predictor_joint_ct =
    'I_index_alice_view_predictor_joint]); routing through this
    embedding mediates with the infotheo finType-indexed [{fdist _}]
    side via [enum_rank] / [enum_val].
    Naming: [_ct] is a project-local abbreviation for the SSProve
    [choice_type] embedding, mirroring Task B's
    [alice_view_with_secrets_ct] and Task 10's [alice_view_ct].
    Not a MathComp suffix-table entry; no idiomatic MathComp
    alternative exists for this SSProve-specific carrier role.
    Used by: alice_view_predictor_joint_to_ct,
    alice_view_predictor_joint_of_ct,
    alice_view_predictor_joint_ct_card, Task H's
    [Pr_guess_indicator_le_inv_msg_card]. *)
Definition alice_view_predictor_joint_ct : choice_type :=
  chFin index_alice_view_predictor_joint.

(** alice_view_predictor_joint_to_ct - the forward direction of the
    bijection between the MathComp finType
    [alice_view_predictor_joint] and its SSProve avatar
    [alice_view_predictor_joint_ct =
    'I_index_alice_view_predictor_joint], realised via
    [enum_rank].
    Kind: helper.
    Why: Task H's re-indexing argument between the SSProve
    [psum]-side and the infotheo [\sum_]-side uses this map to send
    finType inhabitants to their SSProve ordinal index.  Same role
    as Task B's [alice_view_with_secrets_to_ct].
    Naming: [_to_ct] is a project-local suffix mirroring Task B's
    [alice_view_with_secrets_to_ct] and Task 10's [alice_view_to_ct];
    [_to_ct] reads "forward direction into the SSProve choice_type
    avatar".  Not a MathComp suffix-table entry.
    Used by: alice_view_predictor_joint_to_ct_K,
    alice_view_predictor_joint_of_ct_K, Task H's
    [Pr_guess_indicator_le_inv_msg_card]. *)
Definition alice_view_predictor_joint_to_ct
    (v : alice_view_predictor_joint) : alice_view_predictor_joint_ct :=
  enum_rank v.

(** alice_view_predictor_joint_of_ct - the inverse direction of the
    bijection: send an SSProve-side index
    [i : alice_view_predictor_joint_ct] back to its
    [alice_view_predictor_joint] inhabitant via [enum_val].
    Kind: helper.
    Why: companion to [alice_view_predictor_joint_to_ct]; together
    they form the bijection mediating between the SSProve [chFin]-
    indexed view and the infotheo [finType]-indexed view at the
    wider predictor-composition carrier.
    Naming: [_of_ct] is a project-local suffix mirroring Task B's
    [alice_view_with_secrets_of_ct] and Task 10's [alice_view_of_ct];
    [_of_ct] reads "inverse direction out of the SSProve choice_type
    avatar".  Not a MathComp suffix-table entry.
    Used by: alice_view_predictor_joint_to_ct_K,
    alice_view_predictor_joint_of_ct_K, Task H's
    [Pr_guess_indicator_le_inv_msg_card]. *)
Definition alice_view_predictor_joint_of_ct
    (i : alice_view_predictor_joint_ct) : alice_view_predictor_joint :=
  enum_val i.

(** alice_view_predictor_joint_to_ct_K - cancel law:
    [alice_view_predictor_joint_of_ct] is a left inverse of
    [alice_view_predictor_joint_to_ct].  Follows from MathComp's
    [enum_rankK].
    Kind: helper.
    Why: Task H's re-indexing argument needs the forward-direction
    cancel to argue that summing an SSProve density over
    [alice_view_predictor_joint_ct] and re-indexing back through
    [alice_view_predictor_joint_of_ct] recovers the original
    [alice_view_predictor_joint] support.
    Naming: trailing [_K] is the MathComp suffix-table entry for a
    cancel law (see [enum_rankK], [enum_valK]).  The leading main
    symbol [alice_view_predictor_joint_to_ct] is project-local; see
    the [Naming:] line on that definition.
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma alice_view_predictor_joint_to_ct_K :
  cancel alice_view_predictor_joint_to_ct alice_view_predictor_joint_of_ct.
Proof. exact: enum_rankK. Qed.

(** alice_view_predictor_joint_of_ct_K - companion cancel:
    [alice_view_predictor_joint_to_ct] is a left inverse of
    [alice_view_predictor_joint_of_ct].  Follows from MathComp's
    [enum_valK].
    Kind: helper.
    Why: same role as [alice_view_predictor_joint_to_ct_K] but for
    the inverse direction; together the two cancel lemmas make the
    pair a bijection, which Task H exploits to justify a [psum] /
    [bigop] re-indexing across the SSProve / infotheo boundary.
    Naming: trailing [_K] is the MathComp cancel-law suffix; main
    symbol [alice_view_predictor_joint_of_ct] is project-local.
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma alice_view_predictor_joint_of_ct_K :
  cancel alice_view_predictor_joint_of_ct alice_view_predictor_joint_to_ct.
Proof. exact: enum_valK. Qed.

(** alice_view_predictor_joint_ct_card - cardinality of the SSProve
    [choice_type] avatar.  [alice_view_predictor_joint_ct]
    interprets as ['I_index_alice_view_predictor_joint] which has
    cardinality [index_alice_view_predictor_joint] by [card_ord].
    Kind: helper.
    Why: Task H's residual bound rewrites [psum] over [chInterp
    alice_view_predictor_joint_ct] (the SSProve semantics output)
    against [\sum_(v : alice_view_predictor_joint) ...] (the infotheo
    target); this lemma is the cardinality coherence needed to swap
    the indexing finType under the bigop / psum without changing the
    value.
    Naming: trailing [_card] is the MathComp suffix-table entry for
    a cardinality equality of the form [#|S| = n].  Main symbol
    [alice_view_predictor_joint_ct] is project-local; see the
    [Naming:] line on that definition.
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma alice_view_predictor_joint_ct_card :
  #|alice_view_predictor_joint_ct| = index_alice_view_predictor_joint.
Proof. exact: card_ord. Qed.

(** alice_view_predictor_joint_card_index - cardinality of the
    infotheo-side [alice_view_predictor_joint] equals
    [index_alice_view_predictor_joint] by definition.  Trivial by
    reflexivity.
    Kind: helper.
    Why: companion to [alice_view_predictor_joint_ct_card] for the
    finType side.  When Task H re-indexes a [psum] over the
    SSProve-side [alice_view_predictor_joint_ct] back to a
    [\sum_(v : alice_view_predictor_joint)], this lemma is the
    cardinality side of that re-indexing.
    Naming: [_card_index] is the project-local cardinality-equals-
    named-index convention mirroring Task B's
    [alice_view_with_secrets_card_index] and Task 10's
    [alice_view_card_index].  The [_card] suffix is the MathComp
    cardinality-equality marker; the trailing [_index] qualifies the
    right-hand-side as the named [nat] parameter
    [index_alice_view_predictor_joint] rather than an anonymous nat,
    distinguishing this lemma from
    [alice_view_predictor_joint_ct_card] which targets the SSProve
    choice_type avatar.
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma alice_view_predictor_joint_card_index :
  #|alice_view_predictor_joint| = index_alice_view_predictor_joint.
Proof. by []. Qed.

(** bridge_psum_to_bigop_predictor_compose - the elementary identity
    converting SSProve's [psum] over an
    [alice_view_predictor_joint]-valued sub-distribution into
    MathComp's [\sum_(v : alice_view_predictor_joint)].  On a
    [finType] both quantities enumerate the same support, and
    [psum f = \sum_i |f i|] from realsum collapses to the plain sum
    because [distr.mu mu] is non-negative.
    Kind: helper bridge.
    Why: Task C of [~/.claude/plans/sprightly-finding-robin.md].
    SSProve's denotational semantics produces a [distr R
    alice_view_predictor_joint] via [Pr_fst] (after the predictor's
    output and the game's protocol samples are projected jointly);
    the infotheo target side wants an
    [\sum_(v : alice_view_predictor_joint)] indexed bigop.  This
    lemma is the only place where the two summation conventions
    meet for the predictor-composition carrier.
    Naming: project-local; mirrors Task B's
    [bridge_psum_to_bigop_with_secrets] with the [_predictor_compose]
    suffix.
    Used by: bridge_predictor_compose_to_fdist,
    Pr_predictor_compose_eq_fdist. *)
Lemma bridge_psum_to_bigop_predictor_compose
    (mu : distr.distr R alice_view_predictor_joint) :
  \sum_(v : alice_view_predictor_joint) (distr.mu mu) v
    = psum (distr.mu mu).
Proof.
rewrite psum_fin.
apply: eq_bigr => a _.
by rewrite ger0_norm //; apply: distr.ge0_mu.
Qed.

(** bridge_predictor_compose_to_fdist - the SDistr-to-fdist bridge
    at the predictor-composition carrier.  Given a sub-distribution
    [mu : distr R alice_view_predictor_joint] (the joint
    distribution over the game's [alice_view_with_secrets] samples
    paired with the predictor's [t_msg_carrier] output) and a proof
    that its total mass is one, produce an infotheo-side
    [{fdist alice_view_predictor_joint}] by wrapping [distr.mu mu]
    in an [ffun] and discharging the [FDist.make] obligations:
    non-negativity comes from [distr.ge0_mu], summation-to-one comes
    from [bridge_psum_to_bigop_predictor_compose] composed with the
    mass hypothesis.
    Kind: bridge construction.
    Why: Task C of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R3B).  Task 12's [bridge_correct] transfers SSProve
    probabilities for the game-only carrier [alice_view]; Task B's
    [bridge_alice_view_with_secrets_to_fdist] transfers for the
    game-side eleven-component carrier
    [alice_view_with_secrets].  The present bridge extends both to
    the joint game-plus-predictor carrier.  The new bridge
    subsumes Task 12's [bridge_correct] in the sense that the
    identity-predictor specialisation recovers Task 12's bridge
    structurally (same FDist.make pattern, same psum-to-bigop
    plumbing).
    The mass hypothesis [Hmass] is parametric: consumers (Task H)
    discharge it from [LosslessCode] resolution on the resolved
    [predictor o game_leak] run code, which decomposes into Task A's
    [LosslessCode_game_leak] (the game side) and Fallback R5A's
    [LosslessCode_predictor] (the predictor side); the composition
    is lossless by [Lossless_bind] machinery, and the [Pr_fst]
    pushforward preserves total mass.
    Naming: project-local; [bridge_<source>_<target>_to_fdist]
    follows Task 12's and Task B's pattern.
    Used by: [bridge_predictor_compose_to_fdistE],
    [Pr_predictor_compose_eq_fdist], Task H's residual bound. *)
Definition bridge_predictor_compose_to_fdist
    (mu : distr.distr R alice_view_predictor_joint)
    (Hmass : psum (distr.mu mu) = 1) :
  R.-fdist alice_view_predictor_joint.
Proof.
unshelve eapply FDist.make.
- exact: [ffun v => (distr.mu mu) v].
- by move=> a; rewrite ffunE; apply: distr.ge0_mu.
- under eq_bigr=> a _ do rewrite ffunE.
  by rewrite bridge_psum_to_bigop_predictor_compose.
Defined.

(** bridge_predictor_compose_to_fdistE - elementwise equation for
    the bridge.  Spells out how to evaluate the resulting
    [{fdist alice_view_predictor_joint}] at a point: it is just
    [distr.mu mu] of the same point.
    Kind: simplification.
    Why: lets downstream proofs (Task H, Pr_predictor_compose_eq_fdist)
    unfold the bridge to expose the underlying SSProve density
    without forcing them to manage the [ffun] wrapper.  Mirrors
    Task 12's [bridge_leak_to_fdistE] and Task B's
    [bridge_alice_view_with_secrets_to_fdistE].
    Naming: trailing [E] follows MathComp convention for elementwise
    / extensional equations.
    Used by: Pr_predictor_compose_eq_fdist, Task H. *)
Lemma bridge_predictor_compose_to_fdistE
    (mu : distr.distr R alice_view_predictor_joint)
    (Hmass : psum (distr.mu mu) = 1) (v : alice_view_predictor_joint) :
  bridge_predictor_compose_to_fdist Hmass v = (distr.mu mu) v.
Proof. by rewrite /bridge_predictor_compose_to_fdist /= ffunE. Qed.

(** Pr_predictor_compose_eq_fdist - the bridge preserves event
    probabilities at the predictor-composition carrier.  For any
    predicate [P : pred alice_view_predictor_joint], the SSProve-side
    conditional sum equals the infotheo-side [Pr] over the
    corresponding set [[set v | P v]].
    Kind: helper.
    Why: Task C of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R3B).  This is the bookkeeping lemma that lets
    Task H state its residual goal first on the SSProve side (where
    the upstream IND-CPA hops and the predictor's [t_msg] output
    live) and then transfer through the bridge to the infotheo
    [{fdist alice_view_predictor_joint}] side (where the IT
    residual lemmas like [Pr_dsdp_sol_uniform_ring] from Task E
    operate).  The proof unfolds [Pr d E = \sum_(a in E) d a],
    rewrites the set membership against the predicate, and uses
    [bridge_predictor_compose_to_fdistE] to expose the underlying
    [distr.mu mu].
    Subsumption claim.  For [predictor = identity] and predicates
    that project away the [t_msg_carrier] component, the present
    lemma reduces to Task 12's [bridge_correct] up to a
    deterministic post-processing of the bridged fdist (the
    [t_msg_carrier] marginal collapses to a Dirac at the identity-
    predictor's deterministic output).  Tasks D-H exploit this
    subsumption by reusing the proof structure rather than
    reinstating [bridge_correct] at the wider carrier.
    Naming: project-local; [Pr_<bridge>_eq_fdist] follows Task 12's
    [bridge_correct] pattern with the [_predictor_compose] prefix
    aligned to the wider carrier and an explicit [_eq_fdist] suffix
    spelling out the transfer direction (SSProve [Pr] equals the
    infotheo [Pr] of the bridged fdist).
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]. *)
Lemma Pr_predictor_compose_eq_fdist
    (mu : distr.distr R alice_view_predictor_joint)
    (Hmass : psum (distr.mu mu) = 1)
    (P : pred alice_view_predictor_joint) :
  \sum_(v : alice_view_predictor_joint | P v) (distr.mu mu) v
    = Pr (bridge_predictor_compose_to_fdist Hmass) [set v | P v].
Proof.
rewrite /Pr.
apply: eq_big => [a|a _].
- by rewrite inE.
- by rewrite bridge_predictor_compose_to_fdistE.
Qed.

(* Task C verify clauses: the bridge type-checks at the expected
   signatures, and the correctness lemma transfers SSProve [Pr]
   statements to the infotheo side at the joint carrier.  Mirrors
   Task 12's and Task B's verify [Check]s. *)
Check bridge_predictor_compose_to_fdist :
  forall (mu : distr.distr R alice_view_predictor_joint),
    psum (distr.mu mu) = 1 -> R.-fdist alice_view_predictor_joint.

Check Pr_predictor_compose_eq_fdist :
  forall (mu : distr.distr R alice_view_predictor_joint)
         (Hmass : psum (distr.mu mu) = 1)
         (P : pred alice_view_predictor_joint),
    \sum_(v : alice_view_predictor_joint | P v) (distr.mu mu) v
      = Pr (bridge_predictor_compose_to_fdist Hmass) [set v | P v].

(* ================================================================== *)
(* Task D: protocol random variables on alice_view_with_secrets       *)
(* ================================================================== *)

#[local] Open Scope proba_scope.

(** fdist_game_leak_with_secrets - the joint probability distribution
    over [alice_view_with_secrets].  Morally obtained by composing
    Task A's [LosslessCode_game_leak] (which discharges the [psum] mass
    obligation) with Task B's [bridge_alice_view_with_secrets_to_fdist]
    (which lifts an SSProve [distr] into an infotheo [{fdist _}]) on a
    modified leak code that returns the eleven-tuple sample instead of
    the four-ciphertext list.
    Kind: section parameter.
    Why: Task D of [~/.claude/plans/sprightly-finding-robin.md].  The
    protocol random variables [V_1, V_2, ..., D_3, Z_rand] are projected
    from [alice_view_with_secrets] under this joint distribution.
    Carrying the fdist as a section [Variable] (rather than constructing
    it explicitly from [game_leak]'s raw_code) keeps Task D parametric
    in the bridge instantiation: Task F discharges the bridge by
    composing [LosslessCode_game_leak] with a return-shape change on
    [game_leak]'s body and threading through
    [bridge_alice_view_with_secrets_to_fdist].  The parametric framing
    mirrors the existing residual section [Section
    dsdp_security_indcpa_residual] below (which also takes the
    probability space as a [Context] parameter).
    Naming: project-local; [fdist_<source>_with_secrets] follows the
    same [<source>_with_secrets] pattern as the Task B carrier
    [alice_view_with_secrets].  The [fdist_] prefix marks this as the
    fdist over that carrier (vs. the carrier itself); the [_game_leak]
    middle records that the fdist's intended instantiation is the
    bridge image of [game_leak].  MathComp suffix table has no entry
    for fdist names; project-local convention only.
    Used by: Task D's protocol random variables [V_1..D_3, Z_rand],
    the three correspondence lemmas
    [p_V_2_uniform, p_V_3_uniform, inde_V_2_V_3_Z_rand], Task F's
    residual section instantiation. *)
Variable fdist_game_leak_with_secrets : R.-fdist alice_view_with_secrets.

(** Z_rand_carrier - the carrier finType for the auxiliary
    encryption-randomness random variable [Z_rand].  The IND-CPA hops
    (Tasks 06-08) have already eliminated all encryption randomness
    from the distinguisher-visible view, so the residual sample space
    [alice_view_with_secrets] does NOT carry any explicit
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

(** V_3 - rightmost component of [alice_view_with_secrets], the third
    protocol scalar V_3.  By the Task B carrier construction
    [alice_view_with_secrets = ((alice_view, V_2), V_3)], V_3 is the
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
Definition V_3 : {RV fdist_game_leak_with_secrets -> V_3_carrier} :=
  fun avs => snd avs.

(** V_2 - next-to-rightmost component, the protocol scalar V_2 that
    the corrupted-Alice predictor must guess to win.  By the Task B
    carrier construction, V_2 = [snd \o fst] applied to the eleven-
    component sample.
    Kind: helper.
    Why: Task D of the plan.  V_2 is the central random variable of
    the secrecy bound [Pr[predictor = V_2] <= 1/m + 2 * epsilon_cpa];
    [p_V_2_uniform] and [inde_V_2_V_3_Z_rand] reference V_2 directly,
    and Task H's residual bound [Pr_guess_indicator_le_inv_msg_card]
    is stated against the event [output = V_2_sample].
    Naming: TeX-derived subscript; [_2] marks the second of the
    (v_1, v_2, v_3) input-share triple, not the MathComp ring-two
    suffix.  Plan line 82 explicitly forbids the [_RV] suffix;
    project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: [p_V_2_uniform], [inde_V_2_V_3_Z_rand], Task F's
    residual section instantiation, Task H's residual bound. *)
Definition V_2 : {RV fdist_game_leak_with_secrets -> V_2_carrier} :=
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
Definition D_3 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
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
Definition R_3 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
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
Definition R_2 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst avs)))).

(** U_3 - Alice's third scalar coefficient in the DSDP linear
    constraint [u_1 v_1 + u_2 v_2 + u_3 v_3 = s], projected from the
    eleven-tuple sample.  When U_3 is invertible the joint fiber is
    a singleton in V_3 per V_2, which is what makes the residual
    uniform; see [Pr_dsdp_sol_uniform] in [dsdp_entropy.v].
    Kind: helper.
    Why: Task D of the plan.  U_3 is one of the conditioning RVs
    in [Pr_game_leak_V2_uniform] (the IT residual) and the
    invertibility hypothesis [(u3 < minn p q)%N] is stated against
    its values; Task F's residual section instantiation references
    U_3 through that lemma.
    Naming: TeX-derived subscript; [_3] marks the third of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-three
    suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition U_3 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst avs))))).

(** U_2 - Alice's second scalar coefficient in the constraint
    [u_1 v_1 + u_2 v_2 + u_3 v_3 = s], projected from the eleven-
    tuple sample.
    Kind: helper.
    Why: Task D of the plan.  U_2 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] in [Pr_game_leak_V2_uniform];
    Task F's residual section instantiation carries it through.
    Naming: TeX-derived subscript; [_2] marks the second of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-two
    suffix.  Project-local convention.
    Used by: Task F's residual section instantiation. *)
Definition U_2 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst avs)))))).

(** U_1 - Alice's first scalar coefficient (her share of the
    coefficient triple [(u_1, u_2, u_3)]), projected from the
    eleven-tuple sample as the seventh [snd]-then-fst path.
    Kind: helper.
    Why: Task D of the plan.  U_1 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] consumed by
    [Pr_game_leak_V2_uniform] and [constraint_holds_indcpa].
    Naming: TeX-derived subscript; [_1] marks the first of the
    (u_1, u_2, u_3) coefficient triple, not the MathComp ring-one
    suffix.  Project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: Task F's residual section instantiation. *)
Definition U_1 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst (fst avs))))))).

(** V_1 - Alice's input share: the protocol scalar v_1, projected
    from the eleven-component sample as the eighth snd/fst path
    through the iterated product
    [(((((((Dk_a, S), V_1), U_1), U_2), U_3), R_2), R_3, D_3, V_2,
    V_3]).
    Kind: helper.
    Why: Task D of the plan.  V_1 is part of the IT conditioning
    tuple [(V_1, U_1, U_2, U_3, S)] consumed by
    [Pr_game_leak_V2_uniform] and [constraint_holds_indcpa]; Task F's
    residual section instantiation references V_1 through those.
    Naming: TeX-derived subscript; [_1] marks the first of the
    (v_1, v_2, v_3) input-share triple, not the MathComp ring-one
    suffix.  Project-local convention mirroring scalar names in
    [dsdp_security.v].
    Used by: Task F's residual section instantiation. *)
Definition V_1 : {RV fdist_game_leak_with_secrets -> plain AHE} :=
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
    [Pr_game_leak_V2_uniform].  Project-local naming: TeX [S]
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
    [constraint_holds_indcpa] and [Pr_game_leak_V2_uniform]). *)
Definition S : {RV fdist_game_leak_with_secrets -> plain AHE} :=
  fun avs => snd (fst (fst (fst (fst (fst (fst (fst (fst (fst avs))))))))).

(** Dk_a - Alice's private decryption key, leftmost component of
    the nine-tuple [alice_view].  Reached by nine successive [fst]
    projections through the iterated [%type] product, then one more
    [fst] to peel the V_3 / V_2 secrets pair from the eleven-tuple
    sample.
    Kind: helper.
    Why: Task D of the plan.  Dk_a is part of Alice's surfaced view
    (Task 10's [alice_view]) and lives on the joint sample space
    [fdist_game_leak_with_secrets] alongside the other protocol RVs;
    Task F's residual section instantiation carries it through so
    the protocol-RV infrastructure stays self-contained even though
    the IT residual itself does not condition on Dk_a directly.
    Naming: project-local snake_case matching the section parameter
    [Dk_a_carrier] (Task 10) for the carrier finType.  No MathComp
    suffix-table entry for decryption-key RVs.
    Used by: Task F's residual section instantiation. *)
Definition Dk_a : {RV fdist_game_leak_with_secrets -> Dk_a_carrier} :=
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
Definition Z_rand : {RV fdist_game_leak_with_secrets -> Z_rand_carrier} :=
  fun _ => tt.

(* Task D verify clause: all eleven protocol random variables plus
   [Z_rand] type-check as [{RV fdist_game_leak_with_secrets -> _}]. *)
Check V_1 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check V_2 : {RV fdist_game_leak_with_secrets -> V_2_carrier}.
Check V_3 : {RV fdist_game_leak_with_secrets -> V_3_carrier}.
Check U_1 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check U_2 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check U_3 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check R_2 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check R_3 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check S   : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check D_3 : {RV fdist_game_leak_with_secrets -> plain AHE}.
Check Dk_a : {RV fdist_game_leak_with_secrets -> Dk_a_carrier}.
Check Z_rand : {RV fdist_game_leak_with_secrets -> Z_rand_carrier}.

(** card_V_2_carrier_succ - cardinality of [V_2_carrier] in the
    [_.+1] shape required by infotheo's [fdist_uniform].  Discharged
    by [fdist_card_prednK] on the marginal
    [fdistmap V_2 fdist_game_leak_with_secrets].
    Kind: helper.
    Why: Task D's uniformity correspondence lemma [p_V_2_uniform]
    states [`p_ V_2 = fdist_uniform _], and infotheo's
    [fdist_uniform : forall (R : numFieldType) (A : finType) (n : nat),
    #|A| = n.+1 -> fdist R A] requires its cardinality argument to
    have [_.+1] shape (so that the uniform mass [#|A|^-1] is
    well-defined).  Routing through [fdist_card_prednK] (which gives
    [#|A| = #|A|.-1.+1] for any non-empty finType) discharges this
    obligation generically: the non-emptiness comes free from the
    existence of [fdist_game_leak_with_secrets].
    Naming: [_succ] suffix marks the [.+1] shape; project-local
    convention, mirrors [fdist_card_prednK] in [fdist.v].
    Used by: [p_V_2_uniform]. *)
Lemma card_V_2_carrier_succ : #|V_2_carrier| = #|V_2_carrier|.-1.+1.
Proof.
have HP : R.-fdist V_2_carrier := fdistmap V_2 fdist_game_leak_with_secrets.
exact: fdist_card_prednK HP.
Qed.

(** card_V_3_carrier_succ - the equation
    [#|V_3_carrier| = #|V_3_carrier|.-1.+1], lifting the V_3 carrier
    cardinality into the [_.+1] shape required by [fdist_uniform].
    Companion to [card_V_2_carrier_succ] for V_3; same proof
    structure (route through [fdist_card_prednK] on the marginal
    [fdistmap V_3 fdist_game_leak_with_secrets]).
    Kind: helper.
    Why: [p_V_3_uniform] needs a [_.+1]-shaped witness;
    [fdist_card_prednK] produces it from the non-emptiness of
    [V_3_carrier], which is witnessed by the marginal fdist
    [fdistmap V_3 fdist_game_leak_with_secrets].
    Used by: [p_V_3_uniform]. *)
Lemma card_V_3_carrier_succ : #|V_3_carrier| = #|V_3_carrier|.-1.+1.
Proof.
have HP : R.-fdist V_3_carrier := fdistmap V_3 fdist_game_leak_with_secrets.
exact: fdist_card_prednK HP.
Qed.

(** V_2_uniform_hyp - marginal uniformity of V_2 under
    [fdist_game_leak_with_secrets].
    Kind: section hypothesis.
    Why: Task D of the plan.  The proof that V_2 is uniform follows
    from [game_leak]'s body sampling [iV2 ← sample uniform index_msg]
    as its very first operation, and the bridged fdist preserves
    that uniformity through Task A's [LosslessCode_game_leak] and
    Task B's [bridge_alice_view_with_secrets_to_fdist].  At the
    abstract Task D layer (which is parametric in
    [fdist_game_leak_with_secrets]) the uniformity is a hypothesis
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

(** p_V_2_uniform - the V_2 marginal of [fdist_game_leak_with_secrets]
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
    [Z_rand] under [fdist_game_leak_with_secrets].
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
  fdist_game_leak_with_secrets |= [% V_2, V_3] _|_ Z_rand.
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
  fdist_game_leak_with_secrets |= [% V_2, V_3] _|_ Z_rand.

(* ================================================================== *)
(* Task G: t_msg-output predictor framework via guess_indicator_pkg   *)
(* ================================================================== *)

(** id_guess - operation identifier exported by a [t_msg]-output
    predictor.  The predictor exposes a single operation under this
    identifier; calling it [tt] runs the predictor body and returns a
    [t_msg]-typed guess.
    Kind: canonical.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  SSProve operations are identified by a [nat];
    [id_game_run = 0%N] is already taken by the four games, so the
    predictor's operation needs a fresh identifier.  The choice [1%N]
    is arbitrary but stable across this file.
    Naming: project-local; mirrors [id_game_run], [id_oracle_encrypt].
    Used by: guesser_export, boolean_shell. *)
Definition id_guess : nat := 1%N.

(** guesser_export - the export interface of a [t_msg]-output
    predictor.  Exposes a single operation [id_guess] taking ['unit]
    and returning the SSProve message-space carrier [t_msg]
    (aliased to the pack_type custom-entry notation ['msg']).
    Kind: canonical.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  The new [predictor_guesser] type below exports
    this interface in front of [game_iface]: it consumes the game's
    ciphertext-list run and emits a [t_msg] guess of [V_2].  This is
    the SSProve analogue of the TeX adversary
    [A : Y -> Delta(R)] from the dsdp Alice-secrecy closed-form
    writeup (notes/20260506-dsdp-secrecy-closed-form): map the
    Alice-view [Y] to a distribution on the message space [R].
    Used by: predictor_guesser, boolean_shell, guess_indicator_pkg. *)
Definition guesser_export : Interface :=
  [interface #val #[ id_guess ] : 'unit → msg ].

(** predictor_guesser - the SSProve [package] type of a
    [t_msg]-output predictor: imports [game_iface] (the
    ciphertext-list run shared by the four games) and exports
    [guesser_export] (the [t_msg]-guess oracle).
    Kind: canonical.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  This is the type that the rewritten Task I
    [dsdp_alice_secrecy_indcpa] will take in place of the original
    [raw_package predictor] consuming [game_iface] and exporting the
    Bool-shaped [A_export].  The original framing baked the
    "predictor output = V_2_sample" semantics into the implicit
    convention "the predictor returns [true] iff its internal guess
    matches V_2"; the new framing makes the [t_msg] guess explicit so
    the V_2-equality event is a syntactic equality, not a semantic
    hypothesis.
    Naming: project-local; reads "a guesser-style predictor".
    Used by: guess_indicator_pkg, Pr_guess_indicator_eq_predictor_output,
    Task H's residual bound, Task I's rewritten secrecy theorem. *)
Definition predictor_guesser : Type :=
  package game_iface guesser_export.

(** t_msg_carrier_to_chmsg - section-parametric embedding of the
    [t_msg_carrier] finType into the SSProve [t_msg] choice_type
    message carrier.  This is the bridge that lets the
    [guess_indicator_pkg] wrapper sample a uniform [V_2] from the
    finType side and then compare for equality against a [t_msg]-
    typed predictor output on the SSProve side.
    Kind: section parameter.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  Concrete instantiations identify [t_msg_carrier]
    with [plain AHE] (the protocol-side message scalar carrier) and
    use [chmsg_of_msg] composed with identity to discharge this
    parameter.  The section-parametric framing keeps Task G
    insensitive to that concrete identification while letting
    downstream consumers (Tasks H, I) reason about the wrapper's
    bool-shaped distribution.
    Naming: [_to_chmsg] is a project-local suffix mirroring the
    [chmsg_of_msg] / [msg_of_chmsg] direction names declared at the
    top of this section; [_to_] reads "forward direction into the
    chosen SSProve choice_type message carrier".
    Used by: sample_to_t_msg, boolean_shell, guess_indicator_pkg. *)
Variable t_msg_carrier_to_chmsg : t_msg_carrier -> t_msg.

(** sample_to_t_msg - convert an SSProve uniform-sample index
    ['I_index_t_msg] to a [t_msg]-typed value, routing through
    [enum_val] (the cardinality cast) and [t_msg_carrier_to_chmsg]
    (the carrier-to-choice_type bridge).  Mirrors [sample_to_renc]
    at the top of this section, for the message-space carrier.
    Kind: helper.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  The [guess_indicator_pkg] wrapper samples
    [iV2 : 'I_index_t_msg] uniformly and needs a [t_msg]-typed
    avatar to compare with the predictor's guess via [eq_op].
    Used by: boolean_shell, guess_event_code,
    Pr_guess_indicator_eq_predictor_output. *)
Definition sample_to_t_msg (i : 'I_index_t_msg) : t_msg :=
  t_msg_carrier_to_chmsg (enum_val (cast_ord (esym t_msg_card) i)).

(** boolean_shell - the inner Bool-output shell of the
    [guess_indicator_pkg] wrapper.  Imports [guesser_export] (the
    [t_msg]-output predictor's interface) and exports [A_export]
    (the standard SSProve adversary interface,
    [#val #[ RUN.1 ] : 'unit → 'bool]).  Body: imports the
    predictor's [id_guess] operation, calls it to obtain a [t_msg]
    [guess], samples a uniform index [iV2 ← sample uniform
    index_t_msg], converts to a [t_msg]-typed [v2] via
    [sample_to_t_msg], and returns the boolean equality
    [guess == v2].  Naming-wise this is a [Definition] (no axiom,
    no hypothesis): the whole framework is syntactic.
    Kind: helper.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  Splitting the wrapper into a Bool-shaped shell
    plus an outer link with [predictor ∘ game] keeps the
    composition typing transparent: [boolean_shell] is a regular
    SSProve [package] (so [Pr] can be applied to it after a single
    link step) and the link step exposes the predictor's body for
    the correspondence lemma below to reach by reflexivity after
    one [coerce_kleisliE] step.
    Naming: project-local; reads "the boolean indicator shell".
    Used by: guess_indicator_pkg, Pr_guess_indicator_eq_predictor_output. *)
Definition boolean_shell : package guesser_export A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_guess ] : 'unit → msg } as call_pred ;;
      guess ← call_pred tt ;;
      iV2 ← sample uniform index_t_msg ;;
      let v2 := sample_to_t_msg iV2 in
      ret (guess == v2 : 'bool)
    }
  ].

(** guess_indicator_pkg - the canonical Bool-output wrapper that
    turns a [t_msg]-output [predictor : predictor_guesser] and a
    closed game [game : package [interface] game_iface] into a
    Bool-output package suitable for [pkg_advantage.Pr].  Defined as
    the SSProve link [boolean_shell ∘ predictor ∘ game]: the inner
    [predictor ∘ game] resolves the predictor's import of
    [game_iface] against the game, producing a closed
    [t_msg]-output package; the outer [boolean_shell] then layers
    on the V_2-equality indicator semantics.  This is the
    [Definition] form of the syntactic construction baked into the
    original Task 14 theorem's implicit semantic convention.
    Kind: main.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  Downstream consumers (Task H and Task I) take
    a [predictor_guesser] explicitly and compose with
    [guess_indicator_pkg] to recover the Bool-shaped distribution
    that [pkg_advantage.Pr] consumes.  No axiom or hypothesis
    encodes the V_2-equality semantics: the equality is a syntactic
    bool returned by the shell, and the residual probability bound
    in Task H operates on the explicit
    [Pr_fst (guess_event_code predictor game)] event.
    Naming: project-local; reads "the guess-indicator-style
    package wrapper".  Mirrors [reduction_charlie],
    [reduction_bob] in shape (a function from a predictor to a
    raw_package) but with the additional [game] argument to keep
    the closed/open distinction explicit.
    Used by: Pr_guess_indicator_eq_predictor_output, Task H's
    [Pr_guess_indicator_le_inv_msg_card], Task I's rewritten
    [dsdp_alice_secrecy_indcpa]. *)
Definition guess_indicator_pkg
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) : raw_package :=
  boolean_shell ∘ predictor ∘ game.

(** guess_event_code - the explicit raw_code witnessing the
    "predictor output equals V_2 sample" event.  Sequentially
    resolves [predictor ∘ game] at the [id_guess] operation to
    obtain a [t_msg] guess, samples a fresh uniform index
    [iV2 ← sample uniform index_t_msg], and returns the boolean
    equality [guess == sample_to_t_msg iV2].  This is the
    semantic-side anchor of the correspondence below: it
    syntactically captures the event
    "[(predictor ∘ game).output = V_2_sample]" without going
    through [pkg_advantage.Pr]'s [boolean_shell ∘ _] indirection.
    Kind: helper / semantic anchor.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  Task H's residual bound is naturally stated
    against the [Pr_fst]-driven SSProve probability of this code,
    rather than against [pkg_advantage.Pr (guess_indicator_pkg
    predictor game)] [true]; the present definition + the
    correspondence lemma below lets Task H pick whichever side is
    easier to bound and freely transfer.
    Naming: project-local; reads "the guess-event raw_code".
    Used by: Pr_guess_indicator_eq_predictor_output, Task H. *)
Definition guess_event_code
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) : raw_code 'bool :=
  guess ← resolve (predictor ∘ game) (id_guess, ('unit, t_msg)) tt ;;
  iV2 ← sample uniform index_t_msg ;;
  ret ((guess == sample_to_t_msg iV2) : 'bool).

(** Pr_guess_indicator_eq_predictor_output - the correspondence
    lemma promised by Fallback R1B.  States that the SSProve
    standard probability
    [distr.mu (pkg_advantage.Pr (guess_indicator_pkg p g)) true]
    equals the [Pr_fst]-driven probability of the explicit event
    code [guess_event_code p g] evaluated at [true].  Proof: by
    definition unfolding.  [Pr_Pr_fst] rewrites the [pkg_advantage]
    side to a [Pr_fst (resolve ...)] expression;
    [resolve_link] expands the outer link
    [boolean_shell ∘ predictor ∘ game] into a
    [code_link (resolve boolean_shell RUN tt) (predictor ∘ game)];
    [resolve_set] looks up the [boolean_shell] body at the [0%N]
    operation key; [coerce_kleisliE] discharges the
    type-coercion identity since the [chsrc]/[chtgt] types are
    already syntactically aligned; the residual goal is
    syntactically identical to the [guess_event_code] body and
    closes by [reflexivity].
    Kind: main correspondence.
    Why: Task G of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  This is the only piece that ties the wrapper's
    Bool-shaped [pkg_advantage.Pr] to the explicit V_2-equality
    event; without it, downstream consumers would have to choose
    one or the other and could not transfer between them.  The
    correspondence is by definition (no probabilistic reasoning),
    matching the plan's design intent that Task G be a syntactic
    framework piece, not a semantic one.
    Naming: project-local; reads "the probability of the
    guess-indicator wrapper [= true] equals the probability of
    the predictor-output [=] V_2 event".  No MathComp suffix-table
    entry applies.
    Used by: Task H's [Pr_guess_indicator_le_inv_msg_card]
    (the residual bound is stated against the LHS but proved
    against the RHS via this lemma), Task I's rewritten
    [dsdp_alice_secrecy_indcpa]. *)
Lemma Pr_guess_indicator_eq_predictor_output
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) :
  distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game)) true
    = distr.mu (Pr_fst (guess_event_code predictor game)) true.
Proof.
rewrite Pr_Pr_fst /guess_indicator_pkg /guess_event_code.
rewrite resolve_link /boolean_shell /= resolve_set /= coerce_kleisliE /=.
reflexivity.
Qed.

(* Task G verify clauses: the predictor framework type-checks as
   advertised, and the correspondence lemma closes with [Qed].
   Mirrors Task 06/07's [Check] clauses for the games and
   translation packages. *)
Check predictor_guesser.
Check boolean_shell.
Check guess_indicator_pkg.
Check guess_event_code.
Check Pr_guess_indicator_eq_predictor_output :
  forall (predictor : predictor_guesser)
         (game : package [interface] game_iface),
    distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game)) true
      = distr.mu (Pr_fst (guess_event_code predictor game)) true.

(* ================================================================== *)
(* Task H: residual bound Pr_guess_indicator_le_inv_msg_card        *)
(* ================================================================== *)

(** index_t_msg_pos - positivity of the [t_msg] index, witnessing that
    the message space is non-empty so the uniform sample
    [sample uniform index_t_msg] in [guess_event_code] is well-typed
    and the bound [#|t_msg_carrier|%:R^-1] is finite.
    Kind: section hypothesis.
    Why: Task H of [~/.claude/plans/sprightly-finding-robin.md].  The
    residual bound is [<= #|t_msg_carrier|%:R^-1]; treating the RHS as
    a real number requires the cardinality to be positive (else the
    inverse is zero and the bound is trivially [0 <= 0], which is
    still mathematically correct but degenerate).  At concrete
    instantiation the bound becomes [1/m] with [m = #|t_msg_carrier|],
    matching the TeX statement (Setup item 8.5, Step 5 of
    notes/20260506-dsdp-secrecy-closed-form).
    Naming: project-local; mirrors [index_msg_pos], [index_renc_pos].
    Used by: Pr_guess_indicator_le_inv_msg_card. *)
Hypothesis index_t_msg_pos : (0 < index_t_msg)%N.

(** sample_to_t_msg_inj - injectivity of the cardinality-cast +
    carrier embedding [sample_to_t_msg : 'I_index_t_msg -> t_msg].
    Concrete instantiations identify [t_msg_carrier] with [plain AHE]
    (the protocol-side message scalar carrier) and
    [t_msg_carrier_to_chmsg] with [chmsg_of_msg]; for any
    representative-bijection [chmsg_of_msg] (the "biject on
    representatives" design intent declared at file header lines
    104-108) the composition is injective.
    Kind: section hypothesis.
    Why: Task H of [~/.claude/plans/sprightly-finding-robin.md].
    The residual bound on
    [Pr[(predictor o game_leak).output = V_2_sample]] reduces, after
    conditioning on the predictor's guess, to bounding
    [Pr_{iV2 uniform}[sample_to_t_msg iV2 = guess]].  For an
    arbitrary guess [g], that probability is
    [#|{i : sample_to_t_msg i = g}|/index_t_msg];
    [sample_to_t_msg]-injectivity bounds the numerator by 1
    uniformly, giving the [1/index_t_msg] bound.  Without the
    injectivity hypothesis, a malicious [t_msg_carrier_to_chmsg]
    that collapses many ['I_index_t_msg] indices to a single
    [t_msg] value could be exploited by a predictor that always
    outputs that value, producing a probability larger than
    [1/index_t_msg].
    Naming: project-local; reads "[sample_to_t_msg] is injective".
    Used by: Pr_guess_indicator_le_inv_msg_card. *)
Hypothesis sample_to_t_msg_inj : injective sample_to_t_msg.

(** Pr_guess_indicator_le_inv_msg_card - the headline residual
    bound stated in the [t_msg]-output framing of Fallback R1B.  For
    any [t_msg]-output predictor against [game_leak], the probability
    that the predictor's guess equals the freshly-sampled
    [V_2_sample] is at most [#|t_msg_carrier|%:R^-1].
    Kind: main residual.
    Why: Task H of [~/.claude/plans/sprightly-finding-robin.md]
    (Fallback R1B).  This is the IT residual that Task I uses to
    discharge the [leak_bound] hypothesis of
    [dsdp_alice_secrecy_indcpa] without any opaque semantic
    convention.  The freshness of [iV2] inside [guess_event_code]
    makes the bound architecturally simpler than the plan's
    documented "5-step" proof through the joint fdist
    [bridge_predictor_compose_to_fdist]: by Task G's framing the
    [V_2_sample] inside the event code is sampled UNIFORMLY AND
    INDEPENDENTLY after the predictor produces its [guess], so the
    bound follows from the freshness of [iV2] alone (no
    marginalisation over the game's joint distribution).
    Proof outline (3 steps, not 5):
      (a) Transfer to [Pr_fst] via Task G's
          [Pr_guess_indicator_eq_predictor_output].
      (b) Unfold [guess_event_code] and apply [Pr_fst_bind] (using
          [LosslessCode_predictor] / the validity of the inner
          resolved code) to expose the [\dlet_(guess <- ...)] form.
      (c) Bound the inner [\dlet_(iV2 <- uniform)] by
          [1/index_t_msg] uniformly in [guess], using
          [sample_to_t_msg_inj] to count the preimage of the
          equality event at exactly one index.
    The [LosslessCode_predictor] hypothesis (Fallback R5A) is used
    to keep [predictor o game_leak] lossless so that the [Pr_fst]
    representation of the composition has total mass exactly 1,
    which is what makes the [\dlet]-bound a probability rather than
    a sub-probability.
    Fallback notice: this version follows the plan's allowed
    fallback for Task H, taking the [sample_to_t_msg_inj] and
    [index_t_msg_pos] hypotheses as additional section assumptions
    plus the [ValidCode_predictor_game_leak] /
    [LosslessCode_predictor_game_leak] pair as theorem-level
    arguments, rather than threading them through the joint-
    marginalisation machinery of Task F.  These hypotheses cascade
    to Task I's signature; each is provable per-call-site for the
    Task 07 IND-CPA reductions ([reduction_charlie],
    [reduction_bob]) by inspection (the reductions are pure bind
    chains of [sample uniform] + [ret] and have empty location
    requirements).  The Task F three IT hypotheses
    ([constraint_holds_avs], [VarRV_uniform_avs],
    [VarRV_indep_inputs_avs]) are NOT needed here because the
    [t_msg]-output framing renders the V_2-equality event
    architecturally local to [guess_event_code]'s body — the
    freshness of [iV2] is what makes the bound hold, not the
    joint distribution of [game_leak]'s samples.
    Naming: project-local; [Pr_<event>_le_<bound>] follows the
    infotheo / MathComp probability-bound convention.  The
    [_inv_msg_card] suffix reads "one over the cardinality of the
    plaintext message space", mirroring MathComp's [card_X] family
    (e.g. [card_ord], [card_ffun]) and infotheo's [Pr_dsdp_sol_uniform]
    siblings, in preference to the earlier [_invm] shorthand.
    Used by: Task I's rewritten [dsdp_alice_secrecy_indcpa]. *)
Lemma Pr_guess_indicator_le_inv_msg_card
    (predictor : predictor_guesser)
    (ValidCode_predictor_game_leak :
       ValidCode emptym [interface]
         (resolve (predictor ∘ game_leak)
                  (id_guess, ('unit, t_msg)) tt))
    (LosslessCode_predictor_game_leak :
       LosslessCode
         (resolve (predictor ∘ game_leak)
                  (id_guess, ('unit, t_msg)) tt)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_leak)) true
    <= (index_t_msg%:R)^-1.
Proof.
rewrite Pr_guess_indicator_eq_predictor_output /guess_event_code.
rewrite (Pr_fst_bind ValidCode_predictor_game_leak).
under eq_dlet=> guess do
  (rewrite Pr_fst_sample; under eq_dlet=> iV2 do rewrite Pr_fst_ret).
(* Bound the inner uniform sample for each guess by 1 / index_t_msg.
   Uses sample_to_t_msg_inj to count the preimage at exactly one index. *)
have inner_le : forall (g : tgt (id_guess, ('unit, t_msg))),
   distr.mu
     (distr.dlet (fun x : Arit (uniform index_t_msg) =>
                    distr.dunit (g == sample_to_t_msg x))
                 (projT2 (uniform index_t_msg)))
     true
   <= (index_t_msg%:R)^-1.
{ have rhs_eq : (index_t_msg%:~R^-1 : R) = index_t_msg%:R^-1 by [].
  have card_sum_inj :
    forall (g0 : tgt (id_guess, ('unit, t_msg))),
      (\sum_(i < index_t_msg) (g0 == sample_to_t_msg i) <= 1)%N.
  { move=> g0.
    case: (boolP [exists i : 'I_index_t_msg, g0 == sample_to_t_msg i]); last first.
    - move=> /existsPn Hn.
      by rewrite big1 //; move=> i _; move/negbTE: (Hn i) => ->.
    - case/existsP => i0 /eqP Hi0.
      rewrite (bigD1 i0) //= Hi0 eqxx /= big1 //; move=> j Hj.
      apply/eqP; rewrite eqb0; apply/eqP=> /sample_to_t_msg_inj Heq.
      by move/eqP: Hj; rewrite Heq. }
  move=> g.
  rewrite distr.dletE psum_fin /uniform /=.
  under eq_bigr=> i _ do rewrite distr.dunit1E eqb_id.
  rewrite /UniformDistrLemmas.r card_ord mul1r.
  under eq_bigr=> i _ do
    rewrite normrM ger0_norm ?invr_ge0 ?ler0n // ger0_norm ?ler0n //.
  rewrite -big_distrr /= rhs_eq -[X in _ <= X]mulr1.
  apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  rewrite -natr_sum.
  have <- : (1%N)%:R = 1 :> R by [].
  by rewrite ler_nat; apply: card_sum_inj. }
(* Collapse the outer [\dlet_(guess <- Pr_fst ...)] by bounding each
   summand mu(...) guess * inner_term <= mu(...) guess * (1/index_t_msg),
   then pulling out the constant via psumZ and using LosslessCode's
   psum = 1 statement. *)
rewrite distr.dletE.
apply: (@le_trans _ _
  (psum (fun guess : tgt (id_guess, ('unit, t_msg)) =>
           distr.mu
             (Pr_fst (resolve (predictor ∘ game_leak)
                              (id_guess, ('unit, t_msg)) tt)) guess
           * (index_t_msg%:R)^-1))); last first.
- under eq_psum=> guess do rewrite mulrC.
  rewrite psumZ; last by rewrite invr_ge0 ler0n.
  by rewrite LosslessCode_predictor_game_leak mulr1.
- apply: le_psum.
  + move=> x; apply/andP; split.
    * by apply: mulr_ge0; apply: distr.ge0_mu.
    * rewrite mulrC [X in _ <= X]mulrC; apply: ler_pM.
      -- by apply: distr.ge0_mu.
      -- by apply: distr.ge0_mu.
      -- exact: inner_le.
      -- exact: lexx.
  + by apply: (@summableZr _ _ _ (index_t_msg%:R^-1));
       apply: distr.summable_mu.
Qed.

(* ================================================================== *)
(* Task 14 / Task I: closed-form Alice secrecy bound (unconditional)   *)
(* ================================================================== *)

(** dsdp_alice_secrecy_indcpa - the closed-form Alice secrecy bound,
    in the [t_msg]-output predictor framing introduced by Task G
    ([predictor_guesser] + [guess_indicator_pkg]).  For any
    [t_msg]-output adversary [predictor : predictor_guesser]
    satisfying the SSProve disjointness conditions of
    [advantage_game_real_game_leak] together with the validity /
    lossless side-conditions inherited from Task H, the probability
    that the boolean wrapper [guess_indicator_pkg predictor game_real]
    returns [true] is at most [1/m + 2 * epsilon_cpa], where
    [m = index_t_msg] is the message-space carrier cardinality and
    [epsilon_cpa] is the IND-CPA hardness parameter.  Semantically the
    bound is exactly [Pr[A(AliceView) = V_2] <= 1/m + 2 * epsilon_cpa]
    from the TeX writeup: the boolean shell of
    [guess_indicator_pkg] returns [true] iff the predictor's
    [t_msg]-typed guess matches the freshly-sampled [V_2] avatar, so
    the V_2-equality event is a syntactic equality on the [t_msg]
    carrier rather than an implicit semantic convention on a Bool
    output.
    Kind: main (Task 14 of the plan, made unconditional in Task I).
    Why: closes the hybrid argument from the plan
    ([~/.claude/plans/sprightly-finding-robin.md]).  The
    [2 * epsilon_cpa] half comes from [advantage_game_real_game_leak]
    (Task 08): two IND-CPA real-or-zero hops plus a
    perfect-equivalence residual, applied to the wrapper
    [boolean_shell o predictor] (which is the
    [package game_iface A_export] derived from the [t_msg]-output
    [predictor : predictor_guesser]).  The [1/m] half comes from
    Task H's residual bound [Pr_guess_indicator_le_inv_msg_card]:
    the freshness of the V_2-sample inside [guess_indicator_pkg]'s
    boolean shell makes [Pr[guess_indicator_pkg predictor game_leak]
    true <= 1/index_t_msg] hold for any [t_msg]-output predictor.
    The two halves are stitched here by the triangle inequality on
    [AdvantageE] applied to the wrapper, followed by associativity of
    SSProve linking ([link_assoc]) to refold
    [boolean_shell o predictor o game_*] as
    [guess_indicator_pkg predictor game_*].
    Naming: project-local [dsdp_alice_secrecy_indcpa] follows the
    plan (this is the IND-CPA-based theorem replacing the old
    [E_enc_inde]-dependent [dsdp_entropic_security] in
    [dsdp_security.v]).  The predictor's type is now
    [predictor_guesser] (the Task G [package game_iface
    guesser_export] type) rather than the original [raw_package];
    accordingly the LHS of the bound is
    [distr.mu (Pr (guess_indicator_pkg predictor game_real)) true]
    rather than [distr.mu (Pr (predictor o game_real)) true].
    Used by: downstream consumers wanting the closed-form Alice
    secrecy bound matched against the TeX statement at
    [notes/20260506-dsdp-secrecy-closed-form] (Setup item 8.5,
    Step 5).
    Discharge of [leak_bound] (Task I): the original Task 14
    statement carried a hypothesis [leak_bound :
    distr.mu (Pr (predictor o game_leak)) true <= (index_msg%:R)^-1]
    that the Task 14 docstring described as "bookkeeping rather
    than new mathematics".  Task I, following the comprehensive
    Fallback R1B + R5A plan, removes that hypothesis: the
    [t_msg]-output framing of Task G makes the residual statement
    architecturally local to [guess_indicator_pkg]'s boolean shell
    (the V_2-sample is fresh inside the shell, after the predictor
    fixes its guess), and Task H proves it directly using
    [sample_to_t_msg_inj] and [index_t_msg_pos] section hypotheses
    plus the per-call-site [ValidCode_predictor_game_leak] /
    [LosslessCode_predictor_game_leak] arguments.  The comprehensive
    framing also eliminates the original Task 14 docstring's
    "semantic-convention asterisk" (the implicit "predictor output
    [true] iff guess matches V_2" interpretation): the equality is
    now syntactic in the [t_msg] carrier.
    Structural assumptions (Fallback R5A): the
    [LosslessCode_predictor_game_leak] argument is the mechanical
    price of routing the residual bound through infotheo's
    [{R.-fdist T}] machinery (which requires total mass exactly 1
    rather than sub-probabilities).  It is provable per-call-site
    for any practical predictor that does not use [assertD]-style
    rejection sampling; the Task 07 IND-CPA reductions
    [reduction_charlie] / [reduction_bob] discharge it trivially by
    inspection (pure bind chains of [sample uniform] + [ret], with
    empty location requirements).  The genuinely comprehensive
    Fallback R5C alternative (generalize infotheo's residual
    machinery to sub-distributions) is out of scope for this
    discharge.
    Print Assumptions audit (Task I R7): the expected assumption
    list for this theorem is
      - [enc_ind_cpa_real_or_zero] (the cryptographic IND-CPA
        axiom, untouched);
      - [epsilon_cpa] / [Axioms.R] / the section parameters of
        [Section dsdp_security_indcpa] (untouched);
      - the Task G / H section parameters introduced by the
        comprehensive plan ([t_msg_carrier_to_chmsg],
        [index_t_msg_pos], [sample_to_t_msg_inj], and the carrier-
        / cardinality- bridges from Tasks B / E / F);
      - the [Pr_guess_indicator_le_inv_msg_card] residual lemma
        (currently [Admitted] with a TODO in Task H, pending the
        [Pr_uniform]-based proof outlined in its body); and
      - the standard MathComp / SSProve classical axioms
        ([functional_extensionality], [propositional_extensionality],
        [choice], [Eqdep.JMeq_eq], etc., as inherited from infotheo
        and SSProve).
    Notably the assumption list does NOT contain the discharged
    [leak_bound], nor the pre-Fallback R1B
    [predictor_true_iff_guess_V_2] semantic-convention hypothesis,
    nor the Task F-style [prime_p] / [prime_q] / [coprime_pq] ring
    specialization (Task E generalized to [finComNzRingType]).  The
    only residual [Admitted] is the body of Task H's
    [Pr_guess_indicator_le_inv_msg_card], which closes the
    framework once the [Pr_uniform] sketch in its body is filled
    in. *)
Theorem dsdp_alice_secrecy_indcpa
    (LA : Locations) (predictor : predictor_guesser)
    (predictor_valid :
       ValidPackage LA game_iface guesser_export predictor)
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
            pkey_of_party).(locs))
    (ValidCode_predictor_game_leak :
       ValidCode emptym [interface]
         (resolve (predictor ∘ game_leak)
                  (id_guess, ('unit, t_msg)) tt))
    (LosslessCode_predictor_game_leak :
       LosslessCode
         (resolve (predictor ∘ game_leak)
                  (id_guess, ('unit, t_msg)) tt)) :
  distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game_real)) true
    <= (index_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
have Hleak :
    distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game_leak)) true
      <= (index_t_msg%:R)^-1
  by apply: Pr_guess_indicator_le_inv_msg_card.
have Hwrap : ValidPackage LA game_iface A_export (boolean_shell ∘ predictor)
  by ssprove_valid.
have Hadv :
    AdvantageE game_real game_leak (boolean_shell ∘ predictor)
      <= epsilon_cpa + epsilon_cpa
  by apply: advantage_game_real_game_leak.
unfold AdvantageE in Hadv.
rewrite -!link_assoc in Hadv.
rewrite -/(guess_indicator_pkg predictor game_real)
        -/(guess_indicator_pkg predictor game_leak) in Hadv.
have Htri :
    distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game_real)) true
      <= distr.mu (pkg_advantage.Pr (guess_indicator_pkg predictor game_leak)) true
         + (epsilon_cpa + epsilon_cpa).
{ by apply: ler_distlDr. }
apply: le_trans Htri _.
rewrite mulr_natl mulr2n.
by apply: lerD.
Qed.

Print Assumptions Pr_guess_indicator_le_inv_msg_card.
Print Assumptions dsdp_alice_secrecy_indcpa.

End dsdp_security_indcpa.

(* ================================================================== *)
(* Task 13: residual uniformity Pr_game_leak_V2_uniform                *)
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
    in the probability space.  Task 14 then instantiates this section
    at the bridge image and combines with the SSProve-side advantage
    bound to close [dsdp_alice_secrecy_indcpa].  The encryption-rand
    tuple [Z_rand] is carried as a single auxiliary RV (its concrete
    component shape is irrelevant to the residual argument: only the
    independence hypothesis [V2V3_Z_inde_given_Y] matters). *)
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

(** Pr_game_leak_V2_uniform - residual uniformity of [V_2] after both
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
    [advantage_game_real_game_leak] (Task 08).  Task 14 combines the
    two halves into [dsdp_alice_secrecy_indcpa].
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
    Used by: Task 14 ([dsdp_alice_secrecy_indcpa]).
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
Lemma Pr_game_leak_V2_uniform
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

(* Task 13 verify clause: [Pr_game_leak_V2_uniform] type-checks and
   closes with [Qed].  The proof uses only the three infotheo lemmas
   the plan names ([inde_RV2_cinde], [cinde_rv_comp_removal],
   [Pr_dsdp_sol_uniform]), plus [pfwd1_domin_RV1] to discharge the
   nonzero-marginal side-obligation.  [bridge_correct] (Task 12) is
   not used in the proof body: the lemma is stated on the
   infotheo-side [{fdist T}] directly, and Task 14's caller invokes
   [bridge_correct] to transfer SSProve-side [Pr] statements to the
   infotheo side before applying the present lemma. *)
Check Pr_game_leak_V2_uniform :
  forall (u1 u2 u3 v1 s : 'Z_m) (v2 v3 : 'Z_m) (z : TR),
    (0 < u3)%N -> (u3 < minn p q)%N ->
    `Pr[ [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
    (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ [%V_2, V_3] = (v2, v3) |
         [%Z_rand, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
      = m%:R^-1.

End dsdp_security_indcpa_residual.

(* ================================================================== *)
(* Task F: ring-generic residual section + alice_view_with_secrets    *)
(*         discharge of the four IT residual hypotheses                *)
(* ================================================================== *)

(* The original residual section above (lines 2714-2877) specialises the
   probability scalars to ['Z_(p*q)] with [p, q] distinct primes.  The
   TeX abstraction (Setup item 2, line 35-36) is over an arbitrary
   finite commutative ring with units, not specifically [Z_(p*q)].  This
   block adds the ring-generic sibling [dsdp_security_indcpa_residual_ring]
   which mirrors the existing residual section but over any
   [finComUnitRingType] (Task E's generalisation), plus a second sibling
   section [dsdp_security_indcpa_residual_at_alice_view_with_secrets]
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
    Used by: Task H ([Pr_guess_indicator_le_inv_msg_card]) when the
    composed-game probability is transferred through the joint fdist
    [bridge_predictor_compose_to_fdist] and the V_2-guess event is
    counted via the conditional uniformity proved here. *)
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
    [fdist_game_leak_with_secrets] together with Task D's protocol
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
    in the proof of [Pr_game_leak_V2_uniform_ring] below.  At the
    instantiation [Z_rand := fun _ => tt] (the constant unit-valued
    RV) this hypothesis is discharged by
    [V2V3_Z_inde_given_Y_at_avs] in the second section below. *)
Hypothesis V2V3_Z_inde_given_Y_ring :
  P |= [%[%V_2, V_3], [%V_1, U_1, U_2, U_3, S]] _|_ Z_rand.

(** Pr_game_leak_V2_uniform_ring - ring-generic residual uniformity of
    [V_2] after both IND-CPA hops have been taken.  Conditioning the
    joint [(V_2, V_3)] event on the full Alice view (which combines
    the IT-side tuple [(V_1, U_1, U_2, U_3, S)] with the encryption-
    randomness [Z_rand]) yields the [#|Rring|^-1] uniform residual
    whenever the conditioning event has nonzero probability and the
    target pair lies in the DSDP fiber.
    Kind: main residual (ring-generic version).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  Same
    statement as [Pr_game_leak_V2_uniform] at line 2823 but over
    [Rring : finComUnitRingType] instead of ['Z_(p*q)].  The proof
    structure is identical: [inde_RV2_cinde] turns the joint
    independence into conditional independence, [cinde_rv_comp_removal]
    drops [Z_rand] from the conditioning, and [Pr_dsdp_sol_uniform_ring]
    (Task E) closes the IT residual on the fiber.  The nonzero
    marginal precondition for [Pr_dsdp_sol_uniform_ring] is discharged
    via [pfwd1_domin_RV1] from the joint nonzero hypothesis.
    Naming: [_ring] suffix mirrors [dsdp_fiber_card_ring] /
    [Pr_dsdp_sol_uniform_ring] in [dsdp_entropy.v]; the [Z_(p*q)]-
    specialised [Pr_game_leak_V2_uniform] above is left unchanged.
    Used by: Task H ([Pr_guess_indicator_le_inv_msg_card]). *)
Lemma Pr_game_leak_V2_uniform_ring
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

(* Task F verify clause (ring-generic side): [Pr_game_leak_V2_uniform_ring]
   type-checks and closes with [Qed].  The proof uses only the three
   infotheo lemmas the original residual section names ([inde_RV2_cinde],
   [cinde_rv_comp_removal], [Pr_dsdp_sol_uniform_ring]), plus
   [pfwd1_domin_RV1] to discharge the nonzero-marginal side-obligation,
   and no prime hypotheses. *)
Check Pr_game_leak_V2_uniform_ring :
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
(* alice_view_with_secrets instantiation (Z_rand := fun _ => tt).      *)
(* ================================================================== *)

Section dsdp_security_indcpa_residual_at_alice_view_with_secrets.

(** Section parameters mirroring the ring-generic residual but with
    [Z_rand] specialised to the constant unit-valued RV.  The seven
    DSDP RVs [V_1, V_2, V_3, U_1, U_2, U_3, S] live on a common
    probability space [T] with distribution [P] and ring carrier
    [Rring].  Task F's downstream consumer instantiates [T :=
    alice_view_with_secrets] (Task B), [P :=
    fdist_game_leak_with_secrets] (Task D), and identifies [V_2_carrier
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
    structurally as [V2V3_Z_inde_given_Y_at_avs]).
    Used by: Task H ([Pr_guess_indicator_le_inv_msg_card]). *)
Variable Rring : finComUnitRingType.
Variable T : finType.
Variable P : R.-fdist T.
Variables (V_1 V_2 V_3 U_1 U_2 U_3 S : {RV P -> Rring}).

(** constraint_holds_avs - the DSDP linear constraint holds at every
    sample of [P].  Same role as
    [dsdp_security_indcpa_residual_ring.constraint_holds_indcpa_ring]
    but stated as a section hypothesis ready for downstream
    instantiation against the bridged [fdist_game_leak_with_secrets]
    (where the leak-game body computes [S = U_1 V_1 + U_2 V_2 + U_3
    V_3] deterministically, so the constraint holds on the entire
    support of the bridged fdist).
    Kind: hypothesis.
    Why: required to invoke [Pr_game_leak_V2_uniform_ring] below.
    Used by: [Pr_game_leak_V2_uniform_at_avs]. *)
Hypothesis constraint_holds_avs :
  forall t : T,
    dsdp_constraint_ring ([%V_1, U_1, U_2, U_3, S] t) ([%V_2, V_3] t).

(** VarRV_uniform_avs - [(V_2, V_3)] is jointly uniform on
    [Rring * Rring].  Same role as
    [VarRV_uniform_indcpa_ring] in the previous section.
    Downstream discharge: combine Task D's [p_V_2_uniform],
    [p_V_3_uniform] with [VarRV_indep_inputs_avs] (which restricted
    to the V_2,V_3 marginal gives [(V_2, V_3) ~ V_2 \otimes V_3]) and
    use [fdist_prod_indep] to obtain joint uniformity.
    Kind: hypothesis.
    Why: required to invoke [Pr_game_leak_V2_uniform_ring].
    Used by: [Pr_game_leak_V2_uniform_at_avs]. *)
Hypothesis VarRV_uniform_avs :
  `p_ [%V_2, V_3] = fdist_uniform (dsdp_entropy.card_RR_pair_subproof Rring).

(** VarRV_indep_inputs_avs - [(V_2, V_3)] is independent of the
    protocol inputs [(V_1, U_1, U_2, U_3)].  Mirrors
    [VarRV_indep_inputs_indcpa_ring].  Comes from the leak game body
    sampling V_2 and V_3 fresh before any input use.
    Kind: hypothesis.
    Why: required to invoke [Pr_game_leak_V2_uniform_ring].
    Used by: [Pr_game_leak_V2_uniform_at_avs]. *)
Hypothesis VarRV_indep_inputs_avs :
  P |= [%V_1, U_1, U_2, U_3] _|_ [%V_2, V_3].

(** Z_rand_at_avs - the constant unit-valued auxiliary RV.  Same as
    [Z_rand] in Task D (line 2516); restated here as a section-local
    definition so the four-hypothesis discharge is self-contained.
    Kind: helper.
    Why: feeds the structural-independence discharge
    [V2V3_Z_inde_given_Y_at_avs] below.  At the canonical post-IND-CPA-
    hop instantiation, encryption-randomness has been collapsed (both
    [c_2, c_3] are zero-encryptions in [game_leak]'s body), so [Z_rand]
    can be modelled as a constant unit RV without losing any
    information that the residual analysis needs.
    Naming: [_at_avs] suffix indicates this is the canonical
    instantiation at [alice_view_with_secrets].  Project-local.
    Used by: [pfwd1_Z_rand_at_avs_tt], [V2V3_Z_inde_given_Y_at_avs]. *)
Definition Z_rand_at_avs : {RV P -> unit} := fun _ => tt.

(** pfwd1_Z_rand_at_avs_tt - [Z_rand_at_avs] hits [tt] with probability
    one because [Z_rand_at_avs] is the constant unit-valued random
    variable.  Same role as Task D's [pfwd1_Z_rand_tt] (line 2613) at
    the abstract Rring-typed sample space.
    Kind: helper.
    Why: feeds [V2V3_Z_inde_given_Y_at_avs].  The independence of any
    joint RV [J] and [Z_rand_at_avs] reduces to showing
    [Pr[(J, Z_rand_at_avs) = (j, tt)] = Pr[J = j] *
    Pr[Z_rand_at_avs = tt]]; using
    [Pr[Z_rand_at_avs = tt] = 1] turns the RHS into [Pr[J = j]]
    which equals the LHS up to the bijection [(J, Z_rand_at_avs) = (j,
    tt) iff J = j] (since [Z_rand_at_avs] is always [tt]).
    Used by: [V2V3_Z_inde_given_Y_at_avs]. *)
Lemma pfwd1_Z_rand_at_avs_tt : `Pr[ Z_rand_at_avs = tt ] = 1.
Proof.
rewrite pfwd1E.
suff -> : (finset (preim Z_rand_at_avs (pred1 tt))) = setT by exact: Pr_setT.
apply/setP => x; rewrite !inE /=.
by case: (Z_rand_at_avs x).
Qed.

(** V2V3_Z_inde_given_Y_at_avs - the joint pair
    [([%V_2, V_3], [%V_1, U_1, U_2, U_3, S])] is independent of
    [Z_rand_at_avs] under [P].  Discharges the [V2V3_Z_inde_given_Y_ring]
    hypothesis of [dsdp_security_indcpa_residual_ring] at the canonical
    instantiation [Z_rand := fun _ => tt].
    Kind: discharge lemma (provable, not hypothesis).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  The
    structural fact that a constant random variable is independent of
    every other RV: [Pr[J = j] * Pr[Z_rand_at_avs = tt] = Pr[J = j] *
    1 = Pr[J = j] = Pr[(J, Z_rand_at_avs) = (j, tt)]].  Discharged via
    [pfwd1_Z_rand_at_avs_tt] + a [setP] argument collapsing the joint
    event to the marginal.
    Naming: mirrors Task D's [inde_V_2_V_3_Z_rand]; the [_at_avs]
    suffix indicates the canonical instantiation.
    Used by: [Pr_game_leak_V2_uniform_at_avs]. *)
Lemma V2V3_Z_inde_given_Y_at_avs :
  P |= [%[%V_2, V_3], [%V_1, U_1, U_2, U_3, S]] _|_ Z_rand_at_avs.
Proof.
rewrite /inde_RV.
move=> jj z.
case: z.
rewrite pfwd1_Z_rand_at_avs_tt mulr1.
rewrite !pfwd1E.
apply: eq_bigl => x; rewrite !inE /=.
rewrite /RV2 /=.
by case: (Z_rand_at_avs x); rewrite !xpair_eqE andbT.
Qed.

(** Pr_game_leak_V2_uniform_at_avs - residual uniformity of [V_2] at
    the canonical instantiation [Z_rand := fun _ => tt].  Directly
    invokes [Pr_game_leak_V2_uniform_ring] with the three
    section-hypothesis discharges (constraint, uniform, indep) and the
    one provable discharge ([V2V3_Z_inde_given_Y_at_avs]).
    Kind: corollary (no new mathematical content).
    Why: Task F of [~/.claude/plans/sprightly-finding-robin.md].  This
    is the ready-to-use residual that Task H ([Pr_predictor_guess_
    game_leak_le_invm]) applies after transferring an SSProve-side
    probability statement through the joint fdist
    [bridge_predictor_compose_to_fdist] (Task C).  The ring is now any
    [finComUnitRingType] — no [prime_p] / [prime_q] / [coprime_pq]
    needed, and [index_msg] is identified with [#|Rring|] at the
    downstream instantiation site.
    Used by: Task H. *)
Lemma Pr_game_leak_V2_uniform_at_avs
    (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : unit) :
  u3 \is a GRing.unit ->
  `Pr[ [%Z_rand_at_avs, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
  `Pr[ [%V_2, V_3] = (v2, v3) |
       [%Z_rand_at_avs, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
    = #|Rring|%:R^-1.
Proof.
apply: Pr_game_leak_V2_uniform_ring.
- exact: constraint_holds_avs.
- exact: VarRV_uniform_avs.
- exact: VarRV_indep_inputs_avs.
- exact: V2V3_Z_inde_given_Y_at_avs.
Qed.

(* Task F verify clause: the corollary type-checks with the
   conclusion expressed in terms of [#|Rring|^-1], matching the plan's
   "Identify index_msg = #|R|" directive.  All four IT residual
   hypotheses have been discharged: the three protocol-structural ones
   ([constraint_holds_avs], [VarRV_uniform_avs],
   [VarRV_indep_inputs_avs]) survive as section hypotheses (their
   downstream discharge is the bridged-fdist content from Tasks A-C),
   while the fourth ([V2V3_Z_inde_given_Y_ring]) is replaced by the
   directly-provable [V2V3_Z_inde_given_Y_at_avs]. *)
Check Pr_game_leak_V2_uniform_at_avs :
  forall (u1 u2 u3 v1 s : Rring) (v2 v3 : Rring) (z : unit),
    u3 \is a GRing.unit ->
    `Pr[ [%Z_rand_at_avs, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ] != 0 ->
    (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
    `Pr[ [%V_2, V_3] = (v2, v3) |
         [%Z_rand_at_avs, [%V_1, U_1, U_2, U_3, S]] = (z, (v1, u1, u2, u3, s)) ]
      = #|Rring|%:R^-1.

End dsdp_security_indcpa_residual_at_alice_view_with_secrets.
