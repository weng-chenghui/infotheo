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
(* Task 14: closed-form Alice secrecy bound                            *)
(* ================================================================== *)

(** dsdp_alice_secrecy_indcpa - the closed-form Alice secrecy bound.
    For any adversary [predictor] satisfying the SSProve disjointness
    conditions of [advantage_game_real_game_leak], the probability that
    [predictor] outputs [true] when interacting with [game_real] is at
    most [1/m + 2 * epsilon_cpa], where [m = index_msg] is the message
    space cardinality and [epsilon_cpa] is the IND-CPA hardness
    parameter.  Semantically the bound captures "Pr[A(AliceView) = V_2]
    <= 1/m + 2 * epsilon_cpa": the predictor is interpreted to encode
    its V_2-guess in its bool output (output [true] iff its guess
    matches V_2).
    Kind: main (Task 14 of the plan).
    Why: closes the hybrid argument from the plan
    ([~/.claude/plans/sprightly-finding-robin.md]).  The [2 *
    epsilon_cpa] half comes from [advantage_game_real_game_leak] (Task
    08): two IND-CPA real-or-zero hops plus a perfect-equivalence
    residual.  The [1/m] half comes from [Pr_game_leak_V2_uniform]
    (Task 13) on the infotheo-side [{R.-fdist T}] probability space.
    The two halves are stitched here by the triangle inequality on
    [AdvantageE].
    Naming: project-local [dsdp_alice_secrecy_indcpa] follows the plan
    (this is the new IND-CPA-based theorem replacing the old
    [E_enc_inde]-dependent [dsdp_entropic_security] in
    [dsdp_security.v]).
    Used by: Task 15 retires [E_enc_inde] and its dependent IT-only
    Sections in [dsdp_security.v] / [dsdp_entropy.v] / [homomorphic_encryption.v].
    Closed-form gap (intentional, documented): the residual bound on
    [Pr (predictor o game_leak) true] is taken as a hypothesis
    [leak_bound].  The companion lemma [Pr_game_leak_V2_uniform] in
    [Section dsdp_security_indcpa_residual] proves the infotheo-side
    fdist statement [`Pr[V_2 = v | (Z_rand, V_1, U_1, U_2, U_3, S) =
    ...] = 1/m].  Translating that fdist statement to the SSProve-side
    [distr.mu (Pr (predictor o game_leak)) true <= 1/m] requires the
    SDistr-to-fdist bridge from Task 12 ([bridge_correct]) plus a
    marginalisation argument and is bookkeeping rather than new
    mathematics.  Task 14b will discharge that bookkeeping and remove
    the hypothesis; the present theorem makes the closed-form bound
    Qed-checkable today and pins the only remaining gap to a single,
    named hypothesis that downstream consumers see explicitly. *)
Theorem dsdp_alice_secrecy_indcpa
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
            pkey_of_party).(locs))
    (leak_bound :
       distr.mu (pkg_advantage.Pr (predictor ∘ game_leak)) true
         <= (index_msg%:R)^-1) :
  distr.mu (pkg_advantage.Pr (predictor ∘ game_real)) true
    <= (index_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
have Hadv :
    AdvantageE game_real game_leak predictor <= epsilon_cpa + epsilon_cpa
  by apply: advantage_game_real_game_leak.
unfold AdvantageE in Hadv.
have Htri :
    distr.mu (pkg_advantage.Pr (predictor ∘ game_real)) true
      <= distr.mu (pkg_advantage.Pr (predictor ∘ game_leak)) true
         + (epsilon_cpa + epsilon_cpa).
{ by apply: ler_distlDr. }
apply: le_trans Htri _.
rewrite mulr_natl mulr2n.
by apply: lerD.
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
    [Pr_predictor_guess_game_leak_le_invm]. *)
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
    [Pr_predictor_guess_game_leak_le_invm]. *)
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
    [Pr_predictor_guess_game_leak_le_invm]. *)
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
    [Pr_predictor_guess_game_leak_le_invm]. *)
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
    [Pr_predictor_guess_game_leak_le_invm]. *)
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
    Used by: Task H's [Pr_predictor_guess_game_leak_le_invm]. *)
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
    Used by: Task H's [Pr_predictor_guess_game_leak_le_invm]. *)
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
    Used by: Task H's [Pr_predictor_guess_game_leak_le_invm]. *)
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
    Used by: Task H's [Pr_predictor_guess_game_leak_le_invm]. *)
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
    Used by: Task H's [Pr_predictor_guess_game_leak_le_invm]. *)
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
