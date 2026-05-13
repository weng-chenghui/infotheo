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
From mathcomp Require Import matrix ring boolp finmap reals.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition.
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

(** game_leak — ciphertext-free residual.  Returns an empty ciphertext
    list, modelling the worldwhere all four ciphertext slots have been
    replaced by deterministic functions of fresh encryption-randomness
    independent of (V_2, V_3, U_2, U_3, R_2, R_3).  Used to close the
    advantage triangle in Task 08.
    Kind: main.
    Why: Task 06 of the plan.  Once both IND-CPA hops have been taken,
    the remaining ciphertext content is independent of the protocol
    secret V_2.  Returning the empty accumulator makes this explicit at
    the package level.  The residual uniformity argument
    (Pr_game_leak_V2_uniform, Task 13) acts on this package.
    Used by: Tasks 08 (advantage triangle), 09 (perfect equivalence),
    13 (residual uniformity). *)
Definition game_leak :
  package [interface] game_iface :=
  [package emptym ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      ret ([::] : cipher_list)
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
    Proof status: Admitted; to be discharged by Task 09 via SSProve
    relational logic ([eq_rel_perf_ind_eq], [simplify_eq_rel],
    [ssprove_sync_eq], [rreflexivity_rule]), mirroring
    [IND_CPA_equiv_false] in [SSProve/examples/PRF.v] line 328.
    Used by: advantage_hop_real_h1, advantage_game_real_game_leak. *)
Lemma game_real_equiv_charlie_real :
  game_real ≈₀ translation_charlie ∘ oracle_real.
Proof.
  (* TODO Task 09: SSProve relational-logic equality. *)
Admitted.

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
    Proof status: Admitted; to be discharged by Task 09 via SSProve
    [eq_rel_perf_ind_eq].
    Used by: advantage_hop_real_h1, advantage_game_real_game_leak. *)
Lemma charlie_zero_equiv_game_hybrid_one :
  translation_charlie ∘ oracle_zero ≈₀ game_hybrid_one.
Proof.
  (* TODO Task 09: SSProve relational-logic equality. *)
Admitted.

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
    Proof status: Admitted; to be discharged by Task 09 via SSProve
    [eq_rel_perf_ind_eq] as for the Charlie case.
    Used by: advantage_hop_h1_h2, advantage_game_real_game_leak. *)
Lemma game_hybrid_one_equiv_bob_real :
  game_hybrid_one ≈₀ translation_bob ∘ oracle_real.
Proof.
  (* TODO Task 09: SSProve relational-logic equality. *)
Admitted.

(** bob_zero_equiv_game_hybrid_two — perfect equivalence between the
    Bob translation linked with the zero-encryption oracle and
    [game_hybrid_two].  Symmetric to [game_hybrid_one_equiv_bob_real]:
    both sides freeze Charlie and Bob slots to zero-encryptions.
    Kind: helper.
    Naming: SSProve game-equivalence convention; `equiv` placed medially
    between the two game operands so both sides of the [≈₀] relation are
    readable at the hop-2 boundary.
    Why: Task 08 uses this at the right end of the second IND-CPA hop.
    Proof status: Admitted; to be discharged by Task 09 via SSProve
    [eq_rel_perf_ind_eq].
    Used by: advantage_hop_h1_h2, advantage_game_real_game_leak. *)
Lemma bob_zero_equiv_game_hybrid_two :
  translation_bob ∘ oracle_zero ≈₀ game_hybrid_two.
Proof.
  (* TODO Task 09: SSProve relational-logic equality. *)
Admitted.

(** game_hybrid_two_perfect_game_leak — perfect equivalence between
    [game_hybrid_two] and [game_leak].  Once both ciphertext slots are
    zero-encryptions of the constant [0%R], the four-cipher accumulator
    carries no information about the protocol secrets (V_2, U_2, U_3,
    R_2, R_3); the residual is a function of fresh encryption randomness
    only.  Task 09 closes the equivalence formally by showing the joint
    distribution over the accumulator marginalises to a constant-list
    distribution agreeing with [game_leak]'s empty list under the
    observable projection used by the predictor.
    Kind: helper.
    Naming: SSProve game-equivalence convention; `perfect` placed
    medially between the two game operands marking the residual
    perfect-equivalence (zero-advantage) hop in the triangle chain.
    Why: Task 08 uses this at the right end of the triangle to collapse
    the residual hop [AdvantageE game_hybrid_two game_leak predictor] to
    zero, so the [2 * epsilon_cpa] bound closes.
    Proof status: Admitted; to be discharged by Task 09 via SSProve
    relational logic ([eq_rel_perf_ind_eq], [ssprove_swap_seq_rhs],
    [ssprove_code_simpl], [prove_perfect]) plus
    residual-distribution collapse.
    Used by: advantage_game_real_game_leak. *)
Lemma game_hybrid_two_perfect_game_leak :
  game_hybrid_two ≈₀ game_leak.
Proof.
  (* TODO Task 09: SSProve relational-logic equality
     plus residual-distribution collapse. *)
Admitted.

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

End dsdp_security_indcpa.
