(* DSDP Alice secrecy under IND-CPA, concrete-section instantiation.

   Builds AHE carriers (Renc / t_msg / t_cipher), finType bridges
   (rand_finType / cipher_finType), inhabitance witnesses
   (msg_inhabited / renc_inhabited / pub_key_inhab), and cancel laws
   (chmsg_of_msgK / chcipher_of_cipherK) at an arbitrary
   [AHE : AHEncType], plus their idealised / Benaloh / Paillier
   specialisations.  T1's V_2-aware game chain will plug these in
   to build the rebuilt closed-form secrecy bound.

   The earlier vacuous-chain closed-form theorem (Task I /
   dsdp_alice_secrecy_indcpa) and its random-guess corollaries
   (Task L / M / O / P) were retired in commit T0 after the
   predictor-side boolean_shell was found to sample a fresh
   independent iV2 disconnected from any IND-CPA hop.

   Plan: ~/.claude/plans/sprightly-finding-robin.md (T0 cleanup, T1
   rebuild).
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
Require Import dsdp_security_indcpa.
Require Import smc.ssprove_ext_lossless.
Require Import idealized_ahe.
From infotheo.homomorphic_encryption.benaloh1994 Require Import benaloh_ahe.
From infotheo.homomorphic_encryption.paillier1999 Require Import paillier_ahe.

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

(* Pin SSProve's real type as the ambient realType for this file (matches
   the convention in [dsdp_security_indcpa.v:47]). *)
Notation R := SSProve.Crypt.Axioms.R.

Module Concrete.

Section concrete.

(** AHE - the abstract AHE scheme this concrete instantiation is
    parametric in.  Matches the convention in
    [dsdp_security_indcpa.v:56].
    Kind: parameter.
    Why: the concrete carriers built below are functions of [AHE].
    Different AHE schemes give different concrete carriers, but the
    same closed-form bound applies uniformly.
    Used by: every concrete carrier and bijection below. *)
Variable AHE : AHEncType.

(** rand_finType, rand_finType_eq - extra finType-bridging variables
    for [rand AHE], which is a bare [Type] (per [he_types.v:40]) not a
    [finType].  Plan audit correction #5: SSProve cannot sample over
    a bare Type, so the concrete section declares a finType carrier
    plus an equality hypothesis tying its [Finite.sort] to [rand AHE].
    Kind: parameter + hypothesis.
    Why: needed to instantiate the abstract [Renc] / [rand_of_renc]
    section parameters.  For idealised AHE both reduce to [erefl]
    since [rand (Idealized_HETypes 'F_p) = 'F_p] which already carries
    a [finType] instance.
    Used by: Renc, rand_of_renc. *)
Variable rand_finType : Finite.type.
Hypothesis rand_finType_eq : Finite.sort rand_finType = rand AHE.

(** cipher_finType, cipher_finType_eq - extra finType-bridging
    variables for [cipher AHE], which is an [nzRingType] (per
    [he_types.v:43]) not a [finType].  Same pattern as
    [rand_finType].  Plan note: this was flagged as a possible extra
    bridge in the "If you stall" section.
    Kind: parameter + hypothesis.
    Why: needed to build [t_cipher := chFin
    #|cipher_finType|] and discharge [chcipher_of_cipher] /
    [cipher_of_chcipher] cleanly.  For idealised AHE the
    cipher is [Fp p] (a finComNzRingType hence a finType); the
    hypothesis is [erefl].
    Used by: t_cipher, chcipher_of_cipher,
    cipher_of_chcipher. *)
Variable cipher_finType : Finite.type.
Hypothesis cipher_finType_eq : Finite.sort cipher_finType = cipher AHE.

(** msg_inhabited, renc_inhabited, pub_key_inhab - inhabitance
    witnesses for [plain AHE], [rand_finType], and [pub_key AHE].
    Required to discharge auxiliary positivity hypotheses (used in
    the [Print Assumptions] closure transitively) and to build the
    constant [pkey_of_party] function.  Plan risk R1
    explicitly anticipated this need.
    Kind: parameter.
    Why: [AHEncType] does not carry inhabitance proofs in its mixin,
    so the concrete section requests them externally.  At idealised
    AHE all three are [0%R] or [GRing.zero].  [pub_key_inhab] is
    typed directly at [pub_key AHE] rather than at a separate
    [pub_key_finType] bridge: AHE schemes whose [pub_key] is a
    Record (Benaloh, Paillier) do not carry a [Finite] instance,
    and the only use of an inhabitance witness for [pub_key] in
    this concrete section is to build the constant [pkey_of_party]
    function, which does not need finite-type machinery.
    Used by: pkey_of_party (pub_key_inhab);
    index_msg_gt0 / index_renc_gt0 /
    index_t_msg_gt0 (msg / renc inhabited). *)
Variable msg_inhabited : plain AHE.
Variable renc_inhabited : rand_finType.
Variable pub_key_inhab : pub_key AHE.

(** index_msg - cardinality index for the plaintext-scalar
    carrier.  Picks [#|plain AHE|] so the cardinality coherence laws
    close by [erefl].
    Kind: concrete-carrier index.
    Why: discharges the abstract [index_msg : nat] section parameter
    of [Section dsdp_security_indcpa] (line 156).
    Used by: T1 V_2-aware rebuild. *)
Definition index_msg : nat := #|plain AHE|.

(** index_renc - cardinality index for the
    encryption-randomness carrier.  Picks [#|rand_finType|].
    Kind: concrete-carrier index.
    Why: discharges [index_renc] of the abstract section (line 68).
    Used by: T1 V_2-aware rebuild. *)
Definition index_renc : nat := #|rand_finType|.

(** Renc - concrete instantiation of the abstract [Renc :
    finType] section parameter (line 63).  Set to [rand_finType].
    Kind: concrete carrier.
    Why: discharges [Renc] of the abstract section.
    Used by: T1 V_2-aware rebuild. *)
Definition Renc : finType := rand_finType.

(** t_msg - concrete SSProve [choice_type] avatar of the
    message carrier, picked as [chFin #|plain AHE|].  The
    interpretation is ['I_#|plain AHE|], so [enum_rank] / [enum_val]
    bridge cleanly.
    Kind: concrete choice_type.
    Why: discharges [t_msg : choice_type] of the abstract section
    (line 91).
    Used by: T1 V_2-aware game chain (sprightly-finding-robin Task T1). *)
Definition t_msg : choice_type := chFin #|plain AHE|.

(** t_cipher - concrete SSProve [choice_type] avatar of the
    ciphertext carrier, picked as [chFin #|cipher_finType|].  Mirrors
    [t_msg] for the ciphertext side.
    Kind: concrete choice_type.
    Why: discharges [t_cipher : choice_type] of the abstract section
    (line 92).
    Used by: T1 V_2-aware rebuild. *)
Definition t_cipher : choice_type := chFin #|cipher_finType|.

(** msg_of_chmsg - concrete bijection from [t_msg]
    to [plain AHE].  [t_msg] interprets as
    ['I_#|plain AHE|], so [enum_val] is exactly the right shape.
    Kind: concrete bijection.
    Why: discharges [msg_of_chmsg : t_msg -> plain AHE] of the
    abstract section (line 93).
    Used by: T1 V_2-aware rebuild. *)
Definition msg_of_chmsg : t_msg -> plain AHE :=
  fun i => enum_val i.

(** chmsg_of_msg - concrete inverse [plain AHE ->
    t_msg].
    Kind: concrete bijection.
    Why: discharges [chmsg_of_msg : plain AHE -> t_msg] of the
    abstract section (line 94).
    Used by: T1 V_2-aware rebuild. *)
Definition chmsg_of_msg : plain AHE -> t_msg :=
  fun m => enum_rank m.

(** cipher_of_chcipher - concrete bijection [t_cipher
    -> cipher AHE], routing through [enum_val] on [cipher_finType]
    and the [cipher_finType_eq] cast.
    Kind: concrete bijection.
    Why: discharges [cipher_of_chcipher : t_cipher -> cipher AHE] of
    the abstract section (line 112).
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_of_chcipher : t_cipher -> cipher AHE :=
  fun i => eq_rect _ id (enum_val i : cipher_finType) _ cipher_finType_eq.

(** chcipher_of_cipher - concrete inverse [cipher AHE ->
    t_cipher].
    Kind: concrete bijection.
    Why: discharges [chcipher_of_cipher : cipher AHE -> t_cipher] of
    the abstract section (line 95).
    Used by: T1 V_2-aware rebuild. *)
Definition chcipher_of_cipher : cipher AHE -> t_cipher :=
  fun c => enum_rank (eq_rect _ id c _ (esym cipher_finType_eq)
                       : cipher_finType).

(** msg_of_idx - concrete bridge from ['I_index_msg]
    to [plain AHE].  Since [index_msg := #|plain AHE|] the
    domain is ['I_#|plain AHE|], so [enum_val] applies directly.
    Kind: concrete bijection.
    Why: discharges [msg_of_idx : 'I_index_msg -> plain AHE] of the
    abstract section (line 168).
    Used by: T1 V_2-aware rebuild. *)
Definition msg_of_idx : 'I_index_msg -> plain AHE :=
  fun i => enum_val i.

(** rand_of_renc - concrete bridge from [Renc] to
    [rand AHE].  Routes through the [rand_finType_eq] cast.
    Kind: concrete bijection.
    Why: discharges [rand_of_renc : Renc -> rand AHE] of the abstract
    section (line 86).
    Used by: T1 V_2-aware rebuild. *)
Definition rand_of_renc : Renc -> rand AHE :=
  fun r => eq_rect _ id r _ rand_finType_eq.

(** pkey_of_party - constant function assigning the same
    public key to every party.  The protocol logic does not depend on
    the key values themselves (the IND-CPA hops are key-independent
    at this layer), so a constant suffices.  Returns [pub_key_inhab]
    directly: since [pub_key_inhab] is now typed at [pub_key AHE]
    (Task N refactor), no [eq_rect] cast is needed.
    Kind: concrete supply.
    Why: discharges [pkey_of_party : party_id -> pub_key AHE] of the
    abstract section (line 149).
    Used by: T1 V_2-aware rebuild. *)
Definition pkey_of_party : party_id -> pub_key AHE :=
  fun _ => pub_key_inhab.

(** renc_card - cardinality coherence for [Renc].
    Closes by reflexivity since [Renc := rand_finType] and
    [index_renc := #|rand_finType|].
    Kind: coherence.
    Why: discharges [renc_card : #|Renc| = index_renc] (line 69).
    Used by: T1 V_2-aware rebuild. *)
Lemma renc_card : #|Renc| = index_renc.
Proof. by []. Qed.

(** index_msg_gt0 - positivity of [index_msg].
    Follows from [msg_inhabited : plain AHE] via [card_gt0P].
    Kind: positivity.
    Why: discharges [index_msg_pos] (line 1364) when needed in the
    [Print Assumptions] closure.
    Used by: downstream Task L. *)
Lemma index_msg_gt0 : (0 < index_msg)%N.
Proof. by apply/card_gt0P; exists msg_inhabited. Qed.

(** index_renc_gt0 - positivity of [index_renc].
    Follows from [renc_inhabited : rand_finType] via [card_gt0P].
    Kind: positivity.
    Why: discharges [index_renc_pos] (line 1365).
    Used by: downstream Task L. *)
Lemma index_renc_gt0 : (0 < index_renc)%N.
Proof. by apply/card_gt0P; exists renc_inhabited. Qed.

(** chmsg_of_msgK - cancel law for the message-side
    bijection.  Follows from MathComp's [enum_rankK].
    Kind: cancellation.
    Why: discharges [chmsg_of_msgK] (line 144).
    Used by: T1 V_2-aware rebuild. *)
Lemma chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.
Proof. exact: enum_rankK. Qed.

(** chcipher_of_cipherK - cancel law for the ciphertext-side
    bijection.  Routes through [eq_rect] cancellation on the
    [cipher_finType_eq] cast plus [enum_rankK].
    Kind: cancellation.
    Why: discharges [chcipher_of_cipherK] (line 130).
    Used by: T1 V_2-aware rebuild. *)
Lemma chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Proof.
move=> c.
rewrite /chcipher_of_cipher /cipher_of_chcipher.
rewrite enum_rankK.
by destruct cipher_finType_eq.
Qed.

End concrete.

End Concrete.

(* ================================================================== *)
(* Idealised-AHE specialisation                                        *)
(* ================================================================== *)

(** Module Idealized - idealised AHE specialisation (AHE / finType /
    inhabitance carriers) at the idealised AHE instance
    [Idealized_HETypes 'F_p] parametric in any [p : nat] (primality
    not required: MathComp's ['F_p] routes through [pdiv] making it a
    [finComNzRingType] unconditionally).  The three finType-bridge
    hypotheses of [Module Concrete] reduce to [erefl] since [rand],
    [pub_key], and [cipher] of the idealised AHE are all ['F_p] which
    already carries a [finType] instance.  Inhabitance witnesses are
    [GRing.zero : 'F_p].  T1's V_2-aware rebuild plugs these carriers
    into the new game chain.
    Plan: ~/.claude/plans/sprightly-finding-robin.md (T0 cleanup, T1
    rebuild). *)
Module Idealized.

Section idealized.

(** p - the modulus chosen for the idealised AHE.  Variable so the
    corollary is parametric in any nat.  MathComp's ['F_p] notation
    automatically routes through [pdiv] / [Fp_finComNzRingType] so
    primality of [p] is NOT required: ['F_p : finComNzRingType] holds
    for any [p : nat].
    Kind: parameter.
    Why: [Idealized_HETypes 'F_p] uses ['F_p] for all five HETypes
    carriers (see [idealized_ahe.v:49-54]).
    Used by: ahe, rand_fin, cipher_fin. *)
Variable p : nat.

(** ahe - the concrete idealised AHE scheme at ['F_p].  Built via
    [@AHEnc.Pack] over [Idealized_HETypes 'F_p] using the
    [Idealized_isEncDec] and [Idealized_isAHEnc] mixin instances
    declared in [idealized_ahe.v].  Mirrors the
    [Idealized_AHEnc_local] pattern in [dsdp_correctness.v:79-82].
    Kind: concrete carrier.
    Why: T1's V_2-aware rebuild needs a concrete [AHEncType] to
    specialise the [Module Concrete] carriers.  Idealised AHE is the
    simplest concrete instance.
    Used by: T1 V_2-aware rebuild. *)
Definition ahe : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes 'F_p)
    (@AHEnc.Class (Idealized_HETypes 'F_p)
      (@Idealized_isEncDec 'F_p)
      (@Idealized_isAHEnc 'F_p)).

(** rand_fin - finType carrier for [rand ahe].  Set to ['F_p]
    since the idealised AHE picks [msgT] (i.e. ['F_p]) for all
    five HETypes carriers (see [idealized_ahe.v:49-54]).
    Kind: concrete carrier.
    Why: discharges the [rand_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition rand_fin : Finite.type := 'F_p.

(** rand_fin_E - [Finite.sort rand_fin = rand ahe].  Both sides
    reduce to ['F_p] by [Idealized_HETypes]'s definition, so [erefl]
    closes it.  Suffix [E] is MathComp's canonical equational-rewrite
    suffix.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_fin_E : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe], same pattern
    as [rand_fin].
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'F_p.

(** cipher_fin_E - [Finite.sort cipher_fin = cipher ahe].  Closes
    by [erefl] for the same reason as [rand_fin_E].
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_fin_E : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

End idealized.

End Idealized.

(* ================================================================== *)
(* Task O: Benaloh 1994 AHE specialisation                             *)
(* ================================================================== *)

(** Module Benaloh - Benaloh 1994 AHE specialisation (AHE / finType / inhabitance carriers) at the
    Benaloh 1994 AHE instance [BenalohHETypes n r] parametric in any
    [n r : nat] with [1 < n] and [1 < r].  The carriers are:
    - [plain ahe = 'Z_r] (canonical [finType])
    - [rand ahe = {unit 'Z_n}] (canonical [finType] via [FinRing])
    - [cipher ahe = 'Z_n] (canonical [finType])
    - [pub_key ahe = BenalohPubKey n r] (a [Record], NOT a [finType])
    Inhabitance for [pub_key ahe] is built directly via
    [@MkBenalohPubKey n r 1%g pub_gen_order1] where [pub_gen_order1]
    proves [(val 1%g) ^+ r = 1] by [FinRing.val_unit1] + [expr1n].
    The Task N refactor of [Module Concrete] (taking [pub_key_inhab]
    directly at [pub_key AHE] rather than at a separate [Finite.type]
    bridge) makes this work without declaring an HB [Finite] instance
    on the [BenalohPubKey] record.

    T1's V_2-aware rebuild plugs these carriers into the new game
    chain.  Discharging [enc_ind_cpa_real_or_zero] from the
    higher-residuosity assumption (the cryptographic security of
    Benaloh) is a separate project out of scope here.
    Plan: ~/.claude/plans/sprightly-finding-robin.md (T0 cleanup, T1
    rebuild). *)
Module Benaloh.

Section benaloh.

(** n, r - the Benaloh modulus and message-block parameters.  [n] is
    the RSA-style composite (a product of two primes in the standard
    Benaloh instantiation), [r] is the message-space modulus dividing
    [phi(n)].  Both [> 1] so that ['Z_n] and ['Z_r] are non-trivial.
    Kind: parameter.
    Why: [BenalohHETypes n r] depends on both.
    Used by: ahe, rand_fin, cipher_fin. *)
Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(** ahe - the concrete Benaloh AHE scheme at parameters [n r].  Built
    via [@AHEnc.Pack] over [BenalohHETypes n r] using the
    [Benaloh_isEncDec] and [Benaloh_isAHEnc] mixin instances declared
    in [homomorphic_encryption/benaloh1994/benaloh_ahe.v].  Note that
    [Benaloh_isEncDec] takes only [n r] (no positivity hypotheses) and
    [Benaloh_isAHEnc] takes [n r] plus [r_gt1] only ([n_gt1] is not
    consumed by either mixin).  [n_gt1] is still declared as a section
    hypothesis to keep the API at the Benaloh module surface uniform
    with the mathematical statement (non-trivial [n]).
    Kind: concrete carrier.
    Why: T1's V_2-aware rebuild needs a concrete [AHEncType] to
    specialise the [Module Concrete] carriers.
    Used by: T1 V_2-aware rebuild. *)
Definition ahe : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r)
       (Benaloh_isEncDec n r)
       (@Benaloh_isAHEnc n r r_gt1)).

(** rand_fin - finType carrier for [rand ahe = {unit 'Z_n}].  Already
    a [finType] via MathComp's [FinRing] unit-group machinery, so the
    [Finite.type] ascription suffices.
    Kind: concrete carrier.
    Why: discharges the [rand_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition rand_fin : Finite.type := {unit 'Z_n} : Finite.type.

(** rand_fin_E - [Finite.sort rand_fin = rand ahe].  Both sides reduce
    to [{unit 'Z_n}] by [BenalohHETypes]'s definition, so [erefl]
    closes it.  Suffix [E] is MathComp's canonical equational-rewrite
    suffix.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_fin_E : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe = 'Z_n].  Already a
    [finType] via MathComp's ['Z_n] canonical structure.
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'Z_n : Finite.type.

(** cipher_fin_E - [Finite.sort cipher_fin = cipher ahe].  Closes by
    [erefl] for the same reason as [rand_fin_E].
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_fin_E : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

(** msg_inhab - plaintext inhabitance witness, picked as [0 : 'Z_r].
    Kind: inhabitance witness.
    Why: discharges the [msg_inhabited] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition msg_inhab : plain ahe := 0%R.

(** renc_inhab - encryption-randomness inhabitance witness, picked as
    [1%g : {unit 'Z_n}] (the identity unit).  Declared for
    completeness even though [renc_inhabited] is typically pruned at
    section close when not transitively referenced.
    Kind: inhabitance witness.
    Why: matches the API surface; not always transitively required.
    Used by: T1 V_2-aware rebuild. *)
Definition renc_inhab : rand_fin := 1%g.

(** pub_gen_order1 - the [pub_gen_order] proof obligation of
    [BenalohPubKey] at the choice [pub_gen := 1%g] (the identity unit
    of the multiplicative group of ['Z_n]).  Proof: [val 1%g = 1] by
    [FinRing.val_unit1], then [1 ^+ r = 1] by [expr1n].  Name uses 3
    underscore-components per the snake_case naming convention.
    Kind: proof obligation.
    Why: needed to construct [pub_key_inhab] via [MkBenalohPubKey].
    Used by: pub_key_inhab. *)
Lemma pub_gen_order1 : (val (1%g : {unit 'Z_n})) ^+ r = 1.
Proof. by rewrite FinRing.val_unit1 expr1n. Qed.

(** pub_key_inhab - public-key inhabitance witness at [pub_key ahe =
    BenalohPubKey n r].  Built directly via [@MkBenalohPubKey n r 1%g
    pub_gen_order1] (taking [n r] explicitly since
    [Set Implicit Arguments] makes them implicit on
    [MkBenalohPubKey]).
    Kind: inhabitance witness.
    Why: discharges the [pub_key_inhab] section variable of
    [Module Concrete] introduced by the Task N refactor.
    Used by: T1 V_2-aware rebuild. *)
Definition pub_key_inhab : pub_key ahe :=
  @MkBenalohPubKey n r 1%g pub_gen_order1.

End benaloh.

End Benaloh.

(* ================================================================== *)
(* Paillier 1999 AHE specialisation                                    *)
(* ================================================================== *)

(** Module Paillier - Paillier 1999 AHE specialisation (AHE / finType
    / inhabitance carriers) at the Paillier 1999 AHE instance
    [PaillierHETypes n] parametric in any [n : nat] with [1 < n].
    The carriers are:
    - [plain ahe = 'Z_n] (canonical [finType])
    - [rand ahe = {unit 'Z_(n*n)}] (canonical [finType] via [FinRing])
    - [cipher ahe = 'Z_(n*n)] (canonical [finType])
    - [pub_key ahe = PaillierPubKey n] (a [Record], NOT a [finType])
    Inhabitance for [pub_key ahe] is built directly via
    [@MkPaillierPubKey n 1 pub_gen_order1] where [pub_gen_order1]
    proves [(1 : 'Z_(n*n)) ^+ n = 1] by [expr1n].  Taking
    [pub_key_inhab] directly at [pub_key AHE] rather than at a
    separate [Finite.type] bridge avoids declaring an HB [Finite]
    instance on the [PaillierPubKey] record.

    T1's V_2-aware rebuild plugs these carriers into the new game
    chain.  Discharging [enc_ind_cpa_real_or_zero] from the DCR
    assumption (the cryptographic security of Paillier) is a separate
    project out of scope here.
    Plan: ~/.claude/plans/sprightly-finding-robin.md (T0 cleanup, T1
    rebuild). *)
Module Paillier.

Section paillier.

(** n - the Paillier modulus.  [n] is the RSA-style composite (a
    product of two primes in the standard Paillier instantiation).
    The single positivity hypothesis [n_gt1] ensures the underlying
    ['Z_n] and ['Z_(n*n)] are non-trivial.
    Kind: parameter.
    Why: [PaillierHETypes n] depends on [n].
    Used by: ahe, rand_fin, cipher_fin. *)
Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

(** ahe - the concrete Paillier AHE scheme at parameter [n].  Built
    via [@AHEnc.Pack] over [PaillierHETypes n] using the
    [Paillier_isEncDec] and [Paillier_isAHEnc] mixin instances declared
    in [homomorphic_encryption/paillier1999/paillier_ahe.v].
    [Paillier_isEncDec] takes only [n] (no positivity hypotheses);
    [Paillier_isAHEnc] takes [n] plus [n_gt1].
    Kind: concrete carrier.
    Why: T1's V_2-aware rebuild needs a concrete [AHEncType] to
    specialise the [Module Concrete] carriers.
    Used by: T1 V_2-aware rebuild. *)
Definition ahe : AHEncType :=
  @AHEnc.Pack (PaillierHETypes n)
    (@AHEnc.Class (PaillierHETypes n)
       (@Paillier_isEncDec n)
       (@Paillier_isAHEnc n n_gt1)).

(** rand_fin - finType carrier for [rand ahe = {unit 'Z_(n*n)}].
    Already a [finType] via MathComp's [FinRing] unit-group machinery,
    so the [Finite.type] ascription suffices.
    Kind: concrete carrier.
    Why: discharges the [rand_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition rand_fin : Finite.type := {unit 'Z_(n * n)} : Finite.type.

(** rand_fin_E - [Finite.sort rand_fin = rand ahe].  Both sides reduce
    to [{unit 'Z_(n*n)}] by [PaillierHETypes]'s definition, so [erefl]
    closes it.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_fin_E : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe = 'Z_(n*n)].  Already
    a [finType] via MathComp's ['Z_(n*n)] canonical structure.
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'Z_(n * n) : Finite.type.

(** cipher_fin_E - [Finite.sort cipher_fin = cipher ahe].  Closes by
    [erefl] for the same reason as [rand_fin_E].  The [Let n2 := (n*n)]
    binding inside [Section paillier_instance] in [paillier_ahe.v] does
    NOT seal [n2] across module boundaries: outside the section, [n2]
    expands to [(n*n)%N], which matches the right-hand side here.
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_fin_E : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

(** msg_inhab - plaintext inhabitance witness, picked as [0 : 'Z_n].
    Kind: inhabitance witness.
    Why: discharges the [msg_inhabited] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition msg_inhab : plain ahe := 0%R.

(** renc_inhab - encryption-randomness inhabitance witness, picked as
    [1%g : {unit 'Z_(n*n)}] (the identity unit).  Declared for
    completeness even though [renc_inhabited] is typically pruned at
    section close when not transitively referenced.
    Kind: inhabitance witness.
    Why: matches the API surface; not always transitively required.
    Used by: T1 V_2-aware rebuild. *)
Definition renc_inhab : rand_fin := 1%g.

(** pub_gen_order1 - the [pub_gen_order] proof obligation of
    [PaillierPubKey] at the choice [pub_gen := 1 : 'Z_(n*n)] (the
    multiplicative one of the ring ['Z_(n*n)]).  Proof: [1 ^+ n = 1]
    by [expr1n].  Note that unlike Benaloh (which uses [{unit 'Z_n}]
    for [pub_gen]), Paillier's [pub_gen] is plain ['Z_(n*n)] so no
    [FinRing.val_unit1] step is needed.
    Kind: proof obligation.
    Why: needed to construct [pub_key_inhab] via [MkPaillierPubKey].
    Used by: pub_key_inhab. *)
Lemma pub_gen_order1 : (1 : 'Z_(n * n)) ^+ n = 1.
Proof. exact: expr1n. Qed.

(** pub_key_inhab - public-key inhabitance witness at [pub_key ahe =
    PaillierPubKey n].  Built directly via [@MkPaillierPubKey n 1
    pub_gen_order1] (taking [n] explicitly since [Set Implicit
    Arguments] makes it implicit on [MkPaillierPubKey]).
    Kind: inhabitance witness.
    Why: discharges the [pub_key_inhab] section variable of
    [Module Concrete] introduced by the Task N refactor.
    Used by: T1 V_2-aware rebuild. *)
Definition pub_key_inhab : pub_key ahe :=
  @MkPaillierPubKey n 1 pub_gen_order1.

End paillier.

End Paillier.
