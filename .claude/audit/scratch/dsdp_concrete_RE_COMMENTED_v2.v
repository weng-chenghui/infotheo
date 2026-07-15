(* DSDP Alice secrecy under IND-CPA, concrete-section instantiation.

   Builds AHE carriers (Renc / t_msg / t_cipher), finType bridges
   (rand_finType / cipher_finType), inhabitance witnesses
   (msg_witness / renc_witness / pub_key_witness), and cancel laws
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

(** msg_witness, renc_witness, pub_key_witness - inhabitance
    witnesses for [plain AHE], [rand_finType], and [pub_key AHE].
    Required to discharge auxiliary positivity hypotheses (used in
    the [Print Assumptions] closure transitively) and to build the
    constant [pkey_of_party] function.  Plan risk R1
    explicitly anticipated this need.
    Kind: parameter.
    Why: [AHEncType] does not carry inhabitance proofs in its mixin,
    so the concrete section requests them externally.  At idealised
    AHE all three are [0%R] or [GRing.zero].  [pub_key_witness] is
    typed directly at [pub_key AHE] rather than at a separate
    [pub_key_finType] bridge: AHE schemes whose [pub_key] is a
    Record (Benaloh, Paillier) do not carry a [Finite] instance,
    and the only use of an inhabitance witness for [pub_key] in
    this concrete section is to build the constant [pkey_of_party]
    function, which does not need finite-type machinery.
    Used by: pkey_of_party (pub_key_witness);
    card_msg_gt0 / card_renc_gt0 /
    card_t_msg_gt0 (msg / renc inhabited). *)
Variable msg_witness : plain AHE.
Variable renc_witness : rand_finType.
Variable pub_key_witness : pub_key AHE.

(** card_msg - cardinality index for the plaintext-scalar
    carrier.  Picks [#|plain AHE|] so the cardinality coherence laws
    close by [erefl].
    Kind: concrete-carrier index.
    Why: discharges the abstract [card_msg : nat] section parameter
    of [Section dsdp_security_indcpa] (line 156).
    Used by: T1 V_2-aware rebuild. *)
Definition card_msg : nat := #|plain AHE|.

(** card_renc - cardinality index for the
    encryption-randomness carrier.  Picks [#|rand_finType|].
    Kind: concrete-carrier index.
    Why: discharges [card_renc] of the abstract section (line 68).
    Used by: T1 V_2-aware rebuild. *)
Definition card_renc : nat := #|rand_finType|.

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

(** msg_of_idx - concrete bridge from ['I_card_msg]
    to [plain AHE].  Since [card_msg := #|plain AHE|] the
    domain is ['I_#|plain AHE|], so [enum_val] applies directly.
    Kind: concrete bijection.
    Why: discharges [msg_of_idx : 'I_card_msg -> plain AHE] of the
    abstract section (line 168).
    Used by: T1 V_2-aware rebuild. *)
Definition msg_of_idx : 'I_card_msg -> plain AHE :=
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
    at this layer), so a constant suffices.  Returns [pub_key_witness]
    directly: since [pub_key_witness] is now typed at [pub_key AHE]
    (Task N refactor), no [eq_rect] cast is needed.
    Kind: concrete supply.
    Why: discharges [pkey_of_party : party_id -> pub_key AHE] of the
    abstract section (line 149).
    Used by: T1 V_2-aware rebuild. *)
Definition pkey_of_party : party_id -> pub_key AHE :=
  fun _ => pub_key_witness.

(** renc_card - cardinality coherence for [Renc].
    Closes by reflexivity since [Renc := rand_finType] and
    [card_renc := #|rand_finType|].
    Kind: coherence.
    Why: discharges [renc_card : #|Renc| = card_renc] (line 69).
    Used by: T1 V_2-aware rebuild. *)
Lemma renc_card : #|Renc| = card_renc.
Proof. by []. Qed.

(** card_msg_gt0 - positivity of [card_msg].
    Follows from [msg_witness : plain AHE] via [card_gt0P].
    Kind: positivity.
    Why: discharges [card_msg_gt0] (line 1364) when needed in the
    [Print Assumptions] closure.
    Used by: downstream Task L. *)
Lemma card_msg_gt0 : (0 < card_msg)%N.
Proof. by apply/card_gt0P; exists msg_witness. Qed.

(** card_renc_gt0 - positivity of [card_renc].
    Follows from [renc_witness : rand_finType] via [card_gt0P].
    Kind: positivity.
    Why: discharges [card_renc_gt0] (line 1365).
    Used by: downstream Task L. *)
Lemma card_renc_gt0 : (0 < card_renc)%N.
Proof. by apply/card_gt0P; exists renc_witness. Qed.

(* Bijection to build type bridge between AHE and SSProve. *)
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

(** card_t_msg - cardinality index used by [dsdp_alice_secrecy]'s
    residual bound [1 / card_t_msg].  Set equal to [card_msg] (i.e.
    [#|plain AHE|]) since V_2 is sampled uniformly over [plain AHE]
    via [msg_of_idx] and the indicator compares the predictor's
    [t_msg]-guess to that V_2.
    Kind: concrete-carrier index.
    Why: discharges [dsdp_security_indcpa]'s abstract [card_t_msg]
    section parameter at the concrete carriers so the closed-form
    bound numerically reads [1 / #|plain AHE| + 2 * epsilon_cpa].
    Used by: random_guess_adv, secrecy_random_guess. *)
Definition card_t_msg : nat := card_msg.

(* Positivity index keeping the 1/card_t_msg residual in the
   Alice-secrecy closed-form bound non-vacuous, and supplying the
   strict positivity that downstream entropy bounds (log_id,
   entropy_ge_bound) require on the predictor's guess space. *)
Lemma card_t_msg_gt0 : (0 < card_t_msg)%N.
Proof. exact: card_msg_gt0. Qed.

(** Pr_guess_enc_zero_le_invm - the IT residual bound at [game_enc_zero],
    taken as a Section hypothesis at the concrete instance.  Mirrors
    [dsdp_security_indcpa.Pr_guess_enc_zero_le_invm] specialised to the
    concrete carriers.
    Kind: section hypothesis.
    Why: required by [dsdp_alice_secrecy] which consumes the IT half
    of the closed-form bound abstractly; discharging it from the
    [cPr_V2_V3_uniform_on_fiber_joint] chain in
    [dsdp_security_indcpa.v] is tracked separately (out of scope for
    U1).
    Used by: secrecy_random_guess. *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : dsdp_security_indcpa.predictor_guesser t_msg t_cipher),
    distr.mu (pkg_advantage.Pr
                (dsdp_security_indcpa.guess_indicator_pkg predictor
                   (dsdp_security_indcpa.game_enc_zero (AHE:=AHE) renc_card
                      rand_of_renc (t_msg:=t_msg) (t_cipher:=t_cipher)
                      chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx)))
              true
      <= (card_t_msg%:R)^-1.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

(* A stateless oracle-free adversary used for the lower-bound
   side of the Alice-secrecy theorem: it ignores all leaked
   ciphertexts, samples a fresh uniform plaintext from the AHE
   plain space, and returns it (cast through chmsg_of_msg) as its
   guess at V_2. Built over the emptym location set so that the
   chain_valid obligation of dsdp_alice_secrecy unifies with
   valid_boolean_shell_link by reflexivity. *)
Definition random_guess_adv : dsdp_security_indcpa.predictor_guesser t_msg t_cipher :=
  [package emptym ;
    #def #[ dsdp_security_indcpa.id_guess ] (_ : 'unit) : msg
    {
      iV ← sample uniform #|plain AHE| ;;
      ret (chmsg_of_msg (enum_val iV))
    }
  ].

Check random_guess_adv : dsdp_security_indcpa.predictor_guesser t_msg t_cipher.

(** secrecy_random_guess - the closed-form Alice-secrecy bound at
    the trivial random-guess adversary.  Discharges the eight
    [fseparate] obligations of [dsdp_alice_secrecy] by [fseparate0m]
    (since [random_guess_adv]'s locations are [emptym]) and the
    [chain_valid] obligation by
    [dsdp_security_indcpa.valid_boolean_shell_link] applied to
    [random_guess_adv].
    Kind: main.
    Why: instantiates [dsdp_alice_secrecy] at the concrete
    random-guess adversary to produce the closed-form
    [(card_t_msg^-1 + 2 * epsilon_cpa)] numeric secrecy bound;
    consumed by [Idealized.secrecy_random_guess],
    [Benaloh.secrecy_random_guess], and
    [Paillier.secrecy_random_guess] in this file. *)
Corollary secrecy_random_guess :
  distr.mu
    (pkg_advantage.Pr
       (dsdp_security_indcpa.guess_indicator_pkg random_guess_adv
          (dsdp_security_indcpa.game_real (AHE:=AHE) renc_card
             rand_of_renc (t_msg:=t_msg) (t_cipher:=t_cipher)
             chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx)))
    true
    <= (card_t_msg%:R)^-1 + 2%:R * indcpa_ror.epsilon_cpa.
Proof.
refine (@dsdp_security_indcpa.dsdp_alice_secrecy
          AHE Renc card_renc renc_card rand_of_renc
          t_msg t_cipher msg_of_chmsg chmsg_of_msg
          chcipher_of_cipher cipher_of_chcipher
          chcipher_of_cipherK chmsg_of_msgK
          pkey_of_party card_msg msg_of_idx
          card_t_msg
          Pr_guess_enc_zero_le_invm
          emptym random_guess_adv _ _ _ _ _ _ _ _ _).
- exact: (valid_boolean_shell_link random_guess_adv).
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
Qed.

(** Pr_real_gt0 - strict positivity of [Pr at game_real with
    random_guess_adv] at the concrete carriers.  Narrower than the
    deleted universal [Pr_guess_real_ge_invm]: quantifies only at
    the specific witness predictor used by [entropy_random_guess].

    Information-theoretic discharge sketch (out of scope here):
    [random_guess_adv] samples [iV] fresh and uniform over
    [#|plain AHE|]; [game_real] samples V_2 fresh and uniform over
    the same space; the two samples live at distinct SSProve
    sampling sites and are jointly independent.  Therefore
    [Pr[guess = V_2] = 1/card_t_msg] exactly, giving the strict
    positivity claim.  Encoding this pointwise identity needs the
    [chmsg_of_msgK] cancel law plus SSProve's Fubini machinery
    (~50-100 lines) - tracked as follow-up.

    Kind: section hypothesis.
    Why: feeds [entropy_ge_bound]'s new [Pr_real_gt0] slot for the
    random-guess corollary.  Replaces the universal
    [Pr_guess_real_ge_invm] that was structurally false on
    anti-echo adversaries (type-level anti-echo is now blocked by
    the narrower [predictor_iface], but ciphertext-decryption-based
    anti-correlation could still violate the universal [>= 1/m]
    bound; the weaker [> 0] claim survives because
    [random_guess_adv] never queries any oracle and is
    unconditionally V_2-independent).
    Naming: 3 components inside [Module Concrete / Section concrete];
    externally referenced as [Pr_real_gt0].  Canonical
    [_gt0] suffix for [0 < x] (AUTHORITY.md).
    Used by: entropy_random_guess. *)
Hypothesis Pr_real_gt0 :
  (0 < distr.mu (pkg_advantage.Pr
                   (dsdp_security_indcpa.guess_indicator_pkg
                      random_guess_adv
                      (dsdp_security_indcpa.game_real (AHE:=AHE) renc_card
                         rand_of_renc (t_msg:=t_msg) (t_cipher:=t_cipher)
                         chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx)))
                 true)%R.

(** epsilon_cpa_ge0 - nonnegativity of the IND-CPA error parameter
    at the concrete instance.  Same shape as
    [dsdp_security_indcpa.epsilon_cpa_ge0]; [indcpa_ror.epsilon_cpa]
    is declared as a bare [Parameter] without positivity, so the
    constraint is restated here.
    Kind: section hypothesis.
    Why: needed for [entropy_random_guess] transitively through
    [entropy_ge_bound] (its [log_id] step requires
    [1 + 2 * m * eps > 0]).
    Used by: entropy_random_guess. *)
Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

(** entropy_random_guess - the closed-form Alice-secrecy bound in
    entropy form at the trivial random-guess adversary.
    Specialises [dsdp_security_indcpa.entropy_ge_bound] exactly the
    same way [secrecy_random_guess] specialises [dsdp_alice_secrecy]:
    [chain_valid] by [valid_boolean_shell_link], the eight
    [fseparate] obligations by [fseparate0m] (since
    [random_guess_adv] has [emptym] locations).
    Kind: main.
    Why: produces the entropy-form numeric bound
    [log m - log (1 + 2 * m * epsilon_cpa)] at the concrete carriers;
    mirrors [secrecy_random_guess]'s probability-form bound through
    U2's log-monotonicity bridge.  Consumed by the
    [Idealized] / [Benaloh] / [Paillier] specialisations below.
    Naming: 3-token snake_case [entropy_random_guess] mirrors
    [secrecy_random_guess] at the entropy level. *)
Corollary entropy_random_guess :
  (dsdp_security_indcpa.bound card_t_msg
   <= dsdp_security_indcpa.entropy (AHE:=AHE) (Renc:=Renc) (card_renc:=card_renc)
        renc_card rand_of_renc
        (t_msg:=t_msg) (t_cipher:=t_cipher)
        chmsg_of_msg chcipher_of_cipher pkey_of_party
        (card_msg:=card_msg) msg_of_idx
        random_guess_adv)%R.
Proof.
refine (@dsdp_security_indcpa.entropy_ge_bound
          AHE Renc card_renc renc_card rand_of_renc
          t_msg t_cipher msg_of_chmsg chmsg_of_msg
          chcipher_of_cipher cipher_of_chcipher
          chcipher_of_cipherK chmsg_of_msgK
          pkey_of_party card_msg msg_of_idx
          card_t_msg card_t_msg_gt0
          Pr_guess_enc_zero_le_invm
          epsilon_cpa_ge0
          emptym random_guess_adv _ _ _ _ _ _ _ _ _ _).
- exact: (valid_boolean_shell_link random_guess_adv).
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: fseparate0m.
- exact: Pr_real_gt0.
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
Import Concrete.

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

(** rand_finE - [Finite.sort rand_fin = rand ahe].  Both sides
    reduce to ['F_p] by [Idealized_HETypes]'s definition, so [erefl]
    closes it.  Suffix [E] is MathComp's canonical equational-rewrite
    suffix.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe], same pattern
    as [rand_fin].
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'F_p.

(** cipher_finE - [Finite.sort cipher_fin = cipher ahe].  Closes
    by [erefl] for the same reason as [rand_finE].
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

(** pub_key_witness - public-key inhabitance witness at [pub_key ahe = 'F_p].
    Picked as [0 : 'F_p].
    Kind: inhabitance witness.
    Why: discharges the [pub_key_witness] section variable of
    [Module Concrete] at the idealised instance; needed to
    instantiate [secrecy_random_guess] at this specialisation.
    Used by: secrecy_random_guess. *)
Definition pub_key_witness : pub_key ahe := 0%R.

(** msg_witness - plaintext inhabitance witness at [plain ahe = 'F_p].
    Picked as [0 : 'F_p].
    Kind: inhabitance witness.
    Why: needed for [entropy_random_guess], which transitively
    consumes [card_t_msg_gt0] (whose [Qed]-opaque proof
    references [msg_witness] at the abstract level).
    [secrecy_random_guess] did not need this because the
    [dsdp_alice_secrecy] underlying it does not take
    [card_t_msg_gt0] as an explicit argument.
    Used by: entropy_random_guess. *)
Definition msg_witness : plain ahe := 0%R.

(** Pr_guess_enc_zero_le_invm - IT residual bound at the idealised
    [game_enc_zero] specialised carriers.  Mirrors
    [Module Concrete]'s Section hypothesis at the idealised
    instance.
    Kind: section hypothesis.
    Why: required by [secrecy_random_guess] which abstracts
    over the IT half of the bound; discharging it from the residual
    uniformity chain is tracked separately.
    Used by: secrecy_random_guess. *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor :
            dsdp_security_indcpa.predictor_guesser
              (t_msg ahe) (t_cipher cipher_fin)),
    distr.mu
      (pkg_advantage.Pr
         (dsdp_security_indcpa.guess_indicator_pkg predictor
            (dsdp_security_indcpa.game_enc_zero (AHE:=ahe)
               (renc_card rand_fin)
               (rand_of_renc (AHE:=ahe)
                  (rand_finType:=rand_fin) rand_finE)
               (t_msg:=t_msg ahe)
               (t_cipher:=t_cipher cipher_fin)
               (chmsg_of_msg (AHE:=ahe))
               (chcipher_of_cipher (AHE:=ahe)
                  (cipher_finType:=cipher_fin) cipher_finE)
               (pkey_of_party (AHE:=ahe) pub_key_witness)
               (msg_of_idx (AHE:=ahe)))))
      true
      <= ((card_t_msg ahe)%:R)^-1.

(** secrecy_random_guess - the closed-form Alice-secrecy bound at
    the idealised AHE instance and the trivial random-guess
    adversary.  Specialises [secrecy_random_guess] at the
    idealised carriers and the Section-local
    [Pr_guess_enc_zero_le_invm].
    Kind: main.
    Why: provides the idealised-AHE closed-form bound required by
    the entropy-form corollaries in U3 that lift the probability
    inequality to a mutual-information statement.
    Used by: Idealized.entropy_random_guess in U3. *)
Definition secrecy_random_guess :
  distr.mu
    (pkg_advantage.Pr
       (dsdp_security_indcpa.guess_indicator_pkg
          (random_guess_adv ahe cipher_fin)
          (dsdp_security_indcpa.game_real (AHE:=ahe)
             (renc_card rand_fin)
             (rand_of_renc (AHE:=ahe)
                (rand_finType:=rand_fin) rand_finE)
             (t_msg:=t_msg ahe)
             (t_cipher:=t_cipher cipher_fin)
             (chmsg_of_msg (AHE:=ahe))
             (chcipher_of_cipher (AHE:=ahe)
                (cipher_finType:=cipher_fin) cipher_finE)
             (pkey_of_party (AHE:=ahe) pub_key_witness)
             (msg_of_idx (AHE:=ahe)))))
    true
    <= ((card_t_msg ahe)%:R)^-1 + 2%:R * indcpa_ror.epsilon_cpa
  := @secrecy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE pub_key_witness Pr_guess_enc_zero_le_invm.

(** Pr_real_gt0 - strict positivity at the idealised carriers for
    [random_guess_adv]'s specific predictor.  Narrower than
    the deleted universal [Pr_guess_real_ge_invm]; only quantifies
    over the random-guess witness.  Naming: 3 components inside
    [Module Idealized / Section idealized]; externally
    [Idealized.Pr_real_gt0].  Canonical [_gt0] suffix.
    Kind: section hypothesis.
    Why: feeds [entropy_random_guess]'s new [Pr_real_gt0]
    slot at the idealised instance.  See [Module Concrete]'s
    [Pr_real_gt0] docstring for the IT discharge sketch.
    Used by: entropy_random_guess. *)
Hypothesis Pr_real_gt0 :
  (0 < distr.mu
        (pkg_advantage.Pr
           (dsdp_security_indcpa.guess_indicator_pkg
              (random_guess_adv ahe cipher_fin)
              (dsdp_security_indcpa.game_real (AHE:=ahe)
                 (renc_card rand_fin)
                 (rand_of_renc (AHE:=ahe)
                    (rand_finType:=rand_fin) rand_finE)
                 (t_msg:=t_msg ahe)
                 (t_cipher:=t_cipher cipher_fin)
                 (chmsg_of_msg (AHE:=ahe))
                 (chcipher_of_cipher (AHE:=ahe)
                    (cipher_finType:=cipher_fin) cipher_finE)
                 (pkey_of_party (AHE:=ahe) pub_key_witness)
                 (msg_of_idx (AHE:=ahe)))))
        true)%R.

(** epsilon_cpa_ge0 - nonnegativity of the IND-CPA error parameter.
    Mirrors [Module Concrete]'s Section hypothesis.
    Kind: section hypothesis.
    Why: needed for [entropy_random_guess] transitively through
    [entropy_random_guess].
    Used by: entropy_random_guess. *)
Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

(** entropy_random_guess - the closed-form Alice-secrecy bound in
    entropy form at the idealised AHE instance and the trivial
    random-guess adversary.  Specialises
    [entropy_random_guess] at the idealised carriers and
    the Section-local hypotheses.
    Kind: main.
    Why: provides the idealised-AHE entropy-form numeric bound
    [log m - log (1 + 2 * m * epsilon_cpa)] required by the
    information-theoretic Alice-secrecy statement.
    Used by: downstream consumers of the entropy-form bound. *)
Definition entropy_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.entropy (AHE:=ahe)
        (renc_card rand_fin)
        (rand_of_renc (AHE:=ahe)
           (rand_finType:=rand_fin) rand_finE)
        (t_msg:=t_msg ahe)
        (t_cipher:=t_cipher cipher_fin)
        (chmsg_of_msg (AHE:=ahe))
        (chcipher_of_cipher (AHE:=ahe)
           (cipher_finType:=cipher_fin) cipher_finE)
        (pkey_of_party (AHE:=ahe) pub_key_witness)
        (msg_of_idx (AHE:=ahe))
        (random_guess_adv ahe cipher_fin))%R
  := @entropy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE msg_witness pub_key_witness
       Pr_guess_enc_zero_le_invm Pr_real_gt0 epsilon_cpa_ge0.

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
    The Task N refactor of [Module Concrete] (taking [pub_key_witness]
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
Import Concrete.

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
(* D001-bypass: n_gt1 is declared for API-surface uniformity with the
   abstract Benaloh module (the mathematical statement requires
   non-trivial n); it is not transitively consumed by any entity in
   Section benaloh because BenalohHETypes / Benaloh_isEncDec /
   Benaloh_isAHEnc all rely only on r_gt1. *)
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

(** rand_finE - [Finite.sort rand_fin = rand ahe].  Both sides reduce
    to [{unit 'Z_n}] by [BenalohHETypes]'s definition, so [erefl]
    closes it.  Suffix [E] is MathComp's canonical equational-rewrite
    suffix.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe = 'Z_n].  Already a
    [finType] via MathComp's ['Z_n] canonical structure.
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'Z_n : Finite.type.

(** cipher_finE - [Finite.sort cipher_fin = cipher ahe].  Closes by
    [erefl] for the same reason as [rand_finE].
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

(** msg_witness - plaintext inhabitance witness, picked as [0 : 'Z_r].
    Kind: inhabitance witness.
    Why: discharges the [msg_witness] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition msg_witness : plain ahe := 0%R.

(** renc_witness - encryption-randomness inhabitance witness, picked as
    [1%g : {unit 'Z_n}] (the identity unit).  Declared for
    completeness even though [renc_witness] is typically pruned at
    section close when not transitively referenced.
    Kind: inhabitance witness.
    Why: matches the API surface; not always transitively required.
    Used by: T1 V_2-aware rebuild. *)
Definition renc_witness : rand_fin := 1%g.

(** pub_gen_order1 - the [pub_gen_order] proof obligation of
    [BenalohPubKey] at the choice [pub_gen := 1%g] (the identity unit
    of the multiplicative group of ['Z_n]).  Proof: [val 1%g = 1] by
    [FinRing.val_unit1], then [1 ^+ r = 1] by [expr1n].  Name uses 3
    underscore-components per the snake_case naming convention.
    Kind: proof obligation.
    Why: needed to construct [pub_key_witness] via [MkBenalohPubKey].
    Used by: pub_key_witness. *)
Lemma pub_gen_order1 : (val (1%g : {unit 'Z_n})) ^+ r = 1.
Proof. by rewrite FinRing.val_unit1 expr1n. Qed.

(** pub_key_witness - public-key inhabitance witness at [pub_key ahe =
    BenalohPubKey n r].  Built directly via [@MkBenalohPubKey n r 1%g
    pub_gen_order1] (taking [n r] explicitly since
    [Set Implicit Arguments] makes them implicit on
    [MkBenalohPubKey]).
    Kind: inhabitance witness.
    Why: discharges the [pub_key_witness] section variable of
    [Module Concrete] introduced by the Task N refactor.
    Used by: T1 V_2-aware rebuild. *)
Definition pub_key_witness : pub_key ahe :=
  @MkBenalohPubKey n r 1%g pub_gen_order1.

(** Pr_guess_enc_zero_le_invm - IT residual bound at the Benaloh
    specialised carriers.  Mirrors [Module Concrete]'s Section
    hypothesis at the Benaloh instance.
    Kind: section hypothesis.
    Why: required by [secrecy_random_guess] which abstracts
    over the IT half of the bound; the cryptographic-side discharge
    via the higher-residuosity assumption is out of scope here.
    Used by: secrecy_random_guess. *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor :
            dsdp_security_indcpa.predictor_guesser
              (t_msg ahe) (t_cipher cipher_fin)),
    distr.mu
      (pkg_advantage.Pr
         (dsdp_security_indcpa.guess_indicator_pkg predictor
            (dsdp_security_indcpa.game_enc_zero (AHE:=ahe)
               (renc_card rand_fin)
               (rand_of_renc (AHE:=ahe)
                  (rand_finType:=rand_fin) rand_finE)
               (t_msg:=t_msg ahe)
               (t_cipher:=t_cipher cipher_fin)
               (chmsg_of_msg (AHE:=ahe))
               (chcipher_of_cipher (AHE:=ahe)
                  (cipher_finType:=cipher_fin) cipher_finE)
               (pkey_of_party (AHE:=ahe) pub_key_witness)
               (msg_of_idx (AHE:=ahe)))))
      true
      <= ((card_t_msg ahe)%:R)^-1.

(** secrecy_random_guess - the closed-form Alice-secrecy bound at
    the Benaloh 1994 AHE instance and the trivial random-guess
    adversary.  Specialises [secrecy_random_guess] at the
    Benaloh carriers and the Section-local [Pr_guess_enc_zero_le_invm].
    Kind: main.
    Why: provides the Benaloh-instance closed-form bound required by
    the entropy-form corollaries in U3 that lift the probability
    inequality to a mutual-information statement.
    Used by: Benaloh.entropy_random_guess in U3. *)
Definition secrecy_random_guess :
  distr.mu
    (pkg_advantage.Pr
       (dsdp_security_indcpa.guess_indicator_pkg
          (random_guess_adv ahe cipher_fin)
          (dsdp_security_indcpa.game_real (AHE:=ahe)
             (renc_card rand_fin)
             (rand_of_renc (AHE:=ahe)
                (rand_finType:=rand_fin) rand_finE)
             (t_msg:=t_msg ahe)
             (t_cipher:=t_cipher cipher_fin)
             (chmsg_of_msg (AHE:=ahe))
             (chcipher_of_cipher (AHE:=ahe)
                (cipher_finType:=cipher_fin) cipher_finE)
             (pkey_of_party (AHE:=ahe) pub_key_witness)
             (msg_of_idx (AHE:=ahe)))))
    true
    <= ((card_t_msg ahe)%:R)^-1 + 2%:R * indcpa_ror.epsilon_cpa
  := @secrecy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE pub_key_witness Pr_guess_enc_zero_le_invm.

(** Pr_real_gt0 - strict positivity at the Benaloh carriers for
    [random_guess_adv]'s specific predictor.  Narrower than
    the deleted universal [Pr_guess_real_ge_invm].  Naming: 3
    components inside [Module Benaloh / Section benaloh]; externally
    [Benaloh.Pr_real_gt0].
    Kind: section hypothesis.
    Why: feeds [entropy_random_guess]'s new [Pr_real_gt0]
    slot at the Benaloh instance.  See [Module Concrete]'s
    [Pr_real_gt0] docstring for the IT discharge sketch.
    Used by: entropy_random_guess. *)
Hypothesis Pr_real_gt0 :
  (0 < distr.mu
        (pkg_advantage.Pr
           (dsdp_security_indcpa.guess_indicator_pkg
              (random_guess_adv ahe cipher_fin)
              (dsdp_security_indcpa.game_real (AHE:=ahe)
                 (renc_card rand_fin)
                 (rand_of_renc (AHE:=ahe)
                    (rand_finType:=rand_fin) rand_finE)
                 (t_msg:=t_msg ahe)
                 (t_cipher:=t_cipher cipher_fin)
                 (chmsg_of_msg (AHE:=ahe))
                 (chcipher_of_cipher (AHE:=ahe)
                    (cipher_finType:=cipher_fin) cipher_finE)
                 (pkey_of_party (AHE:=ahe) pub_key_witness)
                 (msg_of_idx (AHE:=ahe)))))
        true)%R.

(** epsilon_cpa_ge0 - nonnegativity of the IND-CPA error parameter.
    Mirrors [Module Concrete]'s Section hypothesis.
    Kind: section hypothesis.
    Why: needed for [entropy_random_guess] transitively through
    [entropy_random_guess].
    Used by: entropy_random_guess. *)
Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

(** entropy_random_guess - the closed-form Alice-secrecy bound in
    entropy form at the Benaloh 1994 AHE instance and the trivial
    random-guess adversary.  Specialises
    [entropy_random_guess] at the Benaloh carriers and the
    Section-local hypotheses.
    Kind: main.
    Why: provides the Benaloh-instance entropy-form numeric bound
    [log m - log (1 + 2 * m * epsilon_cpa)] required by the
    information-theoretic Alice-secrecy statement.
    Used by: downstream consumers of the entropy-form bound. *)
Definition entropy_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.entropy (AHE:=ahe)
        (renc_card rand_fin)
        (rand_of_renc (AHE:=ahe)
           (rand_finType:=rand_fin) rand_finE)
        (t_msg:=t_msg ahe)
        (t_cipher:=t_cipher cipher_fin)
        (chmsg_of_msg (AHE:=ahe))
        (chcipher_of_cipher (AHE:=ahe)
           (cipher_finType:=cipher_fin) cipher_finE)
        (pkey_of_party (AHE:=ahe) pub_key_witness)
        (msg_of_idx (AHE:=ahe))
        (random_guess_adv ahe cipher_fin))%R
  := @entropy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE msg_witness pub_key_witness
       Pr_guess_enc_zero_le_invm Pr_real_gt0 epsilon_cpa_ge0.

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
    [pub_key_witness] directly at [pub_key AHE] rather than at a
    separate [Finite.type] bridge avoids declaring an HB [Finite]
    instance on the [PaillierPubKey] record.

    T1's V_2-aware rebuild plugs these carriers into the new game
    chain.  Discharging [enc_ind_cpa_real_or_zero] from the DCR
    assumption (the cryptographic security of Paillier) is a separate
    project out of scope here.
    Plan: ~/.claude/plans/sprightly-finding-robin.md (T0 cleanup, T1
    rebuild). *)
Module Paillier.
Import Concrete.

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

(** rand_finE - [Finite.sort rand_fin = rand ahe].  Both sides reduce
    to [{unit 'Z_(n*n)}] by [PaillierHETypes]'s definition, so [erefl]
    closes it.
    Kind: coherence.
    Why: discharges the [rand_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

(** cipher_fin - finType carrier for [cipher ahe = 'Z_(n*n)].  Already
    a [finType] via MathComp's ['Z_(n*n)] canonical structure.
    Kind: concrete carrier.
    Why: discharges the [cipher_finType] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition cipher_fin : Finite.type := 'Z_(n * n) : Finite.type.

(** cipher_finE - [Finite.sort cipher_fin = cipher ahe].  Closes by
    [erefl] for the same reason as [rand_finE].  The [Let n2 := (n*n)]
    binding inside [Section paillier_instance] in [paillier_ahe.v] does
    NOT seal [n2] across module boundaries: outside the section, [n2]
    expands to [(n*n)%N], which matches the right-hand side here.
    Kind: coherence.
    Why: discharges the [cipher_finType_eq] hypothesis of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

(** msg_witness - plaintext inhabitance witness, picked as [0 : 'Z_n].
    Kind: inhabitance witness.
    Why: discharges the [msg_witness] section variable of
    [Module Concrete].
    Used by: T1 V_2-aware rebuild. *)
Definition msg_witness : plain ahe := 0%R.

(** renc_witness - encryption-randomness inhabitance witness, picked as
    [1%g : {unit 'Z_(n*n)}] (the identity unit).  Declared for
    completeness even though [renc_witness] is typically pruned at
    section close when not transitively referenced.
    Kind: inhabitance witness.
    Why: matches the API surface; not always transitively required.
    Used by: T1 V_2-aware rebuild. *)
Definition renc_witness : rand_fin := 1%g.

(** pub_gen_order1 - the [pub_gen_order] proof obligation of
    [PaillierPubKey] at the choice [pub_gen := 1 : 'Z_(n*n)] (the
    multiplicative one of the ring ['Z_(n*n)]).  Proof: [1 ^+ n = 1]
    by [expr1n].  Note that unlike Benaloh (which uses [{unit 'Z_n}]
    for [pub_gen]), Paillier's [pub_gen] is plain ['Z_(n*n)] so no
    [FinRing.val_unit1] step is needed.
    Kind: proof obligation.
    Why: needed to construct [pub_key_witness] via [MkPaillierPubKey].
    Used by: pub_key_witness. *)
Lemma pub_gen_order1 : (1 : 'Z_(n * n)) ^+ n = 1.
Proof. exact: expr1n. Qed.

(** pub_key_witness - public-key inhabitance witness at [pub_key ahe =
    PaillierPubKey n].  Built directly via [@MkPaillierPubKey n 1
    pub_gen_order1] (taking [n] explicitly since [Set Implicit
    Arguments] makes it implicit on [MkPaillierPubKey]).
    Kind: inhabitance witness.
    Why: discharges the [pub_key_witness] section variable of
    [Module Concrete] introduced by the Task N refactor.
    Used by: T1 V_2-aware rebuild. *)
Definition pub_key_witness : pub_key ahe :=
  @MkPaillierPubKey n 1 pub_gen_order1.

(** Pr_guess_enc_zero_le_invm - IT residual bound at the Paillier
    specialised carriers.  Mirrors [Module Concrete]'s Section
    hypothesis at the Paillier instance.
    Kind: section hypothesis.
    Why: required by [secrecy_random_guess] which abstracts
    over the IT half of the bound; the cryptographic-side discharge
    via the DCR assumption is out of scope here.
    Used by: secrecy_random_guess. *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor :
            dsdp_security_indcpa.predictor_guesser
              (t_msg ahe) (t_cipher cipher_fin)),
    distr.mu
      (pkg_advantage.Pr
         (dsdp_security_indcpa.guess_indicator_pkg predictor
            (dsdp_security_indcpa.game_enc_zero (AHE:=ahe)
               (renc_card rand_fin)
               (rand_of_renc (AHE:=ahe)
                  (rand_finType:=rand_fin) rand_finE)
               (t_msg:=t_msg ahe)
               (t_cipher:=t_cipher cipher_fin)
               (chmsg_of_msg (AHE:=ahe))
               (chcipher_of_cipher (AHE:=ahe)
                  (cipher_finType:=cipher_fin) cipher_finE)
               (pkey_of_party (AHE:=ahe) pub_key_witness)
               (msg_of_idx (AHE:=ahe)))))
      true
      <= ((card_t_msg ahe)%:R)^-1.

(** secrecy_random_guess - the closed-form Alice-secrecy bound at
    the Paillier 1999 AHE instance and the trivial random-guess
    adversary.  Specialises [secrecy_random_guess] at the
    Paillier carriers and the Section-local [Pr_guess_enc_zero_le_invm].
    Kind: main.
    Why: provides the Paillier-instance closed-form bound required
    by the entropy-form corollaries in U3 that lift the probability
    inequality to a mutual-information statement.
    Used by: Paillier.entropy_random_guess in U3. *)
Definition secrecy_random_guess :
  distr.mu
    (pkg_advantage.Pr
       (dsdp_security_indcpa.guess_indicator_pkg
          (random_guess_adv ahe cipher_fin)
          (dsdp_security_indcpa.game_real (AHE:=ahe)
             (renc_card rand_fin)
             (rand_of_renc (AHE:=ahe)
                (rand_finType:=rand_fin) rand_finE)
             (t_msg:=t_msg ahe)
             (t_cipher:=t_cipher cipher_fin)
             (chmsg_of_msg (AHE:=ahe))
             (chcipher_of_cipher (AHE:=ahe)
                (cipher_finType:=cipher_fin) cipher_finE)
             (pkey_of_party (AHE:=ahe) pub_key_witness)
             (msg_of_idx (AHE:=ahe)))))
    true
    <= ((card_t_msg ahe)%:R)^-1 + 2%:R * indcpa_ror.epsilon_cpa
  := @secrecy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE pub_key_witness Pr_guess_enc_zero_le_invm.

(** Pr_real_gt0 - strict positivity at the Paillier carriers for
    [random_guess_adv]'s specific predictor.  Narrower than
    the deleted universal [Pr_guess_real_ge_invm].  Naming: 3
    components inside [Module Paillier / Section paillier]; externally
    [Paillier.Pr_real_gt0].
    Kind: section hypothesis.
    Why: feeds [entropy_random_guess]'s new [Pr_real_gt0]
    slot at the Paillier instance.  See [Module Concrete]'s
    [Pr_real_gt0] docstring for the IT discharge sketch.
    Used by: entropy_random_guess. *)
Hypothesis Pr_real_gt0 :
  (0 < distr.mu
        (pkg_advantage.Pr
           (dsdp_security_indcpa.guess_indicator_pkg
              (random_guess_adv ahe cipher_fin)
              (dsdp_security_indcpa.game_real (AHE:=ahe)
                 (renc_card rand_fin)
                 (rand_of_renc (AHE:=ahe)
                    (rand_finType:=rand_fin) rand_finE)
                 (t_msg:=t_msg ahe)
                 (t_cipher:=t_cipher cipher_fin)
                 (chmsg_of_msg (AHE:=ahe))
                 (chcipher_of_cipher (AHE:=ahe)
                    (cipher_finType:=cipher_fin) cipher_finE)
                 (pkey_of_party (AHE:=ahe) pub_key_witness)
                 (msg_of_idx (AHE:=ahe)))))
        true)%R.

(** epsilon_cpa_ge0 - nonnegativity of the IND-CPA error parameter.
    Mirrors [Module Concrete]'s Section hypothesis.
    Kind: section hypothesis.
    Why: needed for [entropy_random_guess] transitively through
    [entropy_random_guess].
    Used by: entropy_random_guess. *)
Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

(** entropy_random_guess - the closed-form Alice-secrecy bound in
    entropy form at the Paillier 1999 AHE instance and the trivial
    random-guess adversary.  Specialises
    [entropy_random_guess] at the Paillier carriers and the
    Section-local hypotheses.
    Kind: main.
    Why: provides the Paillier-instance entropy-form numeric bound
    [log m - log (1 + 2 * m * epsilon_cpa)] required by the
    information-theoretic Alice-secrecy statement.
    Used by: downstream consumers of the entropy-form bound. *)
Definition entropy_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.entropy (AHE:=ahe)
        (renc_card rand_fin)
        (rand_of_renc (AHE:=ahe)
           (rand_finType:=rand_fin) rand_finE)
        (t_msg:=t_msg ahe)
        (t_cipher:=t_cipher cipher_fin)
        (chmsg_of_msg (AHE:=ahe))
        (chcipher_of_cipher (AHE:=ahe)
           (cipher_finType:=cipher_fin) cipher_finE)
        (pkey_of_party (AHE:=ahe) pub_key_witness)
        (msg_of_idx (AHE:=ahe))
        (random_guess_adv ahe cipher_fin))%R
  := @entropy_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE msg_witness pub_key_witness
       Pr_guess_enc_zero_le_invm Pr_real_gt0 epsilon_cpa_ge0.

End paillier.

End Paillier.
