(** IND-CPA real-or-zero hypothesis as an SSProve reduction-package interface.

    Per the audited plan at ~/.claude/plans/sprightly-finding-robin.md, Task 05.
    The file declares the IND-CPA real-or-zero hypothesis
    [enc_ind_cpa_real_or_zero] for the AHE scheme used by DSDP.  Two oracle
    packages [oracle_encrypt_real] and [oracle_encrypt_zero] expose a single
    encryption operation parametric in [party_id]: the real oracle returns
    [Enc pk_p m r] for a fresh [r], the zero oracle returns [Enc pk_p 0 r']
    for a fresh [r'].  The hypothesis bounds the [AdvantageE] of any adversary
    discriminating these two oracles by [epsilon_cpa].

    Design commitments (Rocq audit, plan section "Design commitments"):
    - Commitment 1: encryption randomness is a finType ([Renc]), with an
      index [index_renc : nat] for [sample uniform].  The file is parametric
      over [AHE : AHEncType] and these two carriers.
    - Commitment 5: the real-type binder for [AdvantageE] is pinned to
      [SSProve.Crypt.Axioms.R] via a [Notation R].

    The hypothesis ships with no proof: it is the cryptographic assumption
    that replaces the false IT idealisation [E_enc_inde] from
    [homomorphic_encryption.v].  Downstream consumers (Tasks 06-08) supply
    concrete adversaries via [predictor_via_oracle_charlie] and [predictor_via_oracle_bob] and
    feed them through this hypothesis using the SSProve [ssprove triangle]
    idiom from [theories/Crypt/examples/PRF.v]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import homomorphic_encryption.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(** R — SSProve's real type pinned for this file.
    Kind: canonical.
    Why: Design Commitment 5 of the Rocq audit.  [AdvantageE] returns a value
    in the [R : realType] declared at [SSProve.Crypt.Axioms.R]; pinning it
    here keeps the [epsilon_cpa : R] and the [AdvantageE _ _ _ <= epsilon_cpa]
    comparison in the same realType.
    Used by: enc_ind_cpa_real_or_zero, downstream IND-CPA hops. *)
Notation R := SSProve.Crypt.Axioms.R.

Section indcpa_ror.

(** AHE — the additively homomorphic encryption scheme this file is
    parametric over.  Instantiated downstream against Benaloh or Paillier. *)
Variable AHE : AHEncType.

(** Renc — finType carrier for encryption randomness (Design Commitment 1).
    [rand AHE] is declared as a bare [Type] in
    [homomorphic_encryption/he_types.v]; SSProve cannot [sample] from a bare
    [Type], so Tasks 05-13 use a refined finType.  Concrete instantiation
    against Benaloh/Paillier identifies [Renc] with [rand AHE] downstream. *)
Variable Renc : finType.

(** index_renc — natural number indexing [Renc] for [sample uniform].
    Why: [sample uniform n] takes a [nat] index, but the encryption call
    needs a value in [Renc].  The hypothesis [renc_card] below fixes the
    cardinality relationship so the two are interchangeable.
    Used by: oracle_encrypt_real, oracle_encrypt_zero. *)
Variable index_renc : nat.

(** renc_card — fixes the [Renc] cardinality at [index_renc] so an
    [@Ordinal index_renc] sample lifts to an [Renc] value via [enum_val].
    Kind: canonical.
    Why: bridges the SSProve [sample uniform index_renc] world (which lives
    in ['I_index_renc]) to the AHE [Renc] world (which is a finType).
    Used by: oracle_encrypt_real, oracle_encrypt_zero. *)
Hypothesis renc_card : #|Renc| = index_renc.

(** sample_to_renc — convert an SSProve uniform sample into an [Renc] value
    by routing through [enum_val] and the cardinality bridge [renc_card].
    Kind: helper.
    Why: [sample uniform index_renc] returns an ['I_index_renc].  The AHE
    [enc] expects an [Renc].  This helper plumbs them together using
    [enum_val] composed with the cardinality cast.
    Used by: oracle_encrypt_real, oracle_encrypt_zero. *)
Definition sample_to_renc (i : 'I_index_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

(** rand_of_renc — abstract conversion from the SSProve-side [Renc] finType
    to the AHE-side encryption-randomness carrier [rand AHE].  Required
    because [enc] is typed with [rand AHE] (a bare [Type]) but SSProve
    must sample over a finType.
    Kind: helper.
    Why: bridges Design Commitment 1 (SSProve sampling over a finType) and
    the AHE interface (which fixes [rand : Type]).  Downstream
    instantiations against Benaloh/Paillier provide a concrete map.
    Used by: oracle_encrypt_real_pkg, oracle_encrypt_zero_pkg. *)
Variable rand_of_renc : Renc -> rand AHE.

(** t_msg / t_cipher / msg_of_chmsg / chcipher_of_cipher — abstract
    conversions between the SSProve [choice_type] message and ciphertext
    carriers and the AHE [plain AHE] / [cipher AHE] types.  Provided by
    the surrounding [Variable]s so this file is insensitive to the
    concrete plain-message and ciphertext representations. *)
Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.

(** pkey_of_party — supplies the public key for a party.  Section-parametric
    so this file does not commit to a specific key-generation strategy.
    Kind: canonical.
    Why: every party in DSDP carries its own AHE public key.  The oracles
    encrypt under that key, looked up via this section variable.
    Used by: oracle_encrypt_real, oracle_encrypt_zero. *)
Variable pkey_of_party : party_id -> pub_key AHE.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'cipher'" := t_cipher (in custom pack_type at level 2).
Local Notation "'party'" := 'nat (in custom pack_type at level 2).

(** id_oracle_encrypt — oracle operation identifier shared by both oracles.
    Both [oracle_encrypt_real] and [oracle_encrypt_zero] export this single
    operation, so they share an interface and [AdvantageE] is well-typed
    on them.
    Kind: canonical.
    Why: SSProve operations are identified by a [nat]; the chosen value
    [42] is arbitrary but stable across the two oracles in this file.
    Used by: oracle_encrypt_real_pkg, oracle_encrypt_zero_pkg,
    oracle_encrypt_iface. *)
Definition id_oracle_encrypt : nat := 42.

(** oracle_encrypt_iface — the export interface common to both oracles.
    Exposes a single operation indexed by [id_oracle_encrypt] that takes a
    pair [(party_index : nat, message : msg)] and returns a ciphertext.
    Kind: canonical.
    Why: [AdvantageE oracle_encrypt_real oracle_encrypt_zero] requires the
    two packages to share an export interface, otherwise their composition
    with the adversary is ill-typed.  This is the shared signature.
    Used by: oracle_encrypt_real_pkg, oracle_encrypt_zero_pkg,
    enc_ind_cpa_real_or_zero. *)
Definition oracle_encrypt_iface : Interface :=
  [interface
    #val #[ id_oracle_encrypt ] : 'nat × msg → cipher
  ].

(** party_of_nat — bridge between the SSProve [nat] wire type and the
    [party_id] discrete enumeration.  Total: out-of-range indices fold to
    [NoParty], matching the [nat_to_party_id] convention in
    [homomorphic_encryption/homomorphic_encryption.v:98].
    Kind: helper.
    Why: oracle operations receive party indices as [nat] (SSProve wire
    type) but the public-key lookup [pkey_of_party] expects a [party_id].
    Used by: oracle_encrypt_real_pkg, oracle_encrypt_zero_pkg. *)
Definition party_of_nat (n : nat) : party_id := nat_to_party_id n.

(** oracle_encrypt_real_pkg — the real-encryption oracle package.
    On a query [(p, m)], samples fresh randomness [r] uniformly from [Renc]
    (via [sample_to_renc]) and returns the AHE ciphertext
    [enc (pkey_of_party (party_of_nat p)) m r], wrapped into the SSProve
    cipher carrier via [chcipher_of_cipher].
    Kind: main.
    Why: one half of the IND-CPA real-or-zero hypothesis.  Models the real
    encryption oracle that the IND-CPA reduction uses to populate the
    ciphertext slots of the DSDP protocol view.
    Used by: oracle_encrypt_real, enc_ind_cpa_real_or_zero. *)
Definition oracle_encrypt_real_pkg :
  package
    [interface]
    oracle_encrypt_iface :=
  [package emptym ;
    #def #[ id_oracle_encrypt ] (q : 'nat × msg) : cipher
    {
      let '(p, m) := q in
      r ← sample uniform index_renc ;;
      ret (chcipher_of_cipher
             (enc (pkey_of_party (party_of_nat p))
                  (msg_of_chmsg m)
                  (rand_of_renc (sample_to_renc r))))
    }
  ].

(** oracle_encrypt_zero_pkg — the zero-encryption oracle package.
    On a query [(p, m)], discards [m], samples fresh randomness [r']
    uniformly from [Renc], and returns the AHE ciphertext of the additive
    identity [0_R : plain AHE] under [pkey_of_party (party_of_nat p)].
    Kind: main.
    Why: the other half of the IND-CPA real-or-zero hypothesis.  Models
    the ideal world in which every ciphertext slot is independent of the
    plaintext modulo the encryption-randomness law.
    Used by: oracle_encrypt_zero, enc_ind_cpa_real_or_zero. *)
Definition oracle_encrypt_zero_pkg :
  package
    [interface]
    oracle_encrypt_iface :=
  [package emptym ;
    #def #[ id_oracle_encrypt ] (q : 'nat × msg) : cipher
    {
      let '(p, _) := q in
      r ← sample uniform index_renc ;;
      ret (chcipher_of_cipher
             (enc (pkey_of_party (party_of_nat p))
                  (0%R : plain AHE)
                  (rand_of_renc (sample_to_renc r))))
    }
  ].

(** oracle_encrypt_real — the real-encryption oracle exposed as a
    [raw_package], the form [AdvantageE] expects.
    Kind: canonical.
    Why: [AdvantageE] in [pkg_advantage.v:79] is stated over [raw_package],
    so we project the package to its raw form for use in the hypothesis.
    Used by: enc_ind_cpa_real_or_zero. *)
Definition oracle_encrypt_real : raw_package :=
  pack oracle_encrypt_real_pkg.

(** oracle_encrypt_zero — the zero-encryption oracle as a [raw_package].
    Kind: canonical.
    Why: companion to [oracle_encrypt_real] for the [AdvantageE] call in
    [enc_ind_cpa_real_or_zero].
    Used by: enc_ind_cpa_real_or_zero. *)
Definition oracle_encrypt_zero : raw_package :=
  pack oracle_encrypt_zero_pkg.

End indcpa_ror.

(** epsilon_cpa — the IND-CPA hardness parameter, abstract real number in
    [R] (i.e., [SSProve.Crypt.Axioms.R]).  Top-level parameter so the
    hypothesis below quantifies it once and downstream files share the
    same security parameter.
    Kind: canonical.
    Why: the IND-CPA advantage bound is parametric in the security
    parameter; pinning a concrete value would over-constrain the
    cryptographic assumption.
    Used by: enc_ind_cpa_real_or_zero, downstream advantage_bound theorems. *)
Parameter epsilon_cpa : reals.Real.sort R.

(** enc_ind_cpa_real_or_zero — the IND-CPA real-or-zero hypothesis.
    For every choice of AHE scheme, encryption randomness carrier, message
    and ciphertext carriers, public-key map, and every adversary
    [reduction], the SSProve advantage of distinguishing
    [oracle_encrypt_real] from [oracle_encrypt_zero] is at most
    [epsilon_cpa].  This is the cryptographic assumption that replaces the
    false IT idealisation [E_enc_inde] from
    [homomorphic_encryption.v:281].
    Kind: main.
    Why: only realistic encryption assumption needed by the DSDP Alice
    secrecy proof in the new file [dsdp_security_indcpa.v].  Combined with
    [Pr_dsdp_sol_uniform] (the IT residual on the joint sample), it yields
    the closed-form bound [1/m + 2 * epsilon_cpa] on the predictor's
    success probability.  Stated at the top level (outside the Section) so
    Section parameters are universally quantified and the hypothesis is
    visible to downstream files via [Require Import indcpa_ror.].
    Used by: dsdp_security_indcpa.v Tasks 08-14 (advantage_bound,
    dsdp_alice_secrecy_indcpa, dsdp_alice_unp_entropy_indcpa). *)
Axiom enc_ind_cpa_real_or_zero :
  forall (AHE : AHEncType) (Renc : finType) (index_renc : nat)
         (renc_card : #|Renc| = index_renc)
         (rand_of_renc : Renc -> rand AHE)
         (t_msg t_cipher : choice_type)
         (msg_of_chmsg : t_msg -> plain AHE)
         (chcipher_of_cipher : cipher AHE -> t_cipher)
         (pkey_of_party : party_id -> pub_key AHE)
         (reduction : raw_package),
    AdvantageE
      (oracle_encrypt_real AHE Renc index_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party)
      (oracle_encrypt_zero AHE Renc index_renc renc_card rand_of_renc
         t_msg t_cipher chcipher_of_cipher pkey_of_party)
      reduction <= epsilon_cpa.

(** Task 05 verification: both oracle packages type-check as SSProve
    [package _ _ _], and the IND-CPA hypothesis type-checks against
    [AdvantageE] from [pkg_advantage.v]. *)
Check oracle_encrypt_real.
Check oracle_encrypt_zero.
Check oracle_encrypt_real_pkg.
Check oracle_encrypt_zero_pkg.
Check @enc_ind_cpa_real_or_zero.
