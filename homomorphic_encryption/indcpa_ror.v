(** The IND-CPA real-or-zero advantage functional.

    Two oracle packages [oracle_encrypt_real] and [oracle_encrypt_zero]
    export one encryption operation parametric in [party_id]: on a query
    [(p, m)] the real oracle answers [enc pk_p m r] and the zero oracle
    answers [enc pk_p 0 r'], each for freshly sampled randomness.
    [indcpa_epsilon] applied to a reduction package is the [AdvantageE] of
    that package distinguishing the two oracles.

    Design commitments (Rocq audit):
    - Commitment 1: encryption randomness is a finType [Renc] with an index
      [index_renc : nat] for [sample uniform]; the file is parametric over
      [AHE : AHEncType] and these two carriers.
    - Commitment 5: the real-type binder of [AdvantageE] is pinned to
      [SSProve.Crypt.Axioms.R] via a [Notation R].

    Every computational bound downstream is an [indcpa_epsilon] of an
    explicitly constructed reduction, so no scheme-independent constant
    bounding it is assumed anywhere. *)

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
    here keeps [indcpa_epsilon : R] and every comparison against it in the
    same realType.
    Used by: indcpa_epsilon, downstream IND-CPA hops. *)
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
    indcpa_epsilon. *)
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
    Why: the real half of the real-or-zero pair.  Models the encryption
    oracle that an IND-CPA reduction uses to populate the ciphertext slots
    of the DSDP protocol view.
    Used by: oracle_encrypt_real, indcpa_epsilon. *)
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
    Why: the zero half of the real-or-zero pair.  Models the ideal world in
    which every ciphertext slot is independent of the plaintext modulo the
    encryption-randomness law.
    Used by: oracle_encrypt_zero, indcpa_epsilon. *)
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
    so we project the package to its raw form.
    Used by: indcpa_epsilon. *)
Definition oracle_encrypt_real : raw_package :=
  pack oracle_encrypt_real_pkg.

(** oracle_encrypt_zero — the zero-encryption oracle as a [raw_package].
    Kind: canonical.
    Why: companion to [oracle_encrypt_real] for the [AdvantageE] call in
    [indcpa_epsilon].
    Used by: indcpa_epsilon. *)
Definition oracle_encrypt_zero : raw_package :=
  pack oracle_encrypt_zero_pkg.

End indcpa_ror.

(** indcpa_epsilon — the IND-CPA real-or-zero advantage of [reduction]: the
    [AdvantageE] of distinguishing [oracle_encrypt_real] from
    [oracle_encrypt_zero]. *)
Definition indcpa_epsilon
    (AHE : AHEncType) (Renc : finType) (index_renc : nat)
    (renc_card : #|Renc| = index_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type)
    (msg_of_chmsg : t_msg -> plain AHE)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (pkey_of_party : party_id -> pub_key AHE)
    (reduction : raw_package) : R :=
  AdvantageE
    (oracle_encrypt_real AHE Renc index_renc renc_card rand_of_renc
       t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party)
    (oracle_encrypt_zero AHE Renc index_renc renc_card rand_of_renc
       t_msg t_cipher chcipher_of_cipher pkey_of_party)
    reduction.

(** Both oracle packages type-check as SSProve [package _ _ _]. *)
Check oracle_encrypt_real.
Check oracle_encrypt_zero.
Check oracle_encrypt_real_pkg.
Check oracle_encrypt_zero_pkg.
