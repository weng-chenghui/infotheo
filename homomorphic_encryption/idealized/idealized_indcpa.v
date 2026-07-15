(** The IND-CPA real-or-zero advantage bound of the idealized scheme.

    [idealized_enc pk m r = m] returns its plaintext, so a single oracle query
    separates [oracle_encrypt_real] from [oracle_encrypt_zero] with certainty
    and [enc_ind_cpa_real_or_zero] forces [1 <= epsilon_cpa] at that scheme.
    Collapsing [epsilon_cpa] back to one constant shared by every [AHEncType]
    therefore contradicts any bound below 1. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import he_types enc_dec ahe_enc.
Require Import homomorphic_encryption.
Require Import indcpa_ror.
Require Import idealized_ahe.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(** R — SSProve's real type, pinned as in [indcpa_ror.v]. *)
Notation R := SSProve.Crypt.Axioms.R.

(** idealized_ahe_f2 — the idealized scheme of [idealized_ahe.v] over the
    plaintext space ['F_2], packed as an [AHEncType].
    Kind: canonical.
    Why: [enc_ind_cpa_real_or_zero] and [epsilon_cpa] are indexed by an
    [AHEncType]; ['F_2] is the smallest plaintext space with [1 != 0].
    Used by: epsilon_cpa_idealized_ge1. *)
Definition idealized_ahe_f2 : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes 'F_2)
    (@AHEnc.Class (Idealized_HETypes 'F_2)
      (@Idealized_isEncDec 'F_2) (@Idealized_isAHEnc 'F_2)).

(** idealized_msg_of_chmsg — the SSProve ['bool] message carrier marshalled
    into [plain idealized_ahe_f2], sending [true] to [1] and [false] to [0]. *)
Definition idealized_msg_of_chmsg (b : 'bool) : plain idealized_ahe_f2 :=
  if b then 1%R else 0%R.

(** idealized_chcipher_of_cipher — [cipher idealized_ahe_f2] marshalled into
    the SSProve ['bool] ciphertext carrier, injective on [{0, 1}]. *)
Definition idealized_chcipher_of_cipher (c : cipher idealized_ahe_f2) : 'bool :=
  (c != 0%R).

(** idealized_pkey_of_party — the public key of every party; the idealized
    [enc] ignores its key argument. *)
Definition idealized_pkey_of_party (_ : party_id) :
  pub_key idealized_ahe_f2 := 0%R.

(** idealized_rand_of_renc — the encryption randomness of every sample; the
    idealized [enc] ignores its randomness argument. *)
Definition idealized_rand_of_renc (_ : 'I_1) : rand idealized_ahe_f2 := 0%R.

(** idealized_renc_card — the cardinality bridge of [indcpa_ror.v] at the
    one-element randomness carrier ['I_1]. *)
Lemma idealized_renc_card : #|'I_1| = 1%N.
Proof. exact: card_ord. Qed.

(** idealized_oracle_real — the IND-CPA real oracle of [indcpa_ror.v]
    instantiated at [idealized_ahe_f2], ['bool] messages and ciphertexts.
    Kind: canonical.
    Used by: advantage_idealized_eq1, epsilon_cpa_idealized_ge1. *)
Definition idealized_oracle_real : raw_package :=
  oracle_encrypt_real idealized_ahe_f2 'I_1 1 idealized_renc_card
    idealized_rand_of_renc 'bool 'bool idealized_msg_of_chmsg
    idealized_chcipher_of_cipher idealized_pkey_of_party.

(** idealized_oracle_zero — the IND-CPA zero oracle of [indcpa_ror.v]
    instantiated at [idealized_ahe_f2], ['bool] messages and ciphertexts.
    Kind: canonical.
    Used by: advantage_idealized_eq1, epsilon_cpa_idealized_ge1. *)
Definition idealized_oracle_zero : raw_package :=
  oracle_encrypt_zero idealized_ahe_f2 'I_1 1 idealized_renc_card
    idealized_rand_of_renc 'bool 'bool idealized_chcipher_of_cipher
    idealized_pkey_of_party.

(** idealized_distinguisher_pkg — the adversary that queries the encryption
    oracle once on the message [true] and returns the reply.
    Kind: main.
    Why: [idealized_oracle_real] answers [enc _ 1 _ = 1], marshalled to [true];
    [idealized_oracle_zero] answers [enc _ 0 _ = 0], marshalled to [false].
    Used by: advantage_idealized_eq1. *)
Definition idealized_distinguisher_pkg :
  package (oracle_encrypt_iface 'bool 'bool) A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × 'bool → 'bool } as call_enc ;;
      c ← call_enc (0%N, true) ;;
      ret c
    }
  ].

(** idealized_distinguisher — [idealized_distinguisher_pkg] as a [raw_package],
    the form [AdvantageE] expects. *)
Definition idealized_distinguisher : raw_package :=
  pack idealized_distinguisher_pkg.

(** pr_idealized_real — the distinguisher returns [true] against the real
    oracle with probability 1. *)
Lemma pr_idealized_real :
  Pr (idealized_distinguisher ∘ idealized_oracle_real) true = 1%R.
Proof.
rewrite Pr_Pr_fst resolve_link.
rewrite [resolve idealized_distinguisher RUN tt]/resolve
  /idealized_distinguisher /idealized_distinguisher_pkg /= coerce_kleisliE.
rewrite /idealized_oracle_real /oracle_encrypt_real /=.
rewrite /resolve setmE eqxx /mkdef coerce_kleisliE.
rewrite /idealized_chcipher_of_cipher /idealized_msg_of_chmsg /= Pr_fst_sample.
rewrite Pr_fst_ret dletC pr_predT dunit1E eqxx.
by rewrite (@LosslessOp_uniform 1%N isT) mulr1.
Qed.

(** pr_idealized_zero — the distinguisher returns [true] against the zero
    oracle with probability 0. *)
Lemma pr_idealized_zero :
  Pr (idealized_distinguisher ∘ idealized_oracle_zero) true = 0%R.
Proof.
rewrite Pr_Pr_fst resolve_link.
rewrite [resolve idealized_distinguisher RUN tt]/resolve
  /idealized_distinguisher /idealized_distinguisher_pkg /= coerce_kleisliE.
rewrite /idealized_oracle_zero /oracle_encrypt_zero /=.
rewrite /resolve setmE eqxx /mkdef coerce_kleisliE.
rewrite /idealized_chcipher_of_cipher /= Pr_fst_sample.
by rewrite Pr_fst_ret dletC pr_predT dunit1E /= mulr0.
Qed.

(** advantage_idealized_eq1 — the distinguisher separates the two idealized
    oracles with advantage exactly 1. *)
Lemma advantage_idealized_eq1 :
  AdvantageE idealized_oracle_real idealized_oracle_zero
    idealized_distinguisher = 1%R.
Proof.
by rewrite /AdvantageE pr_idealized_real pr_idealized_zero subr0 normr1.
Qed.

(** epsilon_cpa_idealized_ge1 — the IND-CPA real-or-zero bound of the idealized
    scheme is at least 1.
    Kind: main.
    Why: pins [epsilon_cpa] as a per-scheme quantity.  One constant shared by
    every [AHEncType] would have to bound the idealized scheme too, and then
    every [_ <= 2 * epsilon_cpa] bound is vacuous.
    Used by: regression guard on the [epsilon_cpa] signature. *)
Lemma epsilon_cpa_idealized_ge1 : 1 <= epsilon_cpa idealized_ahe_f2.
Proof.
rewrite -advantage_idealized_eq1 /idealized_oracle_real /idealized_oracle_zero.
exact: enc_ind_cpa_real_or_zero.
Qed.
