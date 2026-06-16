(* DSDP headline results — the apex.

   This file centralizes the headline theorems of the DSDP development. Each
   theorem's full proof is presented here over a cloned copy of its source
   section context; the supporting machinery stays in the axis files
   (counting/, symbolic_game/, indcpa_hopping/, convert/) and is referenced, not
   duplicated. The headlines are:

   Information-theoretic (counting axis)
     dsdp_centropy_uniform / dsdp_centropy_uniform_n — H(V2,V3 | view) = log m
     US_compromised_leaks_V2 / US_n_compromised_leaks_V1 — corrupted U leaks V
     bob_privacy_V1 / bob_privacy_V3 — H(V_i | BobView) = log m > 0
     charlie_privacy_V1 / charlie_privacy_V2 — H(V_i | CharlieView) = log m > 0
     relay_privacy_n — H(Y | View) = log m > 0 for a generic relay

   Corrupted-Alice secrecy (indcpa_hopping axis), the guessing triangle
     dsdp_alice_view_advantage_le — AdvantageE <= 2 * epsilon_cpa
     dsdp_alice_guess_ideal_le — guess <= 1/m (all-zero endpoint)
     dsdp_alice_guess_advantage_le — AdvantageE <= 2 * epsilon_cpa
     dsdp_alice_guess_real_le — guess <= 1/m + 2 * epsilon_cpa
     dsdp_alice_unpredictability_ge — H_unp >= log m - log (1 + 2 m epsilon_cpa) *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum lra.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
From SSProve.Crypt Require Import HybridArgument.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy extra_proba extra_algebra extra_entropy rouche_capelli.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code dsdp_symbolic_exec dsdp_game_derivation.
Require Import dsdp_indcpa_advantage dsdp_convert dsdp_guess_fiber.
Require Import dsdp_view_independence.

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

(* Pin SSProve's real type as the ambient realType. *)
Notation R := SSProve.Crypt.Axioms.R.

(* ================================================================= *)
(* Corrupted-Alice IND-CPA advantage (indcpa_hopping axis)           *)
(* ================================================================= *)

Section dsdp_alice_indcpa.
(* cloned context of Section dsdp_indcpa_advantage *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (msg_of_chmsg : t_msg -> plain AHE) (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (cipher_of_chcipher : t_cipher -> cipher AHE)
  (chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg)
  (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).

Let problem := @dsdp_problem AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
  msg_of_chmsg chmsg_of_msg chcipher_of_cipher cipher_of_chcipher chmsg_of_msgK
  chcipher_of_cipherK pkey_of_party card_msg msg_of_idx rand0.

(* dsdp_alice_view_advantage_le — for the concrete dsdp_problem instance, every
   adversary's advantage distinguishing the real corrupted-Alice cipher view
   from the all-zero view is at most 2 * epsilon_cpa. *)
Theorem dsdp_alice_view_advantage_le (Adv : dsdp_indcpa_adversary problem) :
  AdvantageE (real_game problem) (zero_game problem) (adv_package Adv)
    <= 2%:R * epsilon_cpa.
Proof.
have H := dsdp_indcpa_secrecy Adv.
rewrite /problem in H *.
by rewrite dsdp_problem_hops in H.
Qed.

End dsdp_alice_indcpa.
