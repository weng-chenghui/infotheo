(* DSDP corrupted-Alice computational (IND-CPA) secrecy — the one-record facade.

   This file is the public presentation of the DSDP corrupted-Alice
   computational secrecy result.  A researcher supplies a concrete homomorphic
   encryption scheme plus the marshalling between its plaintexts/ciphertexts and
   SSProve choice types; the corrupted-view model itself is FIXED to DSDP inside
   the [dsdp_problem] record (the symbolically-executed corrupted-Alice program
   [palice_sym], the derived hop stream, and the challenge set to Bob's secret
   name).  [dsdp_problem_secure] then reads off the [2 * epsilon_cpa] bound by a
   single application of the generic [dsdp_indcpa_secrecy].

   This is the modern, derivation-backed parallel to the hand-written
   [ref/dsdp_security_indcpa.v]: same headline statement, but the game is the
   one auto-derived from the single DSDP program rather than a manual fixture. *)

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
Require Import dsdp_game_code.
Require Import dsdp_symbolic.
Require Import dsdp_game_symbolic.

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

Section dsdp_indcpa_security.
(* the only inputs a researcher supplies: the corrupt-view model is fixed to DSDP
   inside the record; these are the concrete scheme + marshalling. *)
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

(* dsdp_problem — THE one control record: the DSDP corrupted-Alice model
   (palice_sym, the derived hop stream, challenge = Bob's secret name) plus the
   chosen scheme + marshalling. Everything downstream is a projection of this. *)
Definition dsdp_problem : dsdp_indcpa_secrecy_problem :=
  {| sp_card_plaintext  := card_msg ; sp_card_randomness := card_renc ;
     sp_corrupted_party_program := palice_sym ;
     sp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts ;
     sp_challenge_secret := dsdp_v2_name ;
     sp_leak_order := fun combines recvs => combines ++ recvs ;
     sp_enc_scheme := AHE ; sp_rand_carrier := Renc ;
     sp_rand_carrier_card := renc_card ; sp_rand_of_carrier := rand_of_renc ;
     sp_choice_msg_type := t_msg ; sp_choice_cipher_type := t_cipher ;
     sp_choice_msg_of_plain := chmsg_of_msg ; sp_plain_of_choice_msg := msg_of_chmsg ;
     sp_choice_msg_of_plainK := chmsg_of_msgK ;
     sp_choice_cipher_of_cipher := chcipher_of_cipher ;
     sp_cipher_of_choice_cipher := cipher_of_chcipher ;
     sp_choice_cipher_of_cipherK := chcipher_of_cipherK ;
     sp_pub_key_of_party := pkey_of_party ; sp_msg_of_index := msg_of_idx ;
     sp_fallback_rand := rand0 |}.

(* the corrupted-Alice trace of dsdp_problem has exactly two encryption hops. *)
Example dsdp_problem_hops : count_obs_hops (corrupted_view dsdp_problem) = 2.
Proof. by []. Qed.

(* dsdp_problem_secure — the capstone, over the record's OWN games: every
   adversary's advantage distinguishing real_game dsdp_problem from
   zero_game dsdp_problem is at most 2 * epsilon_cpa. One application of the
   generic dsdp_indcpa_secrecy, reducing the hop count to 2. *)
Example dsdp_problem_secure (Adv : dsdp_indcpa_adversary dsdp_problem) :
  AdvantageE (real_game dsdp_problem) (zero_game dsdp_problem) (adv_package Adv)
    <= 2%:R * epsilon_cpa.
Proof. have H := dsdp_indcpa_secrecy Adv. by rewrite dsdp_problem_hops in H. Qed.
End dsdp_indcpa_security.

(* ------------------------------------------------------------------ *)
(* Capstone: the IND-CPA bound holds for the DERIVED game.             *)
(* ------------------------------------------------------------------ *)

(* dsdp_advantage_derived — the DSDP corollary of [dsdp_indcpa_secrecy]: any
   adversary's advantage distinguishing the real derived game from its all-zero
   endpoint is at most [2 * epsilon_cpa].  Parameters and premises mirror the
   loose-argument back-end interface verbatim; the proof packages the loose
   arguments into a [dsdp_indcpa_secrecy_problem] and a [dsdp_indcpa_adversary],
   instantiates the generic [dsdp_indcpa_secrecy], and reduces
   [count_obs_hops (corrupted_view (dsdp_problem ...))] to [2]. *)
Lemma dsdp_advantage_derived
    (AHE : AHEncType) (Renc : finType) (card_renc : nat)
    (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type) (msg_of_chmsg : t_msg -> plain AHE)
    (chmsg_of_msg : plain AHE -> t_msg)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg)
    (pkey_of_party : party_id -> pub_key AHE)
    (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE)
    (rand0 : rand AHE) (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA (game_iface t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (A_disj_oze : fseparate LA
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE
    (denote_game renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0
       (all_real (game_of_trace (dsdp_alice_obs card_msg card_renc))))
    (denote_game renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0
       (all_zero (game_of_trace (dsdp_alice_obs card_msg card_renc))))
    A <= 2%:R * epsilon_cpa.
Proof.
pose P : dsdp_indcpa_secrecy_problem :=
  {| sp_card_plaintext  := card_msg ;
     sp_card_randomness := card_renc ;
     sp_corrupted_party_program := palice_sym ;
     sp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts ;
     sp_challenge_secret := dsdp_v2_name ;
     sp_leak_order := fun combines recvs => combines ++ recvs ;
     sp_enc_scheme := AHE ;
     sp_rand_carrier := Renc ;
     sp_rand_carrier_card := renc_card ;
     sp_rand_of_carrier := rand_of_renc ;
     sp_choice_msg_type := t_msg ;
     sp_choice_cipher_type := t_cipher ;
     sp_choice_msg_of_plain := chmsg_of_msg ;
     sp_plain_of_choice_msg := msg_of_chmsg ;
     sp_choice_msg_of_plainK := chmsg_of_msgK ;
     sp_choice_cipher_of_cipher := chcipher_of_cipher ;
     sp_cipher_of_choice_cipher := cipher_of_chcipher ;
     sp_choice_cipher_of_cipherK := chcipher_of_cipherK ;
     sp_pub_key_of_party := pkey_of_party ;
     sp_msg_of_index := msg_of_idx ;
     sp_fallback_rand := rand0 |}.
pose Adv : dsdp_indcpa_adversary P :=
  @Build_dsdp_indcpa_adversary P LA A A_valid A_disj_state A_disj_ore A_disj_oze.
have H := dsdp_indcpa_secrecy Adv.
move: H; by [].
Qed.
