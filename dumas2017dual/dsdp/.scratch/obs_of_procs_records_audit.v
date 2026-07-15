(* ADVERSARIAL AUDIT of the obs_of_procs record machinery. Scratch only; do not commit. *)

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

Notation R := SSProve.Crypt.Axioms.R.

(* ====== reuse the reduction-check's verified defs (NOT re-verified) ====== *)

Definition pbob_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pbob Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 10) 22 23).
Definition pcharlie_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pcharlie Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 11) 24 25).

Fixpoint first_send (p : proc symbolic_data) : option symbolic_data :=
  match p with
  | smc_interpreter.Init _ k => first_send k
  | smc_interpreter.Send _ d _ => Some d
  | _ => None
  end.

Definition dsdp_received_hop_ciphertexts : seq symbolic_data :=
  pmap first_send [:: pbob_sym ; pcharlie_sym].

Fixpoint walk_obs (p : proc symbolic_data) (resp : seq symbolic_data) (next : nat)
  : seq alice_obs :=
  match p with
  | smc_interpreter.Init _ k => walk_obs k resp next
  | smc_interpreter.Recv _ f =>
      match resp with
      | [::] => [::]
      | r :: rs =>
          match symbolic_get_cipher r with
          | Some (HE_enc party (HE_var secret) _) =>
              AO_recv_hop party secret next
                :: walk_obs (f (SD_cipher (HE_var next))) rs next.+1
          | _ => [::]
          end
      end
  | smc_interpreter.Send _ d k =>
      match symbolic_get_cipher d with
      | Some c => AO_combine next c :: walk_obs k resp next.+1
      | None => walk_obs k resp next
      end
  | smc_interpreter.Ret _ => [::]
  | smc_interpreter.Finish => [::]
  | smc_interpreter.Fail => [::]
  end.

Definition bound_names (w : seq alice_obs) : seq nat :=
  foldr (fun o acc =>
    match o with
    | AO_recv_hop _ _ result => result :: acc
    | AO_combine result _ => result :: acc
    | _ => acc
    end) [::] w.

Fixpoint term_value_names (t : he_term) : seq nat :=
  match t with
  | HE_var x => [:: x]
  | HE_const _ => [::]
  | HE_enc _ m _ => term_value_names m
  | HE_dec _ c => term_value_names c
  | HE_emul a b => term_value_names a ++ term_value_names b
  | HE_epow a b => term_value_names a ++ term_value_names b
  | HE_add a b => term_value_names a ++ term_value_names b
  | HE_sub a b => term_value_names a ++ term_value_names b
  | HE_mul a b => term_value_names a ++ term_value_names b
  end.

Fixpoint term_rnd_names (t : he_term) : seq nat :=
  match t with
  | HE_var _ => [::]
  | HE_const _ => [::]
  | HE_enc _ m r => term_rnd_names m ++ [:: r]
  | HE_dec _ c => term_rnd_names c
  | HE_emul a b => term_rnd_names a ++ term_rnd_names b
  | HE_epow a b => term_rnd_names a ++ term_rnd_names b
  | HE_add a b => term_rnd_names a ++ term_rnd_names b
  | HE_sub a b => term_rnd_names a ++ term_rnd_names b
  | HE_mul a b => term_rnd_names a ++ term_rnd_names b
  end.

Definition obs_value_names (o : alice_obs) : seq nat :=
  match o with
  | AO_recv_hop _ secret _ => [:: secret]
  | AO_combine _ expr => term_value_names expr
  | _ => [::]
  end.

Definition obs_rnd_names (o : alice_obs) : seq nat :=
  match o with
  | AO_combine _ expr => term_rnd_names expr
  | _ => [::]
  end.

Definition collect_samples (card_msg card_renc : nat) (w : seq alice_obs)
  : seq alice_obs :=
  let bound := bound_names w in
  let vals  := undup (flatten [seq obs_value_names o | o <- w]) in
  let rnds  := undup (flatten [seq obs_rnd_names o | o <- w]) in
  let vals' := [seq x <- vals | x \notin bound] in
  let rnds' := [seq x <- rnds | x \notin bound] in
  [seq AO_sample_val card_msg x | x <- vals']
    ++ [seq AO_sample_rnd card_renc x | x <- rnds'].

Definition combine_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with AO_combine result _ => Some result | _ => None end) w.
Definition recv_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with AO_recv_hop _ _ result => Some result | _ => None end) w.

Definition obs_of_procs (corrupt : proc symbolic_data)
    (hop_sends : seq symbolic_data) (challenge : nat)
    (leak : seq nat -> seq nat -> seq nat) (card_msg card_renc : nat)
  : seq alice_obs :=
  let w := walk_obs corrupt hop_sends 100 in
  collect_samples card_msg card_renc w
    ++ [:: AO_put challenge]
    ++ w
    ++ [:: AO_leak (leak (combine_names w) (recv_names w)) ].

(* ============ TARGET 1: the two records ============ *)

Record dsdp_indcpa_secrecy_problem := {
  sp_card_plaintext  : nat ;
  sp_card_randomness : nat ;
  sp_corrupted_party_program : proc symbolic_data ;
  sp_received_hop_ciphertexts : seq symbolic_data ;
  sp_challenge_secret : nat ;
  sp_leak_order : seq nat -> seq nat -> seq nat ;
  sp_enc_scheme : AHEncType ;
  sp_rand_carrier : finType ;
  sp_rand_carrier_card : #|sp_rand_carrier| = sp_card_randomness ;
  sp_rand_of_carrier : sp_rand_carrier -> rand sp_enc_scheme ;
  sp_choice_msg_type : choice_type ;
  sp_choice_cipher_type : choice_type ;
  sp_choice_msg_of_plain : plain sp_enc_scheme -> sp_choice_msg_type ;
  sp_plain_of_choice_msg : sp_choice_msg_type -> plain sp_enc_scheme ;
  sp_choice_msg_of_plainK : cancel sp_choice_msg_of_plain sp_plain_of_choice_msg ;
  sp_choice_cipher_of_cipher : cipher sp_enc_scheme -> sp_choice_cipher_type ;
  sp_cipher_of_choice_cipher : sp_choice_cipher_type -> cipher sp_enc_scheme ;
  sp_choice_cipher_of_cipherK :
    cancel sp_choice_cipher_of_cipher sp_cipher_of_choice_cipher ;
  sp_pub_key_of_party : party_id -> pub_key sp_enc_scheme ;
  sp_msg_of_index : 'I_sp_card_plaintext -> plain sp_enc_scheme ;
  sp_fallback_rand : rand sp_enc_scheme ;
}.

(* ============ TARGET 2: projections ============ *)

Definition corrupted_view (P : dsdp_indcpa_secrecy_problem) : seq alice_obs :=
  obs_of_procs (sp_corrupted_party_program P) (sp_received_hop_ciphertexts P)
    (sp_challenge_secret P) (sp_leak_order P)
    (sp_card_plaintext P) (sp_card_randomness P).

Definition game_of_problem (P : dsdp_indcpa_secrecy_problem) : game_code :=
  game_of_trace (corrupted_view P).

Definition game_iface_P (P : dsdp_indcpa_secrecy_problem) : Interface :=
  game_iface (sp_choice_msg_type P) (sp_choice_cipher_type P).

Definition protocol_state_P (P : dsdp_indcpa_secrecy_problem) : Locations :=
  protocol_state (sp_choice_msg_type P).

Definition real_oracle_P (P : dsdp_indcpa_secrecy_problem) :=
  oracle_real_pkg (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_plain_of_choice_msg) P.(sp_choice_cipher_of_cipher) (sp_pub_key_of_party P).

Definition zero_oracle_P (P : dsdp_indcpa_secrecy_problem) :=
  oracle_zero_pkg (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    (sp_choice_msg_type P) P.(sp_choice_cipher_of_cipher) (sp_pub_key_of_party P).

Definition real_game (P : dsdp_indcpa_secrecy_problem) : raw_package :=
  denote_game (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_choice_msg_of_plain) P.(sp_choice_cipher_of_cipher)
    (sp_pub_key_of_party P) P.(sp_msg_of_index) (sp_fallback_rand P)
    (all_real (game_of_problem P)).

Definition zero_game (P : dsdp_indcpa_secrecy_problem) : raw_package :=
  denote_game (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_choice_msg_of_plain) P.(sp_choice_cipher_of_cipher)
    (sp_pub_key_of_party P) P.(sp_msg_of_index) (sp_fallback_rand P)
    (all_zero (game_of_problem P)).

Record dsdp_indcpa_adversary (P : dsdp_indcpa_secrecy_problem) := {
  adv_locations : Locations ;
  adv_package   : raw_package ;
  adv_valid : ValidPackage adv_locations (game_iface_P P) A_export adv_package ;
  adv_disjoint_from_protocol_state : fseparate adv_locations (protocol_state_P P) ;
  adv_disjoint_from_real_oracle : fseparate adv_locations (real_oracle_P P).(locs) ;
  adv_disjoint_from_zero_oracle : fseparate adv_locations (zero_oracle_P P).(locs) ;
}.

(* local rebuilt gc_dsdp (mirrors the plan's Task-C two-index edit). *)
Definition gc_dsdp_rebuilt (card_renc card_msg : nat) : game_code :=
  GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (GC_sample card_renc (GC_sample card_renc
  (GC_put (HE_var 5)
  (GC_enc_hop 1 (HE_var 5)
  (GC_enc_hop 2 (HE_var 5)
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 5)) (HE_enc 1 (HE_var 4) 1))
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 4)) (HE_enc 2 (HE_var 3) 0))
  (GC_ret [:: HE_var 1 ; HE_var 0 ; HE_var 3 ; HE_var 2 ])
  )))))))))))).

(* The DERIVED dsdp_alice_obs (the plan's D4). *)
Definition dsdp_alice_obs_derived (card_msg card_renc : nat) : seq alice_obs :=
  obs_of_procs palice_sym dsdp_received_hop_ciphertexts 10
    (fun combines recvs => combines ++ recvs) card_msg card_renc.

(* ============ TARGET 3 + 4 : section mirroring dsdp_advantage_derived ============ *)
Section audit_E1.

Variable AHE : AHEncType.
Variable Renc : finType.
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.
Variable rand_of_renc : Renc -> rand AHE.
Variable t_msg t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.
Variable cipher_of_chcipher : t_cipher -> cipher AHE.
Hypothesis chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Variable pkey_of_party : party_id -> pub_key AHE.
Variable card_msg : nat.
Variable msg_of_idx : 'I_card_msg -> plain AHE.
Variable rand0 : rand AHE.

(* dsdp_problem as a record literal. Note: the record's sp_card_plaintext drives
   sp_msg_of_index's domain 'I_sp_card_plaintext; we must supply card_msg there. *)
Definition dsdp_problem : dsdp_indcpa_secrecy_problem :=
  {| sp_card_plaintext  := card_msg ;
     sp_card_randomness := card_renc ;
     sp_corrupted_party_program := palice_sym ;
     sp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts ;
     sp_challenge_secret := 10 ;
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

(* TARGET 3a : corrupted_view reduces to the derived trace, THROUGH projections. *)
Lemma audit_corrupted_view_reduces :
  corrupted_view dsdp_problem = dsdp_alice_obs_derived card_msg card_renc.
Proof. by []. Qed.

(* TARGET 3b : lifted faithfulness through the record projections. *)
Lemma audit_faithful :
  game_of_trace (corrupted_view dsdp_problem) = gc_dsdp_rebuilt card_renc card_msg.
Proof. by []. Qed.

(* TARGET 4 : E1 — the transported theorem (abstract P). *)
Theorem audit_E1 (P : dsdp_indcpa_secrecy_problem)
    (Adv : dsdp_indcpa_adversary P) :
  AdvantageE (real_game P) (zero_game P) (adv_package Adv)
    <= (count_obs_hops (corrupted_view P))%:R * epsilon_cpa.
Proof.
rewrite /real_game /zero_game /game_of_problem.
have Hcnt : count_obs_hops (corrupted_view P)
    = size (hop_sites (game_of_trace (corrupted_view P)))
  by rewrite -count_hops_game_of_trace /hop_sites size_iota.
rewrite Hcnt.
eapply advantage_le.
3: apply: (adv_valid Adv).
1: apply: (P.(sp_choice_cipher_of_cipherK)).
1: apply: (P.(sp_choice_msg_of_plainK)).
1: apply: (adv_disjoint_from_protocol_state Adv).
1: apply: (adv_disjoint_from_real_oracle Adv).
1: apply: (adv_disjoint_from_zero_oracle Adv).
Qed.

End audit_E1.

(* ============ E2 : thin corollary recovering dsdp_advantage_derived shape ============ *)
(* Probe whether the OLD loose-argument theorem can be a corollary of E1. The
   old statement concludes 2%:R * epsilon_cpa over the derived game with the
   loose dsdp_alice_obs_derived trace. We must build a dsdp_problem + an
   adversary record from the loose args, apply audit_E1, then reduce
   count_obs_hops (corrupted_view (dsdp_problem ...)) = 2. *)
Lemma audit_E2_corollary
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
       (all_real (game_of_trace (dsdp_alice_obs_derived card_msg card_renc))))
    (denote_game renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0
       (all_zero (game_of_trace (dsdp_alice_obs_derived card_msg card_renc))))
    A <= 2%:R * epsilon_cpa.
Proof.
pose P : dsdp_indcpa_secrecy_problem :=
  {| sp_card_plaintext  := card_msg ;
     sp_card_randomness := card_renc ;
     sp_corrupted_party_program := palice_sym ;
     sp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts ;
     sp_challenge_secret := 10 ;
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
have HE1 := audit_E1 Adv.
move: HE1.
by [].
Qed.

(* probe theorem to anchor an interactive session *)
Lemma audit_probe : True. Proof. exact: I. Qed.

Print Assumptions audit_E1.
Print Assumptions audit_E2_corollary.
