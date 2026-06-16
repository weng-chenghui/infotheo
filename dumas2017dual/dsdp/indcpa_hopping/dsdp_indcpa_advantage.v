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
Require Import dsdp_symbolic_exec.
Require Import dsdp_game_derivation.

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

Section dsdp_indcpa_advantage.
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

End dsdp_indcpa_advantage.

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

(* ------------------------------------------------------------------ *)
(* Output-exposing hybrid ladder: the Part I IND-CPA bound carried     *)
(* through the wider denotation that adds the id_Sout_get output oracle.   *)
(*                                                                      *)
(* The run oracle is the SAME denote_run as in Part I, so the ladder    *)
(* reuses Part I's run-level perfect equivalences (denote_run_shim_-    *)
(* real_equiv / denote_run_shim_zero_equiv) verbatim; the only          *)
(* difference is that simplify_eq_rel exposes a third (id_Sout_get)        *)
(* reveal-oracle goal at every rung, discharged exactly as the          *)
(* id_v2_get goal.  Every *_leak_S lemma below is the Part I lemma of   *)
(* the same name with id_Sout_get carried alongside id_v2_get; the Part I  *)
(* statements are untouched.                                            *)
(* ------------------------------------------------------------------ *)

Section dsdp_game_code_leak_S.

Variable AHE : AHEncType.
Variable Renc : finType.
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.
Variable rand_of_renc : Renc -> rand AHE.
Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.
Variable cipher_of_chcipher : t_cipher -> cipher AHE.
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Hypothesis chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.
Variable pkey_of_party : party_id -> pub_key AHE.
Variable card_msg : nat.
Variable msg_of_idx : 'I_card_msg -> plain AHE.
Variable rand0 : rand AHE.
(* seed — the initial denotation env carrying the fixed input-weight parameters
   (weights-as-parameters, R-u3-regular).  The hybrid advantage is independent of
   it (S is common context), so it is threaded abstractly here. *)
Variable seed : denv AHE.

(* denote_game_shim_leak_S_raw — the raw three-oracle map underlying the
   output-exposing oracle-routed shim: the [denote_game_shim] run/V_2 pair
   plus the [id_Sout_get] output-reveal oracle. *)
Definition denote_game_shim_leak_S_raw (gc : game_code) (site : nat) : raw_package :=
  mkfmap
    [:: (id_game_run, mkdef 'unit (cipher_list t_cipher)
           (fun _ => denote_run_shim renc_card rand_of_renc chmsg_of_msg
                       chcipher_of_cipher cipher_of_chcipher pkey_of_party
                       msg_of_idx rand0 site 0 seed gc))
      ; (id_v2_get,   mkdef 'unit t_msg (fun _ => denote_v2_get_body chmsg_of_msg))
      ; (id_Sout_get,    mkdef 'unit t_msg (fun _ => denote_Sout_get_body chmsg_of_msg)) ].

(* Discharges the pack_valid field of denote_game_shim_leak_S: the run oracle
   via denote_run_shim_valid, the two reveal oracles by lifting their
   empty-import certificates through valid_injectMap. *)
Lemma denote_game_shim_leak_S_valid (gc : game_code) (site : nat) :
  ValidPackage (protocol_state t_msg) (oracle_encrypt_iface t_msg t_cipher)
    (game_iface_leak_S t_msg t_cipher)
    (denote_game_shim_leak_S_raw gc site).
Proof.
rewrite /denote_game_shim_leak_S_raw /game_iface_leak_S.
apply: valid_package_cons; last by move=> x; exact: denote_run_shim_valid.
apply: valid_package_cons;
  last by move=> x; apply: valid_injectMap; last exact: denote_v2_get_valid.
by apply: valid_package_cons;
  last by move=> x; apply: valid_injectMap; last exact: denote_Sout_get_valid.
Qed.

(* denote_game_shim_leak_S — output-exposing oracle-routed image of a
   [game_code]: [denote_game_shim] extended with the [id_Sout_get] output-reveal
   oracle, exporting [game_iface_leak_S]. *)
Definition denote_game_shim_leak_S (gc : game_code) (site : nat) :
  package (oracle_encrypt_iface t_msg t_cipher) (game_iface_leak_S t_msg t_cipher) :=
  mkpackage (protocol_state t_msg) (denote_game_shim_leak_S_raw gc site)
    (denote_game_shim_leak_S_valid gc site).

(* hop_equiv_real_leak_S — output-exposing real-side per-hop equivalence: ladder
   rung i of [denote_game_leak_S] equals the [denote_game_shim_leak_S] addressed
   at site i composed with the real-encryption oracle. *)
Lemma hop_equiv_real_leak_S (gc : game_code) (i : nat) :
  denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i gc)
  ≈₀ denote_game_shim_leak_S (zero_hop_prefix i gc) i
       ∘ oracle_real renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher
           pkey_of_party.
Proof.
(* simplify_eq_rel exposes the run goal (Part I denote_run_shim_real_equiv,
   reused verbatim since the run oracle is unchanged) then the V_2 and S
   cell-read goals, identical to each other. *)
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- apply: rpost_weaken_rule; first by apply: denote_run_shim_real_equiv.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(* hop_equiv_zero_leak_S — output-exposing zero-side per-hop equivalence: the
   [denote_game_shim_leak_S] addressed at site i composed with the
   zero-encryption oracle equals ladder rung i+1 of [denote_game_leak_S]. *)
Lemma hop_equiv_zero_leak_S (gc : game_code) (i : nat) :
  denote_game_shim_leak_S (zero_hop_prefix i gc) i
    ∘ oracle_zero renc_card rand_of_renc t_msg chcipher_of_cipher
        pkey_of_party
  ≈₀ denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i.+1 gc).
Proof.
(* Same shape as hop_equiv_real_leak_S: the run goal is Part I's
   denote_run_shim_zero_equiv (site pinned at i + 0 by addn0), the two
   cell-read goals are identical. *)
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- rewrite -[i in denote_run_shim _ _ _ _ _ _ _ _ i _ _ _]addn0.
  apply: rpost_weaken_rule; first by apply: denote_run_shim_zero_equiv.
  by move=> [? ?] [? ?] [-> ->].
- rewrite /denote_v2_get_body.
  ssprove_sync_eq=> stored.
  by case: stored => [v|]; rewrite [code_link _ _]/=; apply: r_ret.
- rewrite /denote_Sout_get_body.
  ssprove_sync_eq=> stored.
  by case: stored => [v|]; rewrite [code_link _ _]/=; apply: r_ret.
Qed.

(* advantage_hop_leak_S — one rung of the output-exposing hybrid ladder costs at
   most epsilon_cpa.  Same Advantage_triangle_chain / Advantage_link reduction to
   enc_ind_cpa_real_or_zero as advantage_hop, with the leak_S endpoints. *)
Lemma advantage_hop_leak_S
    (LA : Locations) (A : raw_package) (gc : game_code) (i : nat)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher
          pkey_of_party).(locs))
    (A_disj_oze : fseparate LA
       (oracle_zero_pkg renc_card rand_of_renc t_msg chcipher_of_cipher
          pkey_of_party).(locs)) :
  AdvantageE
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i gc))
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i.+1 gc)) A
    <= epsilon_cpa.
Proof.
have triangle_ineq :=
  Advantage_triangle_chain
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i gc) : raw_package)
    [:: (denote_game_shim_leak_S (zero_hop_prefix i gc) i
           ∘ oracle_real renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher
               pkey_of_party : raw_package)
      ; (denote_game_shim_leak_S (zero_hop_prefix i gc) i
           ∘ oracle_zero renc_card rand_of_renc t_msg chcipher_of_cipher
               pkey_of_party : raw_package) ]
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix i.+1 gc) : raw_package) A.
cbn [advantage_sum] in triangle_ineq.
rewrite ?addrA in triangle_ineq.
apply: (le_trans triangle_ineq).
clear triangle_ineq.
erewrite hop_equiv_real_leak_S by ssprove_valid.
erewrite hop_equiv_zero_leak_S by ssprove_valid.
rewrite GRing.add0r GRing.addr0.
rewrite -Advantage_link.
apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
          rand_of_renc t_msg t_cipher msg_of_chmsg
          chcipher_of_cipher pkey_of_party).
Qed.

(* advantage_sum_ladder_le_leak_S — a contiguous block of n+1 output-exposing
   ladder rungs costs at most n+1 copies of epsilon_cpa.  Same telescoping
   induction as advantage_sum_ladder_le. *)
Lemma advantage_sum_ladder_le_leak_S
    (LA : Locations) (A : raw_package) (gc : game_code)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher
          pkey_of_party).(locs))
    (A_disj_oze : fseparate LA
       (oracle_zero_pkg renc_card rand_of_renc t_msg chcipher_of_cipher
          pkey_of_party).(locs)) :
  forall (n start : nat),
  advantage_sum
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix start gc))
    [seq (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg
            chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed
            (zero_hop_prefix l gc) : raw_package) | l <- iota start.+1 n]
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix (start + n.+1) gc)) A
    <= n.+1 %:R * epsilon_cpa.
Proof.
elim=> [|n IHn] start.
- cbn [iota map advantage_sum]. rewrite addn1 mul1r.
  by apply: advantage_hop_leak_S.
- cbn [iota map advantage_sum]. rewrite mulrSr mulrDl mul1r addrC. apply: lerD.
  + rewrite -addSnnS. exact: IHn.
  + by apply: advantage_hop_leak_S.
Qed.

(* advantage_le_leak_S — the output-exposing analogue of advantage_le: any
   adversary's advantage distinguishing the output-exposing real game from its
   all-zero endpoint is at most [size (hop_sites gc)] copies of epsilon_cpa.
   The empty ladder collapses to advantage_self_zero (reused from Part I,
   generic over raw_package); the non-empty ladder telescopes through
   advantage_sum_ladder_le_leak_S. *)
Lemma advantage_le_leak_S
    (LA : Locations) (A : raw_package) (gc : game_code)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher
          pkey_of_party).(locs))
    (A_disj_oze : fseparate LA
       (oracle_zero_pkg renc_card rand_of_renc t_msg chcipher_of_cipher
          pkey_of_party).(locs)) :
  AdvantageE
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (all_real gc))
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed (all_zero gc)) A
    <= (size (hop_sites gc))%:R * epsilon_cpa.
Proof.
rewrite /all_real /all_zero /hop_sites size_iota.
case Hch: (count_hops gc) => [|m].
- by rewrite advantage_self_zero mul0r.
- have tri :=
    Advantage_triangle_chain
      (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
         pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix 0 gc) : raw_package)
      [seq (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg
              chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed
              (zero_hop_prefix i gc) : raw_package) | i <- iota 1 (count_hops gc - 1)]
      (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
         pkey_of_party msg_of_idx rand0 seed (zero_hop_prefix m.+1 gc) : raw_package) A.
  apply: (le_trans tri).
  rewrite Hch subn1 succnK.
  apply: advantage_sum_ladder_le_leak_S.
  + exact: A_disj_state.
  + exact: A_disj_ore.
  + exact: A_disj_oze.
Qed.

End dsdp_game_code_leak_S.

(* real_game_leak_S — the output-exposing real game of the DSDP problem: the
   all-real endpoint of [game_of_trace (dsdp_alice_obs_leak_S …)] denoted through
   [denote_game_leak_S], exposing the leaked ciphertexts, V_2 and the
   scalar-product output S. *)
Definition real_game_leak_S
    (AHE : AHEncType) (Renc : finType) (card_renc : nat)
    (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type) (chmsg_of_msg : plain AHE -> t_msg)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (pkey_of_party : party_id -> pub_key AHE)
    (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE)
    (rand0 : rand AHE) (seed : denv AHE) : raw_package :=
  denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed
    (all_real (game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded card_msg card_renc))).

(* zero_game_leak_S — the output-exposing all-zero endpoint of the DSDP problem,
   the distinguishing target of the output-exposing secrecy bound. *)
Definition zero_game_leak_S
    (AHE : AHEncType) (Renc : finType) (card_renc : nat)
    (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type) (chmsg_of_msg : plain AHE -> t_msg)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (pkey_of_party : party_id -> pub_key AHE)
    (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE)
    (rand0 : rand AHE) (seed : denv AHE) : raw_package :=
  denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed
    (all_zero (game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded card_msg card_renc))).

(* dsdp_advantage_derived_leak_S — the output-exposing analogue of
   [dsdp_advantage_derived]: any valid adversary distinguishing the
   output-exposing real game from its all-zero endpoint has advantage at most
   [2 * epsilon_cpa].  The output cell adds the common id_Sout_get oracle but no
   encryption hop, so the bound is the Part I bound; [advantage_le_leak_S] gives
   [size (hop_sites …) * epsilon_cpa] and the hop count reduces to 2 by
   [count_hops_game_of_trace] and [dsdp_obs_hops_leak_S]. *)
Lemma dsdp_advantage_derived_leak_S
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
    (rand0 : rand AHE) (seed : denv AHE) (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (A_disj_oze : fseparate LA
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    (zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    A <= 2%:R * epsilon_cpa.
Proof.
rewrite /real_game_leak_S /zero_game_leak_S.
have Hsz : size (hop_sites
    (game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded card_msg card_renc))) = 2
  by rewrite /hop_sites size_iota count_hops_game_of_trace_seeded
             dsdp_obs_hops_leak_S_seeded.
have H := advantage_le_leak_S chcipher_of_cipherK chmsg_of_msgK msg_of_idx rand0 seed
  (game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded card_msg card_renc))
  A_valid A_disj_state A_disj_ore A_disj_oze.
rewrite Hsz in H.
exact: H.
Qed.
