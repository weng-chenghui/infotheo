
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
Require Import smc_session_types pismc_to_ssprove.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_interface dsdp_session_types dsdp_program dsdp_pismc.
Require Import dsdp_security_indcpa.
Require Import smc.ssprove_ext_lossless.

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

Notation R := SSProve.Crypt.Axioms.R.

Section dsdp_security_indcpa_pismc.

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

Definition sample_to_renc (i : 'I_card_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).
Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

Definition cipher_list : choice_type := chList t_cipher.

Local Notation "'ciphers'" := cipher_list (in custom pack_type at level 2).

Definition id_recv_enc_pismc : nat := 3%N.
Definition id_recv_dec_pismc : nat := 4%N.

Definition c2_cell : Location :=
  mkloc 10 (None : option t_cipher).

Definition c3_cell : Location :=
  mkloc 11 (None : option t_cipher).

Definition dsdp_pismc_locs : Locations :=
  unionm (protocol_state t_msg) [fmap c2_cell; c3_cell].

Definition data_dsdp : Type := di_data (Standard_DSDP_Interface AHE).

Definition dsdp_data_to_cipher (d : data_dsdp) : t_cipher :=
  match d with
  | inl (inl (inr c)) => chcipher_of_cipher c
  | _ => chcipher_of_cipher (0%R : cipher AHE)
  end.

Definition dsdp_cipher_to_data (c : t_cipher) : data_dsdp :=
  inl (inl (inr (cipher_of_chcipher c))).

Variable priv_key_witness : priv_key AHE.

Definition dsdp_palice_code
    (dk : priv_key AHE)
    (v1 u1 u2 u3 r2 r3 : plain AHE)
    (ra1 ra2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@palice AHE pkey_of_party dk v1 u1 u2 u3 r2 r3 ra1 ra2).

Definition dsdp_pbob_code
    (dk : priv_key AHE) (v2 : plain AHE) (rb1 rb2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@pbob AHE pkey_of_party dk v2 rb1 rb2).

Definition dsdp_pcharlie_code
    (dk : priv_key AHE) (v3 : plain AHE) (rc1 rc2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@pcharlie AHE pkey_of_party dk v3 rc1 rc2).

Lemma pbob_head_send_eq
    (dk : priv_key AHE) (v2 : plain AHE) (rb1 rb2 : rand AHE) :
  exists tail : code dsdp_pismc_locs
                  (recv_iface t_cipher
                              id_recv_enc_pismc id_recv_dec_pismc)
                  (chList t_cipher),
    dsdp_pbob_code dk v2 rb1 rb2 =
    code_of_send t_cipher id_recv_enc_pismc id_recv_dec_pismc
                 dsdp_pismc_locs
                 alice_idx
                 (chcipher_of_cipher
                    (enc (pkey_of_party Bob) v2 rb1))
                 tail.
Proof. Abort.

Lemma pcharlie_head_send_eq
    (dk : priv_key AHE) (v3 : plain AHE) (rc1 rc2 : rand AHE) :
  exists tail : code dsdp_pismc_locs
                  (recv_iface t_cipher
                              id_recv_enc_pismc id_recv_dec_pismc)
                  (chList t_cipher),
    dsdp_pcharlie_code dk v3 rc1 rc2 =
    code_of_send t_cipher id_recv_enc_pismc id_recv_dec_pismc
                 dsdp_pismc_locs
                 alice_idx
                 (chcipher_of_cipher
                    (enc (pkey_of_party Charlie) v3 rc1))
                 tail.
Proof. Abort.

Definition dsdp_recv_oracle :
  package [interface]
    (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc) :=
  [package [fmap c2_cell; c3_cell] ;
    #def #[ id_recv_enc_pismc ] (n : 'nat) : cipher_t
    {
      stored2 ← get c2_cell ;;
      stored3 ← get c3_cell ;;
      let stored := if n == bob_idx then stored2 else stored3 in
      match stored with
      | Some c => @ret t_cipher c
      | None   =>
          @ret t_cipher
            (chcipher_of_cipher (0%R : cipher AHE))
      end
    } ;
    #def #[ id_recv_dec_pismc ] (n : 'nat) : cipher_t
    {
      stored ← get c2_cell ;;
      match stored with
      | Some c => @ret t_cipher c
      | None   =>
          @ret t_cipher
            (chcipher_of_cipher (0%R : cipher AHE))
      end
    }
  ].

Definition game_real_pismc :
  package [interface] (game_iface t_msg t_cipher) :=
  [package dsdp_pismc_locs ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put (V_2_cell t_msg) := Some (chmsg_of_msg v2) ;;
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
      #put c2_cell := Some (chcipher_of_cipher c2) ;;
      #put c3_cell := Some (chcipher_of_cipher c3) ;;
      alice_sends ← code_link
                      (dsdp_palice_code priv_key_witness
                         (msg_of_idx iV2) (msg_of_idx iV2)
                         u2 u3 r2 r3 ra1 ra2)
                      (pack dsdp_recv_oracle) ;;
      ret (alice_sends ++
           [:: chcipher_of_cipher c2;
               chcipher_of_cipher c3] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

Check game_real_pismc.
Check dsdp_palice_code.
Check dsdp_pbob_code.
Check dsdp_pcharlie_code.
Check pbob_head_send_eq.
Check pcharlie_head_send_eq.
Check dsdp_recv_oracle.

Hypothesis game_real_eq_pismc :
  @game_real AHE Renc card_renc renc_card rand_of_renc
             t_msg t_cipher chmsg_of_msg chcipher_of_cipher
             pkey_of_party card_msg msg_of_idx
    ≈₀ game_real_pismc.

Lemma Pr_eq_of_game_real_eq_pismc
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor
                 (@game_real AHE Renc card_renc renc_card rand_of_renc
                             t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                             pkey_of_party card_msg msg_of_idx))) true
  = distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_real_pismc)) true.
Proof.
Abort.

Theorem dsdp_alice_secrecy_pismc
    (card_t_msg : nat)
    (Pr_guess_enc_zero_le_invm :
       forall (predictor : predictor_guesser t_msg t_cipher),
         distr.mu (pkg_advantage.Pr
                     (guess_indicator_pkg predictor
                        (@game_enc_zero AHE Renc card_renc renc_card
                                    rand_of_renc t_msg t_cipher
                                    chmsg_of_msg chcipher_of_cipher
                                    pkey_of_party card_msg msg_of_idx)))
                  true
           <= (card_t_msg%:R)^-1)
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs))
    (chain_disj_h1 :
       fseparate LA
         (@game_hybrid_one AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_h2 :
       fseparate LA
         (@game_hybrid_two AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_enc_zero :
       fseparate LA
         (@game_enc_zero AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA
         (@game_via_oracle_charlie AHE Renc card_renc renc_card
                               rand_of_renc t_msg t_cipher
                               chmsg_of_msg chcipher_of_cipher
                               cipher_of_chcipher pkey_of_party
                               card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA
         (@game_via_oracle_bob AHE Renc card_renc renc_card
                           rand_of_renc t_msg t_cipher
                           chmsg_of_msg chcipher_of_cipher
                           cipher_of_chcipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real_pismc)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
Abort.

Definition Hunp_pismc (predictor : predictor_guesser t_msg t_cipher) : R :=
  (- log (distr.mu
            (pkg_advantage.Pr
               (guess_indicator_pkg predictor game_real_pismc)) true))%R.

Theorem Hunp_ge_bound_pismc
    (card_t_msg : nat)
    (card_t_msg_gt0 : (0 < card_t_msg)%N)
    (Pr_guess_enc_zero_le_invm :
       forall (predictor : predictor_guesser t_msg t_cipher),
         distr.mu (pkg_advantage.Pr
                     (guess_indicator_pkg predictor
                        (@game_enc_zero AHE Renc card_renc renc_card
                                    rand_of_renc t_msg t_cipher
                                    chmsg_of_msg chcipher_of_cipher
                                    pkey_of_party card_msg msg_of_idx)))
                  true
           <= (card_t_msg%:R)^-1)
    (epsilon_cpa_ge0 : (0 <= epsilon_cpa)%R)
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs))
    (chain_disj_h1 :
       fseparate LA
         (@game_hybrid_one AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_h2 :
       fseparate LA
         (@game_hybrid_two AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_enc_zero :
       fseparate LA
         (@game_enc_zero AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA
         (@game_via_oracle_charlie AHE Renc card_renc renc_card
                               rand_of_renc t_msg t_cipher
                               chmsg_of_msg chcipher_of_cipher
                               cipher_of_chcipher pkey_of_party
                               card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA
         (@game_via_oracle_bob AHE Renc card_renc renc_card
                           rand_of_renc t_msg t_cipher
                           chmsg_of_msg chcipher_of_cipher
                           cipher_of_chcipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs))

    (Pr_real_pismc_gt0 :
       (0 < distr.mu (pkg_advantage.Pr
                        (guess_indicator_pkg predictor game_real_pismc)) true)%R) :
  (bound card_t_msg <= Hunp_pismc predictor)%R.
Proof.
Abort.

Check Pr_eq_of_game_real_eq_pismc.
Check dsdp_alice_secrecy_pismc.
Check Hunp_pismc.
Check Hunp_ge_bound_pismc.

End dsdp_security_indcpa_pismc.
