
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

Notation R := SSProve.Crypt.Axioms.R.

Module Concrete.

Section concrete.

Variable AHE : AHEncType.

Variable rand_finType : Finite.type.
Hypothesis rand_finType_eq : Finite.sort rand_finType = rand AHE.

Variable cipher_finType : Finite.type.
Hypothesis cipher_finType_eq : Finite.sort cipher_finType = cipher AHE.

Variable msg_witness : plain AHE.
Variable renc_witness : rand_finType.
Variable pub_key_witness : pub_key AHE.

Definition card_msg : nat := #|plain AHE|.

Definition card_renc : nat := #|rand_finType|.

Definition Renc : finType := rand_finType.

Definition t_msg : choice_type := chFin #|plain AHE|.

Definition t_cipher : choice_type := chFin #|cipher_finType|.

Definition msg_of_chmsg : t_msg -> plain AHE :=
  fun i => enum_val i.

Definition chmsg_of_msg : plain AHE -> t_msg :=
  fun m => enum_rank m.

Definition cipher_of_chcipher : t_cipher -> cipher AHE :=
  fun i => eq_rect _ id (enum_val i : cipher_finType) _ cipher_finType_eq.

Definition chcipher_of_cipher : cipher AHE -> t_cipher :=
  fun c => enum_rank (eq_rect _ id c _ (esym cipher_finType_eq)
                       : cipher_finType).

Definition msg_of_idx : 'I_card_msg -> plain AHE :=
  fun i => enum_val i.

Definition rand_of_renc : Renc -> rand AHE :=
  fun r => eq_rect _ id r _ rand_finType_eq.

Definition pkey_of_party : party_id -> pub_key AHE :=
  fun _ => pub_key_witness.

Lemma renc_card : #|Renc| = card_renc.
Proof. by []. Qed.

Lemma card_msg_gt0 : (0 < card_msg)%N.
Proof. by apply/card_gt0P; exists msg_witness. Qed.

Lemma card_renc_gt0 : (0 < card_renc)%N.
Proof. by apply/card_gt0P; exists renc_witness. Qed.

Lemma chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.
Proof. exact: enum_rankK. Qed.

Lemma chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Proof.
move=> c.
rewrite /chcipher_of_cipher /cipher_of_chcipher.
rewrite enum_rankK.
by destruct cipher_finType_eq.
Qed.

Definition card_t_msg : nat := card_msg.

Lemma card_t_msg_gt0 : (0 < card_t_msg)%N.
Proof. exact: card_msg_gt0. Qed.

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

Definition random_guess_adv : dsdp_security_indcpa.predictor_guesser t_msg t_cipher :=
  [package emptym ;
    #def #[ dsdp_security_indcpa.id_guess ] (_ : 'unit) : msg
    {
      iV ← sample uniform #|plain AHE| ;;
      ret (chmsg_of_msg (enum_val iV))
    }
  ].

Check random_guess_adv : dsdp_security_indcpa.predictor_guesser t_msg t_cipher.

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

Hypothesis Pr_real_gt0 :
  (0 < distr.mu (pkg_advantage.Pr
                   (dsdp_security_indcpa.guess_indicator_pkg
                      random_guess_adv
                      (dsdp_security_indcpa.game_real (AHE:=AHE) renc_card
                         rand_of_renc (t_msg:=t_msg) (t_cipher:=t_cipher)
                         chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx)))
                 true)%R.

Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

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

Module Idealized.
Import Concrete.

Section idealized.

Variable p : nat.

Definition ahe : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes 'F_p)
    (@AHEnc.Class (Idealized_HETypes 'F_p)
      (@Idealized_isEncDec 'F_p)
      (@Idealized_isAHEnc 'F_p)).

Definition rand_fin : Finite.type := 'F_p.

Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

Definition cipher_fin : Finite.type := 'F_p.

Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

Definition pub_key_witness : pub_key ahe := 0%R.

Definition msg_witness : plain ahe := 0%R.

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

Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

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

Module Benaloh.
Import Concrete.

Section benaloh.

Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.

Hypothesis r_gt1 : (1 < r)%N.

Definition ahe : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r)
       (Benaloh_isEncDec n r)
       (@Benaloh_isAHEnc n r r_gt1)).

Definition rand_fin : Finite.type := {unit 'Z_n} : Finite.type.

Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

Definition cipher_fin : Finite.type := 'Z_n : Finite.type.

Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

Definition msg_witness : plain ahe := 0%R.

Definition renc_witness : rand_fin := 1%g.

Lemma pub_gen_order1 : (val (1%g : {unit 'Z_n})) ^+ r = 1.
Proof. by rewrite FinRing.val_unit1 expr1n. Qed.

Definition pub_key_witness : pub_key ahe :=
  @MkBenalohPubKey n r 1%g pub_gen_order1.

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

Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

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

Module Paillier.
Import Concrete.

Section paillier.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

Definition ahe : AHEncType :=
  @AHEnc.Pack (PaillierHETypes n)
    (@AHEnc.Class (PaillierHETypes n)
       (@Paillier_isEncDec n)
       (@Paillier_isAHEnc n n_gt1)).

Definition rand_fin : Finite.type := {unit 'Z_(n * n)} : Finite.type.

Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

Definition cipher_fin : Finite.type := 'Z_(n * n) : Finite.type.

Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

Definition msg_witness : plain ahe := 0%R.

Definition renc_witness : rand_fin := 1%g.

Lemma pub_gen_order1 : (1 : 'Z_(n * n)) ^+ n = 1.
Proof. exact: expr1n. Qed.

Definition pub_key_witness : pub_key ahe :=
  @MkPaillierPubKey n 1 pub_gen_order1.

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

Hypothesis epsilon_cpa_ge0 : (0 <= indcpa_ror.epsilon_cpa)%R.

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
