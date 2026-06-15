
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

From SSProve.Crypt Require Import Package pkg_composition Pr.

(* SSProve uses some of unicode in its package notation *)
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

(* One can never run a tactic on an unintended goal.
   Every branch is forced into a bullet *)
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* Make record it does not unfold to a match,
   evaluates faster, gives cleaner goals, and
   avoids the eta-conversion problems that plagued non-primitive records *)
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
Variable pub_key_witness : pub_key AHE.

(* `renc` is "Randomness for encryption" *)

Variable renc_witness : rand_finType.

Definition card_msg : nat := #|plain AHE|.
Definition card_renc : nat := #|rand_finType|.
Definition Renc : finType := rand_finType.

(* The type code (choice_type) that names
   the finite type with #|plain AHE| elements.

   To bridge the SSProve type code (choice_type) and math-comp finite type
   with #|plain AHE| elements.
*)
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

(* Bijection to build type bridge between AHE and SSProve. *)
Lemma chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.
Proof. exact: enum_rankK. Qed.

(* Bijection to build type bridge between AHE and SSProve. *)
Lemma chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Proof.
move=> c.
rewrite /chcipher_of_cipher /cipher_of_chcipher.
rewrite enum_rankK.
(* Trick: the equation cipher_finType = cipher AHE
     crosses HB coercions (Finite.sort vs GRing.NzRing.sort)

  `destruct` forces eq_refl by dependent pattern matching,
  collapsing both casts. Not sure know why case:... won't work.
*)
by destruct cipher_finType_eq.
Qed.

Definition card_t_msg : nat := card_msg.

(* At abstract level card_msg and card_t_msg is different.
  - card_msg = #|plain AHE|,
      the size of the protocol scalar space (the universe V_2 lives in).
  - card_t_msg =
      the size of the predictor's guess space (where adversary outputs go).

  In theory we can restrict that card_t_msg < card_msg to have a more
  restricted adversary. In current concrete instances,
  they are, by our choice of the adversary, the same.
*)
Lemma card_t_msg_gt0 : (0 < card_t_msg)%N.
Proof. exact: card_msg_gt0. Qed.

(* For every predictor in the considered class, the probability that the
  predictor correctly guesses V_2 from the leaked-ciphertext game is
  at most 1 / card_t_msg.

  (distr.mu is the probability mass function of a sub-distribution;
   SSProve uses sub-distribution since its relative monad of sub-distributions
   on choice_type.)
*)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : dsdp_security_indcpa.predictor_guesser t_msg t_cipher),
    distr.mu (pkg_advantage.Pr
                (dsdp_security_indcpa.guess_indicator_pkg predictor
                   (dsdp_security_indcpa.game_enc_zero (AHE:=AHE) renc_card
                      rand_of_renc (t_msg:=t_msg) (t_cipher:=t_cipher)
                      chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx)))
              true
      <= (card_t_msg%:R)^-1.

(* Since in SSProve pack we know msg is t_msg. *)
Local Notation "'msg'" := t_msg (in custom pack_type at level 2).


(* A stateless and oracle-free adversary: the predictor ignores all the leaked
   ciphertexts the game provides. When asked for its guess, it samples a fresh
   uniformly random plaintext and submits that as its guess at V_2.

   Used for realizing the lower-bound side of the secrecy theorem.
*)
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
apply: (@dsdp_security_indcpa.dsdp_alice_secrecy
        AHE Renc card_renc renc_card rand_of_renc
        t_msg t_cipher msg_of_chmsg chmsg_of_msg
        chcipher_of_cipher cipher_of_chcipher
        chcipher_of_cipherK chmsg_of_msgK
        pkey_of_party card_msg msg_of_idx
        card_t_msg
        Pr_guess_enc_zero_le_invm
        emptym random_guess_adv).  
- exact: (valid_boolean_shell_link random_guess_adv).
(* fseparate0m: the empty finite map is location-disjoint
   from any other finite map.
   
   Because random_guess_adv is stateless (emptym locations),
   in SSProve, locations map is the explicit declaration of
   "what mutable state cells this package owns";
   And we have one predictor map with its eight different
   possible stateful cells.
*)
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

(* log m  −  log (1 + 2·m·ε_cpa) ≤  -log Pr[guess = V_2]

   Against random_guess_adv,
   V_2's unpredictability reaches the closed-form lower bound.
*)
Corollary Hunp_random_guess :
  (dsdp_security_indcpa.bound card_t_msg
   <= dsdp_security_indcpa.Hunp (AHE:=AHE) (Renc:=Renc) (card_renc:=card_renc)
        renc_card rand_of_renc
        (t_msg:=t_msg) (t_cipher:=t_cipher)
        chmsg_of_msg chcipher_of_cipher pkey_of_party
        (card_msg:=card_msg) msg_of_idx
        random_guess_adv)%R.
Proof.
apply: (@dsdp_security_indcpa.Hunp_ge_bound
        AHE Renc card_renc renc_card rand_of_renc
        t_msg t_cipher msg_of_chmsg chmsg_of_msg
        chcipher_of_cipher cipher_of_chcipher
        chcipher_of_cipherK chmsg_of_msgK
        pkey_of_party card_msg msg_of_idx
        card_t_msg card_t_msg_gt0
        Pr_guess_enc_zero_le_invm
        epsilon_cpa_ge0
        emptym random_guess_adv).
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

(* rand ahe : Type is just a Type at HB level,
   so we need rand_fin for a concrete instance.
*) 
Lemma rand_finE : Finite.sort rand_fin = rand ahe.
Proof. by []. Qed.

Definition cipher_fin : Finite.type := 'F_p.

Lemma cipher_finE : Finite.sort cipher_fin = cipher ahe.
Proof. by []. Qed.

Definition pub_key_witness : pub_key ahe := 0%R.

Definition msg_witness : plain ahe := 0%R.

(* For every predictor in the narrowed class,
   the success probability against game_enc_zero is at most 1/card_t_msg
   (the same as uniform random guessing).

   game_enc_zero: the real game with all V_2-encrypting steps
   replaced by zero-encrypting steps under IND-CPA.

   There are other games for real DSDP (game_real),
   swapped one message (game_hybrid_one),
   swapped two messages (game_hybrid_two).

   Computional side, the chain of advantage that adversary A
   has at distinguishing game G_0 from game G_1 is:

   AdvantageE(game_real,game_hybrid_one)        ≤ ε_cpa
   AdvantageE(game_hybrid_one, game_hybrid_two) ≤ ε_cpa
   AdvantageE(game_hybrid_two, game_enc_zero)       = 0

   Finally we have:

   AdvantageE(game_real, game_enc_zero) ≤ 2·ε_cpa

   which invole the axiom: enc_ind_cpa_real_or_zero
   (the IND-CPA assumption that no SSProve adversary can distinguish
    ciphertext of real from ciphertext from zero with advantage greater
    than ε_cpa).

   Combine with this this hypothesis, we have the whole chain:

   Pr[guess = V_2 in game_real]
     ≤ Pr[guess = V_2 in game_enc_zero]       (1/card_t_msg; here we are)
       + AdvantageE(game_real, game_enc_zero) (2·ε_cpa)
*)
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

(* Use `Concrete.secrecy_random_guess` to define the closed-form
  guessing-probability bound `Pr[guess = V_2] ≤ 1/card_t_msg + 2·ε_cpa`
  for the protocol at the idealised AHE. Analogous definitions
  for Benaloh and Paillier follow below.
*)
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

(* Use `Concrete.Hunp_random_guess` to define the entropy lower bound
  `log card_t_msg − log(1 + 2·card_t_msg·ε_cpa) ≤ H_∞(V_2 | AliceView)`
  for the protocol at the idealised AHE. Analogous definitions for
  Benaloh and Paillier follow below.Use `Concrete.Hunp_random_guess`
  to define the entropy lower bound of the protocol at the idealised AHE.
  Analogous definitions for Benaloh and Paillier follow below. 
*)
Definition Hunp_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.Hunp (AHE:=ahe)
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
  := @Hunp_random_guess ahe rand_fin rand_finE
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

(* This is the one-line proof that the identity element 1 satisfies
  the public-key generator's order obligation (1 ^+ r = 1, trivially),
  used to build the simplest possible pub_key_witness inhabitant
  required to instantiate Module Concrete at the Benaloh / Paillier schemes.
*)
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

Definition Hunp_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.Hunp (AHE:=ahe)
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
  := @Hunp_random_guess ahe rand_fin rand_finE
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

Definition Hunp_random_guess :
  (dsdp_security_indcpa.bound (card_t_msg ahe)
   <= dsdp_security_indcpa.Hunp (AHE:=ahe)
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
  := @Hunp_random_guess ahe rand_fin rand_finE
       cipher_fin cipher_finE msg_witness pub_key_witness
       Pr_guess_enc_zero_le_invm Pr_real_gt0 epsilon_cpa_ge0.

End paillier.

End Paillier.
