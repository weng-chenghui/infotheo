(* Scratch for Task 10 (corrected arch): rich sample fdist with ir1,ir2 capture.
   Develop here, port to the real file's Section dsdp_guess_distribution. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
From SSProve.Crypt Require Import HybridArgument.
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
Require Import dsdp_indcpa_security.
Require Import dsdp_security_indcpa_fiber.

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
#[local] Open Scope proba_scope.
#[local] Open Scope fdist_scope.

Notation R := SSProve.Crypt.Axioms.R.

Section scratch.
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.
Variable predictor : predictor_guesser t_msg t_cipher.
Variable Mfin : finType.
Variable msg_to_fin : t_msg -> Mfin.
Variable fin_to_msg : Mfin -> t_msg.
Hypothesis msg_to_finK : cancel msg_to_fin fin_to_msg.
Variable msg_of_chmsg : t_msg -> plain AHE.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Hypothesis Hmsg_bij : bijective msg_of_idx.
(* ir0 — a default inhabitant of the (non-empty) encryption-randomness space,
   seeding the captured-randomness accumulators before the first hop. *)
Variable ir0 : 'I_card_renc.

(* denote_run_full — mirror of denote_run that, at GC_put_output, additionally
   returns (v3, S, ir1, ir2): the secret read at de Bruijn index iv3, the output
   term S, and the two hop-encryption randomness samples threaded through the
   accumulator pair (each GC_enc_hop shifts in the freshly sampled randomness). *)
Fixpoint denote_run_full
  (iv3 : nat) (ir1 ir2 : 'I_card_renc)
  (e : denv AHE) (gc : game_code) {struct gc}
  : raw_code (cipher_list t_cipher *
              (plain AHE * plain AHE * 'I_card_renc * 'I_card_renc))%type :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        x ← sample uniform card_msg ;;
        denote_run_full iv3 ir1 ir2
          (push_val (Gplain (msg_of_idx x)) e) k
      else if n == card_renc then
        x ← sample uniform card_renc ;;
        denote_run_full iv3 ir1 ir2
          (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k
      else
        x ← sample uniform n ;;
        denote_run_full iv3 ir1 ir2 e k
  | GC_put t k =>
      #put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      denote_run_full iv3 ir1 ir2 e k
  | GC_put_output t k =>
      #put (S_output_cell t_msg) := Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      cl ← denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0 e k ;;
      ret (cl, (as_plain (de_val_nth e iv3),
                as_plain (denote_he pkey_of_party rand0 e t),
                ir1, ir2))
  | GC_let t k =>
      denote_run_full iv3 ir1 ir2
        (push_val (denote_he pkey_of_party rand0 e t) e) k
  | GC_enc_hop pk secret k =>
      ir_hop ← sample uniform card_renc ;;
      denote_run_full iv3 ir2 ir_hop
        (push_val
           (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                         (as_plain (denote_he pkey_of_party rand0 e secret))
                         (rand_of_renc (sample_to_renc renc_card ir_hop)))) e) k
  | GC_ret outs =>
      ret (([seq chcipher_of_cipher (as_cipher (denote_he pkey_of_party rand0 e o)) | o <- outs] : cipher_list t_cipher),
           (0%R, 0%R, ir0, ir0))
  end.

(* denote_run_full_fst — forgetting the captured tuple recovers the plain run. *)
Lemma denote_run_full_fst iv3 ir1 ir2 (e : denv AHE) (gc : game_code) :
  (xy ← denote_run_full iv3 ir1 ir2 e gc ;; ret xy.1)
  = denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
      pkey_of_party msg_of_idx rand0 e gc.
Proof.
elim: gc iv3 ir1 ir2 e => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs]
  iv3 ir1 ir2 e /=.
- case: (n == card_msg); [|case: (n == card_renc)]; cbn [bind]; congr sampler;
    apply: boolp.funext => x; exact: IH.
- cbn [bind]; congr putr; exact: IH.
- by rewrite bind_assoc; cbn [bind]; rewrite bind_ret.
- exact: IH.
- cbn [bind]; congr sampler; apply: boolp.funext => x; exact: IH.
- by [].
Qed.

Let game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed.
Let gc := all_zero (game_of_trace_seeded dsdp_weight_names
                      (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).

(* guess_resolved_full — the rich pair experiment. *)
Definition guess_resolved_full :
  raw_code (t_msg * t_msg *
            (plain AHE * plain AHE * 'I_card_renc * 'I_card_renc))%type :=
  vt ← denote_run_full 6 ir0 ir0 seed gc ;;
  s     ← denote_s_get_body chmsg_of_msg ;;
  guess ← resolve (pack predictor)
            (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) (vt.1, s) ;;
  v2    ← denote_v2_get_body chmsg_of_msg ;;
  ret (guess, v2, vt.2).

(* guess_full_code — the rich observed tuple pushed into the finite carrier:
   (guess, V2, V3, S, ir1, ir2). *)
Definition guess_full_code :
  raw_code (Mfin * Mfin * Mfin * Mfin * 'I_card_renc * 'I_card_renc)%type :=
  gv ← guess_resolved_full ;;
  let '(guess, v2, (v3, s, ir1, ir2)) := gv in
  ret (msg_to_fin guess, msg_to_fin v2,
       msg_to_fin (chmsg_of_msg v3), msg_to_fin (chmsg_of_msg s), ir1, ir2).

(* guess_full_marginal — the (guess, V_2)-projection of the rich observed tuple
   is the bridged pair code [guess_joint_code]. *)
Lemma guess_full_marginal :
  (gv ← guess_full_code ;;
   ret (gv.1.1.1.1.1, gv.1.1.1.1.2)) =
  guess_joint_code renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed predictor msg_to_fin.
Proof.
rewrite /guess_full_code /guess_resolved_full /guess_joint_code bind_assoc.
rewrite (guess_resolved_oracles renc_card rand_of_renc chmsg_of_msg
  chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor).
rewrite !bind_assoc.
have Hcont : forall (x : (cipher_list t_cipher *
    (plain AHE * plain AHE * 'I_card_renc * 'I_card_renc))%type),
  (x0 ← (s ← denote_s_get_body chmsg_of_msg ;;
        guess ← resolve predictor
                  (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
        v2 ← denote_v2_get_body chmsg_of_msg ;;
        ret (guess, v2, x.2)) ;;
   gv ← (let '(guess, v2, (v3, s, ir1, ir2)) := x0 in
        ret (msg_to_fin guess, msg_to_fin v2, msg_to_fin (chmsg_of_msg v3),
             msg_to_fin (chmsg_of_msg s), ir1, ir2)) ;;
   ret (gv.1.1.1.1.1, gv.1.1.1.1.2))
  = (s ← denote_s_get_body chmsg_of_msg ;;
     guess ← resolve predictor
               (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
     v2 ← denote_v2_get_body chmsg_of_msg ;;
     ret (msg_to_fin guess, msg_to_fin v2)).
{ move=> x; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => s; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => guess; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => v2; by case: (x.2) => [] [] [] *. }
transitivity (x ← denote_run_full 6 ir0 ir0 seed gc ;;
     (s ← denote_s_get_body chmsg_of_msg ;;
      guess ← resolve predictor
                (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
      v2 ← denote_v2_get_body chmsg_of_msg ;;
      ret (msg_to_fin guess, msg_to_fin v2))).
{ apply: bind_cong => //; apply: boolp.funext => x; exact: Hcont. }
rewrite -(denote_run_full_fst 6 ir0 ir0 seed gc) !bind_assoc.
apply: bind_cong => //; apply: boolp.funext => x.
cbn [bind].
rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => s.
rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => guess.
by rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => v2.
Qed.

(* guess_lossless — the bridged pair code terminates (existing hypothesis). *)
Hypothesis guess_lossless :
  psum (distr.mu (Pr_fst (guess_joint_code renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    msg_to_fin))) = 1.

(* guess_full_lossless — the rich experiment terminates with probability one. *)
Hypothesis guess_full_lossless : psum (distr.mu (Pr_fst guess_full_code)) = 1.

(* guess_sample_fdist — the Infotheo distribution over the rich tuple. *)
Definition guess_sample_fdist := sdistr_to_fdist guess_full_lossless.

(* fin_to_plain — recover the plaintext from a finite-carrier message. *)
Definition fin_to_plain (m : Mfin) : plain AHE := msg_of_chmsg (fin_to_msg m).

(* Projection RVs from the rich carrier; guess and V2 cross to [plain AHE] via
   [fin_to_plain] (the message-indexing bijection). *)
Definition guess : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.1.
Definition V2 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.2.
Definition V3 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.2.
Definition ir1 : {RV guess_sample_fdist -> 'I_card_renc} :=
  fun t => t.1.2.
Definition ir2 : {RV guess_sample_fdist -> 'I_card_renc} :=
  fun t => t.2.

(* The seeded weight constants (the protocol inputs are constants in the
   all-zero game). *)
Variables (v1 u1 u2 u3 : plain AHE).

(* S — the leaked output as a random variable, the scalar product of the
   constant inputs and the secret samples. *)
Definition S : {RV guess_sample_fdist -> plain AHE} :=
  fun t => dsdp_output v1 u1 u2 u3 (V2 t) (V3 t).

(* S_cell — the physical S carrier component (4th projection), the value the
   predictor conditions on. *)
Definition S_cell : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.2.

(* guess_S_determined — the leaked output is the scalar-product spec of the
   constant inputs and the secret samples; discharges the entropy-side
   constraint hypothesis (S_determined). *)
Lemma guess_S_determined :
  S = (fun t => dsdp_output v1 u1 u2 u3 (V2 t) (V3 t)).
Proof. by []. Qed.

(* guess_joint_fdist_marginal — the bridged pair distribution is the
   (guess, V2)-marginal of the rich sample distribution. *)
Lemma guess_joint_fdist_marginal :
  guess_joint_fdist guess_lossless
  = fdistmap (fun t : (Mfin * Mfin * Mfin * Mfin *
                       'I_card_renc * 'I_card_renc)%type
              => (t.1.1.1.1.1, t.1.1.1.1.2)) guess_sample_fdist.
Proof.
apply: fdist_ext => -[g v2].
rewrite /guess_joint_fdist sdistr_to_fdistE fdistmapE.
Admitted.

End scratch.
