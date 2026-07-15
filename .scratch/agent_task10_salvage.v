(* Scratch for Task 10: rich sample fdist. Develop here, port to the real file. *)
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

(* Check plain AHE is a choice_type usable in raw_code. *)
Check (plain AHE : choiceType).

(* denote_run_full — mirror of denote_run that, at GC_put_output, additionally
   returns the seven plaintext env values (v1,u1,u2,u3,v2,v3,S) read at the
   output point's de Bruijn indices and the output term S. *)
Fixpoint denote_run_full
  (iv1 iu1 iu2 iu3 iv2 iv3 : nat)
  (e : denv AHE) (gc : game_code) {struct gc}
  : raw_code (cipher_list t_cipher *
              (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE * plain AHE * plain AHE))%type :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        x ← sample uniform card_msg ;;
        denote_run_full iv1 iu1 iu2 iu3 iv2 iv3
          (push_val (Gplain (msg_of_idx x)) e) k
      else if n == card_renc then
        x ← sample uniform card_renc ;;
        denote_run_full iv1 iu1 iu2 iu3 iv2 iv3
          (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k
      else
        x ← sample uniform n ;;
        denote_run_full iv1 iu1 iu2 iu3 iv2 iv3 e k
  | GC_put t k =>
      #put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      denote_run_full iv1 iu1 iu2 iu3 iv2 iv3 e k
  | GC_put_output t k =>
      #put (S_output_cell t_msg) := Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      cl ← denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0 e k ;;
      ret (cl, (as_plain (de_val_nth e iv1), as_plain (de_val_nth e iu1),
                as_plain (de_val_nth e iu2), as_plain (de_val_nth e iu3),
                as_plain (de_val_nth e iv2), as_plain (de_val_nth e iv3),
                as_plain (denote_he pkey_of_party rand0 e t)))
  | GC_let t k =>
      denote_run_full iv1 iu1 iu2 iu3 iv2 iv3
        (push_val (denote_he pkey_of_party rand0 e t) e) k
  | GC_enc_hop pk secret k =>
      ir_hop ← sample uniform card_renc ;;
      denote_run_full iv1 iu1 iu2 iu3 iv2 iv3
        (push_val
           (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                         (as_plain (denote_he pkey_of_party rand0 e secret))
                         (rand_of_renc (sample_to_renc renc_card ir_hop)))) e) k
  | GC_ret outs =>
      ret (([seq chcipher_of_cipher (as_cipher (denote_he pkey_of_party rand0 e o)) | o <- outs] : cipher_list t_cipher),
           (0%R, 0%R, 0%R, 0%R, 0%R, 0%R, 0%R))
  end.

(* denote_run_full_fst — forgetting the captured plaintext tuple recovers the
   plain run; the rich run is faithful on the cipher-list channel. *)
Lemma denote_run_full_fst iv1 iu1 iu2 iu3 iv2 iv3 (e : denv AHE) (gc : game_code) :
  (xy ← denote_run_full iv1 iu1 iu2 iu3 iv2 iv3 e gc ;; ret xy.1)
  = denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
      pkey_of_party msg_of_idx rand0 e gc.
Proof.
elim: gc e => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e /=.
- case: (n == card_msg); [|case: (n == card_renc)]; cbn [bind]; congr sampler;
    apply: boolp.funext => x; exact: IH.
- cbn [bind]; congr putr; exact: IH.
- by rewrite bind_assoc; cbn [bind]; rewrite bind_ret.
- exact: IH.
- cbn [bind]; congr sampler; apply: boolp.funext => x; exact: IH.
- by [].
Qed.

(* Concrete output-point de Bruijn indices read off gc_eq:
   v1 = 11, u1 = 8, u2 = 9, u3 = 10, v2 = 7, v3 = 6. *)
Let game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed.
Let gc := all_zero (game_of_trace_seeded dsdp_weight_names
                      (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).

(* guess_resolved_full — the rich pair experiment: the full run exposes the
   output-point env values, then S / guess / V_2 are read as in
   [guess_resolved_oracles]; returns the eight observed messages. *)
Definition guess_resolved_full :
  raw_code (t_msg * t_msg *
            (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE *
             plain AHE * plain AHE))%type :=
  vt ← denote_run_full 11 8 9 10 7 6 seed gc ;;
  s     ← denote_s_get_body chmsg_of_msg ;;
  guess ← resolve (pack predictor)
            (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) (vt.1, s) ;;
  v2    ← denote_v2_get_body chmsg_of_msg ;;
  ret (guess, v2, vt.2).

(* guess_full_code — the rich observed tuple pushed into the finite carrier
   [Mfin]: (guess, V2, V3, S, V1, U1, U2, U3). *)
Definition guess_full_code :
  raw_code (Mfin * Mfin * Mfin * Mfin * Mfin * Mfin * Mfin * Mfin)%type :=
  gv ← guess_resolved_full ;;
  let '(guess, v2, (v1, u1, u2, u3, v2', v3, s)) := gv in
  ret (msg_to_fin guess, msg_to_fin v2,
       msg_to_fin (chmsg_of_msg v3), msg_to_fin (chmsg_of_msg s),
       msg_to_fin (chmsg_of_msg v1), msg_to_fin (chmsg_of_msg u1),
       msg_to_fin (chmsg_of_msg u2), msg_to_fin (chmsg_of_msg u3)).

(* guess_full_marginal — the (guess, V_2)-projection of the rich observed tuple
   is the bridged pair code [guess_joint_code]. *)
Lemma guess_full_marginal :
  (gv ← guess_full_code ;;
   ret (gv.1.1.1.1.1.1.1, gv.1.1.1.1.1.1.2)) =
  guess_joint_code renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed predictor msg_to_fin.
Proof.
rewrite /guess_full_code /guess_resolved_full /guess_joint_code bind_assoc.
rewrite (guess_resolved_oracles renc_card rand_of_renc chmsg_of_msg
  chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor).
rewrite !bind_assoc.
have Hcont : forall (x : (cipher_list t_cipher *
    (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE * plain AHE *
     plain AHE))%type),
  (x0 ← (s ← denote_s_get_body chmsg_of_msg ;;
        guess ← resolve predictor
                  (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
        v2 ← denote_v2_get_body chmsg_of_msg ;;
        ret (guess, v2, x.2)) ;;
   gv ← (let '(guess, v2, (v1, u1, u2, u3, _, v3, s)) := x0 in
        ret (msg_to_fin guess, msg_to_fin v2, msg_to_fin (chmsg_of_msg v3),
             msg_to_fin (chmsg_of_msg s), msg_to_fin (chmsg_of_msg v1),
             msg_to_fin (chmsg_of_msg u1), msg_to_fin (chmsg_of_msg u2),
             msg_to_fin (chmsg_of_msg u3))) ;;
   ret (gv.1.1.1.1.1.1.1, gv.1.1.1.1.1.1.2))
  = (s ← denote_s_get_body chmsg_of_msg ;;
     guess ← resolve predictor
               (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
     v2 ← denote_v2_get_body chmsg_of_msg ;;
     ret (msg_to_fin guess, msg_to_fin v2)).
{ move=> x; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => s; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => guess; rewrite !bind_assoc; apply: bind_cong => //;
    apply: boolp.funext => v2; by case: (x.2) => [] [] [] [] [] [] *. }
transitivity (x ← denote_run_full 11 8 9 10 7 6 seed gc ;;
     (s ← denote_s_get_body chmsg_of_msg ;;
      guess ← resolve predictor
                (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (x.1, s) ;;
      v2 ← denote_v2_get_body chmsg_of_msg ;;
      ret (msg_to_fin guess, msg_to_fin v2))).
{ apply: bind_cong => //; apply: boolp.funext => x; exact: Hcont. }
rewrite -(denote_run_full_fst 11 8 9 10 7 6 seed gc) !bind_assoc.
apply: bind_cong => //; apply: boolp.funext => x.
cbn [bind].
rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => s.
rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => guess.
by rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => v2.
Qed.

(* guess_lossless — the bridged pair code terminates (the existing
   hypothesis, needed to reference [guess_joint_fdist]). *)
Hypothesis guess_lossless :
  psum (distr.mu (Pr_fst (guess_joint_code renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    msg_to_fin))) = 1.

(* guess_full_lossless — the rich experiment terminates with probability one;
   the predictor-losslessness hypothesis for the rich-trace layer (mirrors
   [guess_lossless] on the bridged pair code). *)
Hypothesis guess_full_lossless : psum (distr.mu (Pr_fst guess_full_code)) = 1.

(* guess_sample_fdist — the Infotheo distribution over the rich observed tuple
   (guess, V2, V3, S, V1, U1, U2, U3). *)
Definition guess_sample_fdist := sdistr_to_fdist guess_full_lossless.

(* fin_to_plain — recover the plaintext from a finite-carrier message. *)
Definition fin_to_plain (m : Mfin) : plain AHE := msg_of_chmsg (fin_to_msg m).

(* Projection RVs from the rich carrier, named as in dsdp_entropy_ring; the
   guess and V2 cross to [plain AHE] via [fin_to_plain] (the message-indexing
   bijection). *)
Definition guess : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.1.1.1.
Definition V2 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.1.1.2.
Definition V3 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.1.2.
Definition V1 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.2.
Definition U1 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.2.
Definition U2 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.2.
Definition U3 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.2.

(* S — the leaked output as a random variable, the scalar product of the inputs
   and the secret samples (the entropy-side [S_determined] holds by definition). *)
Definition S : {RV guess_sample_fdist -> plain AHE} :=
  fun t => dsdp_output (V1 t) (U1 t) (U2 t) (U3 t) (V2 t) (V3 t).

(* S_cell — the physical S carrier component (4th projection), the value the
   predictor conditions on; equal to [S] on the run's support by
   [denote_output_termE]. *)
Definition S_cell : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.2.

(* guess_S_determined — the leaked output is the scalar-product spec of the
   inputs and secrets; the fiber-side instance of [S_determined]. *)
Lemma guess_S_determined :
  S = (fun t => dsdp_output (V1 t) (U1 t) (U2 t) (U3 t) (V2 t) (V3 t)).
Proof. by []. Qed.

(* guess_joint_fdist_marginal — the bridged pair distribution is the
   (guess, V2)-marginal of the rich sample distribution. *)
Lemma guess_joint_fdist_marginal :
  guess_joint_fdist guess_lossless
  = fdistmap (fun t : (Mfin * Mfin * Mfin * Mfin * Mfin * Mfin * Mfin * Mfin)%type
              => (t.1.1.1.1.1.1.1, t.1.1.1.1.1.1.2)) guess_sample_fdist.
Proof.
apply: fdist_ext => -[g v2].
rewrite /guess_joint_fdist sdistr_to_fdistE fdistmapE.
Admitted.

End scratch.
