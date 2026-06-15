(* SCRATCH development file for the fiber reflection.  THROWAWAY. *)

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

Notation R := SSProve.Crypt.Axioms.R.

Section dev.
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable predictor : predictor_guesser t_msg t_cipher.
Variable Mfin : finType.
Variable msg_to_fin : t_msg -> Mfin.
Variable fin_to_msg : Mfin -> t_msg.
Hypothesis msg_to_finK : cancel msg_to_fin fin_to_msg.
Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis predictor_locs_disj : fseparate (locs predictor) (protocol_state t_msg).

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher) (in custom pack_type at level 2).

Let game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0.

Let gc := all_zero (game_of_trace (dsdp_alice_obs_leak_S card_msg card_renc)).

Let drun := denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0.
Let dhe := denote_he pkey_of_party rand0.

(* ---- per-constructor unfold lemmas for denote_run (all proven earlier) ---- *)
Lemma drun_smsg (e:denv AHE) k : drun e (GC_sample card_msg k) = (x ← sample uniform card_msg ;; drun (push_val (Gplain (msg_of_idx x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run eqxx. Qed.
Lemma drun_srenc (e:denv AHE) k : drun e (GC_sample card_renc k) = (x ← sample uniform card_renc ;; drun (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run (negbTE card_renc_neq) eqxx. Qed.
Lemma drun_put (e:denv AHE) t k : drun e (GC_put t k) = (#put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_puto (e:denv AHE) t k : drun e (GC_put_output t k) = (#put (S_output_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_let (e:denv AHE) t k : drun e (GC_let t k) = drun (push_val (dhe e t) e) k.
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_ench (e:denv AHE) pk secret k : drun e (GC_enc_hop pk secret k) = (ir ← sample uniform card_renc ;; drun (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk)) (as_plain (dhe e secret)) (rand_of_renc (sample_to_renc renc_card ir)))) e) k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_ret (e:denv AHE) outs : drun e (GC_ret outs) = ret ([seq chcipher_of_cipher (as_cipher (dhe e o)) | o <- outs] : cipher_list t_cipher).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.

Lemma gc_eq : gc = GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc (GC_sample card_renc (GC_put (HE_var 5) (GC_enc_hop 1 (HE_const 0) (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 5)) (HE_enc 1 (HE_var 4) 1)) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 4)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output (HE_add (HE_sub (HE_sub (HE_dec 0 (HE_var 10)) (HE_var 6)) (HE_var 4)) (HE_mul (HE_var 10) (HE_var 10))) (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))))).
Proof. by rewrite /gc; vm_compute. Qed.

(* denote_run_distr — the explicit Pr_code reflection of denote_run: samples
   become dlet over uniforms threading the env; puts update the heap. *)
Fixpoint denote_run_distr (e : denv AHE) (gc : game_code) (h : heap) {struct gc}
  : distr.distr R (cipher_list t_cipher * heap)%type :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        distr.dlet (fun x => denote_run_distr (push_val (Gplain (msg_of_idx x)) e) k h) (projT2 (uniform card_msg))
      else if n == card_renc then
        distr.dlet (fun x => denote_run_distr (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k h) (projT2 (uniform card_renc))
      else
        distr.dlet (fun x : Arit (uniform n) => denote_run_distr e k h) (projT2 (uniform n))
  | GC_put t k =>
      denote_run_distr e k (set_heap h (V_2_cell t_msg) (Some (chmsg_of_msg (as_plain (dhe e t)))))
  | GC_put_output t k =>
      denote_run_distr e k (set_heap h (S_output_cell t_msg) (Some (chmsg_of_msg (as_plain (dhe e t)))))
  | GC_let t k =>
      denote_run_distr (push_val (dhe e t) e) k h
  | GC_enc_hop pk secret k =>
      distr.dlet (fun ir => denote_run_distr (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk)) (as_plain (dhe e secret)) (rand_of_renc (sample_to_renc renc_card ir)))) e) k h) (projT2 (uniform card_renc))
  | GC_ret outs =>
      distr.dunit (([seq chcipher_of_cipher (as_cipher (dhe e o)) | o <- outs] : cipher_list t_cipher), h)
  end.

Lemma denote_run_distrE (gc0 : game_code) (e : denv AHE) (h : heap) :
  Pr_code (drun e gc0) h = denote_run_distr e gc0 h.
Proof.
elim: gc0 e h => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e h /=.
- rewrite /drun /denote_run -/denote_run.
  case: (n == card_msg).
  + rewrite Pr_code_sample; apply: eq_dlet => x; exact: IH.
  + case: (n == card_renc); rewrite Pr_code_sample; apply: eq_dlet => x; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_put; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_put; exact: IH.
- rewrite /drun /denote_run -/denote_run; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_sample; apply: eq_dlet => ir; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_ret //.
Qed.

End dev.
