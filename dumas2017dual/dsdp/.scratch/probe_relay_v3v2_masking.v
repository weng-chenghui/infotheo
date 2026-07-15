(* Probe: is the relay's forwarded secret-bearing ciphertext IT-independent of the
   secret, via one-time-pad masking? Tests the claim my earlier audit got wrong:
   Bob forwards a2 = c3^u3 * E(Charlie,r3), whose plaintext is u3*v3+r3 — masked by
   Alice's fresh r3. If r3 is a one-time pad, a2 hides v3 information-theoretically,
   so bob_privacy_V3 is IT-sound (no IND-CPA needed). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Import BN.
Require Import homomorphic_encryption.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy dsdp_view_independence.
Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section probe_relay_masking.
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Variables (V3 U3 R3 : {RV P -> msg}).
Let VU3 : {RV P -> msg} := V3 \* U3.

(* Alice's mask R3 is a fresh one-time pad: uniform and independent of (V3*U3, V3). *)
Hypothesis R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Hypothesis pR3_unif : `p_ R3 = fdist_uniform card_msg.

(* Tier 1 — the masked plaintext u3*v3 + r3 is independent of V3 (one-time pad). *)
Lemma VU3R_indep_V3 : P |= (VU3 \+ R3) _|_ V3.
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR3_adj : `p_ R3 = fdist_uniform card_TZ.
  by rewrite pR3_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU3 R3 V3 R3_indep_VU3_V3
        (Zp_trunc m).+1 card_TZ pR3_adj).
Qed.

(* Tier 2 — the FORWARDED CIPHERTEXT a2 = E'(Charlie, u3*v3+r3) hides V3.
   This is exactly the claim the earlier audit wrongly called false. *)
Lemma E_charlie_vur3_indep_V3 :
  P |= (E' Charlie `o (VU3 \+ R3)) _|_ V3.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ (VU3 \+ R3) V3 (E' Charlie) idfun
            VU3R_indep_V3.
by rewrite /comp_RV in H *.
Qed.

(* Tier 3 — the privacy headline shape, from BobView _|_ V3 (engine reuse). *)
Variable A : finType.
Variable BobView : {RV P -> A}.
Hypothesis pV3_unif : `p_ V3 = fdist_uniform card_msg.
Hypothesis BobView_indep_V3 : P |= BobView _|_ V3.

Lemma bob_privacy_V3_shape :
  `H(V3 | BobView) = log (m%:R : R) /\ `H(V3 | BobView) > 0.
Proof.
have H_logm : `H(V3 | BobView) = log (m%:R : R).
  by rewrite (inde_cond_entropy BobView_indep_V3) pV3_unif entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

End probe_relay_masking.
