(* Probe: sound IT-secrecy of Alice's input V1 from corrupted Bob / Charlie.
   V1 occurs in no protocol message, so each relay's full real view is a
   deterministic function of inputs independent of V1; inde_RV_comp pushes the
   independence through, and inde_cond_entropy gives H(V1 | View) = log m > 0. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Import BN.
Require Import homomorphic_encryption.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.
Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section dsdp_relay_secrecy_v1.
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

Variables (V1 V2 V3 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_b : {RV P -> Bob.-key Dec msg}.
Variable Dk_c : {RV P -> Charlie.-key Dec msg}.

Let VU3R : {RV P -> msg} := V3 \* U3 \+ R3.
Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.
Let D3 : {RV P -> msg} := VU3R \+ D2.

Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' Charlie `o VU3R.
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' Bob `o D2.
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' Charlie `o D3.

(* Bob's full real view: his key, own input V2, the ciphertext he forwards
   (Charlie's masked term) and the ciphertext of his decrypted masked aggregate.
   No component is a function of V1. *)
Let BobView := [% Dk_b, V2, E_charlie_vur3, E_bob_d2].
(* Charlie's full real view: his key, own input V3, the encrypted aggregate. *)
Let CharlieView := [% Dk_c, V3, E_charlie_d3].

Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.
Hypothesis bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1.
Hypothesis charlie_inputs_indep_V1 : P |= [% Dk_c, V3, D3] _|_ V1.

Let bob_view_recover (w : (((Bob.-key Dec msg * msg) * msg) * msg)%type) :=
  (((w.1.1.1, w.1.1.2), E' Charlie w.1.2), E' Bob w.2).
Let charlie_view_recover (w : ((Charlie.-key Dec msg * msg) * msg)%type) :=
  ((w.1.1, w.1.2), E' Charlie w.2).

Lemma BobView_indep_V1 : P |= BobView _|_ V1.
Proof.
have H := inde_RV_comp bob_view_recover idfun bob_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

Lemma CharlieView_indep_V1 : P |= CharlieView _|_ V1.
Proof.
have H := inde_RV_comp charlie_view_recover idfun charlie_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

Theorem bob_privacy_V1 :
  `H(V1 | BobView) = log (m%:R : R) /\ `H(V1 | BobView) > 0.
Proof.
have H_logm : `H(V1 | BobView) = log (m%:R : R).
  by rewrite (inde_cond_entropy BobView_indep_V1) pV1_unif entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

Theorem charlie_privacy_V1 :
  `H(V1 | CharlieView) = log (m%:R : R) /\ `H(V1 | CharlieView) > 0.
Proof.
have H_logm : `H(V1 | CharlieView) = log (m%:R : R).
  by rewrite (inde_cond_entropy CharlieView_indep_V1) pV1_unif entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

End dsdp_relay_secrecy_v1.
