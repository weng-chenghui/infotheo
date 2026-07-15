(* Evidence probe: prove the FULL bob_privacy_V3 end-to-end from clean one-time-pad
   primitives (no E_enc_inde). If this compiles with only boolp axioms, A' is
   de-risked: the headline `H(V3 | BobView) = log m > 0` follows soundly. *)
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

Section probe_bob_privacy_V3.
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

Variables (V2 V3 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_b : {RV P -> Bob.-key Dec msg}.

Let VU3 : {RV P -> msg} := V3 \* U3.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.

Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' Charlie `o VU3R.
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' Bob `o D2.

(* Bob's full real view: his key, his own input V2, the ciphertext he forwards
   (Charlie's R3-masked term), and the ciphertext of his decrypted masked aggregate. *)
Let BobView := [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(* Clean, satisfiable protocol primitives (witnessed by all inputs i.i.d. uniform):
   R3 is Alice's fresh one-time pad; Bob's data is independent of Charlie's input,
   Charlie's weighted input, and R3. *)
Hypothesis pR3_unif : `p_ R3 = fdist_uniform card_msg.
Hypothesis R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Hypothesis bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3].
Hypothesis pV3_unif : `p_ V3 = fdist_uniform card_msg.

(* The masked plaintext u3*v3 + r3 hides V3 (one-time pad). *)
Let VU3R_indep_V3 : P |= VU3R _|_ V3.
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR3_adj : `p_ R3 = fdist_uniform card_TZ.
  by rewrite pR3_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU3 R3 V3 R3_indep_VU3_V3
        (Zp_trunc m).+1 card_TZ pR3_adj).
Qed.

(* Bob's clean data is independent of (V3, the masked term VU3R): push the clean
   cross-party independence through the deterministic map (v3,vu3,r3) |-> (v3,vu3+r3). *)
Let clean_indep_V3_VU3R : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3R].
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ [% Dk_b, V2, D2] [% V3, VU3, R3]
            idfun (fun w => (w.1.1, w.1.2 + w.2)) bob_data_indep_charlie.
by rewrite /comp_RV /VU3R /add_RV /= in H *.
Qed.

(* The joint masked-input independence, assembled by the graphoid mixing rule. *)
Let bob_inputs_indep_V3 : P |= [% Dk_b, V2, D2, VU3R] _|_ V3.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [% Dk_b, V2, D2]) (Y := V3) (Z := unit_RV P) (W := VU3R)).
split.
- by apply cinde_RV_unit; exact: clean_indep_V3_VU3R.
- by apply cinde_RV_unit; rewrite inde_RV_sym; exact: VU3R_indep_V3.
Qed.

(* Rebuild Bob's full view (with both ciphertexts) from the masked inputs. *)
Let bob_view_of (w : ((((Bob.-key Dec msg * msg) * msg) * msg))%type) :=
  (((w.1.1.1, w.1.1.2), E' Charlie w.2), E' Bob w.1.2).

Let BobView_indep_V3 : P |= BobView _|_ V3.
Proof.
have H := inde_RV_comp bob_view_of idfun bob_inputs_indep_V3.
by rewrite /comp_RV /= in H *.
Qed.

(* bob_privacy_V3 — Bob's full view carries log m bits of uncertainty about
   Charlie's input V3 (one-time-pad masking), unconditionally. *)
Theorem bob_privacy_V3 :
  `H(V3 | BobView) = log (m%:R : R) /\ `H(V3 | BobView) > 0.
Proof.
have H_logm : `H(V3 | BobView) = log (m%:R : R).
  by rewrite (inde_cond_entropy BobView_indep_V3) pV3_unif entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

End probe_bob_privacy_V3.
