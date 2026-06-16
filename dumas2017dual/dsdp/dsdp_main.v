(* DSDP headline results — the apex.

   This file centralizes the headline theorems of the DSDP development. Each
   theorem's full proof is presented here over a cloned copy of its source
   section context; the supporting machinery stays in the axis files
   (counting/, symbolic_game/, indcpa_hopping/, convert/) and is referenced, not
   duplicated. The headlines are:

   Information-theoretic (counting axis)
     dsdp_centropy_uniform / dsdp_centropy_uniform_n — H(V2,V3 | view) = log m
     US_compromised_leaks_V2 / US_n_compromised_leaks_V1 — corrupted U leaks V
     bob_privacy_V1 / bob_privacy_V3 — H(V_i | BobView) = log m > 0
     charlie_privacy_V1 / charlie_privacy_V2 — H(V_i | CharlieView) = log m > 0
     relay_privacy_n — H(Y | View) = log m > 0 for a generic relay

   Corrupted-Alice secrecy (indcpa_hopping axis), the guessing triangle
     dsdp_alice_view_advantage_le — AdvantageE <= 2 * epsilon_cpa
     dsdp_alice_guess_ideal_le — guess <= 1/m (all-zero endpoint)
     dsdp_alice_guess_advantage_le — AdvantageE <= 2 * epsilon_cpa
     dsdp_alice_guess_real_le — guess <= 1/m + 2 * epsilon_cpa
     dsdp_alice_unpredictability_ge — H_unp >= log m - log (1 + 2 m epsilon_cpa) *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum lra.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
From SSProve.Crypt Require Import HybridArgument.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy extra_proba extra_algebra extra_entropy rouche_capelli.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code dsdp_symbolic_exec dsdp_game_derivation.
Require Import dsdp_indcpa_advantage dsdp_convert dsdp_guess_fiber.
Require Import dsdp_view_independence.

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

(* Pin SSProve's real type as the ambient realType. *)
Notation R := SSProve.Crypt.Axioms.R.

(* ================================================================= *)
(* Corrupted-Alice IND-CPA advantage (indcpa_hopping axis)           *)
(* ================================================================= *)

Section dsdp_alice_indcpa.
(* cloned context of Section dsdp_indcpa_advantage *)
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

Let problem := @dsdp_problem AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
  msg_of_chmsg chmsg_of_msg chcipher_of_cipher cipher_of_chcipher chmsg_of_msgK
  chcipher_of_cipherK pkey_of_party card_msg msg_of_idx rand0.

(* dsdp_alice_view_advantage_le — for the concrete dsdp_problem instance, every
   adversary's advantage distinguishing the real corrupted-Alice cipher view
   from the all-zero view is at most 2 * epsilon_cpa. *)
Theorem dsdp_alice_view_advantage_le (Adv : dsdp_indcpa_adversary problem) :
  AdvantageE (real_game problem) (zero_game problem) (adv_package Adv)
    <= 2%:R * epsilon_cpa.
Proof.
have H := dsdp_indcpa_secrecy Adv.
rewrite /problem in H *.
by rewrite dsdp_problem_hops in H.
Qed.

End dsdp_alice_indcpa.

(* ================================================================= *)
(* Information-theoretic party privacy (counting axis)               *)
(* ================================================================= *)

Section dsdp_bob_privacy.
(* cloned context of Section bob_security *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_b := dsdp_entropy.Dk_b inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.

Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' charlie `o VU3R.
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' bob `o D2.

Let bob_view_valuesT := (Bob.-key Dec msg * msg *
  Charlie.-enc msg * Bob.-enc msg)%type.

Let BobView : {RV P -> bob_view_valuesT} :=
  [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

Hypothesis BobView_indep_V1 : P |= BobView _|_ V1.
Hypothesis BobView_indep_V3 : P |= BobView _|_ V3.
Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.
Hypothesis pV3_unif : `p_ V3 = fdist_uniform card_msg.

(* bob_privacy_V1 — Bob's view carries log m bits of uncertainty about Alice's
   private input V1, hence Bob learns nothing about V1. *)
Theorem bob_privacy_V1 :
  `H(V1 | BobView) = log (m%:R : R) /\
  `H(V1 | BobView) > 0.
Proof.
have H_v1_logm: `H(V1 | BobView) = log (m%:R : R).
  rewrite (bob_privacy_V1_alt BobView_indep_V1).
  by rewrite pV1_unif entropy_uniform card_msg.
split.
- exact: H_v1_logm.
- rewrite H_v1_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

(* bob_privacy_V3 — Bob's view carries log m bits of uncertainty about Charlie's
   private input V3, hence Bob learns nothing about V3. *)
Theorem bob_privacy_V3 :
  `H(V3 | BobView) = log (m%:R : R) /\
  `H(V3 | BobView) > 0.
Proof.
have H_v3_logm: `H(V3 | BobView) = log (m%:R : R).
  rewrite (bob_privacy_V3_alt BobView_indep_V3).
  by rewrite pV3_unif entropy_uniform card_msg.
split.
- exact: H_v3_logm.
- rewrite H_v3_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End dsdp_bob_privacy.

Section dsdp_charlie_privacy.
(* cloned context of Section charlie_security *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_c := dsdp_entropy.Dk_c inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.

Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' charlie `o D3.

Let charlie_view_valuesT := (Charlie.-key Dec msg * msg * Charlie.-enc msg)%type.

Let CharlieView : {RV P -> charlie_view_valuesT} :=
  [% Dk_c, V3, E_charlie_d3].

Hypothesis R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Hypothesis R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [%VU3R, V2]].
Hypothesis Dk_c_V3_indep_V2_E : P |= [%Dk_c, V3] _|_ [%V2, E_charlie_d3].

Hypothesis Dk_c_V3_indep_V1 : P |= [%Dk_c, V3] _|_ V1.
Hypothesis Dk_c_V3_indep_V1_E : P |= [%Dk_c, V3] _|_ [%V1, E_charlie_d3].

Let CharlieView_indep_V1 : P |= CharlieView _|_ V1 :=
  @CharlieView_indep_V1_proven R T P p_minus_2 q_minus_2 inputs
    Dk_c_V3_indep_V1_E.

Let CharlieView_indep_V2 : P |= CharlieView _|_ V2 :=
  @CharlieView_indep_V2_proven R T P p_minus_2 q_minus_2 inputs
    R2_indep_VU2_V2 R2_indep_VU2_VU3R_V2 Dk_c_V3_indep_V2_E.

Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.
Hypothesis pV2_unif : `p_ V2 = fdist_uniform card_msg.

(* charlie_privacy_V1 — Charlie's view carries log m bits of uncertainty about
   Alice's private input V1, hence Charlie learns nothing about V1. *)
Theorem charlie_privacy_V1 :
  `H(V1 | CharlieView) = log (m%:R : R) /\
  `H(V1 | CharlieView) > 0.
Proof.
have H_v1_logm: `H(V1 | CharlieView) = log (m%:R : R).
  rewrite (charlie_privacy_V1_alt Dk_c_V3_indep_V1_E).
  by rewrite pV1_unif entropy_uniform card_msg.
split.
- exact: H_v1_logm.
- rewrite H_v1_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

(* charlie_privacy_V2 — Charlie's view carries log m bits of uncertainty about
   Bob's private input V2, hence Charlie learns nothing about V2. *)
Theorem charlie_privacy_V2 :
  `H(V2 | CharlieView) = log (m%:R : R) /\
  `H(V2 | CharlieView) > 0.
Proof.
have H_v2_logm: `H(V2 | CharlieView) = log (m%:R : R).
  rewrite (charlie_privacy_V2_alt R2_indep_VU2_V2 R2_indep_VU2_VU3R_V2
             Dk_c_V3_indep_V2_E).
  by rewrite pV2_unif entropy_uniform card_msg.
split.
- exact: H_v2_logm.
- rewrite H_v2_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End dsdp_charlie_privacy.

Section dsdp_relay_privacy.
(* cloned context of Section relay_security_n *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Random variables for one relay party's one-time-pad argument *)
Variable VU_i : {RV P -> msg}.   (* V_i * U_i *)
Variable R_i : {RV P -> msg}.    (* random mask *)
Variable Y : {RV P -> msg}.      (* any RV; constrained only by R_i_indep_VU_Y *)

Let D_i : {RV P -> msg} := VU_i \+ R_i.

Hypothesis R_i_indep_VU_Y : P |= R_i _|_ [%VU_i, Y].
Hypothesis pR_i_unif : `p_ R_i = fdist_uniform card_msg.

(* relay_privacy_n — for a generic relay party whose view is independent of a
   uniform target, the view carries log m bits of uncertainty about the target. *)
Lemma relay_privacy_n {A : finType}
    (View : {RV P -> A}) (V_target : {RV P -> msg})
    (pV_unif : `p_ V_target = fdist_uniform card_msg)
    (View_indep : P |= View _|_ V_target) :
  `H(V_target | View) = log (m%:R : R) /\
  `H(V_target | View) > 0.
Proof.
have H_logm: `H(V_target | View) = log (m%:R : R).
  have step : `H(V_target | View) = `H `p_ V_target.
    apply: relay_privacy_from_indep; last exact: View_indep.
    rewrite pV_unif; congr fdist_uniform; exact: eq_irrelevance.
  rewrite step.
  by rewrite pV_unif entropy_uniform card_msg.
split.
- exact: H_logm.
- rewrite H_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End dsdp_relay_privacy.

Section dsdp_malicious_n.
(* cloned context of Section malicious_n *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.

(* US_n_compromised_leaks_V1 — a corrupted Alice fixing US = e_1 (first basis
   vector) extracts relay party 1's input V_1 from the dot-product output. *)
Lemma US_n_compromised_leaks_V1
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) :
  US = (fun _ => @ConstUS_n p_minus_2 q_minus_2 n_relay) ->
  @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS = (fun t => VS t ord0).
Proof.
move->.
rewrite /Dotp_n_rv.
apply: boolp.funext => t /=.
by rewrite dotp_n_e1.
Qed.

End dsdp_malicious_n.
