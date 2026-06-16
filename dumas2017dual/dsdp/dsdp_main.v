(* DSDP main results — the headline theorems.

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
Require Import entropy_fiber.
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

(* dsdp_experiment — THE one control record: the DSDP corrupted-Alice model
   (palice_sym, the derived hop stream, challenge = Bob's secret name) plus the
   chosen scheme + marshalling. Everything downstream is a projection of this. *)
Definition dsdp_experiment : dsdp_indcpa_experiment :=
  {| exp_card_plaintext  := card_msg ; exp_card_randomness := card_renc ;
     exp_corrupted_party_program := palice_sym ;
     exp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts ;
     exp_challenge_secret := dsdp_v2_name ;
     exp_leak_order := fun combines recvs => combines ++ recvs ;
     exp_enc_scheme := AHE ; exp_rand_carrier := Renc ;
     exp_rand_carrier_card := renc_card ; exp_rand_of_carrier := rand_of_renc ;
     exp_choice_msg_type := t_msg ; exp_choice_cipher_type := t_cipher ;
     exp_choice_msg_of_plain := chmsg_of_msg ; exp_plain_of_choice_msg := msg_of_chmsg ;
     exp_choice_msg_of_plainK := chmsg_of_msgK ;
     exp_choice_cipher_of_cipher := chcipher_of_cipher ;
     exp_cipher_of_choice_cipher := cipher_of_chcipher ;
     exp_choice_cipher_of_cipherK := chcipher_of_cipherK ;
     exp_pub_key_of_party := pkey_of_party ; exp_msg_of_index := msg_of_idx ;
     exp_fallback_rand := rand0 |}.

(* the corrupted-Alice trace of dsdp_experiment has exactly two encryption hops. *)
Example dsdp_experiment_hops : count_obs_hops (corrupted_view dsdp_experiment) = 2.
Proof. by []. Qed.

(* dsdp_alice_view_advantage_le — every adversary's advantage between DSDP's real
   corrupted-Alice game and its all-zero endpoint is at most 2 * epsilon_cpa: the
   generic bound [dsdp_indcpa_secrecy] (any experiment's real-vs-all-zero advantage
   is at most its hop count times epsilon_cpa) at hop count two. [dsdp_experiment]
   is the DSDP instance of such a two-hop experiment, its corrupted-Alice trace
   having exactly two encryption hops ([dsdp_experiment_hops]). *)
Theorem dsdp_alice_view_advantage_le (Adv : dsdp_indcpa_adversary dsdp_experiment) :
  AdvantageE (real_game dsdp_experiment) (zero_game dsdp_experiment) (adv_package Adv)
    <= 2%:R * epsilon_cpa.
Proof.
have H := dsdp_indcpa_secrecy Adv.
by rewrite dsdp_experiment_hops in H.
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

Section dsdp_var_centropy.
(* cloned context of Section dsdp_entropy *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).
Let CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, S].
Let VarRV : {RV P -> (msg * msg)} := [%V2, V3].

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Match the proof term baked into the staying lemmas' fdist_uniform argument so
   the cloned VarRV_uniform hypothesis unifies on application. *)
Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N :=
  dsdp_entropy.card_msg_pair_subproof p_minus_2 q_minus_2.

Hypothesis constraint_holds :
  forall t, dsdp_constraint (CondRV t) (VarRV t).

Hypothesis VarRV_uniform : `p_ VarRV = fdist_uniform card_msg_pair.
Hypothesis VarRV_indep_inputs : P |= [%V1, U1, U2, U3] _|_ VarRV.

Let InputRV : {RV P -> (msg * msg * msg * msg)} := [%V1, U1, U2, U3].

(* dsdp_centropy_uniform — conditioning on Alice's view (V1, U1, U2, U3, S),
   the relay private inputs (V2, V3) retain log m bits of uncertainty. *)
Theorem dsdp_centropy_uniform :
  (forall t, (0 < U3 t)%N) ->
  (forall t, (U3 t < minn p q)%N) ->
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
move=> HU3_pos HU3_lt.
have Hm_pos : (0 < m)%N by rewrite muln_gt0 prime_gt0 // prime_gt0.
apply: (@centropy_jcond_determined_fibers R T P
          (msg * msg)%type (msg * msg * msg * msg)%type msg
          VarRV InputRV S (@dsdp_g p_minus_2 q_minus_2)
          (S_determined constraint_holds) _ m _ Hm_pos).
- move=> [[[v1 u1] u2] u3] s [v2 v3] /= Hcond_pos Hin.
  move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
  move: Ht; rewrite inE => /eqP Ht.
  have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
  have Hu3_pos : (0 < u3)%N by rewrite -HU3t; apply: HU3_pos.
  have Hu3_lt : (u3 < minn p q)%N by rewrite -HU3t; apply: HU3_lt.
  rewrite -dsdp_fiber_eq_abstract in Hin *.
  rewrite (dsdp_fiber_card prime_p prime_q coprime_pq u1 u2 (u3 := u3) v1 s
             Hu3_pos Hu3_lt).
  exact: (Pr_dsdp_sol_uniform prime_p prime_q coprime_pq constraint_holds
            VarRV_uniform VarRV_indep_inputs Hu3_pos Hu3_lt Hcond_pos Hin).
- move=> [[[v1 u1] u2] u3] s Hcond_pos.
  rewrite -dsdp_fiber_eq_abstract.
  move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
  move: Ht; rewrite inE => /eqP Ht.
  have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
  apply: (dsdp_fiber_card prime_p prime_q coprime_pq).
  + by rewrite -HU3t; apply: HU3_pos.
  + by rewrite -HU3t; apply: HU3_lt.
Qed.

End dsdp_var_centropy.

Section dsdp_var_centropy_n.
(* cloned context of Section dsdp_entropy_n *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.

Variable T : finType.
Variable P : R.-fdist T.

Let m_gt0 : (0 < m)%N.
Proof. by rewrite muln_gt0 prime_gt0 // prime_gt0. Qed.

(* Match the proof term baked into dsdp_centropy1_uniform_n's fdist_uniform
   argument so the cloned VarRV_uniform_n hypothesis unifies on application. *)
Let card_ffun_msg : #|{ffun 'I_n_relay.+1 -> msg}| = (m ^ n_relay.+1).-1.+1 :=
  dsdp_entropy.card_ffun_msg_subproof (p_minus_2 := p_minus_2) q_minus_2
    prime_p n_relay.

Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
Let InputT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg})%type.

Variable VarRV : {RV P -> {ffun 'I_n_relay.+1 -> msg}}.
Variable CondRV : {RV P -> CondT_n}.
Variable InputRV : {RV P -> InputT_n}.

Let dsdp_fiber_fn_n (cond : CondT_n) : {set {ffun 'I_n_relay.+1 -> msg}} :=
  let '(v0, u0, u_rel, s) := cond in
  dsdp_fiber_n u_rel (s - u0 * v0).

Let dsdp_proj_input_n (cond : CondT_n) : InputT_n :=
  let '(v0, u0, u_rel, _) := cond in (v0, u0, u_rel).

Hypothesis constraint_fiber_n :
  forall t, VarRV t \in dsdp_fiber_fn_n (CondRV t).

Hypothesis InputRV_proj_n :
  forall t, InputRV t = dsdp_proj_input_n (CondRV t).

Hypothesis VarRV_uniform_n :
  `p_ VarRV = fdist_uniform card_ffun_msg.

Hypothesis VarRV_indep_inputs_n :
  P |= InputRV _|_ VarRV.

Hypothesis joint_eq_input_n :
  forall (cond : CondT_n) (var : {ffun 'I_n_relay.+1 -> msg}),
    var \in dsdp_fiber_fn_n cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, dsdp_proj_input_n cond)].

Let u_of_cond (c : CondT_n) : {ffun 'I_n_relay.+1 -> msg} :=
  let '(_, _, u_rel, _) := c in u_rel.

(* dsdp_centropy_uniform_n — conditioning on the N-party view, the relay private
   inputs retain log (m ^ n_relay) bits of uncertainty. *)
Theorem dsdp_centropy_uniform_n :
  (forall t, (0 < val (u_of_cond (CondRV t) ord_max))%N) ->
  (forall t, (val (u_of_cond (CondRV t) ord_max) < minn p q)%N) ->
  `H(VarRV | CondRV) = log ((m ^ n_relay)%:R : R).
Proof.
move=> HU_pos HU_lt.
rewrite centropy_RVE' /=.
transitivity (\sum_(a : CondT_n)
               `Pr[ CondRV = a ] * log ((m ^ n_relay)%:R : R)).
  apply: eq_bigr => [] [[[v0 u0] u_rel] s] _.
  have [->|Hcond_pos] := eqVneq (`Pr[CondRV = (v0, u0, u_rel, s)]) 0.
    by rewrite !mul0r.
  have Hu_pos: (0 < val (u_rel ord_max))%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have := HU_pos t; rewrite Ht /=.
    by [].
  have Hu_lt: (val (u_rel ord_max) < minn p q)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have := HU_lt t; rewrite Ht /=.
    by [].
  by rewrite (dsdp_centropy1_uniform_n prime_q constraint_fiber_n
                InputRV_proj_n VarRV_uniform_n VarRV_indep_inputs_n
                joint_eq_input_n Hu_pos Hu_lt Hcond_pos).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

End dsdp_var_centropy_n.

Section dsdp_view_independence_main.
(* cloned context of Section dsdp_view_independence *)
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

Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_a := dsdp_entropy.Dk_a inputs.
Let Dk_b := dsdp_entropy.Dk_b inputs.
Let Dk_c := dsdp_entropy.Dk_c inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U1 := dsdp_entropy.U1 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.

Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.
Let S : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

Let E_alice_d3 := E' alice `o D3.
Let E_charlie_v3 := E' charlie `o V3.
Let E_bob_v2 := E' bob `o V2.

Hypothesis E_enc_inde : forall (A B : finType) (p : party_id)
  (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.

Let alice_inputsT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.
Let AliceInputsView := [% Dk_a, V1, U1, U2, U3, R2, R3].
Let alice_view_valuesT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg *
   Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.
Let AliceView : {RV P -> alice_view_valuesT} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* US_compromised_leaks_V2 — a malicious Alice fixing US = (1, 0) reads Bob's
   private input V2 off her view, collapsing its conditional entropy. *)
Theorem US_compromised_leaks_V2 :
  US inputs = ConstUS P p_minus_2 q_minus_2 ->
  ~ `H(V2 | AliceView ) = `H `p_V2.
Proof.
move => H.
have Hinde_bob : P |= [% [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3,
                      E_charlie_v3], V2] _|_ E_bob_v2.
  by apply/inde_RV_sym; apply: E_enc_inde.
have Hinde_charlie : P |= [% [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3], V2]
                       _|_ E_charlie_v3.
  by apply/inde_RV_sym; apply: E_enc_inde.
have Hinde_alice : P |= [% [% Dk_a, S, V1, U1, U2, U3, R2, R3], V2] _|_ E_alice_d3.
  by apply/inde_RV_sym; apply: E_enc_inde.
rewrite (E_enc_ce_contract Hinde_bob card_msg).
rewrite (E_enc_ce_contract Hinde_charlie card_msg).
rewrite (E_enc_ce_contract Hinde_alice card_msg).
pose h := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, s, v1, u1, u2, u3, r2, r3) := o in
   (dk_a, v1, u1, u2, u3, r2, r3, s)).
pose h' := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
  (dk_a, s, v1, u1, u2, u3, r2, r3)).
rewrite -(centropy_RV_contraction _ _ h).
have ->: `H( V2 | [% Dk_a, S, V1, U1, U2, U3, R2, R3, h `o
  [% Dk_a, S, V1, U1, U2, U3, R2, R3]]) =
  `H( V2 | [% Dk_a, S, V1, U1, U2, U3, R2, R3,
  [% Dk_a, V1, U1, U2, U3, R2, R3, S]]).
  by [].
rewrite centropyC (centropy_RV_contraction _ _ h') -/AliceInputsView.
move => H2.
have: `I(V2;[% AliceInputsView, S]) = 0.
  by rewrite mutual_info_RVE H2 subrr.
move/mutual_info_RV0_indep.
(* S_E's imported LHS is the fully-unfolded S; bridge the folded Let S to its
   dot-product form by an explicit equation discharged definitionally. *)
rewrite (_ : S = Dotp2_rv (VS inputs) (US inputs) \+ VU1 inputs);
  last exact: S_E inputs.
rewrite /add_RV //= (ConstUS_discloses_V2 H).
pose z := (fun o : (alice_inputsT * msg) =>
  let '(_, v1, u1, _, _, _, _, v2_r) := o in v2_r - v1 * u1).
move/(inde_RV_comp idfun z).
have -> : z `o [% AliceInputsView, V2 \+ VU1 inputs] = V2.
  rewrite /z /VU1 /comp_RV /add_RV.
  apply: boolp.funext => i //=.
  (* The imported VU1 unfolds to dsdp_entropy.V1/U1 inputs; unfold the cloned
     Lets V1/U1 (exposed only after /= reduces the destructure) so both factors
     are the same ring atom. *)
  rewrite /V1 /U1.
  by ring.
have -> : idfun `o V2 = V2.
  by apply: boolp.funext => i.
apply: neg_self_inde => v2.
rewrite -dist_of_RVE (dsdp_entropy.pV2_unif inputs) fdist_uniformE.
rewrite card_msg invr_eq1 pnatr_eq1.
by apply: contraTneq m_gt1 => ->.
Qed.

End dsdp_view_independence_main.

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

(* ================================================================= *)
(* Corrupted-Alice secrecy: the guessing triangle (indcpa_hopping axis) *)
(* ================================================================= *)

Section dsdp_alice_guess.
(* cloned context of Section dsdp_guess_distribution *)
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

Hypothesis guess_lossless :
  psum (distr.mu (Pr_fst (guess_joint_code renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    msg_to_fin))) = 1.

Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis predictor_locs_disj : fseparate (locs predictor) (protocol_state t_msg).

Variable msg_of_chmsg : t_msg -> plain AHE.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Hypothesis Hmsg_bij : bijective msg_of_idx.
Hypothesis guess_full_lossless :
  psum (distr.mu (Pr_fst (guess_full_code renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    msg_to_fin))) = 1.

Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis seed_wu1 : as_plain (de_val_nth seed 0) = w_u1.
Hypothesis seed_wu2 : as_plain (de_val_nth seed 1) = w_u2.
Hypothesis seed_wu3 : as_plain (de_val_nth seed 2) = w_u3.
Hypothesis seed_wv1 : as_plain (de_val_nth seed 3) = w_v1.

(* zero_game_leak_S instantiated at this section's parameters. *)
Let game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed.

(* real_game — the output-exposing real endpoint game (all-real counterpart). *)
Let real_game : raw_package :=
  real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed.

(* guess_reduction — the IND-CPA distinguisher built from the guessing layer. *)
Let guess_reduction : raw_package :=
  guessing_challenger t_msg t_cipher
    ∘ par (pack predictor) (ID (game_iface_leak_S t_msg t_cipher)).

(* dsdp_alice_guess_ideal_le — the SSProve-side success probability of the
   all-zero guessing experiment is at most 1/card_msg: the connector
   [guess_success_sdistr_eq_fdist] crosses to the Infotheo side, then the fiber
   bound [guess_fdist_success_le]. *)
Lemma dsdp_alice_guess_ideal_le :
  injective (fun v : plain AHE => w_u3 * v) ->
  guess_sdistr_success renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed predictor <= card_msg%:R^-1.
Proof.
move=> Hinj.
rewrite (guess_success_sdistr_eq_fdist msg_to_finK guess_lossless).
exact: (guess_fdist_success_le msg_to_finK guess_lossless card_renc_neq
  predictor_locs_disj chmsg_of_msgK Hmsg_bij guess_full_lossless
  seed_wu1 seed_wu2 seed_wu3 seed_wv1 Hinj).
Qed.

(* guess_sdistr_success_real — the SSProve-side success probability of the
   guessing experiment on the output-exposing real game. *)
Definition guess_sdistr_success_real : R :=
  distr.mu (pkg_advantage.Pr (guessing_experiment predictor real_game)) true.

(* dsdp_alice_guess_advantage_le — the reduction distinguisher's advantage is at
   most [2 * epsilon_cpa]: the output-exposing endpoint games add only the common
   id_Sout_get oracle (no encryption hop), so the Part I IND-CPA bound applies. *)
Lemma dsdp_alice_guess_advantage_le
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (Hore : fseparate (locs predictor)
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (Hoze : fseparate (locs predictor)
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE real_game game guess_reduction <= 2%:R * epsilon_cpa.
Proof.
rewrite /real_game /game.
eapply dsdp_advantage_derived_leak_S.
- exact: chcipher_of_cipherK.
- exact: chmsg_of_msgK.
- exact: guess_reduction_valid.
- exact: predictor_locs_disj.
- exact: Hore.
- exact: Hoze.
Qed.

(* dsdp_alice_guess_real_le — Alice's probability of guessing the challenge
   secret V2 from her cipher view and the leaked scalar-product output S is at
   most 1/card_msg plus twice the IND-CPA advantage: the fiber bound 1/card_msg
   at the all-zero endpoint, plus the 2 * epsilon_cpa cost of moving to the real
   game. *)
Theorem dsdp_alice_guess_real_le
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (Hore : fseparate (locs predictor)
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (Hoze : fseparate (locs predictor)
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party)))
    (Hinj : injective (fun v : plain AHE => w_u3 * v)) :
  guess_sdistr_success_real <= card_msg%:R^-1 + 2%:R * epsilon_cpa.
Proof.
have Hzero : guess_sdistr_success renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    <= card_msg%:R^-1
  by exact: (dsdp_alice_guess_ideal_le Hinj).
apply: (@le_trans _ _ (guess_sdistr_success renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed predictor
    + 2%:R * epsilon_cpa)).
- rewrite addrC -lerBlDr.
  apply: (le_trans (ler_norm _)).
  rewrite guess_advantage_eq.
  exact: (dsdp_alice_guess_advantage_le chcipher_of_cipherK Hore Hoze).
- by rewrite lerD2r.
Qed.

(* Hunp_leak_S — the conditional unpredictability entropy
   [H_unp^C(V_2 | AliceView, S)] for the fixed predictor at the
   output-exposing real game, the negative log of its success
   probability. Cloned context abbreviation; log_id (the algebraic identity
   carrying the probability bound into entropy form) stays in dsdp_guess_fiber. *)
Let Hunp_leak_S : R := (- log guess_sdistr_success_real)%R.

(* dsdp_alice_unpredictability_ge — the entropy lower bound
   [log card_msg - log (1 + 2 * card_msg * epsilon_cpa) <= Hunp_leak_S]:
   the predictor's unpredictability entropy on the output-exposing real game is
   at least the closed-form bound, approaching [log card_msg] as
   [epsilon_cpa -> 0]. *)
Theorem dsdp_alice_unpredictability_ge
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (Hore : fseparate (locs predictor)
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (Hoze : fseparate (locs predictor)
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party)))
    (Hinj : injective (fun v : plain AHE => w_u3 * v))
    (Hpos : (0 < guess_sdistr_success_real)%R)
    (epsilon_cpa_ge0 : (0 <= epsilon_cpa)%R) :
  (log card_msg%:R - log (1 + 2%:R * card_msg%:R * epsilon_cpa)
     <= Hunp_leak_S)%R.
Proof.
rewrite /Hunp_leak_S.
have Hcard0 : (0 < card_msg)%N
  by have [gm _ _] := Hmsg_bij;
     rewrite -[card_msg]card_ord; apply/card_gt0P; exists (gm 0%R).
have Hpr_le :
    (guess_sdistr_success_real <= card_msg%:R^-1 + 2%:R * epsilon_cpa)%R
  by apply: (dsdp_alice_guess_real_le chcipher_of_cipherK Hore Hoze Hinj).
have Hinvm_pos : (0 < card_msg%:R^-1 :> R)%R
  by rewrite invr_gt0 ltr0n Hcard0.
have Hbound_pos : (0 < card_msg%:R^-1 + 2%:R * epsilon_cpa :> R)%R
  by rewrite ltr_pwDl // mulr_ge0 //.
rewrite -(log_id (m := card_msg) (eps := epsilon_cpa) Hcard0 epsilon_cpa_ge0).
by rewrite lerN2 ler_log //.
Qed.

End dsdp_alice_guess.
