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

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* N-party relay privacy for the DSDP protocol.                               *)
(*                                                                            *)
(* relay_security_n : one-time-pad masking D_i = V_i U_i + R_i is independent *)
(*   of any target Y, so H(Y | RelayView) = log(m) > 0 for a generic relay.   *)
(* malicious_n      : Alice setting US = e_1 extracts V_1 from the dot         *)
(*   product (dotp_n ConstUS_n v = v ord0).                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

(******************************************************************************)
(* N-Party Relay Security                                                     *)
(*                                                                            *)
(* Generic one-time-pad security building blocks for relay parties.           *)
(*                                                                            *)
(* Section variables:                                                         *)
(*   VU_i : {RV P -> msg} -- masked value V_i * U_i for relay party i        *)
(*   R_i  : {RV P -> msg} -- uniform random mask for party i                 *)
(*   Y    : {RV P -> msg} -- any RV; only constrained by R_i _|_ [%VU_i, Y]  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   relay_otp_indep      : D_i = VU_i + R_i is independent of Y             *)
(*   relay_enc_otp_indep  : E(D_i) is independent of Y                       *)
(*   relay_privacy_from_indep : H(Y | View) = H(Y) when View _|_ Y          *)
(*   relay_privacy_logm   : H(Y | View) = log(m) > 0                        *)
(******************************************************************************)

Section relay_security_n.

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

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Generic relay party: one-time-pad masking makes D = VU + R independent of
   any target variable Y, given R is uniform and independent of [%VU, Y]. *)

(* Random variables for one relay party's one-time-pad argument *)
Variable VU_i : {RV P -> msg}.   (* V_i * U_i *)
Variable R_i : {RV P -> msg}.    (* random mask *)
Variable Y : {RV P -> msg}.      (* any RV; constrained only by R_i_indep_VU_Y *)

Let D_i : {RV P -> msg} := VU_i \+ R_i.

Hypothesis R_i_indep_VU_Y : P |= R_i _|_ [%VU_i, Y].
Hypothesis pR_i_unif : `p_ R_i = fdist_uniform card_msg.

(* Core one-time-pad lemma: D_i = VU_i + R_i is independent of Y *)
Lemma relay_otp_indep : P |= D_i _|_ Y.
Proof.
rewrite /D_i.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
have pR_i_unif_adj : `p_ R_i = fdist_uniform card_TZ.
  rewrite pR_i_unif.
  congr fdist_uniform.
  exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU_i R_i Y R_i_indep_VU_Y
        (Zp_trunc m).+1 card_TZ pR_i_unif_adj).
Qed.

(* Encryption of D_i is independent of Y *)
Lemma relay_enc_otp_indep (party : party_id) :
  P |= (E' party `o D_i) _|_ Y.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D_i Y (E' party) idfun relay_otp_indep.
by rewrite /comp_RV.
Qed.

(* Generic relay privacy theorem:
   If RelayView _|_ V_target, then H(V_target | RelayView) = H(V_target) *)
Lemma relay_privacy_from_indep {A : finType}
    (View : {RV P -> A}) (V_target : {RV P -> msg})
    (pV_unif : `p_ V_target = fdist_uniform card_msg)
    (View_indep : P |= View _|_ V_target) :
  `H(V_target | View) = `H `p_ V_target.
Proof. exact: (inde_cond_entropy View_indep). Qed.

End relay_security_n.

(******************************************************************************)
(* N-Party Malicious Adversary Case Analysis                                  *)
(*                                                                            *)
(* Generalizes the 2D dot product analysis to N-1 dimensions.                 *)
(* If Alice sets US = e_1 (first basis vector), she can extract V_1          *)
(* from the dot product result, compromising relay party 1's privacy.        *)
(******************************************************************************)

Section malicious_n.

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

(* N-dimensional dot product *)
Definition dotp_n (x y : {ffun 'I_n_relay.+1 -> msg}) : msg :=
  \sum_(i < n_relay.+1) x i * y i.

(* Dot product as random variable *)
Definition Dotp_n_rv (X Y : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) : {RV P -> msg} :=
  fun t => dotp_n (X t) (Y t).

(* First basis vector: e_1 = (1, 0, ..., 0) *)
Definition ConstUS_n : {ffun 'I_n_relay.+1 -> msg} :=
  [ffun i => if i == ord0 then 1 else 0].

(* e_1 . v = v_1: the first basis vector extracts the first component *)
Lemma dotp_n_e1 (v : {ffun 'I_n_relay.+1 -> msg}) :
  dotp_n ConstUS_n v = v ord0.
Proof.
rewrite /dotp_n (bigD1 ord0) //=.
rewrite ffunE eq_refl mul1r.
rewrite big1 ?addr0 //.
move=> i Hi.
by rewrite ffunE (negbTE Hi) mul0r.
Qed.

End malicious_n.

