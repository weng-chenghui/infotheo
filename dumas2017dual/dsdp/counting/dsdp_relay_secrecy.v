From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import boolp.
Require Import realType_ext realType_ln ssr_ext ssralg_ext fdist proba.
Require Import entropy graphoid.
Require Import spp_proba extra_proba extra_entropy extra_algebra.
Require Import homomorphic_encryption.

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
(* Corrupted-relay secrecy in the DSDP protocol: the two relays' full real    *)
(* views and the inputs those views leave uncertain, stated over abstract     *)
(* random variables and the laws they are assumed to obey.                    *)
(*                                                                            *)
(* These are counting-axis bounds, so they hold against a relay of any        *)
(* running time.  Each view is a deterministic function of data independent   *)
(* of the input at issue, and that independence comes from a one-time pad     *)
(* Alice draws and strips, so the ciphertexts in the view may be read as      *)
(* opaque labels and the bound still stands.  The relays are therefore priced *)
(* here and nowhere else; the computational assumptions of the hopping axis   *)
(* price a corrupted Alice.                                                   *)
(*                                                                            *)
(* BobView : Bob's key, his own input V2, the Charlie-key combine Alice sends *)
(*   him, and the Bob-key combine he decrypts.                                *)
(* CharlieView : Charlie's key, his own input V3, and the aggregate           *)
(*   ciphertext Bob forwards to him.                                          *)
(* bob_privacy_V1, charlie_privacy_V1 : H(V1 | view) = log m and it is        *)
(*   positive, for either relay's view: Alice's input occurs in no message.   *)
(* bob_privacy_V3 : H(V3 | BobView) = log m and it is positive, by Alice's    *)
(*   mask R3, which Bob never sees.                                           *)
(* charlie_privacy_V2 : H(V2 | CharlieView) = log m and it is positive, by    *)
(*   Alice's mask R2, which Charlie never sees.                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Section dsdp_relay_secrecy.
(* Alice's input V1 occurs in no protocol message; each corrupted relay's full
   real view is a deterministic function of inputs independent of V1, so its
   conditional entropy about V1 stays at log m. *)
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

(* The plaintext count, as a named term rather than an anonymous subproof, so
   that the uniform hypotheses below survive section discharge in a shape a
   caller can supply. *)
Let card_msg : #|msg| = m := card_Zp_pq p_minus_2 q_minus_2.

Variables (V1 V2 V3 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_b : {RV P -> Bob.-key Dec msg}.
Variable Dk_c : {RV P -> Charlie.-key Dec msg}.

(* Bob's input under Alice's query weight U2.  The weights U1, U2, U3 are
   Alice's, so this is the one place Bob's secret meets a factor he does not
   choose.  It reaches the aggregate only through D2. *)
Let VU2 : {RV P -> msg} := V2 \* U2.

(* Charlie's input under Alice's query weight U3, reaching the aggregate only
   through VU3R. *)
Let VU3 : {RV P -> msg} := V3 \* U3.

(* Charlie's weighted input under Alice's mask R3, the plaintext of the second
   combine Alice sends to Bob.  R3 is Alice's, drawn and stripped by palice of
   dsdp_program.v, so it lies outside Bob's view.  That is what makes
   bob_privacy_V3 unconditional: Bob's independence from V3 rests on a mask he
   never sees, not on the encryption being hard to break. *)
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's weighted input under Alice's mask R2, the plaintext Bob decrypts from
   Alice's first combine.  R2 lies outside Charlie's view, which is what makes
   charlie_privacy_V2 unconditional in the same way. *)
Let D2 : {RV P -> msg} := VU2 \+ R2.

(* The aggregate Charlie decrypts, carrying both relay inputs under Alice's two
   masks.  Alice recovers the output by stripping R2 and R3 from it. *)
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* Alice's second combine, encrypted under Charlie's key and sent to Bob.  It
   sits in Bob's view as opaque data, and the R3 mask inside it keeps V3
   independent of that view on its own. *)
Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' Charlie `o VU3R.

(* Alice's first combine, encrypted under Bob's key.  Bob holds the matching
   decryption key, and what he recovers is D2, already masked by R2. *)
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' Bob `o D2.

(* The aggregate Bob sends on to Charlie, encrypted under Charlie's key.  It
   travels towards Charlie, not away from him: pcharlie of dsdp_program.v
   decrypts it and answers Alice under Alice's key instead. *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' Charlie `o D3.

(* Bob's full real view: his key, his own input V2, the Charlie-key combine
   Alice sends him and which he can only multiply into, and the Bob-key
   combine he decrypts to D2. *)
Definition BobView := [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(* Charlie's full real view: his key, his own input V3, and the aggregate
   ciphertext he receives from Bob. *)
Definition CharlieView := [% Dk_c, V3, E_charlie_d3].

Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.
Hypothesis bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1.
Hypothesis charlie_inputs_indep_V1 : P |= [% Dk_c, V3, D3] _|_ V1.

Let bob_view_of (w : (((Bob.-key Dec msg * msg) * msg) * msg)%type) :=
  (((w.1.1.1, w.1.1.2), E' Charlie w.1.2), E' Bob w.2).
Let charlie_view_of (w : ((Charlie.-key Dec msg * msg) * msg)%type) :=
  ((w.1.1, w.1.2), E' Charlie w.2).

(* BobView_indep_V1 — Bob's view is independent of Alice's input V1. *)
Lemma BobView_indep_V1 : P |= BobView _|_ V1.
Proof.
have H := inde_RV_comp bob_view_of idfun bob_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

(* CharlieView_indep_V1 — Charlie's view is independent of Alice's input
   V1. *)
Lemma CharlieView_indep_V1 : P |= CharlieView _|_ V1.
Proof.
have H := inde_RV_comp charlie_view_of idfun charlie_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

(* bob_privacy_V1 — Bob's view carries log m bits of uncertainty about Alice's
   input V1, hence a corrupted Bob learns nothing about V1.  [3-party] *)
Theorem bob_privacy_V1 :
  `H(V1 | BobView) = log (m%:R : R) /\ `H(V1 | BobView) > 0.
Proof.
have H_logm : `H(V1 | BobView) = log (m%:R : R).
  rewrite (inde_cond_entropy BobView_indep_V1) pV1_unif.
  by rewrite entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

(* charlie_privacy_V1 — Charlie's view carries log m bits of uncertainty about
   Alice's input V1, hence a corrupted Charlie learns nothing about V1.
   [3-party] *)
Theorem charlie_privacy_V1 :
  `H(V1 | CharlieView) = log (m%:R : R) /\ `H(V1 | CharlieView) > 0.
Proof.
have H_logm : `H(V1 | CharlieView) = log (m%:R : R).
  rewrite (inde_cond_entropy CharlieView_indep_V1) pV1_unif.
  by rewrite entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

(* The Charlie-ciphertext Bob forwards carries plaintext V3 * U3 + R3, masked by
   Alice's fresh one-time pad R3, so Bob's full view is independent of V3. *)
Hypothesis pV3_unif : `p_ V3 = fdist_uniform card_msg.
Hypothesis pR3_unif : `p_ R3 = fdist_uniform card_msg.
Hypothesis R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Hypothesis bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3].

(* The masked plaintext V3 * U3 + R3 is independent of V3 (one-time pad). *)
Let VU3R_indep_V3 : P |= VU3R _|_ V3.
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR3_adj : `p_ R3 = fdist_uniform card_TZ.
  by rewrite pR3_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU3 R3 V3 R3_indep_VU3_V3
        (Zp_trunc m).+1 card_TZ pR3_adj).
Qed.

(* Bob's clean data is independent of (V3, the masked term VU3R): push the clean
   cross-party independence through (v3, vu3, r3) |-> (v3, vu3 + r3). *)
Let clean_indep_V3_VU3R : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3R].
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ [% Dk_b, V2, D2] [% V3, VU3, R3]
            idfun (fun w => (w.1.1, w.1.2 + w.2)) bob_data_indep_charlie.
by rewrite /comp_RV /VU3R /add_RV /= in H *.
Qed.

(* The joint masked-input independence, assembled by the graphoid mixing rule.*)
Let bob_inputs_indep_V3 : P |= [% Dk_b, V2, D2, VU3R] _|_ V3.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [% Dk_b, V2, D2]) (Y := V3) (Z := unit_RV P)
         (W := VU3R)).
split.
  by apply cinde_RV_unit; exact: clean_indep_V3_VU3R.
by apply cinde_RV_unit; rewrite inde_RV_sym; exact: VU3R_indep_V3.
Qed.

(* BobView_indep_V3 — Bob's full view is independent of Charlie's input V3. *)
Let BobView_indep_V3 : P |= BobView _|_ V3.
Proof.
have H := inde_RV_comp
  (fun w : (((Bob.-key Dec msg * msg) * msg) * msg)%type =>
     (((w.1.1.1, w.1.1.2), E' Charlie w.2), E' Bob w.1.2))
  idfun bob_inputs_indep_V3.
by rewrite /comp_RV /= in H *.
Qed.

(* bob_privacy_V3 — Bob's view carries log m bits of uncertainty about
   Charlie's input V3, hence a corrupted Bob learns nothing about V3.
   [3-party] *)
Theorem bob_privacy_V3 :
  `H(V3 | BobView) = log (m%:R : R) /\ `H(V3 | BobView) > 0.
Proof.
have H_logm : `H(V3 | BobView) = log (m%:R : R).
  rewrite (inde_cond_entropy BobView_indep_V3) pV3_unif.
  by rewrite entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

(* Charlie's decrypted aggregate D3 carries V2 * U2 masked by Alice's fresh pad
   R2, so the ciphertext Charlie returns to Alice is independent of V2. *)
Hypothesis pV2_unif : `p_ V2 = fdist_uniform card_msg.
Hypothesis pR2_unif : `p_ R2 = fdist_uniform card_msg.
Hypothesis R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Hypothesis R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [%VU3R, V2]].
Hypothesis Dk_c_V3_indep_V2_E : P |= [%Dk_c, V3] _|_ [%V2, E_charlie_d3].

(* D2 = V2 * U2 + R2 is independent of (VU3R, V2) (one-time pad). *)
Let D2_indep_VU3R_V2 : P |= D2 _|_ [%VU3R, V2].
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR2_adj : `p_ R2 = fdist_uniform card_TZ.
  by rewrite pR2_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@lemma_3_5' R T _ msg P VU2 R2 [%VU3R, V2] R2_indep_VU2_VU3R_V2
        (Zp_trunc m).+1 card_TZ pR2_adj).
Qed.

(* D3 = VU3R + D2 is independent of V2: D2 is a uniform mask independent of
   (VU3R, V2), so VU3R + D2 hides V2. *)
Let D3_indep_V2 : P |= D3 _|_ V2.
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR2_adj : `p_ R2 = fdist_uniform card_TZ.
  by rewrite pR2_unif; congr fdist_uniform; exact: eq_irrelevance.
have pD2_unif : `p_ D2 = fdist_uniform card_TZ.
  have R2_VU2_indep : P |= R2 _|_ VU2.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/R2_indep_VU2_V2.
  have VU2_R2_indep : P |= VU2 _|_ R2 by rewrite inde_RV_sym.
  exact: (add_RV_unif VU2 R2 card_TZ pR2_adj VU2_R2_indep).
exact: (@lemma_3_5' R T msg msg P VU3R D2 V2 D2_indep_VU3R_V2
        (Zp_trunc m).+1 card_TZ pD2_unif).
Qed.

(* The ciphertext E'(Charlie, D3) hides V2 (deterministic image of D3). *)
Let E_charlie_d3_indep_V2 : P |= E_charlie_d3 _|_ V2.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D3 V2 (E' Charlie) idfun D3_indep_V2.
by rewrite /E_charlie_d3 /comp_RV.
Qed.

(* CharlieView_indep_V2 — Charlie's full view is independent of Bob's input
   V2. *)
Let CharlieView_indep_V2 : P |= CharlieView _|_ V2.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [%Dk_c, V3]) (Y := V2) (Z := unit_RV P)
         (W := E_charlie_d3)).
split.
  by apply cinde_RV_unit; exact: Dk_c_V3_indep_V2_E.
by apply cinde_RV_unit; rewrite inde_RV_sym; exact: E_charlie_d3_indep_V2.
Qed.

(* charlie_privacy_V2 — Charlie's view carries log m bits of uncertainty about
   Bob's input V2, hence a corrupted Charlie learns nothing about V2.
   [3-party] *)
Theorem charlie_privacy_V2 :
  `H(V2 | CharlieView) = log (m%:R : R) /\ `H(V2 | CharlieView) > 0.
Proof.
have H_logm : `H(V2 | CharlieView) = log (m%:R : R).
  rewrite (inde_cond_entropy CharlieView_indep_V2) pV2_unif.
  by rewrite entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

End dsdp_relay_secrecy.
