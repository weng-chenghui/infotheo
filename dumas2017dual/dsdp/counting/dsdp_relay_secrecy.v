From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import boolp.
Require Import realType_ext realType_ln ssr_ext ssralg_ext fdist proba.
Require Import entropy graphoid.
Require Import spp_proba extra_proba extra_entropy extra_algebra.
Require Import homomorphic_encryption.
Require Import dsdp_random_inputs.

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
(* views and the inputs those views leave uncertain, at one value of          *)
(* dsdp_random_inputs.  The record's eleven random inputs are the run, its    *)
(* uniformity fields and its seven derived laws are what the views are        *)
(* measured against, so a bound here holds at every run the record inhabits,  *)
(* the uniform one of uniform_inputs included.                                *)
(*                                                                            *)
(* These are counting-axis bounds, so they hold against a relay of any        *)
(* running time.  Each view is a deterministic function of data independent   *)
(* of the input at issue, and that independence comes from a one-time pad     *)
(* Alice draws and strips, so the ciphertexts in the view may be read as      *)
(* opaque labels and the bound still stands.  The relays are bounded here     *)
(* and nowhere else, and the computational assumptions of the hopping axis    *)
(* bound a corrupted Alice.  Alice draws the masks R2 and R3 and strips them  *)
(* again in palice of dsdp_program.v.                                         *)
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
Variables (p q : nat).
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.
Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.

(* One 3-party run at this modulus, on the counting side: the sample space,
   the law, the eleven random inputs, and the independence and uniformity
   facts the two views below are measured against. *)
Variable I : dsdp_random_inputs R p_gt1 q_gt1.

Local Notation T := (sampleT I).
Local Notation P := (sample_fdist I).
Local Notation V1 := (V1 I).
Local Notation V2 := (V2 I).
Local Notation V3 := (V3 I).
Local Notation U2 := (U2 I).
Local Notation U3 := (U3 I).
Local Notation R2 := (R2 I).
Local Notation R3 := (R3 I).
Local Notation Dk_b := (Dk_b I).
Local Notation Dk_c := (Dk_c I).

(* The count #|msg| = m of the plaintext ring, the value form the entropy
   statements below read their log at. *)
Let card_msg : #|msg| = m := card_Zp_pq p_gt1 q_gt1.

(* The same count in the successor form fdist_uniform takes.  The record's
   five uniformity fields are stated at this proof. *)
Let card_msg_prednK : #|msg| = m.-1.+1 := card_Zp_pq_prednK p_gt1 q_gt1.

(* The modulus is above one, which is what makes log m positive. *)
Let m_gt1 : (1 < m)%N := pq_gt1 p_gt1 q_gt1.

(* Bob's input under Alice's query weight U2.  It reaches the aggregate only
   through D2. *)
Let VU2 : {RV P -> msg} := V2 \* U2.

(* Charlie's input under Alice's query weight U3, reaching the aggregate only
   through VU3R. *)
Let VU3 : {RV P -> msg} := V3 \* U3.

(* Charlie's weighted input under Alice's mask R3, the plaintext of the
   second combine Alice sends to Bob.  R3 stays with Alice, so
   bob_privacy_V3 rests on a mask outside Bob's view rather than on the
   encryption. *)
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's weighted input under Alice's mask R2, the plaintext Bob decrypts
   from Alice's first combine.  R2 stays with Alice, so it lies outside
   Charlie's view. *)
Let D2 : {RV P -> msg} := VU2 \+ R2.

(* The aggregate Charlie decrypts, carrying both relay inputs under Alice's two
   masks.  Alice recovers the output by stripping R2 and R3 from it. *)
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* Alice's second combine, encrypted under Charlie's key and sent to Bob.
   The mask R3 inside it keeps V3 independent of Bob's view. *)
Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' Charlie `o VU3R.

(* Alice's first combine, encrypted under Bob's key.  Bob holds the matching
   decryption key, and what he recovers is D2, already masked by R2. *)
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' Bob `o D2.

(* The aggregate Bob forwards to Charlie, encrypted under Charlie's key.
   Charlie decrypts it and answers Alice under Alice's key. *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' Charlie `o D3.

(* Bob's full real view: his key, V2, the Charlie-key combine and the Bob-key
   combine.  He multiplies into the first combine and decrypts the second to
   D2. *)
Definition BobView := [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(* Charlie's full real view: his key, his own input V3, and the aggregate
   ciphertext he receives from Bob. *)
Definition CharlieView := [% Dk_c, V3, E_charlie_d3].

Let pV1_unif : `p_ V1 = fdist_uniform card_msg_prednK :=
  dsdp_random_inputs.pV1_unif I.
Let bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1 :=
  dsdp_random_inputs.bob_inputs_indep_V1 I.
Let charlie_inputs_indep_V1 : P |= [% Dk_c, V3, D3] _|_ V1 :=
  dsdp_random_inputs.charlie_inputs_indep_V1 I.

Let bob_view_of (w : (((Bob.-key Dec msg * msg) * msg) * msg)%type) :=
  (((w.1.1.1, w.1.1.2), E' Charlie w.1.2), E' Bob w.2).
Let charlie_view_of (w : ((Charlie.-key Dec msg * msg) * msg)%type) :=
  ((w.1.1, w.1.2), E' Charlie w.2).

(* BobView _|_ V1: Bob's whole view is independent of Alice's input. *)
Lemma BobView_indep_V1 : P |= BobView _|_ V1.
Proof.
have H := inde_RV_comp bob_view_of idfun bob_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

(* CharlieView _|_ V1: Charlie's whole view is independent of Alice's
   input. *)
Lemma CharlieView_indep_V1 : P |= CharlieView _|_ V1.
Proof.
have H := inde_RV_comp charlie_view_of idfun charlie_inputs_indep_V1.
by rewrite /comp_RV /= in H *.
Qed.

(* Given Bob's whole view, Alice's input keeps log m bits of uncertainty.
   A corrupted Bob is bounded here whatever his running time.  [3-party] *)
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

(* Given Charlie's whole view, Alice's input keeps log m bits of uncertainty.
   A corrupted Charlie is bounded here whatever his running time.
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

(* V3 is uniform on the plaintext ring, by the record's pV3_unif field.  The
   bound on Bob's view about V3 rests on this law and on Alice's mask R3. *)
Let pV3_unif : `p_ V3 = fdist_uniform card_msg_prednK :=
  dsdp_random_inputs.pV3_unif I.
Let pR3_unif : `p_ R3 = fdist_uniform card_msg_prednK :=
  dsdp_random_inputs.pR3_unif I.
Let R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3] :=
  dsdp_random_inputs.R3_indep_VU3_V3 I.
Let bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3] :=
  dsdp_random_inputs.bob_data_indep_charlie I.

(* VU3R _|_ V3: the masked plaintext V3 * U3 + R3 hides V3.  R3 is uniform
   and independent of the pair it masks. *)
Let VU3R_indep_V3 : P |= VU3R _|_ V3.
Proof.
exact: (@lemma_3_5' R T msg msg P VU3 R3 V3 R3_indep_VU3_V3
        m.-1 card_msg_prednK pR3_unif).
Qed.

(* [% Dk_b, V2, D2] _|_ [% V3, VU3R]: Bob's clean data is independent of
   Charlie's input and the masked term.  Alice sends that masked term to
   Bob. *)
Let clean_indep_V3_VU3R : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3R].
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ [% Dk_b, V2, D2] [% V3, VU3, R3]
            idfun (fun w => (w.1.1, w.1.2 + w.2)) bob_data_indep_charlie.
by rewrite /comp_RV /VU3R /add_RV /= in H *.
Qed.

(* [% Dk_b, V2, D2, VU3R] _|_ V3: Bob's data with the masked term he
   receives is independent of Charlie's input. *)
Let bob_inputs_indep_V3 : P |= [% Dk_b, V2, D2, VU3R] _|_ V3.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [% Dk_b, V2, D2]) (Y := V3) (Z := unit_RV P)
         (W := VU3R)).
split.
  by apply cinde_RV_unit; exact: clean_indep_V3_VU3R.
by apply cinde_RV_unit; rewrite inde_RV_sym; exact: VU3R_indep_V3.
Qed.

(* BobView _|_ V3: Bob's whole view is independent of Charlie's input. *)
Let BobView_indep_V3 : P |= BobView _|_ V3.
Proof.
have H := inde_RV_comp
  (fun w : (((Bob.-key Dec msg * msg) * msg) * msg)%type =>
     (((w.1.1.1, w.1.1.2), E' Charlie w.2), E' Bob w.1.2))
  idfun bob_inputs_indep_V3.
by rewrite /comp_RV /= in H *.
Qed.

(* Given Bob's whole view, Charlie's input keeps log m bits of uncertainty.
   The independence comes from Alice's mask R3, so the bound holds whatever
   Bob's running time.  [3-party] *)
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

(* V2 is uniform on the plaintext ring, by the record's pV2_unif field.  The
   bound on Charlie's view about V2 rests on this law and on Alice's mask
   R2. *)
Let pV2_unif : `p_ V2 = fdist_uniform card_msg_prednK :=
  dsdp_random_inputs.pV2_unif I.
Let pR2_unif : `p_ R2 = fdist_uniform card_msg_prednK :=
  dsdp_random_inputs.pR2_unif I.
Let R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2] :=
  dsdp_random_inputs.R2_indep_VU2_V2 I.
Let R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [%VU3R, V2]] :=
  dsdp_random_inputs.R2_indep_VU2_VU3R_V2 I.
Let Dk_c_V3_indep_V2_E : P |= [%Dk_c, V3] _|_ [%V2, E_charlie_d3] :=
  dsdp_random_inputs.Dk_c_V3_indep_V2_E_charlie_d3 I.

(* D2 _|_ [% VU3R, V2]: the masked plaintext V2 * U2 + R2 hides V2.  R2 is
   uniform and independent of that pair. *)
Let D2_indep_VU3R_V2 : P |= D2 _|_ [%VU3R, V2].
Proof.
exact: (@lemma_3_5' R T _ msg P VU2 R2 [%VU3R, V2] R2_indep_VU2_VU3R_V2
        m.-1 card_msg_prednK pR2_unif).
Qed.

(* D3 _|_ V2: the aggregate VU3R + D2 is independent of Bob's input.  D2 is
   uniform and independent of the pair [% VU3R, V2]. *)
Let D3_indep_V2 : P |= D3 _|_ V2.
Proof.
have pD2_unif : `p_ D2 = fdist_uniform card_msg_prednK.
  have R2_VU2_indep : P |= R2 _|_ VU2.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/R2_indep_VU2_V2.
  have VU2_R2_indep : P |= VU2 _|_ R2 by rewrite inde_RV_sym.
  exact: (add_RV_unif VU2 R2 card_msg_prednK pR2_unif VU2_R2_indep).
exact: (@lemma_3_5' R T msg msg P VU3R D2 V2 D2_indep_VU3R_V2
        m.-1 card_msg_prednK pD2_unif).
Qed.

(* E_charlie_d3 _|_ V2: the ciphertext Charlie receives is independent of
   Bob's input, being a deterministic image of D3. *)
Let E_charlie_d3_indep_V2 : P |= E_charlie_d3 _|_ V2.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D3 V2 (E' Charlie) idfun D3_indep_V2.
by rewrite /E_charlie_d3 /comp_RV.
Qed.

(* CharlieView _|_ V2: Charlie's whole view is independent of Bob's
   input. *)
Let CharlieView_indep_V2 : P |= CharlieView _|_ V2.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [%Dk_c, V3]) (Y := V2) (Z := unit_RV P)
         (W := E_charlie_d3)).
split.
  by apply cinde_RV_unit; exact: Dk_c_V3_indep_V2_E.
by apply cinde_RV_unit; rewrite inde_RV_sym; exact: E_charlie_d3_indep_V2.
Qed.

(* Given Charlie's whole view, Bob's input keeps log m bits of uncertainty.
   The independence comes from Alice's mask R2, so the bound holds whatever
   Charlie's running time.  [3-party] *)
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
