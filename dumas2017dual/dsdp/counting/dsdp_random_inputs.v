From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid spp_proba.
Require Import extra_proba extra_algebra.
Require Import homomorphic_encryption.

(**md**************************************************************************)
(* # The random inputs of a 3-party DSDP run at one modulus                   *)
(*                                                                            *)
(* A value of dsdp_random_inputs R p_gt1 q_gt1 is the counting side of a      *)
(* 3-party DSDP run at the plaintext modulus p * q, after du2002's            *)
(* scalar_product_random_inputs: one sample space with one law on it, the     *)
(* eleven random inputs of the run, the independence of each against the      *)
(* joint of the other ten, the uniformity of the three plaintext inputs and   *)
(* the two masks, and the six coins the run draws, plaintext-ring elements    *)
(* no ciphertext of the idealized scheme depends on, jointly independent of   *)
(* the eleven.  Every message is a deterministic function of                  *)
(* those eleven, and a party view is a deterministic function of those eleven *)
(* together with the coins that party draws, so the record carries the whole  *)
(* probabilistic content of the counting axis, and a bound proved from its    *)
(* fields holds against a party of any running time.                          *)
(*                                                                            *)
(* The counting side reads the weights and the keys as drawn together with    *)
(* the inputs.  The hopping side of the same security parameter carries its   *)
(* own weights and keys as fixed values inside its scheme instance, and       *)
(* nothing relates the two.                                                   *)
(*                                                                            *)
(* The seven laws are the independence facts the corrupted-relay privacy      *)
(* theorems condition on, each of them one each-against-the-rest field pushed *)
(* through inde_RV_comp and the graphoid contractions into the shape a        *)
(* party's view takes.  They read Alice's two masks R2 and R3 as fresh        *)
(* against the data those masks hide, which is what makes the relay bounds    *)
(* one-time-pad secrecy rather than encryption hardness, so the ciphertexts   *)
(* inside a relay's view may be read as opaque labels and the bound stands.   *)
(*                                                                            *)
(* uniform_inputs inhabits the record at every modulus whose two factors are  *)
(* above one: the three plaintext inputs and the two masks are the five       *)
(* coordinates of a uniformly drawn row                                       *)
(* vector, and Alice's three query weights and the three private keys are     *)
(* constants of the sample space.  Constant weights are what let a condition  *)
(* on a weight hold at every sample; a weight drawn uniformly takes the value *)
(* zero somewhere, where an invertibility condition on it fails.              *)
(*                                                                            *)
(* ```                                                                        *)
(*      dsdp_random_inputs == the counting side of a 3-party run at the       *)
(*                              plaintext modulus p * q                       *)
(*       bob_inputs_indep_V1 == Bob's clean data is independent of V1         *)
(*   charlie_inputs_indep_V1 == Charlie's clean data is independent of V1     *)
(*           R3_indep_VU3_V3 == the second mask is fresh against Charlie's    *)
(*                              weighted input                                *)
(*    bob_data_indep_charlie == Bob's clean data is independent of the whole  *)
(*                              Charlie group                                 *)
(*           R2_indep_VU2_V2 == the first mask is fresh against Bob's         *)
(*                              weighted input                                *)
(*      R2_indep_VU2_VU3R_V2 == the same mask against the pair Alice's first  *)
(*                              combine enters                                *)
(* Dk_c_V3_indep_V2_E_charlie_d3 == Charlie's key and input are independent   *)
(*                              of Bob's input with the aggregate ciphertext  *)
(*            uniform_inputs == the counting side at any such modulus, three  *)
(*                              inputs and two masks uniform and the query    *)
(*                              weights held at three constants               *)
(*    uniform_card_msg, uniform_card_sample, uniform_card_rest == the counts  *)
(*                              of the plaintext ring, of the sample and of   *)
(*                              four coordinates                              *)
(* uniform_sampleT, uniform_sample_fdist == five coordinates of the plaintext *)
(*                              ring, drawn uniformly                         *)
(* uniform_coord, uniform_rest == the letter at one coordinate and the four   *)
(*                              others                                        *)
(*             uniform_split == one coordinate against the four others, with  *)
(*                              both marginals uniform                        *)
(* uniform_view_input, uniform_view_mask == the four other coordinates as one *)
(*                              view of ten, from an input and from a mask    *)
(*    uniform_V1 .. uniform_R3 == the three inputs and the two masks as the   *)
(*                              five coordinates                              *)
(* uniform_U1, uniform_U2, uniform_U3 == Alice's three query weights as       *)
(*                              constants of the sample space                 *)
(* uniform_Dk_a, uniform_Dk_b, uniform_Dk_c == the three private keys as      *)
(*                              constants                                     *)
(* uniform_V1_indep .. uniform_Dk_c_indep == the eleven each-against-the-rest *)
(*                              facts at that law                             *)
(* uniform_coin_ra1 .. uniform_coin_rc2 == the six coins as constants of the  *)
(*                              sample space                                  *)
(*      uniform_coins_indep == the six coins against the eleven inputs at     *)
(*                              that law                                      *)
(* uniform_pV1_unif .. uniform_pR3_unif == uniformity of the three plaintext  *)
(*                              inputs and the two masks                      *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(* =================================================================          *)
(* The counting side of a run at one modulus                                  *)
(* =================================================================          *)

(* Set Strict Implicit brackets the record: {RV P -> A} unfolds to a function
   type whose domain mentions the record, so under the file's ambient Unset
   Strict Implicit every field would take the record value implicitly and
   V1 I would not typecheck. *)
Set Strict Implicit.

(* The counting side of one 3-party DSDP run: one law, eleven random inputs,
   and the six coins the run draws.  Each input is independent of the other
   ten, the six coins jointly of the eleven, and five inputs are uniform. *)
Record dsdp_random_inputs (R : realType) (p q : nat)
    (p_gt1 : (1 < p)%N) (q_gt1 : (1 < q)%N) := {
  (* The finite sample space of one run. *)
  sampleT : finType ;

  (* The law on that space, which every bound below averages over. *)
  sample_fdist : R.-fdist sampleT ;

  (* Alice's private input. *)
  V1 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Bob's private input. *)
  V2 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Charlie's private input. *)
  V3 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's query weight on her own input. *)
  U1 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's query weight on Bob's input. *)
  U2 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's query weight on Charlie's input. *)
  U3 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's mask on the first combine, the one Bob decrypts. *)
  R2 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's mask on the second combine, the one that reaches Charlie. *)
  R3 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* Alice's private key. *)
  Dk_a : {RV (sample_fdist) -> (Alice.-key Dec 'Z_(p * q))} ;
  (* Bob's private key. *)
  Dk_b : {RV (sample_fdist) -> (Bob.-key Dec 'Z_(p * q))} ;
  (* Charlie's private key. *)
  Dk_c : {RV (sample_fdist) -> (Charlie.-key Dec 'Z_(p * q))} ;

  (* The six coins are idealized randomness, elements of the plaintext ring,
     and no ciphertext of the idealized scheme depends on one of them. *)
  (* The coin of Alice's first combine. *)
  coin_ra1 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* The coin of Alice's second combine. *)
  coin_ra2 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* The coin of Bob's encryption of his input to Alice. *)
  coin_rb1 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* The coin of Bob's encryption of the aggregate to Charlie. *)
  coin_rb2 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* The coin of Charlie's encryption of his input to Alice. *)
  coin_rc1 : {RV (sample_fdist) -> ('Z_(p * q))} ;
  (* The coin of Charlie's re-encryption of the answer to Alice. *)
  coin_rc2 : {RV (sample_fdist) -> ('Z_(p * q))} ;

  (* [% V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V1. *)
  V1_indep : sample_fdist |=
    [% V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V1 ;
  (* [% V1, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V2. *)
  V2_indep : sample_fdist |=
    [% V1, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V2 ;
  (* [% V1, V2, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V3. *)
  V3_indep : sample_fdist |=
    [% V1, V2, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V3 ;
  (* [% V1, V2, V3, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U1. *)
  U1_indep : sample_fdist |=
    [% V1, V2, V3, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U1 ;
  (* [% V1, V2, V3, U1, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U2. *)
  U2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U2 ;
  (* [% V1, V2, V3, U1, U2, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U3. *)
  U3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U3 ;
  (* [% V1, V2, V3, U1, U2, U3, R3, Dk_a, Dk_b, Dk_c] _|_ R2. *)
  R2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R3, Dk_a, Dk_b, Dk_c] _|_ R2 ;
  (* [% V1, V2, V3, U1, U2, U3, R2, Dk_a, Dk_b, Dk_c] _|_ R3. *)
  R3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, Dk_a, Dk_b, Dk_c] _|_ R3 ;
  (* [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_b, Dk_c] _|_ Dk_a. *)
  Dk_a_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_b, Dk_c] _|_ Dk_a ;
  (* [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_c] _|_ Dk_b. *)
  Dk_b_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_c] _|_ Dk_b ;
  (* [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b] _|_ Dk_c. *)
  Dk_c_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b] _|_ Dk_c ;

  (* The six coins are jointly independent of the eleven inputs, so adjoining a
     party's own coins to its view leaves every other input at its entropy. *)
  coins_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c]
    _|_ [% coin_ra1, coin_ra2, coin_rb1, coin_rb2, coin_rc1, coin_rc2] ;

  (* V1 is uniform on the plaintext ring 'Z_(p * q). *)
  pV1_unif : `p_ V1 = fdist_uniform (card_Zp_pq_prednK p_gt1 q_gt1) ;
  (* V2 is uniform on the plaintext ring 'Z_(p * q). *)
  pV2_unif : `p_ V2 = fdist_uniform (card_Zp_pq_prednK p_gt1 q_gt1) ;
  (* V3 is uniform on the plaintext ring 'Z_(p * q). *)
  pV3_unif : `p_ V3 = fdist_uniform (card_Zp_pq_prednK p_gt1 q_gt1) ;
  (* R2 is uniform on the plaintext ring, so it masks V2 * U2 completely. *)
  pR2_unif : `p_ R2 = fdist_uniform (card_Zp_pq_prednK p_gt1 q_gt1) ;
  (* R3 is uniform on the plaintext ring, so it masks V3 * U3 completely. *)
  pR3_unif : `p_ R3 = fdist_uniform (card_Zp_pq_prednK p_gt1 q_gt1) }.
Unset Strict Implicit.

(* The two factors of the modulus are read off the two proofs that carry
   them, so a record value is written at the pair of proofs alone. *)
Arguments dsdp_random_inputs _ {p q} _ _.

(* =================================================================          *)
(* The laws a corrupted relay's view is measured against                      *)
(* =================================================================          *)

Section dsdp_random_inputs_laws.
Local Open Scope reals_ext_scope.
Context {R : realType}.
Variables (p q : nat).
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.
Variable I : dsdp_random_inputs R p_gt1 q_gt1.

Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.

(* The law and the eleven random inputs of the record, the names every
   statement below is written in.  No statement here reads a coin. *)
Local Notation P := (sample_fdist I).
Local Notation V1 := (V1 I).
Local Notation V2 := (V2 I).
Local Notation V3 := (V3 I).
Local Notation U1 := (U1 I).
Local Notation U2 := (U2 I).
Local Notation U3 := (U3 I).
Local Notation R2 := (R2 I).
Local Notation R3 := (R3 I).
Local Notation Dk_a := (Dk_a I).
Local Notation Dk_b := (Dk_b I).
Local Notation Dk_c := (Dk_c I).

(* The joint of the ten inputs other than the one being separated, the
   domain every each-against-the-rest projection below reads from. *)
Local Notation rest10 := (msg * msg * msg * msg * msg * msg * msg *
  (Alice.-key Dec msg) * (Bob.-key Dec msg) * (Charlie.-key Dec msg))%type.

(* Bob's input under Alice's query weight U2, reaching the aggregate only
   through D2. *)
Let VU2 : {RV P -> msg} := V2 \* U2.

(* Charlie's input under Alice's query weight U3, reaching the aggregate only
   through VU3R. *)
Let VU3 : {RV P -> msg} := V3 \* U3.

(* Charlie's weighted input under Alice's mask R3, the plaintext of the second
   combine Alice sends to Bob.  R3 is Alice's own, so it lies outside Bob's
   view. *)
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's weighted input under Alice's mask R2, the plaintext Bob decrypts from
   Alice's first combine.  R2 lies outside Charlie's view. *)
Let D2 : {RV P -> msg} := VU2 \+ R2.

(* The aggregate Charlie decrypts, carrying both relay inputs under Alice's
   two masks. *)
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* The aggregate Bob forwards to Charlie under Charlie's key, the one
   ciphertext Charlie's view contains. *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' Charlie `o D3.

(* [% Dk_b, V2, VU3R, D2] _|_ V1: Bob's key, his input and the two combines
   he handles are independent of Alice's input.  It is the record's V1_indep
   field projected onto those four. *)
Lemma bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1.
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.1),
                       w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2 + w.1.1.1.2),
                      w.1.1.1.1.1.1.1.1.1 * w.1.1.1.1.1.1.2 + w.1.1.1.1.2))
  idfun (V1_indep I).
by rewrite /comp_RV /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* [% Dk_c, V3, D3] _|_ V1: Charlie's key, his input and the aggregate he
   decrypts are independent of Alice's input.  It is the record's V1_indep
   field projected onto those three. *)
Lemma charlie_inputs_indep_V1 : P |= [% Dk_c, V3, D3] _|_ V1.
Proof.
have h := inde_RV_comp
  (fun w : rest10 => ((w.2, w.1.1.1.1.1.1.1.1.2),
                      w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2 + w.1.1.1.2
                      + (w.1.1.1.1.1.1.1.1.1 * w.1.1.1.1.1.1.2
                         + w.1.1.1.1.2)))
  idfun (V1_indep I).
by rewrite /comp_RV /D3 /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* R3 _|_ [% VU3, V3]: Alice's second mask is independent of Charlie's
   weighted input and of Charlie's input itself.  R3 is the mask that
   keeps V3 independent of Bob's view. *)
Lemma R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.2)) idfun (R3_indep I).
rewrite /comp_RV /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* [% Dk_b, V2, D2] _|_ [% V3, VU3, R3]: Bob's key, his input and D2 are
   independent of the whole Charlie group.  V3, VU3 and R3 stand together on
   the right, so VU3R may be formed downstream. *)
Lemma bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3].
Proof.
(* Contracting on VU3 directly is unavailable, since VU3 shares V3 with the
   left side.  The V3, U3 and R3 fields are projected and joined by two
   contractions, then reshaped. *)
have hv3 : P |= [% Dk_b, V2, D2] _|_ V3.
  have h := inde_RV_comp
    (fun w : rest10 => ((w.1.2, w.1.1.1.1.1.1.1.1.2),
                        w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.1.2
                        + w.1.1.1.1.2)) idfun (V3_indep I).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hu3 : P |= [% [% Dk_b, V2, D2], V3] _|_ U3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.1.2), w.1.1.1.1.1.1.1.2))
    idfun (U3_indep I).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hr3 : P |= [% [% Dk_b, V2, D2], [% V3, U3]] _|_ R3.
  have h := inde_RV_comp
    (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.2),
                         w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2
                         + w.1.1.1.2), (w.1.1.1.1.1.1.1.2,
                                        w.1.1.1.1.2)))
    idfun (R3_indep I).
  by rewrite /comp_RV /D2 /VU2 /= in h *.
have hstep := inde_RV_contraction (inde_RV_contraction hv3 hu3) hr3.
have h := inde_RV_comp idfun
  (fun w : (msg * msg * msg)%type => ((w.1.1, w.1.1 * w.1.2), w.2)) hstep.
by rewrite /comp_RV /VU3 /= in h *.
Qed.

(* R2 _|_ [% VU2, V2]: Alice's first mask is independent of Bob's
   weighted input and of Bob's input itself.  R2 is the mask that keeps
   V2 independent of Charlie's view. *)
Lemma R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.1.2)) idfun (R2_indep I).
rewrite /comp_RV /VU2 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* R2 _|_ [% VU2, [% VU3R, V2]]: Alice's first mask is independent of the
   whole tuple her first combine enters.  One coordinate wider than
   R2_indep_VU2_V2, which is the width Charlie's aggregate needs. *)
Lemma R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [% VU3R, V2]].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                       w.1.1.1.1.1.1.1.1.2))) idfun (R2_indep I).
rewrite /comp_RV /VU2 /VU3R /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* [% Dk_c, V3] _|_ [% V2, E_charlie_d3]: Charlie's key and his input are
   independent of Bob's input and the ciphertext.  Alice's two masks hide V2
   inside the aggregate, so this needs no encryption assumption. *)
Lemma Dk_c_V3_indep_V2_E_charlie_d3 :
  P |= [% Dk_c, V3] _|_ [% V2, E_charlie_d3].
Proof.
have card_msg_prednK : #|msg| = m.-1.+1 := card_Zp_pq_prednK p_gt1 q_gt1.
have pR2_adj : `p_ R2 = fdist_uniform card_msg_prednK.
  by rewrite (pR2_unif I); congr fdist_uniform; exact: eq_irrelevance.
have r2_rest : P |= R2 _|_ [% VU2, [% VU3R, [% [% Dk_c, V3], V2]]].
  have h := inde_RV_comp
    (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                        (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                         ((w.2, w.1.1.1.1.1.1.1.2),
                          w.1.1.1.1.1.1.1.1.2)))) idfun (R2_indep I).
  rewrite /comp_RV /VU2 /VU3R /VU3 /= in h *.
  by rewrite inde_RV_sym.
have d2_rest : P |= D2 _|_ [% VU3R, [% [% Dk_c, V3], V2]].
  exact: (lemma_3_5' r2_rest pR2_adj).
have pD2_unif : `p_ D2 = fdist_uniform card_msg_prednK.
  have vu2_r2 : P |= VU2 _|_ R2.
    rewrite inde_RV_sym.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/r2_rest.
  exact: (add_RV_unif VU2 R2 card_msg_prednK pR2_adj vu2_r2).
have d3_rest : P |= D3 _|_ [% [% Dk_c, V3], V2].
  exact: (lemma_3_5' d2_rest pD2_unif).
have he : P |= [% [% Dk_c, V3], V2] _|_ E_charlie_d3.
  have hsym : P |= [% [% Dk_c, V3], V2] _|_ D3 by rewrite inde_RV_sym.
  have h := inde_RV_comp idfun (E' Charlie) hsym.
  by rewrite /E_charlie_d3 /comp_RV /= in h *.
apply: inde_RV_contraction; last exact: he.
have h := inde_RV_comp (fun w : rest10 => (w.2, w.1.1.1.1.1.1.1.1.2)) idfun
  (V2_indep I).
by rewrite /comp_RV /= in h *.
Qed.

End dsdp_random_inputs_laws.

(* Every law above has a discharged type that unfolds to a product whose
   binder mentions the record: an independence is a quantification over two
   values of random variables, and a random variable is a function on the
   record's sample space.  Under the file's ambient Unset Strict Implicit the
   record would therefore be implicit.  Pinning it explicit keeps every use
   site free of @. *)
Arguments bob_inputs_indep_V1 {R p q p_gt1 q_gt1} I.
Arguments charlie_inputs_indep_V1 {R p q p_gt1 q_gt1} I.
Arguments R3_indep_VU3_V3 {R p q p_gt1 q_gt1} I.
Arguments bob_data_indep_charlie {R p q p_gt1 q_gt1} I.
Arguments R2_indep_VU2_V2 {R p q p_gt1 q_gt1} I.
Arguments R2_indep_VU2_VU3R_V2 {R p q p_gt1 q_gt1} I.
Arguments Dk_c_V3_indep_V2_E_charlie_d3 {R p q p_gt1 q_gt1} I.

(* =================================================================          *)
(* The counting side is inhabited at every modulus                            *)
(* =================================================================          *)

(* The counting side at any modulus, with Alice's query weights held at three
   values of her choosing: the three plaintext inputs and the two masks are
   the five coordinates of a uniformly drawn row vector, and the three
   weights and the three private keys are constants of the sample space.
   A weight drawn uniformly takes the value zero at some sample, so an
   invertibility condition on that weight fails there.  This is why the
   three weights are constants of the sample space rather than further
   coordinates of the drawn vector. *)
Section dsdp_inputs_uniform.
Local Open Scope vec_ext_scope.
Context {R : realType}.
Variables (p q : nat).
Hypothesis p_gt1 : (1 < p)%N.
Hypothesis q_gt1 : (1 < q)%N.

Local Notation ord5 j := (@Ordinal 5 j erefl).
Local Notation ord4 j := (@Ordinal 4 j erefl).
Local Notation msg := ('Z_(p * q)).

(* The plaintext count at this modulus, in the form fdist_uniform takes its
   argument. *)
Definition uniform_card_msg : #|msg| = (p * q).-1.+1 :=
  card_Zp_pq_prednK p_gt1 q_gt1.

Lemma uniform_card_sample : #|'rV[msg]_5| = (((p * q) ^ 5).-1).+1.
Proof.
rewrite card_mx mul1n (card_Zp_pq p_gt1 q_gt1) prednK//.
by rewrite expn_gt0 (ltnW (pq_gt1 p_gt1 q_gt1)).
Qed.

Lemma uniform_card_rest : #|'rV[msg]_4| = (((p * q) ^ 4).-1).+1.
Proof.
rewrite card_mx mul1n (card_Zp_pq p_gt1 q_gt1) prednK//.
by rewrite expn_gt0 (ltnW (pq_gt1 p_gt1 q_gt1)).
Qed.

Definition uniform_sampleT : finType := 'rV[msg]_5.

Definition uniform_sample_fdist : R.-fdist uniform_sampleT :=
  fdist_uniform uniform_card_sample.

Local Notation P := uniform_sample_fdist.

Definition uniform_coord (i : 'I_5) : {RV P -> msg} := fun v => v ``_ i.

Definition uniform_rest (i : 'I_5) : {RV P -> 'rV[msg]_4} := rV_drop i.

Lemma uniform_split (i : 'I_5) :
  [/\ P |= uniform_rest i _|_ uniform_coord i,
      `p_ (uniform_rest i) = fdist_uniform uniform_card_rest
    & `p_ (uniform_coord i) = fdist_uniform uniform_card_msg].
Proof.
have bij_split : bijective (fun t => (uniform_rest i t, uniform_coord i t)).
  exact: (rV_split_bij msg i).
exact: (uniform_bij_indep uniform_card_rest uniform_card_msg bij_split).
Qed.

(* The rest-tuple seen from an input coordinate: the four other coordinates
   in order.  The three weights and the three keys are read off as
   constants. *)
Definition uniform_view_input (w1 w2 w3 : msg) (w : 'rV[msg]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w1, w2, w3,
   w ``_ (ord4 2), w ``_ (ord4 3),
   @KeyOf Alice Dec msg 0, @KeyOf Bob Dec msg 0, @KeyOf Charlie Dec msg 0).

(* The same tuple seen from a mask coordinate.  Here the three weights sit
   after the three inputs, not after two of them. *)
Definition uniform_view_mask (w1 w2 w3 : msg) (w : 'rV[msg]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w ``_ (ord4 2), w1, w2, w3,
   w ``_ (ord4 3),
   @KeyOf Alice Dec msg 0, @KeyOf Bob Dec msg 0, @KeyOf Charlie Dec msg 0).

Definition uniform_V1 : {RV P -> msg} := uniform_coord (ord5 0).
Definition uniform_V2 : {RV P -> msg} := uniform_coord (ord5 1).
Definition uniform_V3 : {RV P -> msg} := uniform_coord (ord5 2).
Definition uniform_R2 : {RV P -> msg} := uniform_coord (ord5 3).
Definition uniform_R3 : {RV P -> msg} := uniform_coord (ord5 4).

Definition uniform_U1 (w1 : msg) : {RV P -> msg} := fun _ => w1.
Definition uniform_U2 (w2 : msg) : {RV P -> msg} := fun _ => w2.
Definition uniform_U3 (w3 : msg) : {RV P -> msg} := fun _ => w3.

Definition uniform_Dk_a : {RV P -> (Alice.-key Dec msg)} :=
  fun _ => @KeyOf Alice Dec _ 0.
Definition uniform_Dk_b : {RV P -> (Bob.-key Dec msg)} :=
  fun _ => @KeyOf Bob Dec _ 0.
Definition uniform_Dk_c : {RV P -> (Charlie.-key Dec msg)} :=
  fun _ => @KeyOf Charlie Dec _ 0.

(* No bound reads a coin's law, so the six coins of this inhabitant are the
   zero of the plaintext ring. *)

(* The coin of Alice's first combine, a constant of the sample space. *)
Definition uniform_coin_ra1 : {RV P -> msg} := fun _ => 0.
(* The coin of Alice's second combine, a constant of the sample space. *)
Definition uniform_coin_ra2 : {RV P -> msg} := fun _ => 0.
(* The coin of Bob's encryption of his input, a constant. *)
Definition uniform_coin_rb1 : {RV P -> msg} := fun _ => 0.
(* The coin of Bob's encryption of the aggregate, a constant. *)
Definition uniform_coin_rb2 : {RV P -> msg} := fun _ => 0.
(* The coin of Charlie's encryption of his input, a constant. *)
Definition uniform_coin_rc1 : {RV P -> msg} := fun _ => 0.
(* The coin of Charlie's re-encryption of the answer, a constant. *)
Definition uniform_coin_rc2 : {RV P -> msg} := fun _ => 0.

Lemma uniform_V1_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V2, uniform_V3, uniform_U1 w1, uniform_U2 w2,
       uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_V1.
Proof.
have e0 : lift (ord5 0) (ord4 0) = ord5 1 by apply/val_inj.
have e1 : lift (ord5 0) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 0) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 0) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V2, uniform_V3, uniform_U1 w1, uniform_U2 w2,
     uniform_U3 w3, uniform_R2, uniform_R3,
     uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  = uniform_view_input w1 w2 w3 `o uniform_rest (ord5 0).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split (ord5 0).
exact: inde_RV_comp (uniform_view_input w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V2_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V3, uniform_U1 w1, uniform_U2 w2,
       uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_V2.
Proof.
have e0 : lift (ord5 1) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 1) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 1) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 1) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1, uniform_V3, uniform_U1 w1, uniform_U2 w2,
     uniform_U3 w3, uniform_R2, uniform_R3,
     uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  = uniform_view_input w1 w2 w3 `o uniform_rest (ord5 1).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split (ord5 1).
exact: inde_RV_comp (uniform_view_input w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V3_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_U1 w1, uniform_U2 w2,
       uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_V3.
Proof.
have e0 : lift (ord5 2) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 2) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 2) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 2) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1, uniform_V2, uniform_U1 w1, uniform_U2 w2,
     uniform_U3 w3, uniform_R2, uniform_R3,
     uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  = uniform_view_input w1 w2 w3 `o uniform_rest (ord5 2).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split (ord5 2).
exact: inde_RV_comp (uniform_view_input w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R2_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_R2.
Proof.
have e0 : lift (ord5 3) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 3) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 3) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 3) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
     uniform_U2 w2, uniform_U3 w3, uniform_R3,
     uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  = uniform_view_mask w1 w2 w3 `o uniform_rest (ord5 3).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split (ord5 3).
exact: inde_RV_comp (uniform_view_mask w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R3_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R2,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_R3.
Proof.
have e0 : lift (ord5 4) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 4) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 4) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 4) (ord4 3) = ord5 3 by apply/val_inj.
have -> :
  [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
     uniform_U2 w2, uniform_U3 w3, uniform_R2,
     uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  = uniform_view_mask w1 w2 w3 `o uniform_rest (ord5 4).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split (ord5 4).
exact: inde_RV_comp (uniform_view_mask w1 w2 w3) idfun ind.
Qed.

(* The three weights and the three keys are constants of the sample space, so
   six of the eleven each-against-the-rest fields are discharged without
   touching the sample space. *)

(* Alice's first query weight is a constant of the sample space, and a
   constant is independent of every random variable. *)
Lemma uniform_U1_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U2 w2,
       uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_U1 w1.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U2_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_U2 w2.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U3_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_U3 w3.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_a_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_b, uniform_Dk_c]
  _|_ uniform_Dk_a.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_b_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_c]
  _|_ uniform_Dk_b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_c_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b]
  _|_ uniform_Dk_c.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

(* The six coins are constants of the sample space, so they are independent
   of the eleven inputs. *)
Lemma uniform_coins_indep (w1 w2 w3 : msg) :
  P |=
    [% uniform_V1, uniform_V2, uniform_V3, uniform_U1 w1,
       uniform_U2 w2, uniform_U3 w3, uniform_R2, uniform_R3,
       uniform_Dk_a, uniform_Dk_b, uniform_Dk_c]
  _|_ [% uniform_coin_ra1, uniform_coin_ra2, uniform_coin_rb1,
         uniform_coin_rb2, uniform_coin_rc1, uniform_coin_rc2].
Proof.
(* inde_const_RV takes the constant on the left and as a literal const_RV, so
   the six-coin tuple is folded into one constant before it applies. *)
rewrite inde_RV_sym.
have -> : [% uniform_coin_ra1, uniform_coin_ra2, uniform_coin_rb1,
             uniform_coin_rb2, uniform_coin_rc1, uniform_coin_rc2]
        = const_RV P (0, 0, 0, 0, 0, 0) :> {RV P -> _} by [].
exact: inde_const_RV.
Qed.

Lemma uniform_pV1_unif : `p_ uniform_V1 = fdist_uniform uniform_card_msg.
Proof. by have [_ _ unif] := uniform_split (ord5 0). Qed.

Lemma uniform_pV2_unif : `p_ uniform_V2 = fdist_uniform uniform_card_msg.
Proof. by have [_ _ unif] := uniform_split (ord5 1). Qed.

Lemma uniform_pV3_unif : `p_ uniform_V3 = fdist_uniform uniform_card_msg.
Proof. by have [_ _ unif] := uniform_split (ord5 2). Qed.

Lemma uniform_pR2_unif : `p_ uniform_R2 = fdist_uniform uniform_card_msg.
Proof. by have [_ _ unif] := uniform_split (ord5 3). Qed.

Lemma uniform_pR3_unif : `p_ uniform_R3 = fdist_uniform uniform_card_msg.
Proof. by have [_ _ unif] := uniform_split (ord5 4). Qed.

(* An inhabitant of the record at any modulus with both factors above one.
   The three inputs and two masks are five uniform coordinates, and the
   weights, keys and coins are constants. *)
Definition uniform_inputs (w1 w2 w3 : msg) :
    dsdp_random_inputs R p_gt1 q_gt1 := {|
  sampleT := uniform_sampleT ;
  sample_fdist := uniform_sample_fdist ;
  V1 := uniform_V1 ;
  V2 := uniform_V2 ;
  V3 := uniform_V3 ;
  U1 := uniform_U1 w1 ;
  U2 := uniform_U2 w2 ;
  U3 := uniform_U3 w3 ;
  R2 := uniform_R2 ;
  R3 := uniform_R3 ;
  Dk_a := uniform_Dk_a ;
  Dk_b := uniform_Dk_b ;
  Dk_c := uniform_Dk_c ;
  coin_ra1 := uniform_coin_ra1 ;
  coin_ra2 := uniform_coin_ra2 ;
  coin_rb1 := uniform_coin_rb1 ;
  coin_rb2 := uniform_coin_rb2 ;
  coin_rc1 := uniform_coin_rc1 ;
  coin_rc2 := uniform_coin_rc2 ;
  V1_indep := uniform_V1_indep w1 w2 w3 ;
  V2_indep := uniform_V2_indep w1 w2 w3 ;
  V3_indep := uniform_V3_indep w1 w2 w3 ;
  U1_indep := uniform_U1_indep w1 w2 w3 ;
  U2_indep := uniform_U2_indep w1 w2 w3 ;
  U3_indep := uniform_U3_indep w1 w2 w3 ;
  R2_indep := uniform_R2_indep w1 w2 w3 ;
  R3_indep := uniform_R3_indep w1 w2 w3 ;
  Dk_a_indep := uniform_Dk_a_indep w1 w2 w3 ;
  Dk_b_indep := uniform_Dk_b_indep w1 w2 w3 ;
  Dk_c_indep := uniform_Dk_c_indep w1 w2 w3 ;
  coins_indep := uniform_coins_indep w1 w2 w3 ;
  pV1_unif := uniform_pV1_unif ;
  pV2_unif := uniform_pV2_unif ;
  pV3_unif := uniform_pV3_unif ;
  pR2_unif := uniform_pR2_unif ;
  pR3_unif := uniform_pR3_unif |}.

End dsdp_inputs_uniform.
