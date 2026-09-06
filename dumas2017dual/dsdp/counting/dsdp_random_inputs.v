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
(* A value of dsdp_random_inputs R a b is the counting side of a 3-party DSDP *)
(* run at the plaintext modulus a.+2 * b.+2, after du2002's                   *)
(* scalar_product_random_inputs: one sample space with one law on it, the     *)
(* eleven random inputs of the run, the independence of each against the      *)
(* joint of the other ten, and the uniformity of the three plaintext inputs   *)
(* and the two masks.  Every message and every party view of a run is a       *)
(* deterministic function of those eleven, so the record carries the whole    *)
(* probabilistic content of the counting axis, and a bound proved from its    *)
(* fields holds against a party of any running time.                          *)
(*                                                                            *)
(* The seven laws are the independence facts the corrupted-relay privacy      *)
(* theorems condition on, each of them one each-against-the-rest field pushed *)
(* through inde_RV_comp and the graphoid contractions into the shape a        *)
(* party's view takes.  They read Alice's two masks R2 and R3 as fresh        *)
(* against the data those masks hide, which is what makes the relay bounds    *)
(* one-time-pad secrecy rather than encryption hardness, so the ciphertexts   *)
(* inside a relay's view may be read as opaque labels and the bound stands.   *)
(*                                                                            *)
(* uniform_inputs inhabits the record at every modulus: the three plaintext   *)
(* inputs and the two masks are the five coordinates of a uniformly drawn row *)
(* vector, and Alice's three query weights and the three private keys are     *)
(* constants of the sample space.  Constant weights are what let a condition  *)
(* on a weight hold at every sample; a weight drawn uniformly takes the value *)
(* zero somewhere, where an invertibility condition on it fails.              *)
(*                                                                            *)
(* ```                                                                        *)
(*      dsdp_random_inputs == the counting side of a 3-party run at the       *)
(*                              plaintext modulus a.+2 * b.+2                 *)
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
(*            uniform_inputs == the counting side at any modulus, three       *)
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

(* The counting side of a 3-party run at the fixed plaintext modulus
   a.+2 * b.+2, after du2002's scalar_product_random_inputs: one sample space
   with one law on it, the eleven random inputs of the run, their
   independence each against the joint of the other ten, and the uniformity
   of the three plaintext inputs and the two masks.
   The record is named for the counting side's reading of the eleven, where
   the weights and the keys are drawn together with the inputs; the hopping
   side of the same security parameter carries its own weights and keys as
   fixed values inside its scheme instance, and nothing relates the two. *)
Record dsdp_random_inputs (R : realType) (a b : nat) := {
  (* The sample space and the law on it: every random variable below is a
     function on this space and every bound is an average over this law. *)
  sampleT : finType ;
  sample_fdist : R.-fdist sampleT ;

  (* The entire randomness of a 3-party run at this modulus.  Every message
     and every party view is a deterministic function of these eleven, which
     is what lets a bound proved at the inputs transfer to a view. *)
  V1 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  V2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  V3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U1 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  U3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  R2 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  R3 : {RV (sample_fdist) -> ('Z_(a.+2 * b.+2))} ;
  Dk_a : {RV (sample_fdist) -> (Alice.-key Dec 'Z_(a.+2 * b.+2))} ;
  Dk_b : {RV (sample_fdist) -> (Bob.-key Dec 'Z_(a.+2 * b.+2))} ;
  Dk_c : {RV (sample_fdist) -> (Charlie.-key Dec 'Z_(a.+2 * b.+2))} ;

  (* Each input independent of the joint of the other ten, stated
     each-against-the-rest because every derived fact below is one of these
     pushed through inde_RV_comp. *)
  V1_indep : sample_fdist |=
    [% V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V1 ;
  V2_indep : sample_fdist |=
    [% V1, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V2 ;
  V3_indep : sample_fdist |=
    [% V1, V2, U1, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ V3 ;
  U1_indep : sample_fdist |=
    [% V1, V2, V3, U2, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U1 ;
  U2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U3, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U2 ;
  U3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, R2, R3, Dk_a, Dk_b, Dk_c] _|_ U3 ;
  R2_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R3, Dk_a, Dk_b, Dk_c] _|_ R2 ;
  R3_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, Dk_a, Dk_b, Dk_c] _|_ R3 ;
  Dk_a_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_b, Dk_c] _|_ Dk_a ;
  Dk_b_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_c] _|_ Dk_b ;
  Dk_c_indep : sample_fdist |=
    [% V1, V2, V3, U1, U2, U3, R2, R3, Dk_a, Dk_b] _|_ Dk_c ;

  (* Uniformity of R2 and R3 is what makes the relay bounds unconditional,
     one-time-pad masking rather than encryption hardness hiding V2 and V3;
     uniformity of V1, V2, V3 is what makes the conditional entropy equal
     log m rather than merely positive.  Alice's three weights carry no law:
     they are her chosen query, not a sample. *)
  pV1_unif : `p_ V1 = fdist_uniform (card_Zp_pq a b) ;
  pV2_unif : `p_ V2 = fdist_uniform (card_Zp_pq a b) ;
  pV3_unif : `p_ V3 = fdist_uniform (card_Zp_pq a b) ;
  pR2_unif : `p_ R2 = fdist_uniform (card_Zp_pq a b) ;
  pR3_unif : `p_ R3 = fdist_uniform (card_Zp_pq a b) }.
Unset Strict Implicit.

(* =================================================================          *)
(* The laws a corrupted relay's view is measured against                      *)
(* =================================================================          *)

Section dsdp_random_inputs_laws.
Local Open Scope reals_ext_scope.
Context {R : realType}.
Variables (a b : nat).
Variable I : dsdp_random_inputs R a b.

Local Notation p := a.+2.
Local Notation q := b.+2.
Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.

(* The law and the eleven inputs of the record, the names every statement
   below is written in. *)
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

(* The joint of the ten inputs other than one plaintext input: the domain
   every each-against-the-rest projection below reads from. *)
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

(* Bob's key, his own input and the two combines he handles are independent of
   Alice's input V1: V1 occurs in no protocol message, so the V1 field
   projected onto those four suffices. *)
Lemma bob_inputs_indep_V1 : P |= [% Dk_b, V2, VU3R, D2] _|_ V1.
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (((w.1.2, w.1.1.1.1.1.1.1.1.1),
                       w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2 + w.1.1.1.2),
                      w.1.1.1.1.1.1.1.1.1 * w.1.1.1.1.1.1.2 + w.1.1.1.1.2))
  idfun (V1_indep I).
by rewrite /comp_RV /VU3R /VU3 /D2 /VU2 /= in h *.
Qed.

(* Charlie's key, his own input and the aggregate he decrypts are independent
   of Alice's input V1, the same projection of the V1 field on his side. *)
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

(* Alice's second mask is independent of Charlie's weighted input and of
   Charlie's input itself, the R3 field projected onto that pair.  R3 is the
   pad that hides V3 from Bob. *)
Lemma R3_indep_VU3_V3 : P |= R3 _|_ [% VU3, V3].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.2)) idfun (R3_indep I).
rewrite /comp_RV /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* Bob's key, his input and the combine he decrypts are independent of
   Charlie's input, weighted input and mask together.  The V3, U3 and R3
   fields are projected and joined by two contractions, then reshaped, since
   contracting on VU3 directly is unavailable: VU3 shares V3 with the left
   side. *)
Lemma bob_data_indep_charlie : P |= [% Dk_b, V2, D2] _|_ [% V3, VU3, R3].
Proof.
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

(* Alice's first mask is independent of Bob's weighted input and of Bob's
   input itself, the R2 field projected onto that pair.  R2 is the pad that
   hides V2 from Charlie. *)
Lemma R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      w.1.1.1.1.1.1.1.1.2)) idfun (R2_indep I).
rewrite /comp_RV /VU2 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* The same mask against the whole pair Alice's first combine enters, the R2
   field projected one coordinate wider. *)
Lemma R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [% VU3R, V2]].
Proof.
have h := inde_RV_comp
  (fun w : rest10 => (w.1.1.1.1.1.1.1.1.2 * w.1.1.1.1.1.2,
                      (w.1.1.1.1.1.1.1.2 * w.1.1.1.1.2 + w.1.1.1.2,
                       w.1.1.1.1.1.1.1.1.2))) idfun (R2_indep I).
rewrite /comp_RV /VU2 /VU3R /VU3 /= in h *.
by rewrite inde_RV_sym.
Qed.

(* Charlie's key and input are independent of Bob's input together with the
   aggregate ciphertext Charlie receives.  Two one-time-pad steps: R2 is a
   fresh pad inside D2, and D2 is then a fresh pad inside D3, so the whole
   aggregate carries nothing about V2 and neither does its encryption. *)
Lemma Dk_c_V3_indep_V2_E_charlie_d3 :
  P |= [% Dk_c, V3] _|_ [% V2, E_charlie_d3].
Proof.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1 by rewrite card_ord.
have pR2_adj : `p_ R2 = fdist_uniform card_TZ.
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
have pD2_unif : `p_ D2 = fdist_uniform card_TZ.
  have vu2_r2 : P |= VU2 _|_ R2.
    rewrite inde_RV_sym.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/r2_rest.
  exact: (add_RV_unif VU2 R2 card_TZ pR2_adj vu2_r2).
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
Arguments bob_inputs_indep_V1 {R a b} I.
Arguments charlie_inputs_indep_V1 {R a b} I.
Arguments R3_indep_VU3_V3 {R a b} I.
Arguments bob_data_indep_charlie {R a b} I.
Arguments R2_indep_VU2_V2 {R a b} I.
Arguments R2_indep_VU2_VU3R_V2 {R a b} I.
Arguments Dk_c_V3_indep_V2_E_charlie_d3 {R a b} I.

(* =================================================================          *)
(* The counting side is inhabited at every modulus                            *)
(* =================================================================          *)

(* The counting side at any modulus, with Alice's query weights held at three
   values of her choosing: the three plaintext inputs and the two masks are
   the five coordinates of a uniformly drawn row vector, and the three
   weights and the three private keys are constants of the sample space.
   Constant weights are what give the two query records values.  A weight
   drawn uniformly takes the value zero somewhere on the sample space, and
   the honest query asks for a weight invertible at every sample, so no
   setting whose weights are sampled satisfies either query record. *)
Section dsdp_inputs_uniform.
Local Open Scope vec_ext_scope.
Context {R : realType}.
Local Unset Implicit Arguments.

Local Notation ord5 j := (@Ordinal 5 j erefl).
Local Notation ord4 j := (@Ordinal 4 j erefl).
Local Notation msg a b := ('Z_(a.+2 * b.+2)).

(* The plaintext count at this modulus, in the form fdist_uniform takes its
   argument. *)
Definition uniform_card_msg (a b : nat) : #|msg a b| = (a.+2 * b.+2)%N :=
  card_Zp_pq a b.

Lemma uniform_card_sample (a b : nat) :
  #|'rV[msg a b]_5| = (((a.+2 * b.+2) ^ 5).-1).+1.
Proof. by rewrite card_mx mul1n (uniform_card_msg a b) prednK. Qed.

Lemma uniform_card_rest (a b : nat) :
  #|'rV[msg a b]_4| = (((a.+2 * b.+2) ^ 4).-1).+1.
Proof. by rewrite card_mx mul1n (uniform_card_msg a b) prednK. Qed.

Definition uniform_sampleT (a b : nat) : finType := 'rV[msg a b]_5.

Definition uniform_sample_fdist (a b : nat) : R.-fdist (uniform_sampleT a b) :=
  fdist_uniform (uniform_card_sample a b).

Local Notation P a b := (uniform_sample_fdist a b).

Definition uniform_coord (a b : nat) (i : 'I_5) : {RV (P a b) -> msg a b} :=
  fun v => v ``_ i.

Definition uniform_rest (a b : nat) (i : 'I_5) :
    {RV (P a b) -> 'rV[msg a b]_4} :=
  rV_drop i.

Lemma uniform_split (a b : nat) (i : 'I_5) :
  [/\ P a b |= uniform_rest a b i _|_ uniform_coord a b i,
      `p_ (uniform_rest a b i) = fdist_uniform (uniform_card_rest a b)
    & `p_ (uniform_coord a b i) = fdist_uniform (uniform_card_msg a b)].
Proof.
have bij_split : bijective (fun t => (uniform_rest a b i t,
                                      uniform_coord a b i t)).
  exact: (rV_split_bij (msg a b) i).
exact: (uniform_bij_indep (uniform_card_rest a b) (uniform_card_msg a b)
          bij_split).
Qed.

(* The rest-tuple seen from an input coordinate: the four remaining
   coordinates in their original order with the three weights and the three
   keys read off as constants. *)
Definition uniform_view_input (a b : nat) (w1 w2 w3 : msg a b)
    (w : 'rV[msg a b]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w1, w2, w3,
   w ``_ (ord4 2), w ``_ (ord4 3),
   @KeyOf Alice Dec (msg a b) 0, @KeyOf Bob Dec (msg a b) 0,
   @KeyOf Charlie Dec (msg a b) 0).

(* The same tuple seen from a mask coordinate, where the three weights sit
   after the three inputs rather than after two of them. *)
Definition uniform_view_mask (a b : nat) (w1 w2 w3 : msg a b)
    (w : 'rV[msg a b]_4) :=
  (w ``_ (ord4 0), w ``_ (ord4 1), w ``_ (ord4 2), w1, w2, w3,
   w ``_ (ord4 3),
   @KeyOf Alice Dec (msg a b) 0, @KeyOf Bob Dec (msg a b) 0,
   @KeyOf Charlie Dec (msg a b) 0).

Definition uniform_V1 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 0).
Definition uniform_V2 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 1).
Definition uniform_V3 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 2).
Definition uniform_R2 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 3).
Definition uniform_R3 (a b : nat) : {RV (P a b) -> msg a b} :=
  uniform_coord a b (ord5 4).

Definition uniform_U1 (a b : nat) (w1 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w1.
Definition uniform_U2 (a b : nat) (w2 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w2.
Definition uniform_U3 (a b : nat) (w3 : msg a b) : {RV (P a b) -> msg a b} :=
  fun _ => w3.

Definition uniform_Dk_a (a b : nat) :
    {RV (P a b) -> (Alice.-key Dec (msg a b))} :=
  fun _ => @KeyOf Alice Dec _ 0.
Definition uniform_Dk_b (a b : nat) :
    {RV (P a b) -> (Bob.-key Dec (msg a b))} :=
  fun _ => @KeyOf Bob Dec _ 0.
Definition uniform_Dk_c (a b : nat) :
    {RV (P a b) -> (Charlie.-key Dec (msg a b))} :=
  fun _ => @KeyOf Charlie Dec _ 0.

Lemma uniform_V1_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V1 a b.
Proof.
have e0 : lift (ord5 0) (ord4 0) = ord5 1 by apply/val_inj.
have e1 : lift (ord5 0) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 0) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 0) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 0).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 0).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V2 a b.
Proof.
have e0 : lift (ord5 1) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 1) (ord4 1) = ord5 2 by apply/val_inj.
have e2 : lift (ord5 1) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 1) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V3 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 1).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 1).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_V3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_U1 a b w1, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_V3 a b.
Proof.
have e0 : lift (ord5 2) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 2) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 2) (ord4 2) = ord5 3 by apply/val_inj.
have e3 : lift (ord5 2) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_U1 a b w1, uniform_U2 a b w2,
     uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_input a b w1 w2 w3 `o uniform_rest a b (ord5 2).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_input /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 2).
exact: inde_RV_comp (uniform_view_input a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_R2 a b.
Proof.
have e0 : lift (ord5 3) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 3) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 3) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 3) (ord4 3) = ord5 4 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
     uniform_U2 a b w2, uniform_U3 a b w3, uniform_R3 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_mask a b w1 w2 w3 `o uniform_rest a b (ord5 3).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 3).
exact: inde_RV_comp (uniform_view_mask a b w1 w2 w3) idfun ind.
Qed.

Lemma uniform_R3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_R3 a b.
Proof.
have e0 : lift (ord5 4) (ord4 0) = ord5 0 by apply/val_inj.
have e1 : lift (ord5 4) (ord4 1) = ord5 1 by apply/val_inj.
have e2 : lift (ord5 4) (ord4 2) = ord5 2 by apply/val_inj.
have e3 : lift (ord5 4) (ord4 3) = ord5 3 by apply/val_inj.
have -> :
  [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
     uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b,
     uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  = uniform_view_mask a b w1 w2 w3 `o uniform_rest a b (ord5 4).
  apply/funext => v.
  by rewrite /comp_RV /uniform_view_mask /uniform_rest /rV_drop !mxE
    e0 e1 e2 e3.
have [ind _ _] := uniform_split a b (ord5 4).
exact: inde_RV_comp (uniform_view_mask a b w1 w2 w3) idfun ind.
Qed.

(* The three weights and the three keys are constants, and a constant is
   independent of everything.  Six of the eleven each-against-the-rest fields
   are therefore discharged without touching the sample space. *)
Lemma uniform_U1_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U2 a b w2,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U1 a b w1.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U2_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U2 a b w2.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_U3_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_U3 a b w3.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_a_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_b a b, uniform_Dk_c a b]
  _|_ uniform_Dk_a a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_b_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_c a b]
  _|_ uniform_Dk_b a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_Dk_c_indep (a b : nat) (w1 w2 w3 : msg a b) :
  P a b |=
    [% uniform_V1 a b, uniform_V2 a b, uniform_V3 a b, uniform_U1 a b w1,
       uniform_U2 a b w2, uniform_U3 a b w3, uniform_R2 a b, uniform_R3 a b,
       uniform_Dk_a a b, uniform_Dk_b a b]
  _|_ uniform_Dk_c a b.
Proof. by rewrite inde_RV_sym; exact: inde_const_RV. Qed.

Lemma uniform_pV1_unif (a b : nat) :
  `p_ (uniform_V1 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 0). Qed.

Lemma uniform_pV2_unif (a b : nat) :
  `p_ (uniform_V2 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 1). Qed.

Lemma uniform_pV3_unif (a b : nat) :
  `p_ (uniform_V3 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 2). Qed.

Lemma uniform_pR2_unif (a b : nat) :
  `p_ (uniform_R2 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 3). Qed.

Lemma uniform_pR3_unif (a b : nat) :
  `p_ (uniform_R3 a b) = fdist_uniform (uniform_card_msg a b).
Proof. by have [_ _ unif] := uniform_split a b (ord5 4). Qed.

(* The counting side at any modulus with the query held fixed: five
   coordinates of the plaintext ring drawn uniformly for the three inputs and
   the two masks, the three weights and the three keys constant. *)
Definition uniform_inputs (a b : nat) (w1 w2 w3 : msg a b) :
    dsdp_random_inputs R a b := {|
  sampleT := uniform_sampleT a b ;
  sample_fdist := uniform_sample_fdist a b ;
  V1 := uniform_V1 a b ;
  V2 := uniform_V2 a b ;
  V3 := uniform_V3 a b ;
  U1 := uniform_U1 a b w1 ;
  U2 := uniform_U2 a b w2 ;
  U3 := uniform_U3 a b w3 ;
  R2 := uniform_R2 a b ;
  R3 := uniform_R3 a b ;
  Dk_a := uniform_Dk_a a b ;
  Dk_b := uniform_Dk_b a b ;
  Dk_c := uniform_Dk_c a b ;
  V1_indep := uniform_V1_indep a b w1 w2 w3 ;
  V2_indep := uniform_V2_indep a b w1 w2 w3 ;
  V3_indep := uniform_V3_indep a b w1 w2 w3 ;
  U1_indep := uniform_U1_indep a b w1 w2 w3 ;
  U2_indep := uniform_U2_indep a b w1 w2 w3 ;
  U3_indep := uniform_U3_indep a b w1 w2 w3 ;
  R2_indep := uniform_R2_indep a b w1 w2 w3 ;
  R3_indep := uniform_R3_indep a b w1 w2 w3 ;
  Dk_a_indep := uniform_Dk_a_indep a b w1 w2 w3 ;
  Dk_b_indep := uniform_Dk_b_indep a b w1 w2 w3 ;
  Dk_c_indep := uniform_Dk_c_indep a b w1 w2 w3 ;
  pV1_unif := uniform_pV1_unif a b ;
  pV2_unif := uniform_pV2_unif a b ;
  pV3_unif := uniform_pV3_unif a b ;
  pR2_unif := uniform_pR2_unif a b ;
  pR3_unif := uniform_pR3_unif a b |}.

End dsdp_inputs_uniform.
