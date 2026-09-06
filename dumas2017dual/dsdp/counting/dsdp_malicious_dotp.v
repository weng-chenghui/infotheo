From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import ring boolp.
Require Import realType_ext realType_ln ssr_ext ssralg_ext fdist proba.
Require Import entropy graphoid.
Require Import spp_proba extra_proba extra_entropy.
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
(* N-party malicious-Alice extraction for the DSDP protocol, generalizing the *)
(* 2D dot product analysis to N-1 dimensions.                                 *)
(*                                                                            *)
(* The Dotp token of AliceDotpView marks the algebraic model, after           *)
(* Dotp_n_rv, separating that view from the AliceView of the hopping axis.    *)
(*                                                                            *)
(* malicious_n : Alice querying with US = e_1 obtains relay party 1's input   *)
(*   from the dot product, dotp_n ConstUS_n v = v ord0.                       *)
(* US_e1_centropy_VS0_eq0 : that extraction stated as a conditional entropy,  *)
(*   H(VS_0 | View) = 0 whenever the output is a function of the view.        *)
(* US_e1_centropy_V2_eq0 : its 3-party instance at Alice's dot-product view,  *)
(*   ciphertext hops included.                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

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

(* The dot product of two vectors of n_relay.+1 plaintext letters. *)
Definition dotp_n (x y : {ffun 'I_n_relay.+1 -> msg}) : msg :=
  \sum_(i < n_relay.+1) x i * y i.

(* The dot product of two vector-valued random variables, taken sample by
   sample. *)
Definition Dotp_n_rv (X Y : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) :
    {RV P -> msg} :=
  fun t => dotp_n (X t) (Y t).

(* The first basis vector e_1 = (1, 0, ..., 0) of the plaintext ring. *)
Definition ConstUS_n : {ffun 'I_n_relay.+1 -> msg} :=
  [ffun i => if i == ord0 then 1 else 0].

(* The first basis vector reads the first coordinate off a vector:
   dotp_n ConstUS_n v = v ord0. *)
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

Section malicious_n_centropy.

Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.

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

(* A corrupted Alice who fixes her query to e_1 makes the first relay's
   input a function of her view, so that input keeps zero bits of
   uncertainty given the view.  The weights are Alice's to choose, and
   this choice reads a relay's input off the protocol output, which is
   what restricts the secrecy bounds of dsdp_entropy.v to an honest
   query.  [N-party] *)
Theorem US_e1_centropy_VS0_eq0 {A : finType}
    (View : {RV P -> A}) (g : A -> msg)
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}})
    (US_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 n_relay)
    (output_in_view :
       @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS = g `o View) :
  `H( (fun t => VS t ord0) | View ) = 0.
Proof.
have disc : @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS
            = (fun t => VS t ord0).
  rewrite US_e1 /Dotp_n_rv; apply/funext => t /=.
  exact: dotp_n_e1.
have key : (fun t => VS t ord0) = g `o View by rewrite -disc.
rewrite key; exact: centropy_RV_comp0.
Qed.

End malicious_n_centropy.

Section malicious_3party.

Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.

Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

(* One 3-party run at this modulus, on the counting side.  The theorem below
   reads a relay's input off Alice's view at a query she chooses, so it needs
   the run's random inputs and none of the record's independence fields. *)
Variable I : dsdp_random_inputs R p_minus_2 q_minus_2.

Local Notation T := (sampleT I).
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

(* Bob's input under Alice's query weight U2 and her mask R2, the plaintext of
   her first combine. *)
Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.

(* The aggregate Charlie decrypts, both relay inputs under Alice's two
   masks. *)
Let D3 : {RV P -> msg} := V3 \* U3 \+ R3 \+ D2.

(* The protocol output Alice computes: she strips both of her masks from
   the aggregate and adds her own weighted input.  At the query e_1 this
   value is Bob's input V2 itself. *)
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

(* The aggregate under Alice's key, Charlie's closing message to her.         *)
Let E_alice_d3   : {RV P -> Alice.-enc msg}   := E' Alice `o D3.

(* Charlie's input under his own key, his opening message to Alice. *)
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' Charlie `o V3.

(* Bob's input under his own key, his opening message to Alice. *)
Let E_bob_v2     : {RV P -> Bob.-enc msg}     := E' Bob `o V2.

(* Alice's whole honest view in the dot-product model: her key, the
   output S, her own input and her three weights, her two masks, and the
   three ciphertexts of the run.  Bob's input reaches this view only
   inside S and inside his own ciphertext. *)
Definition AliceDotpView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* A corrupted Alice who fixes her query to U2 = 1 and U3 = 0 reads Bob's
   input off her view, which then keeps zero bits of uncertainty about
   it.  The three ciphertexts stay opaque, so the plaintext output alone
   carries V2 and the collapse owes nothing to breaking an encryption.
   [3-party] *)
Theorem US_e1_centropy_V2_eq0 :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  `H( V2 | AliceDotpView ) = 0.
Proof.
move=> HU2 HU3.
pose VS : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then V2 t else V3 t].
pose US : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then U2 t else U3 t].
pose g := fun o : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg
                    * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg) =>
  let '(_, s, _, u1, _, _, _, _, _, _, _) := o in
  let '(_, _, v1, _, _, _, _, _, _, _, _) := o in
  s - v1 * u1.
have HVS0 : (fun t => VS t ord0) = V2.
  by apply/funext => t; rewrite /VS ffunE eqxx.
have HUS_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 1.
  rewrite /US /ConstUS_n; apply/funext => t; apply/ffunP => i.
  by rewrite !ffunE HU2 HU3 /=; case: (i == ord0).
have Hout : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS
             = g `o AliceDotpView.
  rewrite (_ : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = (fun t => V2 t)).
    rewrite /g /AliceDotpView /comp_RV /S /D3 /D2.
    by apply/funext => t /=; rewrite HU2 HU3 /=; ring.
  rewrite HUS_e1 /Dotp_n_rv.
  by apply/funext => t /=; rewrite dotp_n_e1 /VS ffunE eqxx.
have := US_e1_centropy_VS0_eq0 (View := AliceDotpView) (g := g)
          (US := US) (VS := VS) HUS_e1 Hout.
by rewrite HVS0.
Qed.

End malicious_3party.

