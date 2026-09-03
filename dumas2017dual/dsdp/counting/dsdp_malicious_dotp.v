From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import ring boolp.
Require Import realType_ext realType_ln ssr_ext ssralg_ext fdist proba.
Require Import entropy graphoid.
Require Import spp_proba extra_proba extra_entropy.
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
(* N-party malicious-Alice extraction for the DSDP protocol, generalizing the *)
(* 2D dot product analysis to N-1 dimensions.                                 *)
(*                                                                            *)
(* malicious_n : Alice querying with US = e_1 obtains relay party 1's input   *)
(*   from the dot product, dotp_n ConstUS_n v = v ord0.                       *)
(* US_e1_centropy_VS0_eq0 : that extraction priced as a conditional entropy,  *)
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

(* A corrupted Alice fixing her query to e_1 makes relay party 1's input VS_0
   a function of her view: the protocol output is in the view and equals VS_0,
   so its conditional entropy collapses to zero.  Read against the secrecy
   bounds of dsdp_entropy.v, this is what confines them to an honest query.
   The weights are Alice's to choose, and one choice reads a relay's secret
   off the output.  N-party generic; the 3-party result is the n_relay = 1
   instance. *)
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
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_a : {RV P -> Alice.-key Dec msg}.

(* Bob's input under Alice's query weight U2 and her mask R2, the plaintext of
   her first combine. *)
Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.

(* The aggregate Charlie decrypts, both relay inputs under Alice's two
   masks. *)
Let D3 : {RV P -> msg} := V3 \* U3 \+ R3 \+ D2.

(* The protocol output Alice computes: she strips both of her masks from the
   aggregate and adds her own weighted input.  US_e1_centropy_V2_eq0 is the
   statement that at the query e_1 this value is V2 itself. *)
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

(* The aggregate under Alice's key, Charlie's closing message to her.         *)
Let E_alice_d3   : {RV P -> Alice.-enc msg}   := E' Alice `o D3.

(* Charlie's input under his own key, his opening message to Alice. *)
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' Charlie `o V3.

(* Bob's input under his own key, his opening message to Alice. *)
Let E_bob_v2     : {RV P -> Bob.-enc msg}     := E' Bob `o V2.

(* Alice's full real view in the dot-product model: her key, the output S, her
   own inputs and masks, and the three ciphertext hops. V2 appears only inside
   S and the Bob hop.  The view is the honest one; what US_e1_centropy_V2_eq0
   makes malicious is the query US, not this observation.
   Naming: the [Dotp] token marks the algebraic model, after [Dotp_n_rv],
   separating this view from the AliceView of the hopping axis. *)
Definition AliceDotpView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* A malicious Alice fixing her query to e_1 (U2 = 1, U3 = 0) reads Bob's
   private input V2 off her view, ciphertext hops included; its conditional
   entropy collapses to zero.  The hops are opaque here, so the collapse owes
   nothing to breaking an encryption: the plaintext output alone carries V2.
   3-party instance. *)
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

