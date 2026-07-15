(* Feasibility probe for the sound malicious-leak reconstruction.
   De-risks: (A) generic N-party full-leakage theorem via centropy_RV_comp0;
             (B) concrete 3-party view with ciphertext hops, recovery + ring;
             (C) ffun wrapping of (V2,V3)/(U2,U3) for the n_relay=1 instance.
   Pure Infotheo path (no SSProve). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum lra.
From Stdlib Require Import Utf8.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import homomorphic_encryption.
Require Import dsdp_program dsdp_entropy dsdp_view_independence.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(* ============ Probe A: generic N-party full-leakage theorem ============ *)
Section probe_generic.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation m := (p_minus_2.+2 * q_minus_2.+2).
Local Notation msg := 'Z_m.
Variable n_relay : nat.

Theorem probe_leaks_secret {A : finType}
    (View : {RV P -> A}) (g : A -> msg)
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}})
    (US_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 n_relay)
    (output_in_view :
       @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS = g `o View) :
  `H( (fun t => VS t ord0) | View ) = 0.
Proof.
have disc : @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS
            = (fun t => VS t ord0).
  rewrite US_e1 /Dotp_n_rv; apply: boolp.funext => t /=.
  exact: dotp_n_e1.
have key : (fun t => VS t ord0) = g `o View by rewrite -disc.
rewrite key; exact: centropy_RV_comp0.
Qed.

End probe_generic.

(* ============ Probe B: concrete 3-party view with ciphertext hops ============ *)
Section probe_concrete.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation m := (p_minus_2.+2 * q_minus_2.+2).
Local Notation msg := 'Z_m.

Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_a : {RV P -> Alice.-key Dec msg}.

Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.
Let D3 : {RV P -> msg} := V3 \* U3 \+ R3 \+ D2.
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

Let E_alice_d3   : {RV P -> Alice.-enc msg}   := E' Alice `o D3.
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' Charlie `o V3.
Let E_bob_v2     : {RV P -> Bob.-enc msg}     := E' Bob `o V2.

Let AliceView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

Theorem probe_compromised_leaks_V2 :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  `H( V2 | AliceView ) = 0.
Proof.
move=> HU2 HU3.
pose g := fun o : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg
                    * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg) =>
  let '(_, s, _, u1, _, _, _, _, _, _, _) := o in
  let '(_, _, v1, _, _, _, _, _, _, _, _) := o in
  s - v1 * u1.
have key : V2 = g `o AliceView.
  rewrite /g /AliceView /comp_RV /S /D3 /D2.
  apply: boolp.funext => t /=.
  rewrite HU2 HU3 /=.
  ring.
rewrite key; exact: centropy_RV_comp0.
Qed.

End probe_concrete.

(* ============ Probe C: ffun wrapping for the n_relay=1 instance ============ *)
Section probe_ffun_wrap.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation m := (p_minus_2.+2 * q_minus_2.+2).
Local Notation msg := 'Z_m.

Variables (V2 V3 U2 U3 : {RV P -> msg}).

(* wrap the relay pair as an 'I_2 ffun RV *)
Let VSwrap : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then V2 t else V3 t].
Let USwrap : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then U2 t else U3 t].

(* under U2=1,U3=0 the wrapped query is the const ConstUS_n at n_relay=1, and the
   wrapped dot product is V2 *)
Lemma probe_wrap_is_e1 :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  USwrap = fun _ => @ConstUS_n p_minus_2 q_minus_2 1.
Proof.
move=> HU2 HU3; rewrite /USwrap /ConstUS_n.
apply: boolp.funext => t; apply/ffunP => i.
rewrite !ffunE HU2 HU3 /=.
by case: (i == ord0).
Qed.

Lemma probe_wrap_dotp :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  @Dotp_n_rv R T P p_minus_2 q_minus_2 1 USwrap VSwrap = (fun t => V2 t).
Proof.
move=> HU2 HU3.
rewrite (_ : USwrap = fun _ => @ConstUS_n p_minus_2 q_minus_2 1);
  last exact: probe_wrap_is_e1.
rewrite /Dotp_n_rv; apply: boolp.funext => t /=.
rewrite dotp_n_e1 /VSwrap ffunE.
by rewrite eqxx.
Qed.

End probe_ffun_wrap.

(* ===== Probe D: 3-party theorem as a FORMAL INSTANCE of the generic one ===== *)
Section probe_instance.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation m := (p_minus_2.+2 * q_minus_2.+2).
Local Notation msg := 'Z_m.

Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_a : {RV P -> Alice.-key Dec msg}.
Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.
Let D3 : {RV P -> msg} := V3 \* U3 \+ R3 \+ D2.
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.
Let AliceView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3,
     E' Alice `o D3, E' Charlie `o V3, E' Bob `o V2].

Theorem probe_leaks_V2_via_instance :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  `H( V2 | AliceView ) = 0.
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
  by apply: boolp.funext => t; rewrite /VS ffunE eqxx.
have HUS_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 1.
  rewrite /US /ConstUS_n; apply: boolp.funext => t; apply/ffunP => i.
  by rewrite !ffunE HU2 HU3 /=; case: (i == ord0).
have Hout : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = g `o AliceView.
  rewrite (_ : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = (fun t => V2 t)).
    rewrite /g /AliceView /comp_RV /S /D3 /D2.
    by apply: boolp.funext => t /=; rewrite HU2 HU3 /=; ring.
  rewrite HUS_e1 /Dotp_n_rv.
  by apply: boolp.funext => t /=; rewrite dotp_n_e1 /VS ffunE eqxx.
have := probe_leaks_secret (View := AliceView) (g := g) (US := US) (VS := VS)
          HUS_e1 Hout.
by rewrite HVS0.
Qed.

End probe_instance.
