(* DSDP main results — the headline security theorems.

   This file centralizes the headline theorems of the DSDP development. Each
   theorem's full proof is presented here over a cloned copy of its source
   section context; the supporting machinery stays in the axis files and is
   referenced, not duplicated. The file mixes generic N-party results with
   their 3-party DSDP instances; each theorem's comment states its party
   scope.

   The two axes price secrecy in different currencies, and the distinction is
   load-bearing. The counting axis conditions on plaintexts and its bounds are
   unconditional: they hold against an adversary of any running time. The
   game-hopping axis conditions on the ciphertext-carrying view and its bounds
   carry two IND-CPA advantage terms, one at Bob's key and one at Charlie's;
   they say nothing until those advantages are argued small. A bound summing
   an information-theoretic term with an assumption-conditional one is written
   so the two summands stay distinguishable.

   Information-theoretic (counting axis, unconditional)
     dsdp_centropy_uniform : H(V2,V3 | view) = log m  [3-party]
     dsdp_centropy_uniform_n : H(V | view) = log (m^n)  [N-party]
     US_n_compromised_leaks_secret : corrupted Alice leaks a relay's input,
       H(VS_0 | View) = 0  [N-party]
     US_compromised_leaks_V2 : corrupted Alice leaks Bob's V2, H(V2 | View) = 0
       [3-party instance of US_n_compromised_leaks_secret]
     bob_privacy_V1 / charlie_privacy_V1 : H(V1 | RelayView) = log m > 0:
       a corrupted relay learns nothing about Alice's input V1  [3-party]
     bob_privacy_V3 : H(V3 | BobView) = log m > 0: a corrupted Bob learns
       nothing about Charlie's input V3 (R3 one-time-pad masking)  [3-party]
     charlie_privacy_V2 : H(V2 | CharlieView) = log m > 0: a corrupted Charlie
       learns nothing about Bob's input V2 (R2 one-time-pad masking)  [3-party]

   Corrupted Alice at her hopping tuple (fdist axis, IND-CPA-conditional)
     dsdp_alice_guess_fdist_V2_real_le : a predictor of Bob's input succeeds
       with probability at most 1/#|plain| plus the two hop advantages
     dsdp_alice_unpredictability_fdist_ge /
     dsdp_alice_predictor_unpredictability_fdist_ge : the same bound in
       negative-logarithm form, log #|plain| less a correction in the two
       advantages
     dsdp_alice_sim_advantage_fdist_le : every Boolean test separates the real
       joint law from the simulator's by at most the two hop advantages
     dsdp_alice_guess_fdist_view_le : the guessing bound at Alice's whole
       view, her two outgoing combines and her final decrypt included

   The same bounds at the executed fifteen-round piSMC trace
     dsdp_alice_guess_fdist_trace_V2_real_le
     dsdp_alice_trace_predictor_unpredictability_fdist_ge
     dsdp_alice_trace_sim_advantage_fdist_le
     centropy_AliceTrace_AliceRealTuple /
     centropy_AliceView_AliceRealTuple : conditioning on the trace, on the
       view, or on the tuple leaves the same uncertainty about Bob's input,
       so the hop ladder prices all three observations at once

   The same bounds gated on an adversary class
     dsdp_alice_guess_fdist_trace_V2_admissible_le /
     dsdp_alice_guess_fdist_trace_V2_admissible_pq_le : both hop advantages
       charged to the single epsilon of an indcpa_epsilon_assumption, under
       the assumed premise that the two reduction adversaries are in its
       class
     bob_charlie_trace_guess_epsilon_decrypt_ge /
     bob_trace_guess_epsilon_decrypt_ge : an adversary holding Bob's private
       key forces the two advantages to sum to at least 1 - 1/#|plain|, and
       Bob's alone to reach it, which is why the class gate cannot be widened
       to every adversary

   Shannon uncertainty about Bob's input, by conditioner
     centropy_V2_AliceTrace_eq0 : zero at her executed trace, which the trace
       determines
     centropy_V2_Sout_logm / centropy_V2_all_zero_logm : log #|plain| bits at
       the leaked output and at the all-zero endpoint of the hop ladder *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals.

From Stdlib Require Import Utf8.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy extra_proba extra_algebra extra_entropy rouche_capelli.
Require Import entropy_fiber.
Require Import homomorphic_encryption.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import dsdp_malicious_dotp.
Require Import indcpa_game.
Require Import dsdp_alice_fdist_secrecy dsdp_alice_trace_link.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(* ================================================================= *)
(* Information-theoretic party privacy (counting axis)               *)
(* ================================================================= *)

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

(* dsdp_centropy_uniform — conditioning on Alice's inputs and the output
   (V1, U1, U2, U3, S), the plaintext residual (not Alice's full view, which
   also carries her key, masks, and the ciphertext hops), the relay private
   inputs (V2, V3) retain log m bits of uncertainty. The counting axis
   conditions on plaintexts only; the ciphertext-carrying view is the
   fdist_hopping leg's business (the guessing triangle).  [3-party] *)
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

(* The final relay's weight, read off the conditioning tuple.  The two
   hypotheses of dsdp_centropy_uniform_n pin it strictly between zero and
   min(p, q), which makes it invertible modulo m, and that invertibility is
   what leaves the relay inputs uniform given the view. *)
Definition last_relay_weight (c : CondT_n) : msg :=
  (let '(_, _, u_rel, _) := c in u_rel) ord_max.

(* dsdp_centropy_uniform_n — conditioning on the N-party view, the relay private
   inputs retain log (m ^ n_relay) bits of uncertainty.  [N-party] *)
Theorem dsdp_centropy_uniform_n :
  (forall t, (0 < val (last_relay_weight (CondRV t)))%N) ->
  (forall t, (val (last_relay_weight (CondRV t)) < minn p q)%N) ->
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

Section dsdp_malicious_n.
(* cloned context of Section malicious_n *)
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
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.

(* US_n_compromised_leaks_secret — a corrupted Alice fixing her query to e_1
   makes relay party 1's input VS_0 a function of her view: the protocol output
   is in the view and equals VS_0, so its conditional entropy collapses to zero.
   N-party generic; the 3-party result is the n_relay = 1 instance. *)
Theorem US_n_compromised_leaks_secret {A : finType}
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

End dsdp_malicious_n.

Section dsdp_malicious_3party.
(* 3-party instance of US_n_compromised_leaks_secret at n_relay = 1 *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
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
   aggregate and adds her own weighted input.  US_compromised_leaks_V2 is the
   statement that at the query e_1 this value is V2 itself. *)
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

(* The aggregate under Alice's key, Charlie's closing message to her. *)
Let E_alice_d3   : {RV P -> Alice.-enc msg}   := E' Alice `o D3.

(* Charlie's input under his own key, his opening message to Alice. *)
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' Charlie `o V3.

(* Bob's input under his own key, his opening message to Alice. *)
Let E_bob_v2     : {RV P -> Bob.-enc msg}     := E' Bob `o V2.

(* Alice's full real view in the dot-product model: her key, the output S, her
   own inputs and masks, and the three ciphertext hops. V2 appears only inside
   S and the Bob hop.  The view is the honest one; what US_compromised_leaks_V2
   makes malicious is the query US, not this observation.
   Naming: the [Dotp] token marks the algebraic model, after [Dotp_n_rv],
   separating this view from the AliceView of the hopping axis. *)
Definition AliceDotpView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* US_compromised_leaks_V2 — a malicious Alice fixing her query to e_1
   (U2 = 1, U3 = 0) reads Bob's private input V2 off her view, ciphertext hops
   included; its conditional entropy collapses to zero. 3-party instance. *)
Theorem US_compromised_leaks_V2 :
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
  by apply: boolp.funext => t; rewrite /VS ffunE eqxx.
have HUS_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 1.
  rewrite /US /ConstUS_n; apply: boolp.funext => t; apply/ffunP => i.
  by rewrite !ffunE HU2 HU3 /=; case: (i == ord0).
have Hout : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS
             = g `o AliceDotpView.
  rewrite (_ : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = (fun t => V2 t)).
    rewrite /g /AliceDotpView /comp_RV /S /D3 /D2.
    by apply: boolp.funext => t /=; rewrite HU2 HU3 /=; ring.
  rewrite HUS_e1 /Dotp_n_rv.
  by apply: boolp.funext => t /=; rewrite dotp_n_e1 /VS ffunE eqxx.
have := US_n_compromised_leaks_secret (View := AliceDotpView) (g := g)
          (US := US) (VS := VS) HUS_e1 Hout.
by rewrite HVS0.
Qed.

End dsdp_malicious_3party.

(* ================================================================= *)
(* Corrupted-relay secrecy of Alice's input (counting axis)          *)
(* ================================================================= *)

Section dsdp_relay_secrecy_v1.
(* Alice's input V1 occurs in no protocol message; each corrupted relay's full
   real view is a deterministic function of inputs independent of V1, so its
   conditional entropy about V1 stays at log m. *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

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

(* CharlieView_indep_V1 — Charlie's view is independent of Alice's input V1. *)
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
  by rewrite (inde_cond_entropy BobView_indep_V1) pV1_unif entropy_uniform card_msg.
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
  by rewrite (inde_cond_entropy CharlieView_indep_V1) pV1_unif entropy_uniform card_msg.
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

(* The joint masked-input independence, assembled by the graphoid mixing rule. *)
Let bob_inputs_indep_V3 : P |= [% Dk_b, V2, D2, VU3R] _|_ V3.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [% Dk_b, V2, D2]) (Y := V3) (Z := unit_RV P) (W := VU3R)).
split.
- by apply cinde_RV_unit; exact: clean_indep_V3_VU3R.
- by apply cinde_RV_unit; rewrite inde_RV_sym; exact: VU3R_indep_V3.
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

(* bob_privacy_V3 — Bob's view carries log m bits of uncertainty about Charlie's
   input V3, hence a corrupted Bob learns nothing about V3.  [3-party] *)
Theorem bob_privacy_V3 :
  `H(V3 | BobView) = log (m%:R : R) /\ `H(V3 | BobView) > 0.
Proof.
have H_logm : `H(V3 | BobView) = log (m%:R : R).
  by rewrite (inde_cond_entropy BobView_indep_V3) pV3_unif entropy_uniform card_msg.
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

(* CharlieView_indep_V2 — Charlie's full view is independent of Bob's input V2. *)
Let CharlieView_indep_V2 : P |= CharlieView _|_ V2.
Proof.
apply cinde_RV_unit.
apply (mixing_rule (X := [%Dk_c, V3]) (Y := V2) (Z := unit_RV P) (W := E_charlie_d3)).
split.
- by apply cinde_RV_unit; exact: Dk_c_V3_indep_V2_E.
- by apply cinde_RV_unit; rewrite inde_RV_sym; exact: E_charlie_d3_indep_V2.
Qed.

(* charlie_privacy_V2 — Charlie's view carries log m bits of uncertainty about
   Bob's input V2, hence a corrupted Charlie learns nothing about V2.  [3-party] *)
Theorem charlie_privacy_V2 :
  `H(V2 | CharlieView) = log (m%:R : R) /\ `H(V2 | CharlieView) > 0.
Proof.
have H_logm : `H(V2 | CharlieView) = log (m%:R : R).
  by rewrite (inde_cond_entropy CharlieView_indep_V2) pV2_unif entropy_uniform card_msg.
split; first exact: H_logm.
rewrite H_logm -log1; apply: ltr_log; first by [].
by rewrite ltr1n.
Qed.

End dsdp_relay_secrecy_v1.

(* ================================================================= *)
(* Corrupted-Alice secrecy under IND-CPA hopping (fdist axis)        *)
(* ================================================================= *)

Section dsdp_alice_hop_secrecy.
(* cloned context of Section dsdp_alice_fdist_secrecy *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variable pkey_of_party : party_id -> pub_key AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Hypothesis u3_unit : u3 \is a GRing.unit.

Local Notation P := (alice_sample_fdist (R:=R) AHE card_renc).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation hop_tupleT := (dsdp_alice_hop_tupleT AHE Renc).
Local Notation AliceHopTuple i :=
  (AliceHopTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3 i).
Local Notation AliceView :=
  (AliceView (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation alice_view_of_hop_tuple :=
  (alice_view_of_hop_tuple (AHE:=AHE) rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation alice_view_of_hop_tupleE :=
  (alice_view_of_hop_tupleE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation bob_pkey := (bob_pkey pkey_of_party).
Local Notation charlie_pkey := (charlie_pkey pkey_of_party).
Local Notation predictor := (predictor AHE).
Local Notation alice_hop_jointT := (alice_hop_jointT AHE Renc).
Local Notation alice_viewT := (alice_viewT AHE Renc).
Local Notation AliceRealTuple :=
  (AliceRealTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation bob_view_adversary :=
  (bob_view_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation charlie_view_adversary :=
  (charlie_view_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation bob_challenge_adversary :=
  (bob_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation charlie_challenge_adversary :=
  (charlie_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation hop0_advantageE :=
  (hop0_advantageE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation hop1_advantageE :=
  (hop1_advantageE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation alice_hop_game_successE :=
  (alice_hop_game_successE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation guess_event_jointE :=
  (guess_event_jointE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation Sout := (Sout (R:=R) (AHE:=AHE) card_renc v1 u1 u2 u3).
Local Notation AliceSpectator :=
  (AliceSpectator (R:=R) (AHE:=AHE) card_renc rand_of_renc pkey_of_party).
Local Notation alice_spectator_cinde :=
  (alice_spectator_cinde (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation guess_all_zero_le_invm :=
  (guess_all_zero_le_invm (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3_unit).
Local Notation alice_ideal_joint :=
  (alice_ideal_joint (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation alice_ideal_jointE :=
  (alice_ideal_jointE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation alice_predictor_unpredictability :=
  (alice_predictor_unpredictability (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).

Let card_plain_gt0 : (0 < #|plain AHE|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.

(* A predictor reading Alice's real hopping tuple matches Bob's input with
   probability at most uniform guessing over the plaintext space plus the
   advantages of the two hop reductions.  The first summand is
   information-theoretic and unconditional; the two others are
   assumption-conditional, one against Bob's key and one against Charlie's. *)
Theorem dsdp_alice_guess_fdist_V2_real_le
    (predict : predictor hop_tupleT) :
  Pr P [set t | (predict `o AliceRealTuple) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon bob_pkey
           (bob_challenge_adversary (guess_test predict))
       + indcpa_fdist_epsilon charlie_pkey
           (charlie_challenge_adversary (guess_test predict)).
Proof.
rewrite /AliceRealTuple guess_event_jointE -hop0_advantageE -hop1_advantageE.
rewrite -addrA -lerBlDl.
rewrite !alice_hop_game_successE.
apply: le_trans (lerB (lexx _) _) _; last first.
  exact: le_trans (ler_norm _) (ler_distD _ _ _).
by rewrite -guess_event_jointE; exact: guess_all_zero_le_invm.
Qed.

Local Notation bob_guess_epsilon :=
  (bob_guess_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).
Local Notation charlie_guess_epsilon :=
  (charlie_guess_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_party v1 u1 u2 u3).

(* The negative logarithm of a predictor's success probability on Alice's
   real hopping tuple is at least the log of the plaintext-space cardinality
   less a correction in the two hop advantages.  As the advantages go to
   zero the correction vanishes and the bound becomes the value uniform
   guessing would give. *)
Theorem dsdp_alice_unpredictability_fdist_ge (predict : predictor hop_tupleT)
    (Hpos : 0 < Pr P [set t | (predict `o AliceRealTuple) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R
               * (bob_guess_epsilon predict + charlie_guess_epsilon predict))
  <= - log (Pr P [set t | (predict `o AliceRealTuple) t == V2 t]).
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R) by rewrite ltr0n card_plain_gt0.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R
                        * (bob_guess_epsilon predict
                           + charlie_guess_epsilon predict) :> R).
  apply: ltr_pwDl ltr01 (mulr_ge0 (ler0n _ _) _).
  by rewrite addr_ge0 // /bob_guess_epsilon /charlie_guess_epsilon
             /indcpa_fdist_epsilon normr_ge0.
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

Local Notation "'`H_unp^{' g '}'" :=
  (alice_predictor_unpredictability g)
  (at level 0, g at level 200,
   format "'`H_unp^{' g '}'").

(* The same bound read through the named unpredictability quantity. *)
Theorem dsdp_alice_predictor_unpredictability_fdist_ge
    (predict : predictor hop_tupleT)
    (Hpos : 0 < Pr P [set t | (predict `o AliceRealTuple) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R
               * (bob_guess_epsilon predict + charlie_guess_epsilon predict))
  <= `H_unp^{predict}.
Proof.
exact: dsdp_alice_unpredictability_fdist_ge.
Qed.

(* Any Boolean test separates the real joint law of the honest inputs and
   Alice's hopping tuple from the ideal law built by the simulator by at most
   the sum of the two IND-CPA advantages.  Real world is hop 0, ideal world
   is hop 2, and the ladder prices the distance one hop at a time. *)
Theorem dsdp_alice_sim_advantage_fdist_le
    (D : distinguisher alice_hop_jointT) :
  `| Pr (`p_ [% V2, V3, AliceRealTuple]) [set x | D x]
     - Pr alice_ideal_joint [set x | D x] |
  <= indcpa_fdist_epsilon bob_pkey (bob_challenge_adversary D)
     + indcpa_fdist_epsilon charlie_pkey (charlie_challenge_adversary D).
Proof.
rewrite /AliceRealTuple alice_ideal_jointE -hop0_advantageE -hop1_advantageE.
rewrite !alice_hop_game_successE.
exact: ler_distD.
Qed.

(* Alice's whole view obeys the hopping-tuple bound: her two outgoing
   combines and the plaintext of her final decrypt-on-receive are
   deterministic functions of the tuple, so reading them adds no term. *)
Corollary dsdp_alice_guess_fdist_view_le
    (predict : predictor alice_viewT) :
  Pr P [set t | (predict `o AliceView) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon bob_pkey (bob_view_adversary predict)
       + indcpa_fdist_epsilon charlie_pkey (charlie_view_adversary predict).
Proof.
by rewrite alice_view_of_hop_tupleE; exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

(* Conditioned on the leaked output alone, Bob's input still carries
   log #|plain AHE| bits of uncertainty, which is what it carries with no
   conditioning at all.  The leaked output is one affine equation in the two
   secret inputs, so it cuts the sample space to a fiber on which Bob's input
   is still uniform.
   This and the 1/#|plain AHE| term of guess_all_zero_le_invm descend from
   one fact, alice_V2_cond_Sout: the conditional law of Bob's input given the
   leaked output is exactly uniform.  Neither statement is derived from the
   other, and this entropy reading holds at this conditioner alone; at
   Alice's executed trace the same quantity is zero, as
   centropy_V2_AliceTrace_eq0 below records.
   Naming: [logm] names the value the quantity takes, the logarithm of the
   plaintext-space cardinality, as [invm] names its reciprocal in
   [guess_all_zero_le_invm]. *)
Lemma centropy_V2_Sout_logm :
  `H( V2 | Sout ) = log (#|plain AHE|%:R : R).
Proof.
rewrite centropy_RVE'.
transitivity (\sum_(s in plain AHE)
                `Pr[ Sout = s ] * log (#|plain AHE|%:R : R)); last first.
  by rewrite -big_distrl /= sum_pfwd1 mul1r.
apply: eq_bigr => s _.
have [->|Hs] := eqVneq `Pr[ Sout = s ] 0; first by rewrite !mul0r.
congr (_ * _); rewrite -[in RHS](cardsT (plain AHE)).
apply: centropy1_uniform_over_set => //.
- by move=> a _; rewrite cardsT; exact: (alice_V2_cond_Sout u3_unit).
- by move=> a; rewrite in_setT.
Qed.

(* Conditioned on Alice's all-zero view, Bob's input carries the same
   log #|plain AHE| bits it carries given the leaked output alone.  The
   all-zero endpoint of the hop ladder is where the non-degenerate Shannon
   statement holds: both ciphertext slots encrypt zero, so the leaked output
   is the only channel from V2 into the view, and adjoining the spectator
   coordinates costs nothing.  At Alice's executed trace the same quantity is
   zero instead, as centropy_V2_AliceTrace_eq0 below records.
   The guessing-side fact at this same endpoint is guess_all_zero_le_invm,
   which bounds every predictor's success by 1/#|plain AHE|.  The two are
   different quantities: this one averages the conditional entropy over the
   conditioner, that one bounds a probability, and neither is derived from
   the other.
   Naming: [all_zero] names the endpoint, as in [guess_all_zero_le_invm], and
   [logm] the value, as in [centropy_V2_Sout_logm]. *)
Lemma centropy_V2_all_zero_logm :
  `H( V2 | AliceHopTuple 2 ) = log (#|plain AHE|%:R : R).
Proof.
have -> : AliceHopTuple 2
        = @alice_hop_tuple_of_spectator AHE Renc `o [% AliceSpectator, Sout]
  by [].
rewrite (can_centropy_eq (@alice_hop_tuple_of_spectatorK AHE Renc)).
by rewrite (cinde_centropy_eq alice_spectator_cinde) centropy_V2_Sout_logm.
Qed.

End dsdp_alice_hop_secrecy.

(* ================================================================= *)
(* The same bounds at Alice's executed piSMC trace                   *)
(* ================================================================= *)

Section dsdp_alice_trace_secrecy.
(* cloned context of Section dsdp_alice_trace_rv *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Hypothesis u3_unit : u3 \is a GRing.unit.
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

Local Notation P := (alice_sample_fdist (R:=R) AHE card_renc).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE).
Local Notation hop_tupleT := (dsdp_alice_hop_tupleT AHE Renc).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceHopTuple i :=
  (AliceHopTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3 i).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) (AHE:=AHE) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation dsdp_trace_of_hop_tuple :=
  (dsdp_trace_of_hop_tuple rand_of_renc v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation dsdp_trace_of_hop_tupleE :=
  (dsdp_trace_of_hop_tupleE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation bob_challenge_adversary :=
  (bob_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation charlie_challenge_adversary :=
  (charlie_challenge_adversary (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation predictor := (predictor AHE).
Local Notation dsdp_traceT := (dsdp_traceT AHE).
Local Notation trace_jointT := (trace_jointT AHE).
Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation bob_trace_guess_epsilon :=
  (bob_trace_guess_epsilon (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation charlie_trace_guess_epsilon :=
  (charlie_trace_guess_epsilon (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation alice_ideal_joint :=
  (alice_ideal_joint (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation alice_trace_ideal_joint :=
  (alice_trace_ideal_joint (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation dsdp_alice_trace_simulator :=
  (dsdp_alice_trace_simulator (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation dsdp_alice_simulator :=
  (dsdp_alice_simulator (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk).
Local Notation alice_trace_predictor_unpredictability :=
  (alice_trace_predictor_unpredictability (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation alice_trace_guess_pr :=
  (alice_trace_guess_pr (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation bob_trace_decrypt_predictor :=
  (bob_trace_decrypt_predictor rand_of_renc dk_a dk_b dk_c w_rc2).
Local Notation alice_trace_decode_V2E :=
  (alice_trace_decode_V2E (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* A predictor reading Alice's executed fifteen-round trace matches Bob's
   input no better than one reading her hopping tuple: the trace is a
   deterministic function of the tuple, so the tuple bound transfers with no
   extra term. *)
Theorem dsdp_alice_guess_fdist_trace_V2_real_le
    (predict : predictor dsdp_traceT) :
  Pr P [set t | (predict `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_fdist_epsilon (pkey_of_dk Bob)
           (bob_trace_adversary (guess_test predict))
       + indcpa_fdist_epsilon (pkey_of_dk Charlie)
           (charlie_trace_adversary (guess_test predict)).
Proof.
rewrite dsdp_trace_of_hop_tupleE.
exact: (dsdp_alice_guess_fdist_V2_real_le card_renc rand_of_renc
          pkey_of_dk v1 u1 u2 u3_unit
          (predict \o dsdp_trace_of_hop_tuple)).
Qed.

(* The trace guessing bound with both hop advantages replaced by the single
   epsilon an adversary-class assumption gates.  The statement spends three
   currencies.  The right-hand side sums two of them: one over the
   plaintext-space cardinality, information-theoretic and unconditional; and
   twice the assumption's epsilon, conditional on that assumption, pricing
   the two ciphertext replacements at Bob's key and at Charlie's.  The third
   is the two premises, conditional on the class and assumed rather than
   proved.
   bob_trace_guess_epsilon_decrypt_ge below shows that an assumption whose
   classifier admits every adversary is forced to posit an epsilon of at
   least 1 - 1/#|plain AHE|, which is why the class restriction is what makes
   this bound satisfiable.
   Naming: extends [dsdp_alice_guess_fdist_trace_V2_real_le] with the
   [admissible] variant token before [le]; kept long to preserve the family
   grouping. *)
Corollary dsdp_alice_guess_fdist_trace_V2_admissible_le
    (A : indcpa_epsilon_assumption) (predict : predictor dsdp_traceT) :
  indcpa_admissible A (bob_trace_adversary (guess_test predict)) ->
  indcpa_admissible A (charlie_trace_adversary (guess_test predict)) ->
  alice_trace_guess_pr predict
    <= (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A.
Proof.
move=> Hb Hc.
apply: le_trans (dsdp_alice_guess_fdist_trace_V2_real_le predict) _.
rewrite mulr_natl mulr2n addrA.
by rewrite lerD // ?lerD2l //; exact: indcpa_admissible_epsilon_le.
Qed.

(* The decryptor succeeds on every sample. *)
Let decrypt_guess_prE :
  Pr P [set t | (bob_trace_decrypt_predictor `o AliceTrace) t == V2 t] = 1.
Proof.
rewrite -alice_trace_decode_V2E.
rewrite (_ : finset _ = [set: dsdp_alice_sampleT AHE Renc]) ?Pr_setT //.
by apply/setP => t; rewrite !inE eqxx.
Qed.

(* The two hop advantages an adversary holding Bob's private key buys sum to
   at least 1 - 1/#|plain AHE|: the hop ladder's epsilons cannot all be small
   for every adversary, so the class gate of the corollary above is
   load-bearing rather than decoration.
   Naming: names the two epsilons summed, the predictor that realizes them,
   and the direction of the inequality; the right-hand side is a sum with no
   single head symbol, so the name merges the two summands' heads. *)
Corollary bob_charlie_trace_guess_epsilon_decrypt_ge :
  1 - (#|plain AHE|%:R : R)^-1
  <= bob_trace_guess_epsilon bob_trace_decrypt_predictor
     + charlie_trace_guess_epsilon bob_trace_decrypt_predictor.
Proof.
(* The rewrite is confined to the left-hand side: 1 also occurs inside
   #|plain AHE|%:R on the right. *)
rewrite lerBlDl addrA -[X in X <= _]decrypt_guess_prE.
exact: dsdp_alice_guess_fdist_trace_V2_real_le.
Qed.

(* Bob's key alone already carries that whole gap.  The decryptor separates
   the two branches of the hop-0 challenge: at the real bit it reads Bob's
   input off the challenge ciphertext and is right always, and at the zero
   bit it reads zero and is right only on the fiber the leaked output leaves,
   of mass at most 1/#|plain AHE|.  The Charlie-key term of the corollary
   above is therefore not needed: this consumes the hop-0 half of the ladder
   alone, never the composite two-hop bound
   dsdp_alice_guess_fdist_trace_V2_real_le.
   Naming: as above, with the single epsilon the bound charges. *)
Corollary bob_trace_guess_epsilon_decrypt_ge :
  1 - (#|plain AHE|%:R : R)^-1
  <= bob_trace_guess_epsilon bob_trace_decrypt_predictor.
Proof.
pose lifted := bob_trace_decrypt_predictor \o dsdp_trace_of_hop_tuple.
have Hlift : `| Pr P [set t | (lifted `o AliceHopTuple 0) t == V2 t]
              - Pr P [set t | (lifted `o AliceHopTuple 1) t == V2 t] |
            = bob_trace_guess_epsilon bob_trace_decrypt_predictor.
  by rewrite 2!guess_event_jointE -2!alice_hop_game_successE hop0_advantageE.
have HV2 : lifted `o AliceHopTuple 0 = V2.
  by rewrite alice_trace_decode_V2E dsdp_trace_of_hop_tupleE.
have H0 : Pr P [set t | (lifted `o AliceHopTuple 0) t == V2 t] = 1.
  rewrite HV2 (_ : finset _ = [set: dsdp_alice_sampleT AHE Renc]) ?Pr_setT //.
  by apply/setP => t; rewrite !inE eqxx.
(* guess_all_zero_le_invm is stated at hop 2 and used here at hop 1.  Two
   reductions carry it across: the encoded trace is a literal bseq, so nth 3
   discards Charlie's slot, the only slot the two hops differ in; and
   hop0_cipher reduces to enc bob_pkey 0 at both indices, since 0 < i holds
   at 1 and at 2.  Renumbering the trace slots or making either function
   opaque breaks this step. *)
have H1 : Pr P [set t | (lifted `o AliceHopTuple 1) t == V2 t]
          <= #|plain AHE|%:R^-1.
  exact: (guess_all_zero_le_invm card_renc rand_of_renc pkey_of_dk
            v1 u1 u2 u3_unit lifted).
rewrite -Hlift H0.
exact: le_trans (lerB (lexx _) H1) (ler_norm _).
Qed.

(* An assumption that promises a small epsilon has no choice about the
   decrypting predictor: its classifier must answer false on the reduction
   adversary that predictor induces, because that adversary's advantage is
   provably near one.  Whether the class admits an adversary is not free
   bookkeeping; a sound small-epsilon assumption is forced to reject exactly
   the adversary a real attacker would want to be.
   Naming: [not_admissible] states the value the classifier takes, on the
   reduction the decryptor induces. *)
Lemma decrypt_reduction_not_admissible (A : indcpa_epsilon_assumption) :
  indcpa_assumption_epsilon A < 1 - (#|plain AHE|%:R : R)^-1 ->
  indcpa_admissible A
    (bob_trace_adversary (guess_test bob_trace_decrypt_predictor)) = false.
Proof.
move=> Heps; apply/negbTE/negP => Hadm.
have Hle := le_trans bob_trace_guess_epsilon_decrypt_ge
              (indcpa_admissible_epsilon_le dk_b Hadm).
by move: (lt_le_trans Heps Hle); rewrite ltxx.
Qed.

(* The plaintext space has at least two elements, since zero and one differ in
   a nonzero ring. *)
Let card_plain_gt1 : (1 < #|plain AHE|)%N.
Proof.
apply/card_gt1P; exists 0, 1; rewrite !inE; split=> //.
by rewrite eq_sym oner_neq0.
Qed.

(* The two membership premises of the gated guessing bound cannot be dropped.
   With an assumption that admits nobody and promises epsilon zero, the
   premise-free bound is simply false: the decrypting predictor recovers Bob's
   input with certainty while the right-hand side stays below one.  The gate is
   where the bound's truth lives.  The witness here is the assumption that
   admits nobody, so this lemma only closes the premise-free reading;
   decrypt_reduction_not_admissible is what rules out the assumptions that
   matter, and the two together carry the argument.
   Naming: [premises_necessary] names what the statement establishes about
   [dsdp_alice_guess_fdist_trace_V2_admissible_le]. *)
Lemma admissible_le_premises_necessary :
  exists (A : indcpa_epsilon_assumption) (predict : predictor dsdp_traceT),
    ~ (alice_trace_guess_pr predict
         <= (#|plain AHE|%:R : R)^-1 + 2 * indcpa_assumption_epsilon A).
Proof.
have Hvac : forall (dk : priv_key AHE)
    (adv : indcpa_fdist_adversary (R:=R) AHE),
    false -> indcpa_fdist_epsilon (pub_of_priv dk) adv <= 0 by [].
exists {| indcpa_admissible := fun _ => false ;
          indcpa_assumption_epsilon := 0 ;
          indcpa_admissible_epsilon_le := Hvac |}.
exists bob_trace_decrypt_predictor.
have -> : alice_trace_guess_pr bob_trace_decrypt_predictor = 1
  := decrypt_guess_prE.
rewrite /= mulr0 addr0 => Hcon.
have Hlt : (#|plain AHE|%:R : R)^-1 < 1.
  by rewrite invf_lt1 ?ltr1n // ltr0n; exact: ltnW card_plain_gt1.
by move: (le_lt_trans Hcon Hlt); rewrite ltxx.
Qed.

Local Notation "'`H_unp^{' g '}'" :=
  (alice_trace_predictor_unpredictability g)
  (at level 0, g at level 200,
   format "'`H_unp^{' g '}'").

(* The unpredictability of Bob's input at Alice's executed trace obeys the
   same lower bound as at her hopping tuple. *)
Theorem dsdp_alice_trace_predictor_unpredictability_fdist_ge
    (predict : predictor dsdp_traceT)
    (Hpos : 0 < Pr P [set t | (predict `o AliceTrace) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R
               * (bob_trace_guess_epsilon predict
                  + charlie_trace_guess_epsilon predict))
  <= `H_unp^{predict}.
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R).
  by rewrite ltr0n; apply/card_gt0P; exists 0; rewrite inE.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R
                        * (bob_trace_guess_epsilon predict
                           + charlie_trace_guess_epsilon predict) :> R).
  by rewrite ltr_pwDl // mulr_ge0 // addr_ge0 // normr_ge0.
rewrite /alice_trace_predictor_unpredictability.
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_trace_V2_real_le.
Qed.

(* The two honest inputs and Alice's encoded trace obtained from a joint
   hopping-tuple value.
   Naming: the [_of_] connective names the source the conversion reads,
   here the joint carrier of [alice_hop_joint_fdist], not the bare tuple. *)
Let alice_trace_joint_of_hop_joint
    (x : plain AHE * plain AHE * hop_tupleT) : trace_jointT :=
  (x.1.1, x.1.2, dsdp_trace_of_hop_tuple x.2).

Let alice_trace_ideal_jointE :
  alice_trace_ideal_joint
  = fdistmap alice_trace_joint_of_hop_joint alice_ideal_joint.
Proof.
rewrite /alice_trace_ideal_joint /alice_ideal_joint fdistmap_bind.
congr (_ >>= _); apply: boolp.funext => vv.
by rewrite /dsdp_alice_trace_simulator 2!fdistmap_comp.
Qed.

Let alice_trace_real_jointE :
  `p_ [% V2, V3, AliceTrace]
  = fdistmap alice_trace_joint_of_hop_joint
      (`p_ [% V2, V3, AliceHopTuple 0]).
Proof.
by rewrite dsdp_trace_of_hop_tupleE /dist_of_RV fdistmap_comp.
Qed.

(* A Boolean test on Alice's executed trace separates the real trace law from
   the simulated one by at most the two hop advantages of the hopping-tuple
   test it lifts to. *)
Theorem dsdp_alice_trace_sim_advantage_fdist_le
    (D : distinguisher trace_jointT) :
  `| Pr (`p_ [% V2, V3, AliceTrace]) [set x | D x]
     - Pr alice_trace_ideal_joint [set x | D x] |
  <= indcpa_fdist_epsilon (pkey_of_dk Bob) (bob_trace_adversary D)
     + indcpa_fdist_epsilon (pkey_of_dk Charlie) (charlie_trace_adversary D).
Proof.
rewrite alice_trace_real_jointE alice_trace_ideal_jointE.
rewrite -2!(Pr_fdistmap_bool D) 2!(fdistmap_comp D) 2!Pr_fdistmap_bool.
rewrite /bob_trace_adversary /charlie_trace_adversary.
exact: (dsdp_alice_sim_advantage_fdist_le card_renc rand_of_renc
          pkey_of_dk v1 u1 u2 u3 (D \o alice_trace_joint_of_hop_joint)).
Qed.

End dsdp_alice_trace_secrecy.

Section dsdp_alice_trace_uncertainty.
(* cloned context of Section dsdp_alice_trace_centropy *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

Local Notation P := (alice_sample_fdist (R:=R) AHE card_renc).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation AliceHopTuple i :=
  (AliceHopTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3 i).
Local Notation AliceRealTuple :=
  (AliceRealTuple (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation AliceTrace :=
  (AliceTrace (R:=R) (AHE:=AHE) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).
Local Notation AliceView :=
  (AliceView (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation alice_view_of_hop_tupleE :=
  (alice_view_of_hop_tupleE (R:=R) (AHE:=AHE) card_renc rand_of_renc
     pkey_of_dk v1 u1 u2 u3).
Local Notation alice_trace_decode_V2E :=
  (alice_trace_decode_V2E (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* Conditioning on Alice's executed trace leaves the same uncertainty about
   Bob's input as conditioning on her hopping tuple: the trace and the tuple
   determine each other once the two combine coins, which are independent of
   both, are set aside.  The trace is therefore no better an observation than
   the tuple the hop ladder prices. *)
Theorem centropy_AliceTrace_AliceRealTuple :
  `H( V2 | AliceTrace ) = `H( V2 | AliceRealTuple ).
Proof.
rewrite /AliceRealTuple alice_trace_tupleE
        (can_centropy_eq (@trace_of_trace_tupleK AHE Renc rand_of_renc
                            v1 u1 u2 u3 dk_a dk_b dk_c w_rc2)).
rewrite alice_hop_tuple_rand_traceE
        (can_centropy_eq (@hop_tuple_of_rand_traceK AHE Renc)).
by rewrite (inde_centropy_eq
              (combine_rand_trace_indep card_renc rand_of_renc v1 u1 u2 u3
                 dk_a dk_b dk_c)).
Qed.

(* Conditioning on Alice's whole view leaves the same uncertainty about Bob's
   input as conditioning on her hopping tuple: each is a deterministic
   function of the other, so entropy contraction applies both ways. *)
Corollary centropy_AliceView_AliceRealTuple :
  `H( V2 | AliceView ) = `H( V2 | AliceRealTuple ).
Proof.
rewrite /AliceRealTuple.
transitivity (`H( V2 | [% AliceView, AliceHopTuple 0] )).
  by rewrite [in RHS]alice_hop_tuple_of_view centropy_RV_contraction.
rewrite centropy_RV_fdistA.
by rewrite [in LHS]alice_view_of_hop_tupleE centropy_RV_contraction.
Qed.

(* Conditioning on Alice's executed trace leaves no uncertainty about Bob's
   input: her trace carries Bob's ciphertext, and a holder of dk_b reads the
   plaintext off it.  The Shannon reading of the real trace is therefore
   degenerate, and the two equalities above transport that degeneracy to her
   hopping tuple and to her whole view.  The statements about the real trace
   that carry content are the guessing bounds, which quantify over predictors
   holding the public keys alone; conditional entropy quantifies over nothing
   and so charges the decryptor as well. *)
Corollary centropy_V2_AliceTrace_eq0 : `H( V2 | AliceTrace ) = 0.
Proof. by rewrite {1}alice_trace_decode_V2E centropy_RV_comp0. Qed.

End dsdp_alice_trace_uncertainty.

Section dsdp_alice_trace_pq_secrecy.
(* cloned context of Section dsdp_alice_trace_pq_sec *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (v1 u1 u2 u3 : plain AHE).
Hypothesis u3_unit : u3 \is a GRing.unit.
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).
Variables (p q : nat).
(* No positivity hypotheses: #|plain AHE| > 0 is a theorem, so the equation
   already forces 0 < p and 0 < q. *)
Hypothesis card_plain_pq : #|plain AHE| = (p * q)%N.

Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation dsdp_traceT := (dsdp_traceT AHE).
Local Notation predictor := (predictor AHE).
Local Notation indcpa_epsilon_assumption :=
  (indcpa_epsilon_assumption (R:=R) (AHE:=AHE) card_renc rand_of_renc).
Local Notation bob_trace_adversary :=
  (bob_trace_adversary (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation charlie_trace_adversary :=
  (charlie_trace_adversary (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rc2).
Local Notation alice_trace_guess_pr :=
  (alice_trace_guess_pr (R:=R) card_renc rand_of_renc
     v1 u1 u2 u3 dk_a dk_b dk_c w_rb2 w_rc2).

(* The inverse plaintext cardinality at the composite modulus. *)
Let inv_pq_cardE : ((p%:R : R) * q%:R)^-1 = (#|plain AHE|%:R : R)^-1.
Proof. by rewrite card_plain_pq natrM. Qed.

(* The class-conditional trace guessing bound with its unconditional term
   written at the composite modulus p * q, the modulus of the Paillier-style
   instantiations.  The currencies are those of
   dsdp_alice_guess_fdist_trace_V2_admissible_le: the right-hand side sums
   1/(p * q), which is unconditional, and twice the assumption's epsilon,
   which is conditional on that assumption; the two premises are conditional
   on its class and assumed rather than proved.
   Naming: extends [dsdp_alice_guess_fdist_trace_V2_admissible_le] with the
   [pq] variant token before [le]; kept long to preserve the family
   grouping. *)
Corollary dsdp_alice_guess_fdist_trace_V2_admissible_pq_le
    (A : indcpa_epsilon_assumption) (predict : predictor dsdp_traceT) :
  indcpa_admissible A (bob_trace_adversary (guess_test predict)) ->
  indcpa_admissible A (charlie_trace_adversary (guess_test predict)) ->
  alice_trace_guess_pr predict
    <= ((p%:R : R) * q%:R)^-1 + 2 * indcpa_assumption_epsilon A.
Proof.
rewrite inv_pq_cardE.
exact: (dsdp_alice_guess_fdist_trace_V2_admissible_le u3_unit w_rb2).
Qed.

End dsdp_alice_trace_pq_secrecy.
