From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, infotheo axis                              *)
(*                                                                            *)
(* Corrupted-Alice secrecy for the three-party DSDP protocol, proved in       *)
(* infotheo over an explicit product sample space. The sample space carries   *)
(* the two honest inputs, Alice's two mask plaintexts, the randomness of the  *)
(* two hop encryptions and the randomness of Alice's two combines; uniformity *)
(* and independence of the coordinates are theorems of the product            *)
(* construction rather than hypotheses.                                       *)
(*                                                                            *)
(* A one-parameter family of views interpolates from Alice's real view to the *)
(* view whose two ciphertext slots both encrypt zero. Each step of the        *)
(* interpolation is an equality between a distinguishing gap and the          *)
(* real-or-zero advantage of a reduction constructed here, and the all-zero   *)
(* endpoint is bounded by the one-degree-of-freedom solution fiber of the     *)
(* DSDP linear constraint. Every epsilon in this file is therefore the        *)
(* defined advantage of an explicit reduction.                                *)
(*                                                                            *)
(* Headline results: dsdp_alice_guess_fdist_V2_real_le bounds the probability *)
(* that a predictor reading Alice's real view returns Bob's input;            *)
(* dsdp_alice_unpredictability_fdist_ge is its negative-logarithm form;       *)
(* dsdp_alice_sim_advantage_fdist_le bounds the gap between the real joint    *)
(* law and the ideal-world joint law built from dsdp_alice_simulator;         *)
(* dsdp_alice_guess_fdist_full_le transfers the first bound to Alice's full   *)
(* view.                                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*          fdist_prod_bindE == a product distribution with a kernel is the   *)
(*                              bind of its first factor with the pairing of  *)
(*                              each first coordinate                         *)
(*             fdistmap_bind == a pushforward of a bind is the bind of the    *)
(*                              pushforwards                                  *)
(*          Pr_fdistmap_bool == the mass a boolean statistic puts on [true]   *)
(*                              is the probability of the event it defines    *)
(*               fdist_prod2 == the second marginal of a product is its       *)
(*                              second factor                                 *)
(*        fdist_uniform_prod == a uniform distribution over a product type is *)
(*                              the product of the uniform distributions      *)
(*      fdistmap_bij_uniform == the pushforward of a uniform distribution     *)
(*                              along a bijection is uniform                  *)
(*        dsdp_alice_sampleT == the sample space: the two honest inputs,      *)
(*                              Alice's two masks, the two hop encryption     *)
(*                              randomnesses and Alice's two combine          *)
(*                              randomnesses                                  *)
(*        alice_sample_fdist == the uniform product distribution on that      *)
(*                              sample space                                  *)
(*                    V2, V3 == the honest inputs of Bob and of Charlie       *)
(*                    R2, R3 == Alice's two mask plaintexts                   *)
(*                Rho2, Rho3 == the randomness of the two hop encryptions     *)
(*                  RA1, RA2 == the randomness of Alice's two combines        *)
(*                      Sout == the protocol output Alice legitimately learns *)
(*             hop0_cipher i == the Bob-key ciphertext slot, encrypting V2    *)
(*                              for i = 0 and zero for larger i               *)
(*             hop1_cipher i == the Charlie-key ciphertext slot, encrypting   *)
(*                              V3 for i at most 1 and zero for larger i      *)
(*          dsdp_alice_viewT == the type of Alice's reduced view: masks,      *)
(*                              combine randomness, output and the two        *)
(*                              ciphertext slots                              *)
(*   AliceView_zero_prefix i == Alice's view with its first i ciphertext      *)
(*                              slots zeroed                                  *)
(*                 AliceView == Alice's real view, AliceView_zero_prefix 0    *)
(*        AliceView_all_zero == Alice's view with both ciphertext slots       *)
(*                              zeroed, AliceView_zero_prefix 2               *)
(*                  E_bob_v2 == the Bob-key ciphertext of V2                  *)
(*              E_charlie_v3 == the Charlie-key ciphertext of V3              *)
(*            enc_fdist pk v == the law of an encryption of v under pk with   *)
(*                              uniform randomness                            *)
(*    indcpa_fdist_adversary == a single-query real-or-zero adversary: a      *)
(*                              context law adv_choose over adv_context, a    *)
(*                              challenge plaintext adv_plain read off the    *)
(*                              context, and a decision adv_decide on the     *)
(*                              context and the challenge ciphertext          *)
(* indcpa_fdist_success_real == the probability that the adversary accepts    *)
(*                              when the challenge encrypts its chosen        *)
(*                              plaintext                                     *)
(* indcpa_fdist_success_zero == the probability that the adversary accepts    *)
(*                              when the challenge encrypts zero              *)
(*      indcpa_fdist_epsilon == the absolute gap between those two            *)
(*                              probabilities                                 *)
(*        enc_slot_resampleE == the law of a context paired with a slot       *)
(*                              computed from the context and a coordinate    *)
(*                              disjoint from the context factors as a kernel *)
(*                              resampling that coordinate                    *)
(*        hop0_ctxT, Hop0Ctx == the side information of hop 0 and its random  *)
(*                              variable                                      *)
(*        hop1_ctxT, Hop1Ctx == the side information of hop 1 and its random  *)
(*                              variable                                      *)
(*                Hop1PreCtx == the hop-1 context before the hop-0 slot is    *)
(*                              encrypted                                     *)
(*               hop1_ctx_of == the map carrying the hop-1 precontext to the  *)
(*                              hop-1 context                                 *)
(*             hop0_assemble == the inputs and the view rebuilt from a hop-0  *)
(*                              context and a ciphertext in the hop-0 slot    *)
(*             hop1_assemble == the inputs and the view rebuilt from a hop-1  *)
(*                              context and a ciphertext in the hop-1 slot    *)
(*          hop0_reduction D == the reduction of a distinguisher D to Bob's   *)
(*                              key                                           *)
(*          hop1_reduction D == the reduction of a distinguisher D to         *)
(*                              Charlie's key                                 *)
(*        V1c, U1c, U2c, U3c == Alice's four protocol weights as constant     *)
(*                              random variables                              *)
(*      alice_spectator_preT == the sample coordinates Alice's view reads     *)
(*                              besides the two inputs                        *)
(*         AliceSpectatorPre == the random variable of those coordinates      *)
(*            AliceSpectator == everything Alice's all-zero view carries      *)
(*                              besides the output                            *)
(*        alice_spectator_of == the spectator rebuilt from the spectator      *)
(*                              coordinates                                   *)
(*   alice_view_of_spectator == Alice's all-zero view assembled from the      *)
(*                              spectator and the output                      *)
(*           Pr_fdistmap_pre == the mass a pushforward puts on a set is the   *)
(*                              mass its source puts on the preimage of that  *)
(*                              set                                           *)
(*  distinguisher_of_guess g == the distinguisher accepting when the          *)
(*                              predictor g returns the first input of its    *)
(*                              argument                                      *)
(*             fdistmap_prod == the pushforward of a product along a pair of  *)
(*                              coordinate maps is the product of the         *)
(*                              pushforwards                                  *)
(*            fdistmap_prodr == the pushforward of a product along a map      *)
(*                              acting only on the second coordinate keeps    *)
(*                              the first factor                              *)
(*    dsdp_alice_simulator s == the simulated view law at output value s:     *)
(*                              uniform masks, uniform combine randomness, s, *)
(*                              and an encryption of zero under each of the   *)
(*                              two other keys                                *)
(*     alice_spectator_pre2T == the spectator coordinates with the two        *)
(*                              encryption randomnesses last                  *)
(*        AliceSpectatorPre2 == the random variable of that layout            *)
(*   alice_spectator_regroup == the reordering of the spectator coordinates   *)
(*                              onto that layout                              *)
(*      alice_spectator_prod == the spectator rebuilt from the reordered      *)
(*                              spectator coordinates                         *)
(*   alice_spectator_of_view == the spectator slots of a value of Alice's     *)
(*                              view                                          *)
(*         alice_ideal_joint == the ideal-world joint law of the two inputs   *)
(*                              and a simulated view                          *)
(*        alice_view_full_of == the full corrupted view rebuilt from a value  *)
(*                              of the reduced view                           *)
(*           AliceCombineBob == Alice's outgoing combine addressed to Bob's   *)
(*                              key                                           *)
(*       AliceCombineCharlie == Alice's outgoing combine addressed to         *)
(*                              Charlie's key                                 *)
(*            AliceRecvPlain == the plaintext of Alice's final                *)
(*                              decrypt-on-receive                            *)
(*             AliceViewFull == Alice's four real observables: the reduced    *)
(*                              view, the two combines and that plaintext     *)
(*        alice_view_full_ok == those four observables assemble into the      *)
(*                              reconstruction of the full view from the      *)
(*                              reduced view                                  *)
(* ```                                                                        *)
(*                                                                            *)
(* Scope. The statements are average-case over the honest inputs V2 and V3,   *)
(* which are sampled uniformly inside the experiment. Each per-hop epsilon is *)
(* a single-query advantage at a fixed key, a number related to but distinct  *)
(* from the multi-query party-indexed oracle advantage of indcpa_ror.v. A     *)
(* bound here is informative to the extent that its epsilons are small, and   *)
(* holds vacuously once they exceed 1. The efficiency reading of the          *)
(* reductions stays on paper: the adversary is a plain function record, and   *)
(* complexity is argued outside the formalization.                            *)
(*                                                                            *)
(* The notations AliceView and AliceView_all_zero are promoted to the         *)
(* surrounding scope of the section, matching the zero_hop_prefix family of   *)
(* the SSProve axis.                                                          *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section fdist_glue.

Context {R : realType}.

(* A product distribution with kernel is the bind of the first factor with the
   pairing of each first coordinate. *)
Lemma fdist_prod_bindE (T1 T2 : finType) (Q1 : R.-fdist T1)
    (W : T1 -> R.-fdist T2) :
  (Q1 `X W) = Q1 >>= (fun a => fdistmap (fun b => (a, b)) (W a)).
Proof.
apply/fdist_ext => -[a c].
rewrite fdist_prodE /= fdistbindE (bigD1 a) //=.
rewrite big1 ?addr0; last first.
  move=> i ia; rewrite fdistmapE big1 ?mulr0 // => b.
  by rewrite !inE /= xpair_eqE (negbTE ia).
congr (_ * _); rewrite fdistmapE (big_pred1 c) // => b.
by rewrite !inE /= xpair_eqE eqxx.
Qed.

(* Pushing a map through a bind. *)
Lemma fdistmap_bind (T1 T2 T3 : finType) (Q : R.-fdist T1)
    (g : T1 -> R.-fdist T2) (h : T2 -> T3) :
  fdistmap h (Q >>= g) = Q >>= (fun a => fdistmap h (g a)).
Proof. by rewrite /fdistmap fdistbindA. Qed.

(* The mass a boolean statistic puts on [true] is the probability of the
   corresponding event. *)
Lemma Pr_fdistmap_bool (T : finType) (D : T -> bool) (m : R.-fdist T) :
  Pr (fdistmap D m) [set true] = Pr m [set t | D t].
Proof.
rewrite Pr_set1 fdistmapE /Pr; apply: eq_bigl => t.
by rewrite !inE /= eqb_id.
Qed.

(* The second marginal of a genuine product is the second factor. *)
Lemma fdist_prod2 (T1 T2 : finType) (Q1 : R.-fdist T1)
    (Q2 : R.-fdist T2) : (Q1 `x Q2)`2 = Q2.
Proof.
apply/fdist_ext => b; rewrite fdist_sndE.
under eq_bigr do rewrite fdist_prodE /=.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(* A uniform distribution over a product is the product of uniforms. *)
Lemma fdist_uniform_prod (T1 T2 : finType) (n1 n2 n12 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1)
    (c12 : #|((T1 * T2)%type : finType)| = n12.+1) :
  fdist_uniform (R:=R) c12 = (fdist_uniform c1) `x (fdist_uniform c2).
Proof.
apply/fdist_ext => -[a b]; rewrite fdist_prodE !fdist_uniformE.
by rewrite card_prod natrM invfM.
Qed.

(* The pushforward of a uniform along a bijection is uniform. *)
Lemma fdistmap_bij_uniform (T1 T2 : finType) (n1 n2 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1) (g : T1 -> T2) :
  bijective g ->
  fdistmap g (fdist_uniform (R:=R) c1) = fdist_uniform c2.
Proof.
move=> bg; have [h ghK hgK] := bg; apply/fdist_ext => b.
rewrite fdistmapE fdist_uniformE (big_pred1 (h b)); last first.
  by move=> a; rewrite !inE /=; apply/eqP/eqP => [<-|->].
by rewrite fdist_uniformE (bij_eq_card bg).
Qed.

End fdist_glue.

Section dsdp_alice_infotheo_secrecy.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variable pkey_of_party : party_id -> pub_key AHE.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).

Let card_plain_gt0 : (0 < #|plain AHE|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.
Let card_plain : #|plain AHE| = #|plain AHE|.-1.+1.
Proof. by rewrite prednK. Qed.
Let card_plain_pair :
  #|((plain AHE * plain AHE)%type : finType)|
    = (#|plain AHE| * #|plain AHE|)%N.-1.+1.
Proof. by rewrite card_prod prednK // muln_gt0 card_plain_gt0. Qed.
Let card_renc_pair :
  #|((Renc * Renc)%type : finType)|
    = (index_renc.+1 * index_renc.+1)%N.-1.+1.
Proof. by rewrite card_prod card_renc. Qed.

(* The sample space of the corrupted-Alice experiment: the two honest inputs,
   Alice's two mask plaintexts, the randomness of the two hop encryptions, and
   the randomness of Alice's two combines. *)
Definition dsdp_alice_sampleT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * (Renc * Renc))%type.

(* The uniform product distribution on the sample space. *)
Definition alice_sample_fdist : R.-fdist dsdp_alice_sampleT :=
  (((fdist_uniform card_plain_pair) `x (fdist_uniform card_plain_pair))
     `x (fdist_uniform card_renc_pair)) `x (fdist_uniform card_renc_pair).

(* Bob's honest input. *)
Definition V2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.1.
(* Charlie's honest input. *)
Definition V3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.2.
(* Alice's mask on the first combine. *)
Definition R2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.1.
(* Alice's mask on the second combine. *)
Definition R3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.2.
(* The randomness of the encryption Alice receives from Bob. *)
Definition Rho2 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.1.
(* The randomness of the encryption Alice receives from Charlie. *)
Definition Rho3 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.2.
(* The randomness of Alice's first combine. *)
Definition RA1 : {RV alice_sample_fdist -> Renc} := fun t => t.2.1.
(* The randomness of Alice's second combine. *)
Definition RA2 : {RV alice_sample_fdist -> Renc} := fun t => t.2.2.

(* The protocol output Alice legitimately learns, the weighted scalar product
   of her weights with the two honest inputs.
   Naming: [Sout] rather than [S], which shadows the successor of nat, after
   [dsdp_guess_fiber.v]. *)
Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3) `o [% V2, V3].

(* The Bob-key ciphertext slot of Alice's view, encrypting Bob's input at
   index 0 and zero at every larger index. *)
Definition hop0_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Bob) (if (0 < i)%N then 0 else V2 t)
         (rand_of_renc (Rho2 t))).

(* The Charlie-key ciphertext slot of Alice's view, encrypting Charlie's input
   at indices 0 and 1 and zero at every larger index. *)
Definition hop1_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Charlie) (if (1 < i)%N then 0 else V3 t)
         (rand_of_renc (Rho3 t))).

(* The type of Alice's reduced view: her two masks, her two combine
   randomnesses, the leaked output, and the two ciphertexts she receives. *)
Definition dsdp_alice_viewT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * t_cipher * t_cipher)%type.

(* Alice's view with the ciphertext slots of the first i hops replaced by
   encryptions of zero.
   Naming: after the [zero_hop_prefix] family of the SSProve axis. *)
Definition AliceView_zero_prefix (i : nat) :
    {RV alice_sample_fdist -> dsdp_alice_viewT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, hop0_cipher i, hop1_cipher i].

Notation AliceView := (AliceView_zero_prefix 0).
Notation AliceView_all_zero := (AliceView_zero_prefix 2).

(* The ciphertext of Bob's input under Bob's key. *)
Definition E_bob_v2 := hop0_cipher 0.
(* The ciphertext of Charlie's input under Charlie's key. *)
Definition E_charlie_v3 := hop1_cipher 0.

(* The law of an encryption of a plaintext under a public key, with uniform
   encryption randomness. *)
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist t_cipher :=
  fdistmap (fun r => chcipher_of_cipher (enc pk v (rand_of_renc r)))
           (fdist_uniform card_renc).

(* A single-query real-or-zero adversary: a law over a context type, a
   challenge plaintext read off the context, and a decision taken on the
   context and the challenge ciphertext. *)
Record indcpa_fdist_adversary := {
  adv_context : finType ;
  adv_choose : R.-fdist adv_context ;
  adv_plain : adv_context -> plain AHE ;
  adv_decide : adv_context -> t_cipher -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

(* The probability that the adversary accepts when the challenge encrypts the
   plaintext it chose.
   Naming: [_success_real] after [oracle_encrypt_real] and
   [guess_sdistr_success_real]; [Pr_] is reserved for the lemma family. *)
Definition indcpa_fdist_success_real (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk (adv_plain adv c))))
     [set true].

(* The probability that the adversary accepts when the challenge encrypts
   zero.
   Naming: [_success_zero] after [oracle_encrypt_zero]; [Pr_] is reserved for
   the lemma family. *)
Definition indcpa_fdist_success_zero (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk 0)))
     [set true].

(* The real-or-zero advantage of an adversary at a public key: the absolute
   gap between its two success probabilities. *)
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.

(* The law of a context paired with a slot computed from the context and a
   coordinate disjoint from the context is the law of the context with the
   kernel that resamples the coordinate. *)
Lemma enc_slot_resampleE (ctxT : finType) (Q : R.-fdist ctxT)
    (Ctx : {RV alice_sample_fdist -> ctxT})
    (Rho : {RV alice_sample_fdist -> Renc})
    (k : ctxT -> Renc -> t_cipher) :
  `p_ [% Ctx, Rho] = Q `x (fdist_uniform card_renc) ->
  `p_ [% Ctx, (fun t => k (Ctx t) (Rho t))
        : {RV alice_sample_fdist -> t_cipher}]
    = Q `X (fun a => fdistmap (k a) (fdist_uniform card_renc)).
Proof.
move=> Hprod.
have HL : `p_ [% Ctx, (fun t => k (Ctx t) (Rho t))
                : {RV alice_sample_fdist -> t_cipher}]
        = fdistmap (fun p : (ctxT * Renc)%type => (p.1, k p.1 p.2))
                   (`p_ [% Ctx, Rho]).
  by rewrite /dist_of_RV fdistmap_comp.
rewrite HL Hprod [in RHS]fdist_prod_bindE fdist_prod_bindE fdistmap_bind.
congr (_ >>= _); apply/boolp.funext => a.
rewrite !fdistmap_comp.
congr fdistmap; exact/boolp.funext.
Qed.

Let card_renc_gt0 : (0 < #|Renc|)%N.
Proof. by rewrite card_renc. Qed.

Let card_sample_gt0 : (0 < #|dsdp_alice_sampleT|)%N.
Proof.
by rewrite /dsdp_alice_sampleT !card_prod !muln_gt0 card_plain_gt0
           card_renc_gt0.
Qed.

Let card_sample : #|dsdp_alice_sampleT| = #|dsdp_alice_sampleT|.-1.+1.
Proof. by rewrite prednK. Qed.

(* The sample space carries the uniform distribution. *)
Lemma alice_sample_fdistE : alice_sample_fdist = fdist_uniform card_sample.
Proof.
apply/fdist_ext => -[[[vv ms] rho] ra].
rewrite fdist_uniformE /alice_sample_fdist !fdist_prodE !fdist_uniformE.
by rewrite -!invfM -!natrM /dsdp_alice_sampleT !card_prod.
Qed.

(* The side information of hop 0: the inputs, the masks, Alice's combine
   randomness, and the randomness of the hop-1 encryption. *)
Definition hop0_ctxT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * Renc)%type.

(* The random variable of the hop-0 side information. *)
Definition Hop0Ctx : {RV alice_sample_fdist -> hop0_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.2).

Let card_hop0_ctx_gt0 : (0 < #|hop0_ctxT|)%N.
Proof.
by rewrite /hop0_ctxT !card_prod !muln_gt0 card_plain_gt0 card_renc_gt0.
Qed.

Let card_hop0_ctx : #|hop0_ctxT| = #|hop0_ctxT|.-1.+1.
Proof. by rewrite prednK. Qed.

Let card_hop0_pair :
  #|((hop0_ctxT * Renc)%type : finType)|
    = #|((hop0_ctxT * Renc)%type : finType)|.-1.+1.
Proof.
by rewrite prednK // card_prod muln_gt0 card_hop0_ctx_gt0 card_renc_gt0.
Qed.

(* The hop-0 context and the hop-0 encryption randomness are jointly
   uniform. *)
Lemma hop0_pair_uniformE :
  `p_ [% Hop0Ctx, Rho2]
    = (fdist_uniform card_hop0_ctx) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_ctx card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_ctxT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2, (p.2, p.1.2), p.1.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[[v2 v3] [r2 r3]] [ra1 ra2]] rho3] rho2].
Qed.

(* The hop-0 context is uniform. *)
Lemma hop0_ctx_uniformE : `p_ Hop0Ctx = fdist_uniform card_hop0_ctx.
Proof. by rewrite -(fst_RV2 Hop0Ctx Rho2) hop0_pair_uniformE fdist_prod1. Qed.

(* The hop-0 encryption randomness is uniform and independent of the hop-0
   context. *)
Lemma hop0_ctx_prod :
  `p_ [% Hop0Ctx, Rho2] = (`p_ Hop0Ctx) `x (fdist_uniform card_renc).
Proof. by rewrite hop0_ctx_uniformE hop0_pair_uniformE. Qed.

(* The side information of hop 1: the inputs, the masks, Alice's combine
   randomness, and the hop-0 ciphertext of zero. *)
Definition hop1_ctxT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * t_cipher)%type.

(* The random variable of the hop-1 side information. *)
Definition Hop1Ctx : {RV alice_sample_fdist -> hop1_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, hop0_cipher 1 t).

(* The hop-1 side information with the randomness of the hop-0 encryption in
   place of the ciphertext it produces. *)
Definition Hop1PreCtx : {RV alice_sample_fdist -> hop0_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.1).

(* The map carrying a hop-1 precontext to the hop-1 context, encrypting zero in
   the hop-0 slot. *)
Definition hop1_ctx_of (c : hop0_ctxT) : hop1_ctxT :=
  (c.1.1.1, c.1.1.2, c.1.2,
   chcipher_of_cipher (enc (pkey_of_party Bob) 0 (rand_of_renc c.2))).

(* The hop-1 context is the image of the hop-1 precontext under the hop-0
   encryption of zero. *)
Lemma hop1_ctx_ofE : Hop1Ctx = hop1_ctx_of `o Hop1PreCtx.
Proof. by []. Qed.

(* The hop-1 precontext and the hop-1 encryption randomness are jointly
   uniform. *)
Lemma hop1_prectx_pair_uniformE :
  `p_ [% Hop1PreCtx, Rho3]
    = (fdist_uniform card_hop0_ctx) `x (fdist_uniform card_renc).
Proof.
rewrite -(fdist_uniform_prod card_hop0_ctx card_renc card_hop0_pair).
rewrite /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_hop0_pair).
exists (fun p : (hop0_ctxT * Renc)%type =>
          (p.1.1.1.1, p.1.1.1.2, (p.1.2, p.2), p.1.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[[v2 v3] [r2 r3]] [ra1 ra2]] rho2] rho3].
Qed.

(* The hop-1 precontext is uniform. *)
Lemma hop1_prectx_uniformE : `p_ Hop1PreCtx = fdist_uniform card_hop0_ctx.
Proof.
by rewrite -(fst_RV2 Hop1PreCtx Rho3) hop1_prectx_pair_uniformE fdist_prod1.
Qed.

(* The hop-1 encryption randomness is uniform. *)
Lemma rho3_uniformE : `p_ Rho3 = fdist_uniform card_renc.
Proof.
by rewrite -(snd_RV2 Hop1PreCtx Rho3) hop1_prectx_pair_uniformE fdist_prod2.
Qed.

(* A joint law that factors as the product of its marginals is the law of an
   independent pair. *)
Lemma inde_RV_of_prod (A B : finType)
    (X : {RV alice_sample_fdist -> A}) (Y : {RV alice_sample_fdist -> B}) :
  `p_ [% X, Y] = (`p_ X) `x (`p_ Y) -> alice_sample_fdist |= X _|_ Y.
Proof. by move=> H a b; rewrite -!dist_of_RVE H fdist_prodE. Qed.

(* The hop-1 encryption randomness is uniform and independent of the hop-1
   context. *)
Lemma hop1_ctx_prod :
  `p_ [% Hop1Ctx, Rho3] = (`p_ Hop1Ctx) `x (fdist_uniform card_renc).
Proof.
have Hpre : alice_sample_fdist |= Hop1PreCtx _|_ Rho3.
  apply: inde_RV_of_prod.
  by rewrite hop1_prectx_pair_uniformE hop1_prectx_uniformE rho3_uniformE.
have Hctx : alice_sample_fdist |= Hop1Ctx _|_ Rho3.
  by rewrite hop1_ctx_ofE; exact: (inde_RV_comp hop1_ctx_of idfun Hpre).
by rewrite (inde_dist_of_RV2 Hctx) rho3_uniformE.
Qed.

(* The inputs and the view rebuilt from a hop-0 context and a ciphertext in
   the hop-0 slot. *)
Definition hop0_assemble (c : hop0_ctxT) (ch : t_cipher) :
    plain AHE * plain AHE * dsdp_alice_viewT :=
  let: (vv, masks, ra, rho3) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2, ch,
    chcipher_of_cipher
      (enc (pkey_of_party Charlie) vv.2 (rand_of_renc rho3)))).

(* The inputs and the view rebuilt from a hop-1 context and a ciphertext in
   the hop-1 slot. *)
Definition hop1_assemble (c : hop1_ctxT) (ch : t_cipher) :
    plain AHE * plain AHE * dsdp_alice_viewT :=
  let: (vv, masks, ra, c2zero) := c in
  (vv.1, vv.2,
   (masks, ra, dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2, c2zero, ch)).

(* The adversary that challenges Bob's key on the first input and runs the
   distinguisher on the view rebuilt around the challenge. *)
Definition hop0_reduction
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_context := hop0_ctxT ;
     adv_choose := `p_ Hop0Ctx ;
     adv_plain := fun c => c.1.1.1.1 ;
     adv_decide := fun c ch => D (hop0_assemble c ch) |}.

(* The adversary that challenges Charlie's key on the second input and runs
   the distinguisher on the view rebuilt around the challenge. *)
Definition hop1_reduction
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
    indcpa_fdist_adversary :=
  {| adv_context := hop1_ctxT ;
     adv_choose := `p_ Hop1Ctx ;
     adv_plain := fun c => c.1.1.1.2 ;
     adv_decide := fun c ch => D (hop1_assemble c ch) |}.

(* The distinguisher on the real view is the hop-0 reduction facing an
   encryption of the first input. *)
Lemma hop0_real_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 0]) [set x | D x]
    = indcpa_fdist_success_real (pkey_of_party Bob) (hop0_reduction D).
Proof.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_real /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 0])
        = fdistmap (fun p : hop0_ctxT * t_cipher => D (hop0_assemble p.1 p.2))
                   (`p_ [% Hop0Ctx, hop0_cipher 0]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (enc_slot_resampleE (fun (c : hop0_ctxT) r => chcipher_of_cipher
  (enc (pkey_of_party Bob) c.1.1.1.1 (rand_of_renc r))) hop0_ctx_prod)
        fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* The distinguisher on the view with a zeroed hop-0 slot is the hop-0
   reduction facing an encryption of zero. *)
Lemma hop0_zero_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x]
    = indcpa_fdist_success_zero (pkey_of_party Bob) (hop0_reduction D).
Proof.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_zero /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 1])
        = fdistmap (fun p : hop0_ctxT * t_cipher => D (hop0_assemble p.1 p.2))
                   (`p_ [% Hop0Ctx, hop0_cipher 1]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (enc_slot_resampleE (fun (_ : hop0_ctxT) r => chcipher_of_cipher
  (enc (pkey_of_party Bob) 0 (rand_of_renc r))) hop0_ctx_prod)
        fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* Zeroing the hop-0 slot of the view moves the distinguishing probability by
   the advantage of the hop-0 reduction against Bob's key. *)
Lemma hop0_advantageE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 0]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D).
Proof.
by rewrite /indcpa_fdist_epsilon hop0_real_armE hop0_zero_armE.
Qed.

(* The distinguisher on the view with a zeroed hop-0 slot is the hop-1
   reduction facing an encryption of the second input. *)
Lemma hop1_real_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x]
    = indcpa_fdist_success_real (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_real /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 1])
        = fdistmap (fun p : hop1_ctxT * t_cipher => D (hop1_assemble p.1 p.2))
                   (`p_ [% Hop1Ctx, hop1_cipher 1]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (enc_slot_resampleE (fun (c : hop1_ctxT) r => chcipher_of_cipher
  (enc (pkey_of_party Charlie) c.1.1.1.2 (rand_of_renc r))) hop1_ctx_prod)
        fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* The distinguisher on the all-zero view is the hop-1 reduction facing an
   encryption of zero. *)
Lemma hop1_zero_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 2]) [set x | D x]
    = indcpa_fdist_success_zero (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_zero /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 2])
        = fdistmap (fun p : hop1_ctxT * t_cipher => D (hop1_assemble p.1 p.2))
                   (`p_ [% Hop1Ctx, hop1_cipher 2]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite (enc_slot_resampleE (fun (_ : hop1_ctxT) r => chcipher_of_cipher
  (enc (pkey_of_party Charlie) 0 (rand_of_renc r))) hop1_ctx_prod)
        fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* Zeroing the hop-1 slot of the view moves the distinguishing probability by
   the advantage of the hop-1 reduction against Charlie's key. *)
Lemma hop1_advantageE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceView_zero_prefix 2]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
Proof.
by rewrite /indcpa_fdist_epsilon hop1_real_armE hop1_zero_armE.
Qed.

(* Alice's own input as a constant random variable. *)
Definition V1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ w_v1.
(* Alice's first protocol weight as a constant random variable. *)
Definition U1c : {RV alice_sample_fdist -> plain AHE} := const_RV _ w_u1.
(* Alice's second protocol weight as a constant random variable. *)
Definition U2c : {RV alice_sample_fdist -> plain AHE} := const_RV _ w_u2.
(* Alice's third protocol weight as a constant random variable. *)
Definition U3c : {RV alice_sample_fdist -> plain AHE} := const_RV _ w_u3.

(* The sample coordinates the view reads besides the two secret inputs: the
   masks, the two encryption randomnesses, and Alice's combine randomness. *)
Definition alice_spectator_preT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * (Renc * Renc))%type.

(* The random variable of the spectator coordinates. *)
Definition AliceSpectatorPre :
    {RV alice_sample_fdist -> alice_spectator_preT} :=
  fun t => (t.1.1.2, t.1.2, t.2).

Let card_spectator_pre_gt0 : (0 < #|alice_spectator_preT|)%N.
Proof.
by rewrite /alice_spectator_preT !card_prod !muln_gt0 card_plain_gt0
           card_renc_gt0.
Qed.

Let card_spectator_pre :
  #|alice_spectator_preT| = #|alice_spectator_preT|.-1.+1.
Proof. by rewrite prednK. Qed.

Let card_spectator_pre_pair :
  #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|
  = #|((alice_spectator_preT * (plain AHE * plain AHE))%type : finType)|.-1.+1.
Proof.
by rewrite prednK // !card_prod !muln_gt0 card_plain_gt0 card_renc_gt0.
Qed.

(* The spectator coordinates and the secret input pair are jointly uniform. *)
Lemma spectator_pre_pair_uniformE :
  `p_ [% AliceSpectatorPre, [% V2, V3]]
    = (fdist_uniform card_spectator_pre) `x (fdist_uniform card_plain_pair).
Proof.
rewrite -(fdist_uniform_prod card_spectator_pre card_plain_pair
            card_spectator_pre_pair) /dist_of_RV alice_sample_fdistE.
apply: (fdistmap_bij_uniform card_sample card_spectator_pre_pair).
exists (fun p : alice_spectator_preT * (plain AHE * plain AHE) =>
          (p.2, p.1.1.1, p.1.1.2, p.1.2)).
  by move=> [[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[r2 r3] [rho2 rho3]] [ra1 ra2]] [v2 v3]].
Qed.

(* The spectator coordinates are uniform. *)
Lemma spectator_pre_uniformE :
  `p_ AliceSpectatorPre = fdist_uniform card_spectator_pre.
Proof.
by rewrite -(fst_RV2 AliceSpectatorPre [% V2, V3]) spectator_pre_pair_uniformE
           fdist_prod1.
Qed.

(* The two secret inputs are jointly uniform. *)
Lemma alice_var_uniform : `p_ [% V2, V3] = fdist_uniform card_plain_pair.
Proof.
by rewrite -(snd_RV2 AliceSpectatorPre [% V2, V3]) spectator_pre_pair_uniformE
           fdist_prod2.
Qed.

(* The spectator coordinates are independent of the two secret inputs. *)
Lemma spectator_pre_indep :
  alice_sample_fdist |= AliceSpectatorPre _|_ [% V2, V3].
Proof.
apply: inde_RV_of_prod.
by rewrite spectator_pre_pair_uniformE spectator_pre_uniformE alice_var_uniform.
Qed.

(* The four protocol weights form a constant random variable. *)
Lemma alice_inputs_constE :
  [% V1c, U1c, U2c, U3c]
  = const_RV alice_sample_fdist (w_v1, w_u1, w_u2, w_u3).
Proof. by apply: boolp.funext => t; rewrite /V1c /U1c /U2c /U3c !const_RVE. Qed.

(* The protocol weights are independent of the two secret inputs. *)
Lemma alice_var_indep :
  alice_sample_fdist |= [% V1c, U1c, U2c, U3c] _|_ [% V2, V3].
Proof. by rewrite alice_inputs_constE; exact: inde_const_RV. Qed.

(* The protocol weights, the leaked output and the two secret inputs satisfy the
   DSDP linear constraint pointwise. *)
Lemma alice_constraint_holds (t : dsdp_alice_sampleT) :
  dsdp_constraint_ring ([% V1c, U1c, U2c, U3c, Sout] t) ([% V2, V3] t).
Proof.
by rewrite /dsdp_constraint_ring /Sout /comp_RV /dsdp_output /V1c /U1c /U2c /U3c
           /= !const_RVE; ring.
Qed.

(* Conditioned on the protocol weights and the leaked output, the secret input
   pair is uniform on the solution fiber, with mass 1/#|plain AHE|. *)
Lemma alice_VarRV_cond_uniform (s v2 v3 : plain AHE) :
  `Pr[ [% V1c, U1c, U2c, U3c, Sout] = (w_v1, w_u1, w_u2, w_u3, s) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring w_u1 w_u2 w_u3 w_v1 s ->
  `Pr[ [% V2, V3] = (v2, v3)
     | [% V1c, U1c, U2c, U3c, Sout] = (w_v1, w_u1, w_u2, w_u3, s) ]
  = #|plain AHE|%:R^-1.
Proof.
apply: Pr_dsdp_sol_uniform_ring => //; last exact: alice_var_indep.
  exact: alice_constraint_holds.
by rewrite alice_var_uniform; congr fdist_uniform; exact: eq_irrelevance.
Qed.

(* A conditioning coordinate independent of the numerator pair drops out of the
   conditioning view.
   Naming: [cpr_eq] names the conditional probability being rewritten, and
   [drop_indep] the operation performed on it. *)
Lemma cpr_eq_drop_indep {Rr : realType} {U : finType} {P : FDist.t Rr U}
    {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C})
    (a : A) (y : B) (w : C) :
  `Pr[ W = w ] != 0 ->
  P |= W _|_ [% X, Y] ->
  `Pr[ X = a | [% W, Y] = (w, y) ] = `Pr[ X = a | Y = y ].
Proof.
move=> Hw Hindep; rewrite !cpr_eqE.
have HWY : P |= W _|_ Y := inde_RV_comp idfun snd Hindep.
by rewrite (pfwd1_pairCA X W Y a w y) (Hindep w (a, y)) (HWY w y) invfM
           mulrACA (mulfV Hw) mul1r.
Qed.

(* Conditioned on the leaked output alone, Bob's input is uniform on the
   plaintext space. *)
Lemma alice_V2_cond_Sout (a s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ V2 = a | Sout = s ] = #|plain AHE|%:R^-1.
Proof.
move=> Hs.
have [g _ Hg2] : bijective (fun v : plain AHE => w_u3 * v)
  by apply: inj_card_bij.
pose v3star := g (s - w_u1 * w_v1 - w_u2 * a).
have Hfib : (a, v3star) \in dsdp_fiber_ring w_u1 w_u2 w_u3 w_v1 s
  by rewrite inE /=; apply/eqP; rewrite /v3star Hg2; ring.
have Hnum : pfwd1 [% V2, Sout] (a, s)
          = pfwd1 [% [% V2, V3], Sout] ((a, v3star), s).
  rewrite !pfwd1E; congr (Pr _ _).
  apply/setP => t; rewrite !inE /= !xpair_eqE.
  case: (V2 t =P a) => [Hva|_] //=.
  suff -> : (Sout t == s) = (V3 t == v3star) by rewrite andbb.
  rewrite /Sout /comp_RV /dsdp_output /= Hva.
  have -> : s = w_u1 * w_v1 + w_u2 * a + w_u3 * v3star
    by rewrite /v3star Hg2; ring.
  by rewrite (inj_eq (addrI _)) (inj_eq w_u3_inj).
have Hcond_eq : pfwd1 [% V1c, U1c, U2c, U3c, Sout] (w_v1, w_u1, w_u2, w_u3, s)
              = `Pr[ Sout = s ]
  := pfwd1_RV2_compl Sout (fun=> (w_v1, w_u1, w_u2, w_u3)) s.
have HcwN : `Pr[ [% V1c, U1c, U2c, U3c] = (w_v1, w_u1, w_u2, w_u3) ] != 0.
  by apply: contra_neq Hs => /(pfwd1_domin_RV2 Sout s); rewrite -Hcond_eq.
have Hind : alice_sample_fdist
              |= [% V1c, U1c, U2c, U3c] _|_ [% [% V2, V3], Sout]
  by rewrite alice_inputs_constE; exact: inde_const_RV.
rewrite cpr_eqE Hnum -cpr_eqE -(cpr_eq_drop_indep (a, v3star) s HcwN Hind).
by apply: alice_VarRV_cond_uniform; rewrite ?Hcond_eq.
Qed.

(* Conditioned on the leaked output, Bob's input takes any given value with
   probability at most 1/#|plain AHE|. *)
Lemma alice_V2_cond_le (a s : plain AHE) :
  `Pr[ V2 = a | Sout = s ] <= #|plain AHE|%:R^-1.
Proof.
have [H0|Hn0] := eqVneq `Pr[ Sout = s ] 0.
  by rewrite cpr_eqE H0 invr0 mulr0 invr_ge0 ler0n.
by rewrite (alice_V2_cond_Sout a Hn0).
Qed.

(* The leaked output is uniform on the plaintext space. *)
Lemma Sout_uniform : `p_ Sout = fdist_uniform card_plain.
Proof.
have -> : `p_ Sout
        = fdistmap (uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3)) (`p_ [% V2, V3]).
  by rewrite /dist_of_RV fdistmap_comp.
rewrite alice_var_uniform; apply/fdist_ext => s.
rewrite fdistmapE fdist_uniformE.
under eq_bigr do rewrite fdist_uniformE.
have Hcard : #|preim (uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3)) (pred1 s)|
           = #|plain AHE|.
  rewrite -(dsdp_fiber_card_ring w_u1 w_u2 w_v1 s w_u3_inj).
  apply: eq_card => vv; rewrite !inE /= /dsdp_output.
  case: vv => v2 v3 /=; rewrite -subr_eq0 -[RHS]subr_eq0.
  by have -> : w_u1 * w_v1 + w_u2 * v2 + w_u3 * v3 - s
             = w_u2 * v2 + w_u3 * v3 - (s - w_u1 * w_v1) by ring.
rewrite sumr_const Hcard -[LHS]mulr_natr card_prod natrM invfM -mulrA.
by rewrite mulVf ?mulr1 // pnatr_eq0 -lt0n card_plain_gt0.
Qed.

(* Everything Alice's all-zero view carries besides the leaked output. *)
Definition AliceSpectator :
    {RV alice_sample_fdist ->
       ((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)%type}
  := [% [% R2, R3], [% RA1, RA2], hop0_cipher 2, hop1_cipher 2].

(* The spectator rebuilt from the spectator coordinates. *)
Definition alice_spectator_of (c : alice_spectator_preT) :
    ((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)%type :=
  (c.1.1, c.2,
   chcipher_of_cipher (enc (pkey_of_party Bob) 0 (rand_of_renc c.1.2.1)),
   chcipher_of_cipher (enc (pkey_of_party Charlie) 0 (rand_of_renc c.1.2.2))).

(* The spectator is the image of the spectator coordinates under the
   zero-plaintext encryptions. *)
Lemma alice_spectator_ofE :
  AliceSpectator = alice_spectator_of `o AliceSpectatorPre.
Proof.
by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
Qed.

(* The spectator is independent of the two secret inputs. *)
Lemma alice_spectator_indep :
  alice_sample_fdist |= AliceSpectator _|_ [% V2, V3].
Proof.
rewrite alice_spectator_ofE.
exact: (inde_RV_comp alice_spectator_of idfun spectator_pre_indep).
Qed.

(* The spectator is independent of Bob's input paired with the leaked output. *)
Lemma alice_spectator_indep_Sout :
  alice_sample_fdist |= AliceSpectator _|_ [% V2, Sout].
Proof.
exact: (inde_RV_comp idfun (fun p : plain AHE * plain AHE =>
          (p.1, uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3) p))
        alice_spectator_indep).
Qed.

(* The spectator is conditionally independent of Bob's input given the leaked
   output. *)
Lemma alice_spectator_cinde :
  alice_sample_fdist |= AliceSpectator _|_ V2 | Sout.
Proof.
apply: cpr_prd_unit_RV; apply: weak_union.
by apply/cinde_RV_unit; exact: alice_spectator_indep_Sout.
Qed.

(* Alice's all-zero view assembled from the spectator and the leaked output. *)
Definition alice_view_of_spectator
    (p : (((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)
          * plain AHE)%type) : dsdp_alice_viewT :=
  (p.1.1.1.1, p.1.1.1.2, p.2, p.1.1.2, p.1.2).

(* A predictor reading Alice's all-zero view matches Bob's input with
   probability at most 1/#|plain AHE|.
   Naming: [guess] names the success probability being bounded, [all_zero] the
   view it reads, and [invm] the inverse plaintext-space cardinality bounding
   it. *)
Lemma guess_all_zero_le_invm (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView_all_zero) t == V2 t]
    <= #|plain AHE|%:R^-1.
Proof.
apply: (cinde_diagonal_bound
          (cinde_RV_comp (fun sp s => g (alice_view_of_spectator (sp, s)))
             alice_spectator_cinde)) => a c; exact: alice_V2_cond_le.
Qed.

(* The mass a pushforward puts on a set is the mass its source puts on the
   preimage of that set. *)
Lemma Pr_fdistmap_pre {Rr : realType} {A B : finType} (h : A -> B)
    (p : FDist.t Rr A) (E : {set B}) :
  Pr (fdistmap h p) E = Pr p [set a | h a \in E].
Proof.
rewrite /Pr (partition_big h (mem E)) /=; last by move=> a; rewrite inE.
apply: eq_bigr => b bE; rewrite fdistmapE.
by apply: eq_bigl => a; rewrite inE [in RHS]andb_idl // => /eqP ->.
Qed.

(* The distinguisher that accepts when a predictor reading the view slot of its
   input returns the first input. *)
Definition distinguisher_of_guess (g : dsdp_alice_viewT -> plain AHE) :
    plain AHE * plain AHE * dsdp_alice_viewT -> bool :=
  fun x => g x.2 == x.1.1.

(* The event that a predictor matches Bob's input is the acceptance event of
   the associated distinguisher on the joint law of the inputs and the view. *)
Lemma guess_event_jointE (g : dsdp_alice_viewT -> plain AHE) (i : nat) :
  Pr alice_sample_fdist
     [set t | (g `o AliceView_zero_prefix i) t == V2 t]
  = Pr (`p_ [% V2, V3, AliceView_zero_prefix i])
       [set x | distinguisher_of_guess g x].
Proof.
by rewrite /dist_of_RV Pr_fdistmap_pre; apply: eq_bigl => t; rewrite !inE.
Qed.

(* A predictor reading Alice's real view matches Bob's input with probability at
   most 1/#|plain AHE| plus the advantages of the two hop reductions.
   Naming: [dsdp_alice_guess] after [dsdp_alice_guess_V2_real_le] of the
   SSProve axis, with the axis token [fdist] after [guess]. *)
Theorem dsdp_alice_guess_fdist_V2_real_le
    (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess g)).
Proof.
have Hzero : Pr (`p_ [% V2, V3, AliceView_all_zero])
                [set x | distinguisher_of_guess g x]
             <= #|plain AHE|%:R^-1.
  by rewrite -guess_event_jointE; exact: guess_all_zero_le_invm.
rewrite guess_event_jointE -hop0_advantageE -hop1_advantageE -addrA -lerBlDl.
apply: le_trans (lerB (lexx _) Hzero) _.
exact: le_trans (ler_norm _) (ler_distD _ _ _).
Qed.

(* The advantage against Bob's key of the hop-0 reduction of the distinguisher
   associated with a predictor. *)
Let eps0 (g : dsdp_alice_viewT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_party Bob)
    (hop0_reduction (distinguisher_of_guess g)).

(* The advantage against Charlie's key of the hop-1 reduction of the
   distinguisher associated with a predictor. *)
Let eps1 (g : dsdp_alice_viewT -> plain AHE) : R :=
  indcpa_fdist_epsilon (pkey_of_party Charlie)
    (hop1_reduction (distinguisher_of_guess g)).

(* The negative logarithm of the success probability of a predictor reading
   Alice's real view is at least log #|plain AHE| minus the logarithm of one
   plus #|plain AHE| times the sum of the two hop advantages.
   Naming: after [dsdp_alice_unpredictability_entropy_ge] of the SSProve axis,
   with the axis token [fdist] in place of [entropy]. *)
Theorem dsdp_alice_unpredictability_fdist_ge
    (g : dsdp_alice_viewT -> plain AHE)
    (Hpos : 0 < Pr alice_sample_fdist
                  [set t | (g `o AliceView) t == V2 t]) :
  log (#|plain AHE|%:R)
    - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
  <= - log (Pr alice_sample_fdist
              [set t | (g `o AliceView) t == V2 t]).
Proof.
have Hcard_pos : (0 < #|plain AHE|%:R :> R) by rewrite ltr0n card_plain_gt0.
have Heps_ge0 : 0 <= eps0 g + eps1 g
  by rewrite addr_ge0 // /eps0 /eps1 /indcpa_fdist_epsilon normr_ge0.
have Hnum_pos : (0 < 1 + #|plain AHE|%:R * (eps0 g + eps1 g) :> R)
  by exact: ltr_pwDl ltr01 (mulr_ge0 (ler0n _ _) Heps_ge0).
rewrite lerNr opprB -logDiv // ler_log ?posrE ?divr_gt0 //.
rewrite mulrDl mul1r mulrAC (divff (lt0r_neq0 Hcard_pos)) mul1r addrA.
exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

(* The pushforward of a product distribution along a pair of coordinate maps is
   the product of the pushforwards. *)
Lemma fdistmap_prod (A1 A2 B1 B2 : finType) (Q1 : R.-fdist A1)
    (Q2 : R.-fdist A2) (f1 : A1 -> B1) (f2 : A2 -> B2) :
  fdistmap (fun a : (A1 * A2)%type => (f1 a.1, f2 a.2)) (Q1 `x Q2)
  = (fdistmap f1 Q1) `x (fdistmap f2 Q2).
Proof.
apply/fdist_ext => -[b1 b2]; rewrite fdist_prodE !fdistmapE.
rewrite big_distrl /=.
rewrite (eq_bigr (fun i => \sum_(a in preim f2 (pred1 b2)) (Q1 i * Q2 a)));
  last by move=> i _; rewrite big_distrr.
rewrite pair_big /=.
apply: eq_big => [[a1 a2]|[a1 a2] _] /=.
  by rewrite !inE /= xpair_eqE.
by rewrite fdist_prodE.
Qed.

(* The pushforward of a product distribution along a map acting only on the
   second coordinate keeps the first factor. *)
Lemma fdistmap_prodr (A1 A2 B2 : finType) (Q1 : R.-fdist A1)
    (Q2 : R.-fdist A2) (f2 : A2 -> B2) :
  fdistmap (fun a : (A1 * A2)%type => (a.1, f2 a.2)) (Q1 `x Q2)
  = Q1 `x (fdistmap f2 Q2).
Proof.
by rewrite (fdistmap_prod Q1 Q2 idfun f2) fdistmap_id.
Qed.

(* The law a simulator produces from a value of the leaked output: uniform
   masks, uniform combine randomness, that output, and an encryption of zero
   under each of the two other parties' keys. *)
Definition dsdp_alice_simulator (s : plain AHE) :
    R.-fdist dsdp_alice_viewT :=
  ((((fdist_uniform card_plain_pair) `x (fdist_uniform card_renc_pair))
      `x (fdist1 s))
     `x (enc_fdist (pkey_of_party Bob) 0))
    `x (enc_fdist (pkey_of_party Charlie) 0).

(* The spectator coordinates with the two encryption randomnesses last. *)
Definition alice_spectator_pre2T : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * Renc * Renc)%type.

(* The random variable of the reordered spectator coordinates. *)
Definition AliceSpectatorPre2 :
    {RV alice_sample_fdist -> alice_spectator_pre2T} :=
  fun t => (t.1.1.2, t.2, t.1.2.1, t.1.2.2).

(* The reordering of the spectator coordinates that separates the two
   encryption randomnesses. *)
Definition alice_spectator_regroup (c : alice_spectator_preT) :
    alice_spectator_pre2T := (c.1.1, c.2, c.1.2.1, c.1.2.2).

(* The reordered spectator coordinates are the image of the spectator
   coordinates under the reordering. *)
Lemma alice_spectator_regroupE :
  AliceSpectatorPre2 = alice_spectator_regroup `o AliceSpectatorPre.
Proof. by []. Qed.

Let card_masks_ra :
  #|(((plain AHE * plain AHE) * (Renc * Renc))%type : finType)|
  = #|(((plain AHE * plain AHE) * (Renc * Renc))%type : finType)|.-1.+1.
Proof.
by rewrite prednK // !card_prod !muln_gt0 card_plain_gt0 card_renc_gt0.
Qed.

Let card_masks_ra_rho :
  #|(((plain AHE * plain AHE) * (Renc * Renc) * Renc)%type : finType)|
  = #|(((plain AHE * plain AHE) * (Renc * Renc) * Renc)%type : finType)|.-1.+1.
Proof.
by rewrite prednK // !card_prod !muln_gt0 card_plain_gt0 card_renc_gt0.
Qed.

Let card_spectator_pre2 :
  #|alice_spectator_pre2T| = #|alice_spectator_pre2T|.-1.+1.
Proof.
by rewrite prednK // /alice_spectator_pre2T !card_prod !muln_gt0 card_plain_gt0
           card_renc_gt0.
Qed.

(* The reordered spectator coordinates are uniform. *)
Lemma spectator_pre2_uniformE :
  `p_ AliceSpectatorPre2 = fdist_uniform card_spectator_pre2.
Proof.
have -> : `p_ AliceSpectatorPre2
        = fdistmap alice_spectator_regroup (`p_ AliceSpectatorPre).
  by rewrite alice_spectator_regroupE /dist_of_RV fdistmap_comp.
rewrite spectator_pre_uniformE.
apply: (fdistmap_bij_uniform card_spectator_pre card_spectator_pre2).
exists (fun d : alice_spectator_pre2T => (d.1.1.1, (d.1.2, d.2), d.1.1.2)).
  by move=> [[[r2 r3] [rho2 rho3]] [ra1 ra2]].
by move=> [[[[r2 r3] [ra1 ra2]] rho2] rho3].
Qed.

(* The spectator rebuilt from the reordered spectator coordinates. *)
Definition alice_spectator_prod (c : alice_spectator_pre2T) :
    ((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)%type :=
  (c.1.1.1, c.1.1.2,
   chcipher_of_cipher (enc (pkey_of_party Bob) 0 (rand_of_renc c.1.2)),
   chcipher_of_cipher (enc (pkey_of_party Charlie) 0 (rand_of_renc c.2))).

(* The spectator is the image of the reordered spectator coordinates under the
   zero-plaintext encryptions. *)
Lemma alice_spectator_prodE :
  AliceSpectator = alice_spectator_prod `o AliceSpectatorPre2.
Proof.
by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
Qed.

(* The law of the spectator is the product of the mask law, the combine
   randomness law and the two zero-plaintext encryption laws. *)
Lemma alice_spectator_law :
  `p_ AliceSpectator
  = ((((fdist_uniform card_plain_pair) `x (fdist_uniform card_renc_pair))
        `x (enc_fdist (pkey_of_party Bob) 0))
       `x (enc_fdist (pkey_of_party Charlie) 0)).
Proof.
have -> : `p_ AliceSpectator
        = fdistmap alice_spectator_prod (`p_ AliceSpectatorPre2).
  by rewrite alice_spectator_prodE /dist_of_RV fdistmap_comp.
rewrite spectator_pre2_uniformE
        (fdist_uniform_prod card_masks_ra_rho card_renc card_spectator_pre2)
        (fdist_uniform_prod card_masks_ra card_renc card_masks_ra_rho)
        (fdist_uniform_prod card_plain_pair card_renc_pair card_masks_ra).
rewrite /enc_fdist -!fdistmap_prodr -[X in _ = fdistmap _ (_ `x X)]fdistmap_id.
rewrite -fdistmap_prod fdistmap_comp; congr fdistmap.
by apply/boolp.funext => -[[[m ra] rho2] rho3].
Qed.

(* The spectator slots of a value of Alice's view. *)
Definition alice_spectator_of_view (v : dsdp_alice_viewT) :
    ((plain AHE * plain AHE) * (Renc * Renc) * t_cipher * t_cipher)%type :=
  (v.1.1.1.1, v.1.1.1.2, v.1.2, v.2).

(* On a conditioning event that determines the leaked output, the joint mass of
   Alice's all-zero view splits into the leaked-output indicator times the joint
   mass of the spectator. *)
Lemma alice_view_all_zero_pfwd1E (BT : finType)
    (W : {RV alice_sample_fdist -> BT}) (v : dsdp_alice_viewT) (w : BT)
    (s : plain AHE) :
  (forall t, W t = w -> Sout t = s) ->
  pfwd1 [% AliceView_all_zero, W] (v, w)
  = (v.1.1.2 == s)%:R
    * pfwd1 [% AliceSpectator, W] (alice_spectator_of_view v, w).
Proof.
move=> HW; case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_view /=.
case: (altP (sv =P s)) => [->|Hne]; last first.
  rewrite mul0r pfwd1E (_ : finset _ = set0) ?Pr_set0 //.
  apply/setP => t; rewrite !inE; apply/negbTE; apply: contra Hne.
  rewrite !xpair_eqE => /andP[/andP[/andP[/andP[_ Hsv] _] _] Hw].
  by rewrite -(eqP Hsv) (HW t (eqP Hw)).
rewrite mul1r !pfwd1E; congr (Pr _ _).
apply/setP => t; rewrite !inE !xpair_eqE.
case Ew : (W t == w); last by rewrite !andbF.
by rewrite (HW t (eqP Ew)) eqxx !andbT.
Qed.

(* Conditioned on the two secret inputs, Alice's all-zero view follows the
   simulator law fed the leaked output of those inputs.
   Naming: after [bob_view_cond_sim] of [du2002/spp_simulator.v], with the
   [dsdp_alice] prefix separating it from that near-namesake. *)
Lemma dsdp_alice_view_cond_sim (v : dsdp_alice_viewT) (v2 v3 : plain AHE) :
  `Pr[ [% V2, V3] = (v2, v3) ] != 0 ->
  `Pr[ AliceView_all_zero = v | [% V2, V3] = (v2, v3) ]
    = dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 v2 v3) v.
Proof.
move=> Hvv.
have HW t : [% V2, V3] t = (v2, v3) ->
    Sout t = dsdp_output w_v1 w_u1 w_u2 w_u3 v2 v3.
  by rewrite /Sout /comp_RV => ->.
rewrite cpr_eqE (alice_view_all_zero_pfwd1E v HW) (alice_spectator_indep _ _).
rewrite mulrA mulfK // -dist_of_RVE alice_spectator_law.
case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_view /dsdp_alice_simulator !fdist_prodE fdist1E /=.
by ring.
Qed.

(* Conditioned on the leaked output, Alice's all-zero view follows the simulator
   law fed that output. *)
Corollary dsdp_alice_view_cond_sim_S (v : dsdp_alice_viewT)
    (s : plain AHE) :
  `Pr[ Sout = s ] != 0 ->
  `Pr[ AliceView_all_zero = v | Sout = s ] = dsdp_alice_simulator s v.
Proof.
move=> Hs.
have Hind : alice_sample_fdist |= AliceSpectator _|_ Sout.
  exact: (inde_RV_comp idfun (uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3))
            alice_spectator_indep).
rewrite cpr_eqE (alice_view_all_zero_pfwd1E v (fun=> id)) (Hind _ _).
rewrite mulrA mulfK // -dist_of_RVE alice_spectator_law.
case: v => [[[[m ra] sv] c2] c3].
rewrite /alice_spectator_of_view /dsdp_alice_simulator !fdist_prodE fdist1E /=.
by ring.
Qed.

(* The ideal-world joint law of the two secret inputs and a simulated view: the
   honest input law bound to the simulator fed the leaked output. *)
Definition alice_ideal_joint :
    R.-fdist (plain AHE * plain AHE * dsdp_alice_viewT) :=
  `p_ [% V2, V3] >>= (fun vv =>
     fdistmap (fun v => (vv.1, vv.2, v))
       (dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2))).

(* The ideal-world joint law is the joint law of the two secret inputs and
   Alice's all-zero view. *)
Lemma alice_ideal_jointE :
  alice_ideal_joint = `p_ [% V2, V3, AliceView_all_zero].
Proof.
apply/fdist_ext => -[[v2 v3] v].
rewrite fdistbindE (bigD1 (v2, v3)) //= big1 ?addr0; last first.
  move=> [w2 w3] Hne; rewrite [X in _ * X]fdistmapE big1 ?mulr0 // => a.
  by rewrite !inE /= xpair_eqE (negbTE Hne).
rewrite [X in _ * X]fdistmapE (big_pred1 v); last first.
  by move=> a; rewrite !inE /= xpair_eqE eqxx.
rewrite !dist_of_RVE [RHS]pfwd1_pairC /unstable.swap /=.
case: (altP (`Pr[ [% V2, V3] = (v2, v3) ] =P 0)) => H0.
  by rewrite H0 mul0r pfwd1_domin_RV1.
by rewrite -[RHS]cpr_eqE_mul (dsdp_alice_view_cond_sim v H0) mulrC.
Qed.

(* A distinguisher separates the real joint law of the two secret inputs and
   Alice's view from the ideal-world joint law by at most the sum of the
   advantages of the two hop reductions.
   Naming: [sim_advantage] rather than [advantage_sim] because the statement
   bounds a distinguishing gap between two laws instead of instantiating the
   [advantage_sim_le] predicate of [smc/ssprove_ext_simulator.v]. *)
Theorem dsdp_alice_sim_advantage_fdist_le
    (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceView_zero_prefix 0]) [set x | D x]
     - Pr (fdistmap D alice_ideal_joint) [set true] |
  <= indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D)
     + indcpa_fdist_epsilon (pkey_of_party Charlie) (hop1_reduction D).
Proof.
rewrite Pr_fdistmap_bool alice_ideal_jointE.
rewrite -hop0_advantageE -hop1_advantageE.
exact: ler_distD.
Qed.

(* The full corrupted-Alice view rebuilt from a value of the reduced view: that
   value, Alice's two outgoing combines, and the plaintext of her final
   decrypt-on-receive.
   Naming: [_of] after the repository's total-conversion family, paired with
   the [_ok] correctness lemma below as in [bob_ext] and [bob_ext_ok]. *)
Definition alice_view_full_of (v : dsdp_alice_viewT) :
    dsdp_alice_viewT * cipher AHE * cipher AHE * plain AHE :=
  let c_bob := cipher_of_chcipher v.1.2 in
  let c_charlie := cipher_of_chcipher v.2 in
  let r2 := v.1.1.1.1.1 in
  let r3 := v.1.1.1.1.2 in
  let ra1 := v.1.1.1.2.1 in
  let ra2 := v.1.1.1.2.2 in
  let s := v.1.1.2 in
  let combine_bob :=
    Emul (Epow c_bob w_u2)
         (enc (pkey_of_party Bob) r2 (rand_of_renc ra1)) in
  let combine_charlie :=
    Emul (Epow c_charlie w_u3)
         (enc (pkey_of_party Charlie) r3 (rand_of_renc ra2)) in
  let recv_plain := s - w_u1 * w_v1 + r2 + r3 in
  (v, combine_bob, combine_charlie, recv_plain).

(* Alice's outgoing combine toward Bob's key, replaying her real protocol step:
   the ciphertext she received from Bob raised to her second weight, times an
   encryption of her first mask.  Used by alice_view_full_ok. *)
Definition AliceCombineBob : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc (pkey_of_party Bob) (V2 t) (rand_of_renc (Rho2 t))) w_u2)
    (enc (pkey_of_party Bob) (R2 t) (rand_of_renc (RA1 t))).

(* Alice's outgoing combine toward Charlie's key, the symmetric counterpart of
   AliceCombineBob: the ciphertext she received from Charlie raised to her
   third weight, times an encryption of her second mask.  Used by
   alice_view_full_ok. *)
Definition AliceCombineCharlie : {RV alice_sample_fdist -> cipher AHE} :=
  fun t => Emul
    (Epow (enc (pkey_of_party Charlie) (V3 t) (rand_of_renc (Rho3 t))) w_u3)
    (enc (pkey_of_party Charlie) (R3 t) (rand_of_renc (RA2 t))).

(* The plaintext Alice recovers at her final decrypt-on-receive step: the two
   weighted inputs of the other parties plus her two masks.  The last of the
   four observables alice_view_full_ok assembles.
   Naming: Owner-Verb-Noun, parallel to AliceCombineBob and
   AliceCombineCharlie; [Plain] is the AHE plaintext carrier. *)
Definition AliceRecvPlain : {RV alice_sample_fdist -> plain AHE} :=
  fun t => w_u2 * V2 t + w_u3 * V3 t + R2 t + R3 t.

(* Alice's four real observables: her reduced view, her two outgoing combines,
   and the plaintext of her final decrypt-on-receive. *)
Definition AliceViewFull :
    {RV alice_sample_fdist ->
       (dsdp_alice_viewT * cipher AHE * cipher AHE * plain AHE)%type} :=
  [% AliceView, AliceCombineBob, AliceCombineCharlie, AliceRecvPlain].

(* Alice's four real observables assemble into the reconstruction of the full
   view from the reduced view.
   Naming: [_ok] marks the correctness lemma of [alice_view_full_of], after
   the [bob_ext] and [bob_ext_ok] pair. *)
Lemma alice_view_full_ok :
  (fun t => alice_view_full_of (AliceView t))
  = (fun t => (AliceView t, AliceCombineBob t, AliceCombineCharlie t,
               AliceRecvPlain t)).
Proof.
apply/boolp.funext => t.
rewrite /alice_view_full_of /AliceCombineBob /AliceCombineCharlie
        /AliceRecvPlain /= !chcipher_of_cipherK.
congr (_, _, _, _).
by rewrite /Sout /comp_RV /dsdp_output /=; ring.
Qed.

(* Alice's full view is the reconstruction applied to her reduced view. *)
Lemma alice_view_fullE : AliceViewFull = (alice_view_full_of \o AliceView).
Proof. exact: esym alice_view_full_ok. Qed.

(* A predictor reading Alice's full real view matches Bob's input with
   probability at most 1/#|plain AHE| plus the advantages of the two hop
   reductions.
   Naming: [dsdp_alice_guess_fdist] as in the reduced-view headline, with
   [full] naming the view read. *)
Corollary dsdp_alice_guess_fdist_full_le
    (g' : dsdp_alice_viewT * cipher AHE * cipher AHE * plain AHE
          -> plain AHE) :
  Pr alice_sample_fdist [set t | (g' `o AliceViewFull) t == V2 t]
    <= #|plain AHE|%:R^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction
              (distinguisher_of_guess (g' \o alice_view_full_of)))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction
              (distinguisher_of_guess (g' \o alice_view_full_of))).
Proof.
rewrite alice_view_fullE.
exact: dsdp_alice_guess_fdist_V2_real_le.
Qed.

End dsdp_alice_infotheo_secrecy.
