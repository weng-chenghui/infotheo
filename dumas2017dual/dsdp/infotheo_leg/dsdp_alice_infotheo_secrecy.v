(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy, infotheo axis                              *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

Import GRing.Theory.
Import Num.Theory.

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

Definition dsdp_alice_sampleT : finType :=
  ((plain AHE * plain AHE) * (plain AHE * plain AHE)
   * (Renc * Renc) * (Renc * Renc))%type.

Definition alice_sample_fdist : R.-fdist dsdp_alice_sampleT :=
  (((fdist_uniform card_plain_pair) `x (fdist_uniform card_plain_pair))
     `x (fdist_uniform card_renc_pair)) `x (fdist_uniform card_renc_pair).

Definition V2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.1.
Definition V3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.1.2.
Definition R2 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.1.
Definition R3 : {RV alice_sample_fdist -> plain AHE} := fun t => t.1.1.2.2.
Definition Rho2 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.1.
Definition Rho3 : {RV alice_sample_fdist -> Renc} := fun t => t.1.2.2.
Definition RA1 : {RV alice_sample_fdist -> Renc} := fun t => t.2.1.
Definition RA2 : {RV alice_sample_fdist -> Renc} := fun t => t.2.2.

Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry (dsdp_output w_v1 w_u1 w_u2 w_u3) `o [% V2, V3].

Definition hop0_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Bob) (if (0 < i)%N then 0 else V2 t)
         (rand_of_renc (Rho2 t))).
Definition hop1_cipher (i : nat) : {RV alice_sample_fdist -> t_cipher} :=
  fun t => chcipher_of_cipher
    (enc (pkey_of_party Charlie) (if (1 < i)%N then 0 else V3 t)
         (rand_of_renc (Rho3 t))).

Definition dsdp_alice_viewT : finType :=
  ((plain AHE * plain AHE) * (Renc * Renc) * plain AHE
   * t_cipher * t_cipher)%type.

Definition AliceView_zero_prefix (i : nat) :
    {RV alice_sample_fdist -> dsdp_alice_viewT} :=
  [% [% R2, R3], [% RA1, RA2], Sout, hop0_cipher i, hop1_cipher i].

Notation AliceView := (AliceView_zero_prefix 0).
Notation AliceView_all_zero := (AliceView_zero_prefix 2).

Definition E_bob_v2 := hop0_cipher 0.
Definition E_charlie_v3 := hop1_cipher 0.

Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist t_cipher :=
  fdistmap (fun r => chcipher_of_cipher (enc pk v (rand_of_renc r)))
           (fdist_uniform card_renc).

Record indcpa_fdist_adversary := {
  adv_context : finType ;
  adv_choose : R.-fdist adv_context ;
  adv_plain : adv_context -> plain AHE ;
  adv_decide : adv_context -> t_cipher -> bool }.

Arguments adv_choose : clear implicits.
Arguments adv_plain : clear implicits.
Arguments adv_decide : clear implicits.

Definition indcpa_fdist_success_real (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk (adv_plain adv c))))
     [set true].
Definition indcpa_fdist_success_zero (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  Pr (adv_choose adv >>= (fun c => fdistmap (adv_decide adv c)
                                     (enc_fdist pk 0)))
     [set true].
Definition indcpa_fdist_epsilon (pk : pub_key AHE)
    (adv : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk adv - indcpa_fdist_success_zero pk adv |.

(* The law of a context paired with a slot computed from the context and a
   coordinate the context does not read is the law of the context with the
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

Definition Hop1Ctx : {RV alice_sample_fdist -> hop1_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, hop0_cipher 1 t).

Definition Hop1PreCtx : {RV alice_sample_fdist -> hop0_ctxT} :=
  fun t => (t.1.1.1, t.1.1.2, t.2, t.1.2.1).

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
have Hslot :
  `p_ [% Hop0Ctx, hop0_cipher 0]
    = (`p_ Hop0Ctx) `X (fun c : hop0_ctxT =>
        fdistmap (fun r => chcipher_of_cipher
                    (enc (pkey_of_party Bob) c.1.1.1.1 (rand_of_renc r)))
                 (fdist_uniform card_renc))
  := enc_slot_resampleE _ hop0_ctx_prod.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_real /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 0])
        = fdistmap (fun p : (hop0_ctxT * t_cipher)%type =>
                      D (hop0_assemble p.1 p.2))
                   (`p_ [% Hop0Ctx, hop0_cipher 0]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite Hslot fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* The distinguisher on the view with a zeroed hop-0 slot is the hop-0
   reduction facing an encryption of zero. *)
Lemma hop0_zero_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 1]) [set x | D x]
    = indcpa_fdist_success_zero (pkey_of_party Bob) (hop0_reduction D).
Proof.
have Hslot :
  `p_ [% Hop0Ctx, hop0_cipher 1]
    = (`p_ Hop0Ctx) `X (fun _ : hop0_ctxT =>
        fdistmap (fun r => chcipher_of_cipher
                    (enc (pkey_of_party Bob) 0 (rand_of_renc r)))
                 (fdist_uniform card_renc))
  := enc_slot_resampleE _ hop0_ctx_prod.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_zero /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 1])
        = fdistmap (fun p : (hop0_ctxT * t_cipher)%type =>
                      D (hop0_assemble p.1 p.2))
                   (`p_ [% Hop0Ctx, hop0_cipher 1]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite Hslot fdist_prod_bindE fdistmap_bind.
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
have Hslot :
  `p_ [% Hop1Ctx, hop1_cipher 1]
    = (`p_ Hop1Ctx) `X (fun c : hop1_ctxT =>
        fdistmap (fun r => chcipher_of_cipher
                    (enc (pkey_of_party Charlie) c.1.1.1.2 (rand_of_renc r)))
                 (fdist_uniform card_renc))
  := enc_slot_resampleE _ hop1_ctx_prod.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_real /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 1])
        = fdistmap (fun p : (hop1_ctxT * t_cipher)%type =>
                      D (hop1_assemble p.1 p.2))
                   (`p_ [% Hop1Ctx, hop1_cipher 1]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite Hslot fdist_prod_bindE fdistmap_bind.
congr (Pr _ _); congr (_ >>= _); apply/boolp.funext => c.
by rewrite /enc_fdist !fdistmap_comp.
Qed.

(* The distinguisher on the all-zero view is the hop-1 reduction facing an
   encryption of zero. *)
Lemma hop1_zero_armE (D : plain AHE * plain AHE * dsdp_alice_viewT -> bool) :
  Pr (`p_ [% V2, V3, AliceView_zero_prefix 2]) [set x | D x]
    = indcpa_fdist_success_zero (pkey_of_party Charlie) (hop1_reduction D).
Proof.
have Hslot :
  `p_ [% Hop1Ctx, hop1_cipher 2]
    = (`p_ Hop1Ctx) `X (fun _ : hop1_ctxT =>
        fdistmap (fun r => chcipher_of_cipher
                    (enc (pkey_of_party Charlie) 0 (rand_of_renc r)))
                 (fdist_uniform card_renc))
  := enc_slot_resampleE _ hop1_ctx_prod.
rewrite -Pr_fdistmap_bool /indcpa_fdist_success_zero /=.
have -> : fdistmap D (`p_ [% V2, V3, AliceView_zero_prefix 2])
        = fdistmap (fun p : (hop1_ctxT * t_cipher)%type =>
                      D (hop1_assemble p.1 p.2))
                   (`p_ [% Hop1Ctx, hop1_cipher 2]).
  rewrite /dist_of_RV !fdistmap_comp; congr fdistmap.
  by apply/boolp.funext => -[[[[v2 v3] [r2 r3]] [rho2 rho3]] [ra1 ra2]].
rewrite Hslot fdist_prod_bindE fdistmap_bind.
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

End dsdp_alice_infotheo_secrecy.
