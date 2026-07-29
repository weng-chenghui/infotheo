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
Lemma fdist_uniform_prod (T1 T2 : finType) (n1 n2 : nat)
    (c1 : #|T1| = n1.+1) (c2 : #|T2| = n2.+1)
    (c12 : #|((T1 * T2)%type : finType)| = (n1.+1 * n2.+1)%N.-1.+1) :
  fdist_uniform (R:=R) c12 = (fdist_uniform c1) `x (fdist_uniform c2).
Proof.
apply/fdist_ext => -[a b]; rewrite fdist_prodE !fdist_uniformE.
by rewrite card_prod natrM invfM.
Qed.

(* The pushforward of a uniform along a bijection is uniform. *)
Lemma fdistmap_bij_uniform (T1 T2 : finType) (n : nat)
    (c1 : #|T1| = n.+1) (c2 : #|T2| = n.+1) (g : T1 -> T2) :
  bijective g ->
  fdistmap g (fdist_uniform (R:=R) c1) = fdist_uniform c2.
Proof.
case=> h ghK hgK; apply/fdist_ext => b.
rewrite fdistmapE fdist_uniformE (big_pred1 (h b)); last first.
  by move=> a; rewrite !inE /=; apply/eqP/eqP => [<-|->].
by rewrite fdist_uniformE c1 c2.
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

End dsdp_alice_infotheo_secrecy.
