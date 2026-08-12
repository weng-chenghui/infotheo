From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_weighted_words.
From pgg_smc Require Import five_card_group five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_monodromy_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope vec_ext_scope.

Section one_letter.
Variable R : realType.
Variables (N'' m : nat).
Variable sigmas : m.+1.-tuple {perm 'I_N''.+2}.
Variable W : R.-fdist 'I_m.+1.

Lemma fdistmap_head1 :
  fdistmap (fun v : 'rV['I_m.+1]_1 => v ``_ ord0) (W `^ 1) = W.
Proof.
apply/fdist_ext => k; rewrite fdistmapE.
rewrite (big_pred1 (\row_(_ < 1) k)); last first.
  move=> v /=; rewrite !inE.
  apply/idP/idP.
    by move/eqP => H; apply/eqP/rowP => i; rewrite (ord1 i) mxE.
  by move/eqP => ->; rewrite mxE.
by rewrite fdist_rV1 mxE.
Qed.

Lemma rho_from_words_weighted1 :
  @rho_from_words_weighted R N'' m 1 sigmas W = fdistmap (tnth sigmas) W.
Proof.
rewrite /rho_from_words_weighted /word_weighted fdistmap_comp.
have -> : (@word_eval (Gen_PGGTypes sigmas) 1) \o (@tuple_of_row _ 1)
        = (tnth sigmas) \o (fun v : 'rV['I_m.+1]_1 => v ``_ ord0).
  apply: funext => v; rewrite /= /word_eval big_ord1.
  by congr (tnth sigmas _); rewrite tnth_mktuple.
by rewrite -fdistmap_comp fdistmap_head1.
Qed.

End one_letter.

Section invariant3.
Variable R : realType.

Lemma kim_weight_uniform_at0 :
  kim_weight_dist (den_boer_eps0_lt R) (den_boer_eps0_gt R)
  = fdist_uniform (card_ord 5).
Proof.
apply/fdist_ext => k; rewrite kim_weight_distE fdist_uniformE card_ord.
by case: ifP => _; [rewrite subr0 | rewrite mul0r addr0].
Qed.

(* The five-card witness distribution at the den Boer parameters (eps = 0,
   L = 1) IS the C3 rotation image distribution. *)
Lemma denboer_witness_is_rotation :
  sw_rho_dist (mp_security (den_boer_profile R))
  = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).
Proof.
rewrite /den_boer_profile /= rho_from_words_weighted1 kim_weight_uniform_at0.
by congr fdistmap; apply: funext => k; exact: fc_kim_sigmasE.
Qed.

End invariant3.

Print Assumptions denboer_witness_is_rotation.
