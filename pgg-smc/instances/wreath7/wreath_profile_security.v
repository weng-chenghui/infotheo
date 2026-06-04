(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Quantitative security of the MonodromyProfile plugs: floor vs vanishing    *)
(*                                                                            *)
(* The MonodromyProfile demonstration (wreath_monodromy_profile.v) plugs the   *)
(* abelian Z_2 x Z_2, the wreath Z_7 wr S_2 and S_5 into ONE run_* program.    *)
(* This file separates their SECURITY characters as a real-number inequality.  *)
(* It is kept apart from wreath_monodromy_profile.v because the piSMC / session *)
(* notations that file needs shadow ring_scope's numeral notations; here       *)
(* ring_scope is clean.                                                        *)
(*                                                                            *)
(* The L = 1 epsilon bounds (sw_bound_eps) do NOT separate the plugs (wreath   *)
(* 11/7, abelian 1, S_5 6/5): one word length is not where the characters     *)
(* part. The separation is the L -> infinity behaviour of the endpoint         *)
(* distribution sigma |-> sigma s under the protocol walk rho_from_words L:     *)
(*                                                                            *)
(*   abelian  The disjoint transpositions (0 1),(2 3) fix the block {0,1}      *)
(*            setwise, so card 0's endpoint never leaves {0,1}: card 2 keeps    *)
(*            probability 0 for EVERY L, forcing var_dist >= 1/4 with no        *)
(*            dependence on L (abel_var_dist_floor). The walk cannot mix.       *)
(*   S_5      The adjacent transpositions act transitively with a positive      *)
(*            spectral gap, so the Schreier-walk witness's SecurityAsymptotic   *)
(*            has additive floor sa_eps_inf = 0 (s5_eps_inf_zero) and bound     *)
(*            sqrt 5 * (1 - gap)^L with 0 <= 1 - gap < 1 (s5_decay_base_lt1),   *)
(*            so the endpoint reaches uniform: at some L it beats the abelian   *)
(*            floor 1/4 for every start sheet (s5_beats_abelian_floor).         *)
(*                                                                            *)
(* So the same run_* program is floored-insecure at the abelian plug and       *)
(* asymptotically-secure at the S_5 plug: a genuine inequality, not a tie.     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals normedtype sequences.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import pgg_collusion_bound rigidity_abelian_instance.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5 s5_mixing
                            rigidity_s5_instance.
From pgg_reconstruct Require Import pgg_sharing_framework algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

Section profile_security.

Variable R : realType.

(******************************************************************************)
(*     The abelian floor: card 0 never leaves the block {0,1}                  *)
(******************************************************************************)

Let o0a : 'I_4 := Ordinal (n:=4) (isT : (0 < 4)%N).
Let o2a : 'I_4 := Ordinal (n:=4) (isT : (2 < 4)%N).
Let Bblock : {set 'I_4} := [set o0a; Ordinal (n:=4) (isT : (1 < 4)%N)].

(** abel_block_stable — the abelian group keeps card 0 in the block {0,1}.
    Kind: helper.
    Why: the generators (0 1),(2 3) stabilise {0,1} setwise, so the whole
    generated group does (gen_subG into the setwise stabiliser 'N(_|'P)); card 0
    therefore never reaches card 2. The structural root of the security floor.
    Used by: abel_var_dist_floor. *)
Lemma abel_block_stable (g : {perm 'I_4}) :
  g \in pgg_G (Gen_PGGTypes abel_sigmas) -> g o0a \in Bblock.
Proof.
move=> Hg.
have Hsub : pgg_G (Gen_PGGTypes abel_sigmas) \subset 'N(Bblock | 'P)%g.
  rewrite -pgg_sigmas_gen gen_subG.
  apply/subsetP => x /imsetP[i _ ->].
  apply/astabsP => y.
  rewrite /pgg_sigmas (tnth_nth abel_s1) /=.
  case: i => -[|[|i]] Hi //=; rewrite /aperm /abel_s1 /abel_s2;
    case: y => -[|[|[|[|y]]]] Hy //=; rewrite ?permE ?inE //=.
have Hg' := subsetP Hsub g Hg.
move/astabsP: Hg' => /(_ o0a) H.
suff: 'P%act o0a g \in Bblock by [].
by rewrite H !inE eqxx.
Qed.

(** abel_endpoint_card2_zero — card 2 carries no endpoint probability, every L.
    Kind: helper.
    Why: the support of the abelian endpoint walk is achievable(L) ⊆ G, which by
    abel_block_stable maps card 0 into {0,1}; so the pushforward at card 2 is an
    empty sum. Used by: abel_var_dist_floor. *)
Lemma abel_endpoint_card2_zero (L : nat) :
  fdistmap (fun s : {perm 'I_4} => s o0a)
           (@rho_from_words R 2 1 L abel_sigmas) o2a = 0.
Proof.
rewrite /rho_from_words fdistmap_comp fdistmapE.
apply: big_pred0 => w /=.
apply/negbTE/negP => /eqP Heq.
have Hach : word_eval w \in pgg_G (Gen_PGGTypes abel_sigmas).
  apply: (subsetP (achievable_sub (Gen_PGGTypes abel_sigmas) L)).
  by apply/imsetP; exists w.
have Hb := abel_block_stable Hach.
move: Heq; rewrite /comp /= => Heq.
by move: Hb; rewrite Heq !inE.
Qed.

(** abel_var_dist_floor — the abelian endpoint stays >= 1/4 from uniform, all L.
    Kind: main.
    Why: card 2 is unreachable from card 0 (abel_endpoint_card2_zero), so the
    endpoint puts mass 0 on card 2; leq_var_dist at card 2 then floors var_dist
    by |0 - 1/4| = 1/4 independently of the word length L. The "insecure" half
    of the contrast: no protocol length helps. *)
Lemma abel_var_dist_floor (L : nat) :
  (4%:R^-1 <=
   var_dist (fdistmap (fun s : {perm 'I_4} => s o0a)
                      (@rho_from_words R 2 1 L abel_sigmas))
            (fdist_uniform (card_ord 4)))%O.
Proof.
have H := leq_var_dist (fdistmap (fun s : {perm 'I_4} => s o0a)
                          (@rho_from_words R 2 1 L abel_sigmas))
                       (fdist_uniform (card_ord 4)) o2a.
move: H; rewrite abel_endpoint_card2_zero sub0r normrN fdist_uniformE card_ord.
rewrite ger0_norm; last by rewrite invr_ge0 ler0n.
by [].
Qed.

(******************************************************************************)
(*     The S_5 vanishing: the asymptotic floor is 0, base in [0, 1)            *)
(******************************************************************************)

(** s5_eps_inf_zero — the S_5 asymptotic certificate has additive floor 0.
    Kind: main.
    Why: the "secure" half: the Schreier-walk witness's SecurityAsymptotic
    converges to 0 (sa_eps_inf = 0), the opposite of the abelian floor. *)
Lemma s5_eps_inf_zero : sa_eps_inf (s5_asymptotic R) = 0.
Proof. by []. Qed.

(** s5_var_dist_bound — the S_5 endpoint is within sqrt 5 * (1 - gap)^L of uniform.
    Kind: main.
    Why: the geometric decay backing the vanishing security; the base
    1 - s5_gap_R = 181/200 < 1 (s5_decay_base_lt1), so the bound -> 0 as L grows. *)
Lemma s5_var_dist_bound (L : nat) (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                      (rho_from_words L (path_gen_tuple 3)))
            (fdist_uniform (card_ord 5))
   <= Num.sqrt 5%:R * (1 - s5_gap_R R) ^+ L)%O.
Proof. exact: s5_spectral_convergence_gap. Qed.

(** s5_decay_base_lt1 — the geometric decay base lies in [0, 1).
    Kind: helper.
    Why: 0 <= 1 - gap < 1, the contraction that drives s5_var_dist_bound to 0.
    Used by: s5_beats_abelian_floor. *)
Lemma s5_decay_base_lt1 : (0 <= 1 - s5_gap_R R) /\ (1 - s5_gap_R R < 1).
Proof.
split.
  by rewrite subr_ge0 s5_gap_R_le1.
by rewrite ltrBlDr ltrDl s5_gap_R_pos.
Qed.

(******************************************************************************)
(*     The crossover: the S_5 plug beats the abelian floor                     *)
(******************************************************************************)

(** s5_beats_abelian_floor — at some word length the S_5 endpoint is closer to
    uniform than the abelian's permanent floor 1/4, for every start sheet.
    Kind: main.
    Why: THE quantitative separation. var_dist(S_5) <= sqrt 5 * (1 - gap)^L decays
    geometrically to 0 (s5_decay_base_lt1), so it eventually drops below 4%:R^-1,
    the lower bound the abelian plug can never beat (abel_var_dist_floor). Same
    run_* program, two genuinely different security characters. *)
Lemma s5_beats_abelian_floor :
  exists L : nat, forall s : 'I_5,
    (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                        (@rho_from_words R _ _ L (path_gen_tuple 3)))
              (fdist_uniform (card_ord 5)) < 4%:R^-1)%O.
Proof.
have [Ha0 Ha1] := s5_decay_base_lt1.
have Hsqrt5 : (0 < Num.sqrt 5%:R :> R) by rewrite sqrtr_gt0 ltr0n.
have Heps : (0 < (4%:R * Num.sqrt 5%:R)^-1 :> R)
  by rewrite invr_gt0 mulr_gt0 // ltr0n.
have Hb : `|1 - s5_gap_R R| < 1 by rewrite ger0_norm.
have Hcvg := cvg_expr Hb.
have [N HN] : exists N : nat, (1 - s5_gap_R R) ^+ N < (4%:R * Num.sqrt 5%:R)^-1.
  have Hd := (@cvgrPdist_lt R R^o nat _ _ (GRing.exp (1 - s5_gap_R R)) 0).1 Hcvg.
  have [N _ HNb] := Hd _ _ Heps.
  exists N.
  have := HNb N (leqnn N).
  by rewrite sub0r normrN ger0_norm // exprn_ge0.
exists N => s.
apply: (Order.POrderTheory.le_lt_trans (s5_var_dist_bound N s)).
have -> : 4%:R^-1 = Num.sqrt 5%:R * (4%:R * Num.sqrt 5%:R)^-1 :> R.
  rewrite invfM mulrCA mulfV ?mulr1 //.
  exact: lt0r_neq0 Hsqrt5.
rewrite (ltr_pM2l Hsqrt5); exact: HN.
Qed.

End profile_security.
