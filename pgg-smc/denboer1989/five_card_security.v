(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Five-Card Trick: Transitivity and Regularity of the C_5 Action            *)
(*                                                                            *)
(* The five-card trick uses fc_sigma = (0 1 2 3 4), a 5-cycle generating      *)
(* C_5. This file proves:                                                     *)
(*                                                                            *)
(*   fc_G_pos       == the group C_5 is non-trivial (0 < |G|)                 *)
(*   fc_orbit_full  == C_5 acts transitively on 'I_5: the orbit of any        *)
(*                     sheet s under G is all of 'I_5                         *)
(*   fc_eval_inj    == C_5 acts regularly: eval_at s is injective on G        *)
(*                     (since |G| = |'I_5| = 5)                               *)
(*                                                                            *)
(* These properties are prerequisites for the SecurityWitness instantiation.  *)
(*                                                                            *)
(* TODO (future work): populate `sw_exact` of fc_security_uniform with the   *)
(* exact var_dist = 0 equality for the uniform case. This is a one-step      *)
(* follow-up via `security_witness_with_exact`. See five_card_kim.v header   *)
(* for the Kim biased case.                                                   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm action.
From mathcomp Require Import morphism ssralg boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group pgg_collusion_bound
                            pgg_uniform_security.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope group_scope.

Section five_card_security.

(** Local abbreviations *)
Let G := pgg_G FiveCard_M.
Let sigma := fc_sigma.

(******************************************************************************)
(** * Auxiliary: fc_sigma computes as expected                                *)
(******************************************************************************)

Lemma fc_sigma_perm (x : 'I_5) : sigma x = fc_sigma_fun x.
Proof. by rewrite /sigma permE. Qed.

(** sigma^5 = 1 by direct computation *)
Lemma fc_sigma5 : sigma ^+ 5 = 1 :> {perm 'I_5}.
Proof.
apply/permP => x; rewrite perm1.
by case: x => [[|[|[|[|[|x]]]]] hx];
  rewrite !expgSr expg0 !permM !permE //=; apply/val_inj.
Qed.

(** sigma is in G *)
Lemma fc_sigma_in_G : sigma \in G.
Proof.
rewrite /G /FiveCard_M /=.
apply: mem_gen.
by apply/imsetP; exists (Ordinal (ltn0Sn 0)); rewrite // tnth_ord_tuple.
Qed.

(** All powers of sigma are in G *)
Lemma fc_sigma_pow_in_G (k : nat) : sigma ^+ k \in G.
Proof. by apply: groupX; exact: fc_sigma_in_G. Qed.

(******************************************************************************)
(** * Concrete evaluation of sigma^k at each sheet                            *)
(******************************************************************************)

(** We compute sigma^k(s) for k=0..4 and all s by direct expansion. *)

Lemma fc_pow0 (s : 'I_5) : (sigma ^+ 0) s = s.
Proof. by rewrite expg0 perm1. Qed.

Lemma fc_pow1 (s : 'I_5) : val ((sigma ^+ 1) s) = (val s).+1 %% 5.
Proof.
rewrite expg1 fc_sigma_perm /fc_sigma_fun.
by case: s => [[|[|[|[|[|s]]]]] hs].
Qed.

(** For each target x, we exhibit the power of sigma that maps s to x. *)
Lemma fc_reach (s x : 'I_5) :
  exists k : 'I_5, (sigma ^+ val k) s = x.
Proof.
case: s => [[|[|[|[|[|s]]]]] hs];
case: x => [[|[|[|[|[|x]]]]] hx] //;
  try (by exists (Ordinal (isT : (0 < 5)%N)); rewrite expg0 perm1; apply/val_inj);
  try (by exists (Ordinal (isT : (1 < 5)%N));
    rewrite expg1 permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (2 < 5)%N));
    rewrite expgSr expg1 permM !permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (3 < 5)%N));
    rewrite !expgSr expg0 !permM perm1 !permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (4 < 5)%N));
    rewrite !expgSr expg0 !permM perm1 !permE /fc_sigma_fun /=; apply/val_inj).
Qed.

(******************************************************************************)
(** * Non-triviality of G                                                     *)
(******************************************************************************)

Lemma fc_G_pos : (0 < #|G|)%N.
Proof. exact: cardG_gt0. Qed.

(******************************************************************************)
(** * Transitivity: the orbit of any sheet s under G is all of 'I_5          *)
(******************************************************************************)

Lemma fc_orbit_full (s : 'I_5) :
  [set (g : {perm 'I_5}) s | g in G] = [set: 'I_5].
Proof.
have H : forall x : 'I_5, x \in [set (g : {perm 'I_5}) s | g in G] = (x \in [set: 'I_5]).
  move=> x; rewrite inE; apply/imsetP.
  have [k Hk] := fc_reach s x.
  exists (sigma ^+ val k); first exact: fc_sigma_pow_in_G.
  exact/esym/Hk.
apply/setP => x; exact: H.
Qed.

(******************************************************************************)
(** * Regularity: eval_at s is injective on G                                *)
(******************************************************************************)

(** Helper: sigma^k fixes any sheet s implies k is a multiple of 5. *)
Lemma fc_pow_fix_zero (k : nat) (s : 'I_5) :
  (sigma ^+ k) s = s -> k %% 5 = 0%N.
Proof.
rewrite -(expg_mod k fc_sigma5).
have Hlt : k %% 5 < 5 by exact: ltn_pmod.
case: s => [[|[|[|[|[|s]]]]] hs];
  case: (k %% 5) Hlt => [|[|[|[|[|j]]]]] //= Hlt;
  rewrite ?expgSr ?expg0 ?permM ?perm1 ?permE /fc_sigma_fun //=;
  move=> /val_inj //=.
Qed.

(** Key: any element of G that fixes a sheet must be the identity. *)
Lemma fc_fix_imp_id (g : {perm 'I_5}) (s : 'I_5) :
  g \in G -> g s = s -> g = 1.
Proof.
move=> gG gfix.
have Gcyc : G = <[sigma]>.
  rewrite /G /FiveCard_M /=.
  congr (<<_>>%G).
  apply/setP => x; apply/imsetP/set1P.
    by move=> [i _ ->]; rewrite fc_sigmasE.
  by move=> ->; exists ord0; rewrite // fc_sigmasE.
rewrite Gcyc in gG.
have /cycleP [k gk] := gG.
rewrite gk in gfix *.
rewrite -(expg_mod k fc_sigma5).
by rewrite (fc_pow_fix_zero gfix) expg0.
Qed.

Lemma fc_eval_inj (s : 'I_5) :
  {in G &, injective (fun g : {perm 'I_5} => g s)}.
Proof.
move=> g1 g2 g1G g2G Heq.
apply: (mulIg g2^-1).
rewrite mulgV.
apply: (fc_fix_imp_id (s:=s)).
  by rewrite groupM ?groupV.
by rewrite permM Heq permK.
Qed.

(******************************************************************************)
(** * Bridge: pgg_rho is the identity for Gen_PGGTypes                       *)
(******************************************************************************)

(** For Gen_PGGTypes, pgg_rho = gen_incl_morph = id on {perm 'I_5}.
    So the image rhoG = G, and all G-level properties lift to rhoG. *)
Lemma fc_rho_id (g : {perm 'I_5}) : g \in G -> @pgg_rho FiveCard_M g = g.
Proof. by []. Qed.

Let rho := morphism.mfun (@pgg_rho FiveCard_M).

Lemma fc_rhoG_eq : [set rho x | x in G] = G.
Proof.
apply/setP => x; apply/imsetP/idP.
- by move=> [g gG ->].
- by move=> xG; exists x.
Qed.

(******************************************************************************)
(** * SecurityWitness: dealing-phase security with eps = 0                    *)
(******************************************************************************)

Lemma fc_rhoG_pos : (0 < #|[set rho x | x in G]|)%N.
Proof. by rewrite fc_rhoG_eq; exact: fc_G_pos. Qed.

Lemma fc_rhoG_regular (s : 'I_5) :
  {in [set rho x | x in G] &,
   injective (fun sigma0 : {perm 'I_5} => sigma0 s)}.
Proof.
by move=> g1 g2; rewrite fc_rhoG_eq => g1G g2G; exact: (fc_eval_inj g1G g2G).
Qed.

Lemma fc_rhoG_trans (s : 'I_5) :
  [set (sigma0 : {perm 'I_5}) s | sigma0 in [set rho x | x in G]] =
  [set: 'I_5].
Proof.
rewrite fc_rhoG_eq; exact: fc_orbit_full.
Qed.

Section fc_dealing_security.
Variable R : realType.

Definition fc_security_uniform : SecurityWitness R FiveCard_M :=
  uniform_security_witness fc_rhoG_pos fc_rhoG_regular fc_rhoG_trans.

Lemma fc_eps_zero : sw_bound_eps fc_security_uniform = GRing.zero.
Proof. reflexivity. Qed.

End fc_dealing_security.

End five_card_security.
