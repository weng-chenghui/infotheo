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
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm action.
Require Import pgg_interface.
From pgg_smc Require Import five_card.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope group_scope.

Section five_card_security.

(** Local abbreviations *)
Let G := pgg_G FiveCard_M.
Let sigma := fc_sigma.

(******************************************************************************)
(** * Auxiliary: fc_sigma powers compute correctly                            *)
(******************************************************************************)

(** Each power of sigma maps each sheet to a known value.
    We verify this by case analysis + permutation computation. *)

Lemma fc_sigma_perm (x : 'I_5) : sigma x = fc_sigma_fun x.
Proof. by rewrite /sigma permE. Qed.

Lemma fc_sigma_iter (k : nat) (x : 'I_5) :
  (sigma ^+ k) x = iter k sigma x.
Proof.
elim: k => [|k IH]; first by rewrite expg0 perm1.
by rewrite expgSr permM IH.
Qed.

(** Concrete values of sigma^k applied to each sheet *)
Lemma fc_sigma_pow_val (k : nat) (x : 'I_5) :
  val ((sigma ^+ k) x) = ((val x + k) %% 5)%N.
Proof.
elim: k => [|k IH].
  by rewrite expg0 perm1 addn0 modn_small // ltn_ord.
rewrite expgSr permM fc_sigma_perm /fc_sigma_fun IH addnS.
have Hlt : ((val x + k) %% 5 < 5)%N by exact: ltn_pmod.
have Hmod : ((val x + k).+1 %% 5 = ((val x + k) %% 5).+1 %% 5)%N.
  by rewrite -addn1 -modnDml addn1.
rewrite Hmod {Hmod}.
by case: ((val x + k) %% 5)%N Hlt => [|[|[|[|[|n]]]]] //=.
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
(** * Non-triviality of G                                                     *)
(******************************************************************************)

Lemma fc_G_pos : (0 < #|G|)%N.
Proof. exact: cardG_gt0. Qed.

(******************************************************************************)
(** * Transitivity: the orbit of any sheet s under G is all of 'I_5          *)
(******************************************************************************)

(** For any s and x, sigma^((x - s) mod 5) maps s to x. *)

Lemma fc_sigma_reaches (s x : 'I_5) :
  (sigma ^+ ((5 + val x - val s) %% 5)%N) s = x.
Proof.
apply/val_inj.
rewrite fc_sigma_pow_val.
by case: s => [[|[|[|[|[|s]]]]] hs];
   case: x => [[|[|[|[|[|x]]]]] hx].
Qed.

Lemma fc_orbit_full (s : 'I_5) :
  [set (g : {perm 'I_5}) s | g in G] = [set: 'I_5].
Proof.
apply/setP => x; rewrite inE; apply/imsetP.
exists (sigma ^+ ((5 + val x - val s) %% 5)%N).
  exact: fc_sigma_pow_in_G.
exact/esym/fc_sigma_reaches.
Qed.

(******************************************************************************)
(** * Regularity: eval_at s is injective on G                                *)
(******************************************************************************)

(** Key lemma: if sigma^k fixes any sheet, then sigma^k = 1. *)
Lemma fc_sigma_pow_fix (k : nat) (s : 'I_5) :
  (sigma ^+ k) s = s -> (sigma ^+ k = 1 :> {perm 'I_5}).
Proof.
move=> Hfix.
apply/permP => y; rewrite perm1.
have Hk : ((val s + k) %% 5 = val s)%N.
  by have := congr1 val Hfix; rewrite fc_sigma_pow_val.
(* From (s + k) %% 5 = s, we get k %% 5 = 0 *)
have Hk5 : (k %% 5 = 0)%N.
  move: Hk.
  by case: s Hfix => [[|[|[|[|[|s]]]]] hs] _ //= Hmod;
    move: Hmod; rewrite ?(addn0, addnC) //; move/modn_eq.
(* Now sigma^k(y) = (y + k) %% 5 = (y + 0) %% 5 = y *)
apply/val_inj; rewrite fc_sigma_pow_val.
rewrite -(modnDml (val y) k 5) Hk5 addn0 modn_small //.
exact: ltn_ord.
Qed.

(** G = <sigma> is a cyclic group, so G = <<{sigma}>> *)
Lemma fc_G_is_cycle : <<[set tnth fc_sigmas i | i : 'I_1]>>%G = <[sigma]>%G.
Proof.
congr (generated _).
apply/setP => x; apply/imsetP/idP.
  by case=> i _ ->; rewrite tnth_ord_tuple /sigma inE.
rewrite /sigma inE => /eqP ->.
by exists (Ordinal (ltn0Sn 0)); rewrite // tnth_ord_tuple.
Qed.

Lemma fc_sigma_order : #[sigma]%g = 5.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- (* order <= 5: sigma^5 = 1 *)
  rewrite order_dvdn.
  apply/eqP/permP => x; rewrite perm1 fc_sigma_pow_val.
  by case: x => [[|[|[|[|[|x]]]]] hx].
- (* 5 <= order: sigma ≠ 1 so order > 1, and order | 5 (prime), so order = 5 *)
  rewrite -dvdn_prime // ?prime_iff_card //; last first.
    apply/eqP => /(congr1 (fun p : {perm 'I_5} => p (Ordinal (isT : (0 < 5)%N)))).
    by rewrite perm1 expg1 fc_sigma_perm.
  by rewrite order_dvdn; apply/eqP/permP => x;
     rewrite perm1 fc_sigma_pow_val;
     case: x => [[|[|[|[|[|x]]]]] hx].
Qed.

Lemma fc_G_card : #|G| = 5.
Proof.
rewrite /G /FiveCard_M /=.
have -> : <<[set tnth fc_sigmas i | i : 'I_1]>>%G = <[sigma]>%G.
  exact: fc_G_is_cycle.
by rewrite order_cycle fc_sigma_order.
Qed.

(** Every element of G = <sigma> is a power of sigma *)
Lemma fc_in_G_is_power (g : {perm 'I_5}) :
  g \in G -> exists k, g = sigma ^+ k.
Proof.
rewrite /G /FiveCard_M /= fc_G_is_cycle => gInCycle.
have gInTraj : g \in traject (mulg sigma) 1 #[sigma]%g.
  by rewrite -enum_cycle // mem_enum.
move/trajectP: gInTraj => [i Hi Hgi].
exists i; rewrite -Hgi.
by elim: i {Hi} => [|i IH] //=; rewrite expgSr IH.
Qed.

Lemma fc_eval_inj (s : 'I_5) :
  {in G &, injective (fun sigma0 : {perm 'I_5} => sigma0 s)}.
Proof.
move=> g1 g2 g1G g2G Heq.
(* g1 s = g2 s => g2^-1 * g1 fixes s => g2^-1 * g1 = 1 => g1 = g2 *)
suff Hcycle : forall g, g \in G -> g s = s -> g = 1.
  apply: (mulgI g2^-1).
  rewrite mulgV.
  apply: Hcycle; first by rewrite groupM ?groupV.
  by rewrite permM permE /= Heq -permE -permM mulgV perm1.
move=> g gG gfix.
have [k ->] := fc_in_G_is_power gG.
exact: fc_sigma_pow_fix gfix.
Qed.

End five_card_security.
