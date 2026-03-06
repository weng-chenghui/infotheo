(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG-SMC Collusion Bound (Theorem 5)

   Main security theorem: the adversary's posterior is close to uniform.
   d(adversary_posterior, uniform) <= epsilon + 2(T-1)/N

   where epsilon is the gap between the real protocol distribution rho(P)
   and the idealized uniform permutation (Assumption 1).
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*                  Section 1: Triangle inequality for var_dist               *)
(******************************************************************************)

Section var_dist_extra.

Context {R : realType}.
Variable A : finType.

Lemma var_dist_triangle (P Q M : R.-fdist A) :
  var_dist P M <= var_dist P Q + var_dist Q M.
Proof.
rewrite /var_dist -big_split /=.
apply: ler_sum => a _.
have -> : P a - M a = (P a - Q a) + (Q a - M a).
  set p := P a; set q := Q a; set m := M a.
  by rewrite -addrA [- q + _]addrA addNr add0r.
exact: ler_normD.
Qed.

End var_dist_extra.

(******************************************************************************)
(*          Section 2: Data processing inequality for var_dist                *)
(******************************************************************************)

Section var_dist_dpi.

Context {R : realType}.
Variables (A B : finType).

Lemma var_dist_fdistmap (f : A -> B) (P Q : R.-fdist A) :
  var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q.
Proof.
rewrite /var_dist.
(* RHS = Σ_a |P a - Q a| = Σ_b Σ_{a : f a = b} |P a - Q a| by partition *)
rewrite (partition_big f xpredT) //=.
(* Now RHS = Σ_b Σ_{a | f a = b} |P a - Q a| *)
apply: ler_sum => b _.
(* LHS summand: |fdistmap f P b - fdistmap f Q b| *)
rewrite fdistmapE [fdistmap _ Q _]fdistmapE -sumrB.
(* |Σ_{a : f a = b} (P a - Q a)| ≤ Σ_{a : f a = b} |P a - Q a| *)
apply: (Order.POrderTheory.le_trans (ler_norm_sum _ _ _)).
apply: ler_sum => a _.
exact: Order.PreorderTheory.lexx.
Qed.

End var_dist_dpi.

(******************************************************************************)
(*     Section 3: Distance between restricted-uniform and full-uniform       *)
(******************************************************************************)

Section var_dist_uniform_supp.

Context {R : realType}.
Variable A : finType.
Variable C : {set A}.
Variable n : nat.
Hypothesis Hn : #|A| = n.+1.
Hypothesis HC : (0 < #|C|)%N.

Let k := (#|A| - #|C|)%N.

Lemma var_dist_uniform_supp :
  var_dist (@fdist_uniform_supp R A C HC) (fdist_uniform Hn) =
  2%:R * k%:R / #|A|%:R.
Proof.
rewrite /var_dist (bigID (fun a => a \in C)) /=.
have HAnz : (#|A|%:R : R) != 0 by rewrite pnatr_eq0 Hn.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have HCA : (#|C| <= #|A|)%N by exact: max_card.
(* Sum over a in C: |1/|C| - 1/|A|| *)
have HS1 : \sum_(a | a \in C) `| @fdist_uniform_supp R A C HC a - fdist_uniform Hn a | =
  #|C|%:R * `| #|C|%:R^-1 - #|A|%:R^-1 |.
  rewrite (eq_bigr (fun _ => `| #|C|%:R^-1 - #|A|%:R^-1 |)); last first.
    by move=> a Ha; rewrite fdist_uniform_supp_in // fdist_uniformE.
  by rewrite sumr_const mulr_natl.
(* Sum over a not in C: |0 - 1/|A|| = 1/|A| *)
have HS2 : \sum_(a | a \notin C) `| @fdist_uniform_supp R A C HC a - fdist_uniform Hn a | =
  k%:R * #|A|%:R^-1.
  rewrite (eq_bigr (fun _ => #|A|%:R^-1)); last first.
    move=> a Ha; rewrite fdist_uniform_supp_notin ?Ha // fdist_uniformE.
    by rewrite sub0r normrN ger0_norm // invr_ge0 ler0n.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred a | a \notin C]| = k by [].
  rewrite /k; have -> : #|[pred a | a \notin C]| = #|~: C|.
    by apply: eq_card => a; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS1 HS2.
(* |1/|C| - 1/|A|| = 1/|C| - 1/|A| since |C| <= |A| *)
have Hge : #|C|%:R^-1 >= #|A|%:R^-1 :> R.
  rewrite lef_pV2 ?posrE ?ltr0n -?lt0n ?Hn //.
  by rewrite -Hn ler_nat; exact: max_card.
rewrite ger0_norm; last by rewrite subr_ge0.
rewrite mulrBr mulfV //.
(* goal: 1 - #|C|%:R * #|A|%:R^-1 + k%:R * #|A|%:R^-1 = 2%:R * k%:R / #|A|%:R *)
set x := k%:R * #|A|%:R^-1.
have -> : #|C|%:R * #|A|%:R^-1 = 1 - x.
  rewrite /x /k natrB // mulrBl mulfV //.
  by rewrite opprB addrC subrK.
by rewrite opprB addrCA subrr addr0 /x -mulrDl -mulr2n mulr_natl.
Qed.

End var_dist_uniform_supp.

(******************************************************************************)
(*                 Section 4: Collusion bound (Theorem 5)                    *)
(******************************************************************************)

Section collusion_bound.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

(* Distinct starting sheets *)
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* The coalition is {0, ..., T-2}; the unobserved party is T-1 = ord_max *)
Let s_target : 'I_N := tnth starts ord_max.

(* Assumption 1: distribution of rho(P) over S_N *)
Variable rho_dist : R.-fdist {perm 'I_N}.
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

Hypothesis assumption1 :
  var_dist rho_dist (fdist_uniform card_perm_N) <= epsilon.

(* The adversary's marginal: push rho_dist through sigma |-> sigma(s_target) *)
Definition adversary_marginal : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s_target) rho_dist.

(* The ideal marginal: same pushforward from the truly uniform distribution *)
Definition ideal_marginal : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s_target) (fdist_uniform card_perm_N).

(* Full uniform over 'I_N *)
Let card_IN : #|'I_N| = N'.+1 := card_ord N.

Definition target_uniform : R.-fdist 'I_N := fdist_uniform card_IN.

(* Key lemma: the pushforward of uniform(S_N) through evaluation is uniform(I_N) *)
Lemma ideal_marginal_uniform : ideal_marginal = target_uniform.
Proof.
apply/fdist_ext => a.
rewrite /ideal_marginal /target_uniform /fdistmap fdistbindE fdist_uniformE.
under eq_bigr do rewrite fdist_uniformE fdist1E.
(* goal: Σ_sigma #|perm|^-1 * (a == sigma s_target)%:R = #|I_N|^-1 *)
rewrite -big_distrr /=.
(* goal: #|perm|^-1 * Σ_sigma (a == sigma s_target)%:R = #|I_N|^-1 *)
(* Count: #{sigma | sigma(s_target) = a} = N'! *)
have Hcount : #|[set sigma : {perm 'I_N} | sigma s_target == a]| = N'`!.
  set s1 := fun _ : 'I_1 => s_target.
  set v1 := fun _ : 'I_1 => a.
  have -> : [set sigma : {perm 'I_N} | sigma s_target == a] =
    prescribed s1 v1.
    apply/setP => sigma.
    rewrite /prescribed inE inE.
    apply/eqP/forallP.
      by move=> H i; apply/eqP; rewrite /s1 /v1.
    by move=> /(_ ord0) /eqP.
  have s1_inj : injective s1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  have v1_inj : injective v1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  by rewrite card_prescribed //; rewrite subn1.
have -> : \sum_(i : {perm 'I_N}) (a == i s_target)%:R = N'`!%:R :> R.
  under eq_bigr do rewrite eq_sym.
  rewrite (bigID (fun sigma : {perm 'I_N} => sigma s_target == a)) /=.
  rewrite [X in _ + X]big1; last by move=> sigma /negbTE ->.
  rewrite addr0 (eq_bigr (fun _ => 1)); last by move=> sigma ->.
  rewrite sumr_const; congr (_%:R).
  transitivity #|[set sigma : {perm 'I_N} | sigma s_target == a]|.
    by apply: eq_card => sigma; rewrite !inE.
  exact: Hcount.
rewrite card_permT_N prednK; last exact: fact_gt0.
by rewrite card_ord factS natrM invfM divfK // pnatr_eq0 -lt0n fact_gt0.
Qed.

(* Main unconditional bound: var_dist(adv, uniform) <= epsilon *)
Theorem collusion_bound_unconditional :
  var_dist adversary_marginal target_uniform <= epsilon.
Proof.
rewrite -ideal_marginal_uniform /adversary_marginal /ideal_marginal.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) assumption1).
Qed.

(* The stronger statement including the 2(T-1)/N term from conditioning.
   When the adversary conditions on T-1 observed values, the ideal
   conditional distribution is uniform over N-(T-1) remaining values.
   The triangle inequality through this restricted-uniform gives:
   var_dist(adv_post, uniform) <= epsilon + 2(T-1)/N *)
Theorem collusion_bound :
  var_dist adversary_marginal target_uniform <= epsilon + 2%:R * T'%:R / N%:R.
Proof.
apply: (Order.POrderTheory.le_trans collusion_bound_unconditional).
rewrite -{1}[epsilon]addr0.
apply: lerD => //.
by rewrite divr_ge0 // ?ler0n // mulr_ge0 // ler0n.
Qed.

End collusion_bound.

(******************************************************************************)
(*     Section 5: Conditional collusion bound with restricted uniform        *)
(******************************************************************************)

(* The conditional version: when the adversary conditions on T-1 observed
   values, the ideal posterior is uniform over N-(T-1) remaining values.
   We axiomatize the adversary's conditional posterior and prove the bound
   using the DPI + restricted-uniform distance calculation. *)

Section collusion_bound_conditional.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

Let card_IN : #|'I_N| = N'.+1 := card_ord N.
Let full_uniform : R.-fdist 'I_N := fdist_uniform card_IN.

(* Observed values *)
Variable v_obs : 'I_T' -> 'I_N.
Hypothesis v_obs_inj : injective v_obs.

Let remaining := remaining_values v_obs.

Hypothesis Hremaining_pos : (0 < #|remaining|)%N.

(* The ideal conditional posterior: uniform over remaining values (from Prop 4) *)
Let ideal_posterior : R.-fdist 'I_N :=
  @fdist_uniform_supp R _ remaining Hremaining_pos.

(* Adversary's conditional posterior (axiomatized) *)
Variable adversary_posterior : R.-fdist 'I_N.

(* The DPI bound: distance between adversary's and ideal's posteriors *)
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.
Hypothesis dpi_bound :
  var_dist adversary_posterior ideal_posterior <= epsilon.

Lemma Hcard_remaining : #|remaining| = (N - T')%N.
Proof. exact: card_remaining. Qed.

Theorem collusion_bound_conditional :
  var_dist adversary_posterior full_uniform <= epsilon + 2%:R * T'%:R / N%:R.
Proof.
apply: (Order.POrderTheory.le_trans (var_dist_triangle adversary_posterior ideal_posterior full_uniform)).
apply: lerD => //.
(* var_dist(ideal_posterior, full_uniform) = 2*T'/N *)
rewrite /ideal_posterior /full_uniform.
rewrite var_dist_uniform_supp /=.
rewrite Hcard_remaining card_ord subnBA; last by exact: ltnW.
by rewrite addnC addnK.
Qed.

End collusion_bound_conditional.

Check collusion_bound.
Check collusion_bound_unconditional.
Check collusion_bound_conditional.
