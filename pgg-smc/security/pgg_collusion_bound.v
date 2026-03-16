(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG-SMC Collusion Bound (Theorem 5)                                        *)
(*                                                                             *)
(* Sections 1-5: Generic collusion bound with Assumption 1 as hypothesis.      *)
(*   Main result: d(adversary_posterior, uniform) <= epsilon + 2(T-1)/N        *)
(*   where epsilon = var_dist(rho_dist, uniform(S_N)) is the gap between the   *)
(*   real protocol distribution and the idealized uniform permutation.         *)
(*                                                                             *)
(* Section 6: L-free instantiation proving Assumption 1 with concrete epsilon. *)
(*   When word_eval is injective (L-free) and we draw permutations uniformly   *)
(*   from all L-words over Tg generators, the distribution is uniform over     *)
(*   achievable(L) with |achievable(L)| = Tg^L.  The variational distance to  *)
(*   the full uniform over S_N is:                                             *)
(*     epsilon = 2 * (N! - Tg^L) / N!                                          *)
(*   Caveat: assumes the protocol samples words uniformly at random.           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_lfree.

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

(******************************************************************************)
(*  Section 6: L-free instantiation — concrete epsilon for Assumption 1     *)
(******************************************************************************)

(* General lemma: fdistmap of uniform through an injective function
   produces fdist_uniform_supp over the image. *)

Section fdistmap_inj_uniform.

Context {R : realType}.
Variables (A B : finType).
Variable f : A -> B.
Hypothesis f_inj : injective f.

Variable Hcard_A : #|A| = #|A|.-1.+1.

Let img := f @: [set: A].
Let Himg_pos : (0 < #|img|)%N.
Proof.
rewrite card_imset ?cardsT //.
by case: #|A| Hcard_A.
Qed.

Lemma fdistmap_inj_uniform :
  fdistmap f (fdist_uniform Hcard_A) =
  @fdist_uniform_supp R B img Himg_pos.
Proof.
apply/fdist_ext => b.
rewrite fdistmapE.
case/boolP: (b \in img) => Hb.
  (* b in image: exactly one preimage *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hb => [a _ Hab].
  rewrite (bigD1 a) /=; last by rewrite !inE Hab eqxx.
  rewrite fdist_uniformE big1 ?addr0; last first.
    move=> a' /andP [Ha' Hneq].
    rewrite !inE in Ha'.
    move/eqP in Ha'.
    rewrite Hab in Ha'.
    by move/f_inj in Ha'; rewrite Ha' eqxx in Hneq.
  congr (_ ^-1).
  by rewrite card_imset ?cardsT.
(* b not in image: no preimage *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => a.
rewrite inE => /eqP Hfa.
exfalso; move/negP: Hb; apply.
by apply/imsetP; exists a; rewrite ?inE.
Qed.

End fdistmap_inj_uniform.

(* L-free groups have concrete epsilon for Assumption 1 *)

Section lfree_collusion.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

(* Distinct starting sheets *)
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* Generator parameters *)
Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(* L-freeness *)
Hypothesis Hlfree : @lfree M L.

(* Cardinality of word space *)
Lemma card_word_L :
  #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof.
by rewrite card_tuple card_ord prednK // expn_gt0.
Qed.

(* The word distribution: uniform over all L-words *)
Definition word_uniform : R.-fdist (L.-tuple 'I_Tg) :=
  fdist_uniform card_word_L.

(* The induced group element distribution *)
Definition rho_from_words : R.-fdist {perm 'I_N} :=
  fdistmap (@word_eval M L) word_uniform.

(* achievable(L) has positive cardinality *)
Lemma achievable_pos : (0 < #|@achievable M L|)%N.
Proof.
rewrite /achievable -/M.
have -> : #|[set word_eval w | w : pgg_word M L]| = @search_space M L by [].
rewrite lfree_search_space //.
by rewrite expn_gt0.
Qed.

(* Key: rho_from_words is uniform_supp over achievable(L) *)
Lemma rho_from_words_uniform_supp :
  rho_from_words = @fdist_uniform_supp R _ (@achievable M L) achievable_pos.
Proof.
apply/fdist_ext => g.
rewrite /rho_from_words /word_uniform fdistmapE.
case/boolP: (g \in @achievable M L) => Hg.
  (* g in achievable: exactly one preimage *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hg => [w _ Hgw].
  rewrite (bigD1 w) /=; last by rewrite !inE Hgw eqxx.
  rewrite fdist_uniformE big1 ?addr0; last first.
    move=> w' /andP [Hw' Hneq].
    rewrite inE in Hw'; move/eqP in Hw'.
    rewrite Hgw in Hw'; move/Hlfree in Hw'.
    by rewrite Hw' eqxx in Hneq.
  congr (_ ^-1).
  have -> : #|@achievable M L| = @search_space M L by [].
  rewrite lfree_search_space //.
  by rewrite card_tuple card_ord.
(* g not in achievable: no preimage *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => w; rewrite inE => /eqP Hfw.
exfalso; move/negP: Hg; apply.
by apply/imsetP; exists w.
Qed.

(* Cardinality of S_N *)
Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

(* The key bound: achievable subset is smaller than S_N *)
Lemma lfree_search_space_le_fact : (Tg ^ L <= N`!)%N.
Proof.
rewrite -(@lfree_search_space M) //.
apply: (leq_trans (@search_space_leG M L)).
apply: (leq_trans (max_card _)).
by rewrite card_permT_N prednK // fact_gt0.
Qed.

(* Concrete epsilon for Assumption 1 *)
Let lfree_eps : R := 2%:R * (N`! - Tg ^ L)%:R / N`!%:R.

Lemma lfree_eps_ge0 : 0 <= lfree_eps.
Proof.
rewrite /lfree_eps.
apply: divr_ge0; last by rewrite ler0n.
by rewrite mulr_ge0 // ler0n.
Qed.

(* Assumption 1 holds with concrete epsilon *)
Theorem var_dist_lfree_uniform :
  var_dist rho_from_words (fdist_uniform card_perm_N) <= lfree_eps.
Proof.
rewrite rho_from_words_uniform_supp.
rewrite var_dist_uniform_supp /=.
rewrite /lfree_eps.
(* LHS: 2 * (#|perm| - #|achievable|) / #|perm|
   RHS: 2 * (N! - Tg^L) / N! *)
suff -> : (#|{perm 'I_N}| - #|@achievable M L|)%N = (N`! - Tg ^ L)%N.
  suff -> : (#|{perm 'I_N}|%:R : R) = N`!%:R by [].
  by rewrite card_permT_N prednK // fact_gt0.
rewrite card_permT_N prednK; last exact: fact_gt0.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite (@lfree_search_space M).
Qed.

(* Main theorem: applying collusion_bound with concrete epsilon.
   The full bound follows from var_dist_lfree_uniform + the generic
   collusion bound framework. We state it in the form that
   instantiates Assumption 1 concretely. *)
Theorem var_dist_lfree_eval :
  forall (eval_at : {perm 'I_N} -> 'I_N),
  var_dist (fdistmap eval_at rho_from_words)
           (fdistmap eval_at (fdist_uniform card_perm_N))
  <= lfree_eps.
Proof.
move=> eval_at.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)
                                    var_dist_lfree_uniform).
Qed.

End lfree_collusion.

(******************************************************************************)
(*   Section 7: Fiber equidistribution                                       *)
(*                                                                            *)
(*   Defines fibers (preimages of word_eval) and proves that under uniform   *)
(*   word distribution, the probability of each achievable group element is  *)
(*   proportional to its fiber size. Under L-freeness, fibers are singletons *)
(*   and the induced distribution is uniform over achievable(L).             *)
(******************************************************************************)

Section fiber_equidistribution.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Lemma card_word_L' :
  #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof.
by rewrite card_tuple card_ord prednK // expn_gt0.
Qed.

Let word_unif : R.-fdist (L.-tuple 'I_Tg) := fdist_uniform card_word_L'.

(* Fiber: set of words evaluating to a given group element *)
Definition fiber (g : {perm 'I_N}) : {set L.-tuple 'I_Tg} :=
  [set w | @word_eval M L w == g].

(* The probability of g under rho_from_words equals |fiber g| / Tg^L *)
Lemma fiber_prob (g : {perm 'I_N}) :
  fdistmap (@word_eval M L) word_unif g =
  #|fiber g|%:R / (Tg ^ L)%:R.
Proof.
rewrite fdistmapE.
rewrite (eq_bigl (fun a => a \in fiber g)); last first.
  by move=> w; rewrite !inE.
rewrite (eq_bigr (fun _ => (Tg ^ L)%:R^-1)); last first.
  by move=> w _; rewrite fdist_uniformE card_tuple card_ord.
by rewrite big_const iter_addr addr0 -mulr_natr mulrC mulr1 mulrC mulr_natr.
Qed.

(* Under L-freeness, each fiber has at most one element *)
Lemma lfree_fiber_le1 (Hlfree : @lfree M L) (g : {perm 'I_N}) :
  (#|fiber g| <= 1)%N.
Proof.
apply/card_le1_eqP => w1 w2.
rewrite !inE => /eqP Hw1 /eqP Hw2.
by apply: Hlfree; rewrite Hw1 Hw2.
Qed.

(* Under L-freeness, fibers of achievable elements are singletons *)
Lemma lfree_fiber_card1 (Hlfree : @lfree M L) (g : {perm 'I_N}) :
  g \in @achievable M L -> #|fiber g| = 1%N.
Proof.
move=> /imsetP [w _ Hw].
apply/eqP; rewrite eqn_leq lfree_fiber_le1 //=.
apply/card_gt0P; exists w.
by rewrite inE Hw.
Qed.

End fiber_equidistribution.

(******************************************************************************)
(*   Section 8: Generalized collusion bound for arbitrary coalition size k  *)
(******************************************************************************)

(* Generalization of the collusion bound to arbitrary coalition size k.
   Instead of observing T-1 out of T endpoints (with 1 unobserved),
   the adversary observes k out of N endpoints. DPI (var_dist_fdistmap)
   gives the bound for ANY number of observed points. *)

Section collusion_bound_k.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

(* Coalition size k (the number of parties the adversary controls) *)
Variable k : nat.
Hypothesis k_pos : (0 < k)%N.
Hypothesis kN : (k <= N)%N.

(* k distinct starting sheets observed by the coalition *)
Variable obs_starts : k.-tuple 'I_N.
Hypothesis obs_starts_uniq : uniq obs_starts.

(* Assumption 1: distribution of rho(P) over S_N *)
Variable rho_dist : R.-fdist {perm 'I_N}.
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

Hypothesis assumption1 :
  var_dist rho_dist (fdist_uniform card_perm_N) <= epsilon.

(* The joint observation function: sigma |-> (sigma(s_1), ..., sigma(s_k)) *)
Definition joint_observation (sigma : {perm 'I_N}) : k.-tuple 'I_N :=
  [tuple sigma (tnth obs_starts i) | i < k].

(* The adversary's joint marginal *)
Definition adversary_joint : R.-fdist (k.-tuple 'I_N) :=
  fdistmap joint_observation rho_dist.

(* The ideal joint distribution *)
Definition ideal_joint : R.-fdist (k.-tuple 'I_N) :=
  fdistmap joint_observation (fdist_uniform card_perm_N).

(* Main theorem: DPI gives the bound for joint observations *)
Theorem collusion_bound_k :
  var_dist adversary_joint ideal_joint <= epsilon.
Proof.
rewrite /adversary_joint /ideal_joint.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) assumption1).
Qed.

End collusion_bound_k.

Check collusion_bound.
Check collusion_bound_unconditional.
Check collusion_bound_conditional.
Check var_dist_lfree_uniform.
Check var_dist_lfree_eval.
Check collusion_bound_k.
