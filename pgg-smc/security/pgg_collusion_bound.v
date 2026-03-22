(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG Collusion Bound (Theorem 5)                                            *)
(*                                                                             *)
(* Sections 1-5: Generic collusion bound with Assumption 1 as hypothesis.      *)
(*   Main result: d(adversary_posterior, uniform) <= epsilon + 2(T-1)/N        *)
(*   where epsilon = var_dist(rho_dist, uniform(S_N)) is the gap between the   *)
(*   real protocol distribution and the idealized uniform permutation.         *)
(*                                                                             *)
(* Section 6: Word-eval injective instantiation — rho_from_words is           *)
(*   uniform over achievable(L) when word_eval is injective.                   *)
(*   Provides rho_from_words, rho_from_words_uniform_supp, fiber counting.     *)
(*   Concrete epsilon is computed per-instance (not here).                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.

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

(* WARNING: DPI is too loose for spectral convergence analysis.           *)
(* For the spectral path to SecurityWitness, use SchreierCertificate      *)
(* (pgg_schreier.v) which bounds var_dist on 'I_N directly with          *)
(* prefactor sqrt(N), avoiding the sqrt(|G|) blowup from projecting      *)
(* through G. DPI remains valid for collusion_bound_unconditional        *)
(* (different proof structure) but should NOT be used to derive           *)
(* endpoint bounds from group-level spectral analysis.                    *)
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
(*  Section 5b: Pushforward of uniform(S_N) through evaluation = uniform(I_N)*)
(*                                                                            *)
(*  Standalone version of ideal_marginal_uniform (Section 4), extracted from  *)
(*  the collusion bound section to make it usable in other contexts.          *)
(******************************************************************************)

Section fdistmap_eval_uniform_section.

Variable R : realType.
Variable N' : nat.
Let N := N'.+1.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

Lemma fdistmap_eval_uniform (s : 'I_N) :
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (fdist_uniform card_perm_N : R.-fdist _) =
  (fdist_uniform (card_ord N) : R.-fdist _).
Proof.
apply/fdist_ext => a.
rewrite /fdistmap fdistbindE fdist_uniformE.
under eq_bigr do rewrite fdist_uniformE fdist1E.
rewrite -big_distrr /=.
have Hcount : #|[set sigma : {perm 'I_N} | sigma s == a]| = N'`!.
  set s1 := fun _ : 'I_1 => s.
  set v1 := fun _ : 'I_1 => a.
  have -> : [set sigma : {perm 'I_N} | sigma s == a] =
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
have -> : \sum_(i0 : {perm 'I_N}) (a == i0 s)%:R = N'`!%:R :> R.
  under eq_bigr do rewrite eq_sym.
  rewrite (bigID (fun sigma : {perm 'I_N} => sigma s == a)) /=.
  rewrite [X in _ + X]big1; last by move=> sigma /negbTE ->.
  rewrite addr0 (eq_bigr (fun _ => 1)); last by move=> sigma ->.
  rewrite sumr_const; congr (_%:R).
  transitivity #|[set sigma : {perm 'I_N} | sigma s == a]|.
    by apply: eq_card => sigma; rewrite !inE.
  exact: Hcount.
rewrite card_permT_N prednK; last exact: fact_gt0.
by rewrite card_ord factS natrM invfM divfK // pnatr_eq0 -lt0n fact_gt0.
Qed.

End fdistmap_eval_uniform_section.

(******************************************************************************)
(*  Section 6: Word-eval injective instantiation — concrete epsilon for     *)
(*  Assumption 1                                                             *)
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

(* Word-eval injective groups have concrete epsilon for Assumption 1 *)

Section weval_inj_collusion.

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

(* Word-eval injectivity *)
Hypothesis Hlfree : @weval_inj M L.

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
rewrite weval_inj_search_space //.
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
  rewrite weval_inj_search_space //.
  by rewrite card_tuple card_ord.
(* g not in achievable: no preimage *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => w; rewrite inE => /eqP Hfw.
exfalso; move/negP: Hg; apply.
by apply/imsetP; exists w.
Qed.


End weval_inj_collusion.

(******************************************************************************)
(*   Section 7: Fiber equidistribution                                       *)
(*                                                                            *)
(*   Defines fibers (preimages of word_eval) and proves that under uniform   *)
(*   word distribution, the probability of each achievable group element is  *)
(*   proportional to its fiber size. Under word-eval injectivity, fibers    *)
(*   are singletons                                                         *)
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

(* Under word-eval injectivity, each fiber has at most one element *)
Lemma weval_inj_fiber_le1 (Hlfree : @weval_inj M L) (g : {perm 'I_N}) :
  (#|fiber g| <= 1)%N.
Proof.
apply/card_le1_eqP => w1 w2.
rewrite !inE => /eqP Hw1 /eqP Hw2.
by apply: Hlfree; rewrite Hw1 Hw2.
Qed.

(* Under word-eval injectivity, fibers of achievable elements are singletons *)
Lemma weval_inj_fiber_card1 (Hlfree : @weval_inj M L) (g : {perm 'I_N}) :
  g \in @achievable M L -> #|fiber g| = 1%N.
Proof.
move=> /imsetP [w _ Hw].
apply/eqP; rewrite eqn_leq weval_inj_fiber_le1 //=.
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

(******************************************************************************)
(*   Section 9: Pushforward of uniform_supp through support-injective f     *)
(*                                                                            *)
(*   When f is injective on C, fdistmap f (uniform_supp C) = uniform_supp   *)
(*   (f @: C). Combined with var_dist_uniform_supp, this gives a direct     *)
(*   endpoint epsilon = 2*(N - |f @: C|)/N without going through the DPI.   *)
(******************************************************************************)

Section fdistmap_uniform_supp_inj.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.
Variable f : A -> B.
Hypothesis f_inj : {in C &, injective f}.

Let img := f @: C.
Let Himg_pos : (0 < #|img|)%N.
Proof. by rewrite card_in_imset. Qed.

(* When f is injective on C, the pushforward of uniform_supp(C) through f
   is uniform_supp(f(C)). This is the key lemma for direct endpoint epsilon. *)
Lemma fdistmap_uniform_supp_inj :
  fdistmap f (@fdist_uniform_supp R A C HC) =
  @fdist_uniform_supp R B img Himg_pos.
Proof.
apply/fdist_ext => b.
rewrite fdistmapE.
case/boolP: (b \in img) => Hb.
  (* b in image: exactly one preimage in C *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hb => [a Ha Hab].
  rewrite (bigD1 a) /=; last by rewrite !inE Hab eqxx.
  rewrite fdist_uniform_supp_in // big1 ?addr0; last first.
    move=> a' /andP [/eqP Ha' Hneq].
    case/boolP: (a' \in C) => Ha'C; last by rewrite fdist_uniform_supp_notin.
    have Habs : a' = a by apply: f_inj Ha'C Ha _; rewrite Ha' Hab.
    by rewrite Habs eqxx in Hneq.
  congr (_ ^-1).
  by rewrite card_in_imset.
(* b not in image: no preimage in C *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => a /eqP Hfa.
case/boolP: (a \in C) => HaC.
  exfalso; move/negP: Hb; apply.
  by rewrite -Hfa; apply/imsetP; exists a.
by rewrite fdist_uniform_supp_notin.
Qed.

End fdistmap_uniform_supp_inj.

(******************************************************************************)
(*  Section 10: Direct endpoint epsilon for groups with injective perm_endpoint     *)
(*                                                                            *)
(*  When word_eval is injective (weval_inj L) AND perm_endpoint is injective on    *)
(*  achievable(L), the endpoint distribution is uniform_supp over            *)
(*  perm_endpoint(achievable(L)), giving epsilon = 2*(N - Tg^L)/N.                 *)
(*  This is tighter than the DPI bound 2*(N! - Tg^L)/N!.                    *)
(******************************************************************************)

Section direct_endpoint_epsilon.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

(* The endpoint evaluation function *)
Let eval_at (s : 'I_N) : {perm 'I_N} -> 'I_N :=
  fun sigma => sigma s.

(* eval_at s is injective on achievable(L) for each starting sheet s *)
Hypothesis Hinj_s :
  forall s : 'I_N,
  {in @achievable M L &, injective (eval_at s)}.

(* The key bound: epsilon = 2*(N - Tg^L)/N with denominator N, not N! *)
Let direct_eps : R := 2%:R * (N - Tg ^ L)%:R / N%:R.

Lemma direct_eps_ge0 : 0 <= direct_eps.
Proof.
rewrite /direct_eps.
apply: divr_ge0; last by rewrite ler0n.
by rewrite mulr_ge0 // ler0n.
Qed.

Lemma achievable_card_TgL : #|@achievable M L| = (Tg ^ L)%N.
Proof.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

Lemma achievable_pos' : (0 < #|@achievable M L|)%N.
Proof. by rewrite achievable_card_TgL expn_gt0. Qed.

(* The image of achievable through eval_at s has cardinality Tg^L *)
Lemma perm_endpoint_image_card (s : 'I_N) :
  #|(eval_at s) @: @achievable M L| = (Tg ^ L)%N.
Proof.
rewrite card_in_imset; last first.
  have Hs : {in @achievable M L &, injective (eval_at s)}.
    exact: Hinj_s.
  exact: Hs.
exact: achievable_card_TgL.
Qed.

Lemma perm_endpoint_image_pos (s : 'I_N) :
  (0 < #|(eval_at s) @: @achievable M L|)%N.
Proof. by rewrite perm_endpoint_image_card expn_gt0. Qed.

Lemma TgL_leq_N : (Tg ^ L <= N)%N.
Proof.
rewrite -(perm_endpoint_image_card ord0).
apply: (leq_trans (max_card _)).
by rewrite card_ord.
Qed.

(* Direct endpoint bound: for each sheet s, the marginal endpoint
   distribution is at distance 2*(N-Tg^L)/N from uniform.
   This is TIGHTER than the DPI bound 2*(N!-Tg^L)/N!. *)
Theorem var_dist_endpoint_direct (s : 'I_N) :
  var_dist (fdistmap (eval_at s) (rho_from_words L sigmas))
           (fdist_uniform (card_ord N)) <= direct_eps.
Proof.
rewrite (rho_from_words_uniform_supp Hlfree).
have Hs : {in @achievable M L &, injective (eval_at s)}.
  exact: Hinj_s.
rewrite (fdistmap_uniform_supp_inj _ Hs).
rewrite var_dist_uniform_supp.
rewrite perm_endpoint_image_card card_ord /direct_eps.
exact: Order.POrderTheory.lexx.
Qed.

End direct_endpoint_epsilon.

(******************************************************************************)
(*  Section 11: Balanced-case var_dist for non-injective perm_endpoint              *)
(*                                                                            *)
(*  When |achievable(L)| = N (balanced case, i.e., Tg^L = N), the var_dist  *)
(*  of fdistmap perm_endpoint (uniform_supp achievable) against uniform depends     *)
(*  ONLY on the image size, not the fiber distribution. Specifically:         *)
(*    var_dist = 2*(N - |image_s|)/N                                         *)
(*  This equals the var_dist that uniform_supp(image_s) has from uniform.    *)
(*                                                                            *)
(*  Applicable to: OC (Tg^L = 2^2 = 4 = N)                                  *)
(******************************************************************************)

Section balanced_var_dist.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.
Variable f : A -> B.
Variable n : nat.
Hypothesis Hn : #|B| = n.+1.
Hypothesis Hbal : #|C| = n.+1.

Let img := f @: C.

Let Himg_pos : (0 < #|img|)%N.
Proof.
rewrite card_gt0; apply/set0Pn.
have /card_gt0P [a Ha] := HC.
by exists (f a); apply/imsetP; exists a.
Qed.

(* The balanced-case var_dist formula.
   When |C| = |B|, fibers partition C into |B| groups summing to |C| = |B|.
   The var_dist only depends on how many groups are empty (= |B| - |image|). *)
Lemma var_dist_fdistmap_balanced :
  var_dist (fdistmap f (@fdist_uniform_supp R _ C HC))
           (fdist_uniform Hn) =
  2%:R * (#|B| - #|img|)%:R / #|B|%:R.
Proof.
rewrite /var_dist.
have HBnz : (#|B|%:R : R) != 0 by rewrite pnatr_eq0 Hn.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have HCB : #|C| = #|B| by rewrite Hbal Hn.
rewrite (bigID (fun b => b \in img)) /=.
(* For b not in image, fdistmap = 0 *)
have Hnoimg : forall b0 : B, b0 \notin img -> @fdistmap R _ _ f (`U HC) b0 = 0.
  move=> b0 Hb0.
  rewrite fdistmapE big1 //.
  move=> a; rewrite inE => /eqP Hfa.
  apply: fdist_uniform_supp_notin; apply/negP => HaC.
  move/negP: Hb0; apply; apply/imsetP; exists a => //.
(* Sum over b not in img: |0 - 1/|B|| = 1/|B|, count = |B| - |img| *)
have HS2 : \sum_(i | i \notin img)
    `|@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  under eq_bigr => b0 Hb0.
    rewrite Hnoimg // sub0r normrN ger0_norm ?FDist.ge0 // fdist_uniformE.
    over.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N by [].
  have -> : #|[pred i | i \notin img]| = #|~: img|.
    by apply: eq_card => b0; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS2.
(* Reduce to showing the img-sum also equals (|B|-|img|)/|B| *)
suff HS1 : \sum_(i in img)
    `|@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  by rewrite HS1 -mulrDl -mulr2n mulr_natl.
(* Use: Σ_b P(b) = 1 = Σ_b Q(b), so Σ_b (P(b)-Q(b)) = 0 *)
have Hsum0 : \sum_(i : B)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) = 0.
  by rewrite sumrB !FDist.f1 subrr.
(* Signed sum over b not in img *)
have Hnoimg_signed : \sum_(i | i \notin img)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) =
  - ((#|B| - #|img|)%:R / #|B|%:R).
  rewrite (eq_bigr (fun b0 => - fdist_uniform Hn b0)); last first.
    by move=> b0 Hb0; rewrite Hnoimg // sub0r.
  rewrite sumrN (eq_bigr (fun _ => #|B|%:R^-1)); last first.
    by move=> b0 _; rewrite fdist_uniformE.
  rewrite sumr_const mulr_natl.
  have -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N.
    have -> : #|[pred i | i \notin img]| = #|~: img|.
      by apply: eq_card => b0; rewrite inE inE.
    by rewrite cardsCs setCK.
  by [].
(* Signed sum over img = (|B|-|img|)/|B| (from Σ=0 and complement) *)
have Hdiff : \sum_(i in img)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) =
  (#|B| - #|img|)%:R / #|B|%:R.
  move: Hsum0.
  rewrite (bigID (fun b => b \in img)) /= Hnoimg_signed.
  by move/eqP; rewrite addr_eq0 => /eqP ->; rewrite opprK.
(* Each term in img-sum is non-negative (fiber >= 1 implies P(b) >= Q(b)),
   so |P(b)-Q(b)| = P(b)-Q(b) and the abs-sum equals the signed sum *)
rewrite -Hdiff.
apply: eq_bigr => b0 Hb0.
rewrite ger0_norm //; rewrite subr_ge0.
rewrite fdist_uniformE fdistmapE.
have [a0 Ha0C Hfa0] : exists2 a0, a0 \in C & f a0 = b0.
  by move/imsetP: Hb0 => [a0 Ha0C Hfa0]; exists a0.
rewrite (bigD1 a0) /=; last first.
  by rewrite inE; apply/eqP.
apply: ler_wpDr; first by apply: sumr_ge0 => a _; exact: FDist.ge0.
by rewrite fdist_uniform_supp_in // HCB.
Qed.

End balanced_var_dist.

(* Unbalanced case: when |C| <= |B|, the var_dist formula still holds.
   This applies e.g. to S_5 where |achievable(1)| = 4 < 5 = N. *)
Section unbalanced_var_dist.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.
Variable f : A -> B.
Variable n : nat.
Hypothesis Hn : #|B| = n.+1.
Hypothesis HCleB : (#|C| <= #|B|)%N.

Let img := f @: C.

Lemma var_dist_fdistmap_unbalanced :
  var_dist (fdistmap f (@fdist_uniform_supp R _ C HC))
           (fdist_uniform Hn) =
  2%:R * (#|B| - #|img|)%:R / #|B|%:R.
Proof.
rewrite /var_dist.
have HBnz : (#|B|%:R : R) != 0 by rewrite pnatr_eq0 Hn.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite (bigID (fun b => b \in img)) /=.
(* For b not in image, fdistmap = 0 *)
have Hnoimg : forall b0 : B, b0 \notin img -> @fdistmap R _ _ f (`U HC) b0 = 0.
  move=> b0 Hb0.
  rewrite fdistmapE big1 //.
  move=> a; rewrite inE => /eqP Hfa.
  apply: fdist_uniform_supp_notin; apply/negP => HaC.
  move/negP: Hb0; apply; apply/imsetP; exists a => //.
(* Sum over b not in img: |0 - 1/|B|| = 1/|B|, count = |B| - |img| *)
have HS2 : \sum_(i | i \notin img)
    `|@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  under eq_bigr => b0 Hb0.
    rewrite Hnoimg // sub0r normrN ger0_norm ?FDist.ge0 // fdist_uniformE.
    over.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N by [].
  have -> : #|[pred i | i \notin img]| = #|~: img|.
    by apply: eq_card => b0; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS2.
(* Reduce to showing the img-sum also equals (|B|-|img|)/|B| *)
suff HS1 : \sum_(i in img)
    `|@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  by rewrite HS1 -mulrDl -mulr2n mulr_natl.
(* Use: Σ_b P(b) = 1 = Σ_b Q(b), so Σ_b (P(b)-Q(b)) = 0 *)
have Hsum0 : \sum_(i : B)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) = 0.
  by rewrite sumrB !FDist.f1 subrr.
(* Signed sum over b not in img *)
have Hnoimg_signed : \sum_(i | i \notin img)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) =
  - ((#|B| - #|img|)%:R / #|B|%:R).
  rewrite (eq_bigr (fun b0 => - fdist_uniform Hn b0)); last first.
    by move=> b0 Hb0; rewrite Hnoimg // sub0r.
  rewrite sumrN (eq_bigr (fun _ => #|B|%:R^-1)); last first.
    by move=> b0 _; rewrite fdist_uniformE.
  rewrite sumr_const mulr_natl.
  have -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N.
    have -> : #|[pred i | i \notin img]| = #|~: img|.
      by apply: eq_card => b0; rewrite inE inE.
    by rewrite cardsCs setCK.
  by [].
(* Signed sum over img = (|B|-|img|)/|B| (from Σ=0 and complement) *)
have Hdiff : \sum_(i in img)
    (@fdistmap R _ _ f (`U HC) i - fdist_uniform Hn i) =
  (#|B| - #|img|)%:R / #|B|%:R.
  move: Hsum0.
  rewrite (bigID (fun b => b \in img)) /= Hnoimg_signed.
  by move/eqP; rewrite addr_eq0 => /eqP ->; rewrite opprK.
(* Each term in img-sum is non-negative (fiber >= 1, |C| <= |B| implies
   P(b) = fiber/|C| >= 1/|C| >= 1/|B| = Q(b)) *)
rewrite -Hdiff.
apply: eq_bigr => b0 Hb0.
rewrite ger0_norm //; rewrite subr_ge0.
rewrite fdist_uniformE fdistmapE.
have [a0 Ha0C Hfa0] : exists2 a0, a0 \in C & f a0 = b0.
  by move/imsetP: Hb0 => [a0 Ha0C Hfa0]; exists a0.
rewrite (bigD1 a0) /=; last first.
  by rewrite inE; apply/eqP.
apply: ler_wpDr; first by apply: sumr_ge0 => a _; exact: FDist.ge0.
rewrite fdist_uniform_supp_in //.
rewrite -div1r -[_^-1 in X in _ <= X]div1r.
rewrite ler_pdivlMr ?ltr0n -?lt0n //.
by rewrite mulrC div1r ler_pdivrMr ?mul1r ?ler_nat // ltr0n Hn.
Qed.

End unbalanced_var_dist.

(* Unbalanced endpoint image bound: when |C| <= N (e.g., Tg^L < N),
   the bound 2*(N - img_min)/N still holds. *)
Section endpoint_image_bound_unbalanced.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

Lemma var_dist_endpoint_unbalanced
    (HCleN : (Tg ^ L <= N)%N) (s : 'I_N) :
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) =
  2%:R * (N - #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%:R / N%:R.
Proof.
rewrite (rho_from_words_uniform_supp Hlfree).
rewrite (@var_dist_fdistmap_unbalanced R _ _ _ _ _ N' (card_ord N)) //.
  by rewrite !card_ord.
rewrite card_ord.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

Lemma var_dist_endpoint_image_bound_unbalanced
    (HCleN : (Tg ^ L <= N)%N) (img_min : nat) (s : 'I_N)
    (Himg : (img_min <= #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) <= 2%:R * (N - img_min)%:R / N%:R)%O.
Proof.
rewrite var_dist_endpoint_unbalanced //.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: ler_wpM2l; first by rewrite ler0n.
by rewrite ler_nat leq_sub2l.
Qed.

End endpoint_image_bound_unbalanced.

(******************************************************************************)
(*  Section 12: Image size bound via nat-level computation                   *)
(*                                                                            *)
(*  For concrete instances, |perm_endpoint @: achievable| can be computed at the    *)
(*  nat level using eval_word_nat, then reflected to the type level.          *)
(******************************************************************************)

Section endpoint_image_bound.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

(* When Tg^L = N (balanced), the fiber-counted var_dist reduces to
   the image-size formula 2*(N - |image_s|)/N. *)
Lemma var_dist_endpoint_balanced
    (Hbal : (Tg ^ L = N)%N) (s : 'I_N) :
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) =
  2%:R * (N - #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%:R / N%:R.
Proof.
rewrite (rho_from_words_uniform_supp Hlfree).
rewrite (@var_dist_fdistmap_balanced R _ _ _ _ _ N' (card_ord N)).
  by rewrite card_ord /M.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space // Hbal.
Qed.

(* The key corollary: bound var_dist by bounding |image_s| from below *)
Lemma var_dist_endpoint_image_bound
    (Hbal : (Tg ^ L = N)%N) (img_min : nat) (s : 'I_N)
    (Himg : (img_min <= #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) <= 2%:R * (N - img_min)%:R / N%:R)%O.
Proof.
rewrite var_dist_endpoint_balanced //.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: ler_wpM2l; first by rewrite ler0n.
by rewrite ler_nat leq_sub2l.
Qed.

End endpoint_image_bound.

Check collusion_bound.
Check collusion_bound_unconditional.
Check collusion_bound_conditional.
Check collusion_bound_k.
Check fdistmap_uniform_supp_inj.
Check var_dist_endpoint_direct.
