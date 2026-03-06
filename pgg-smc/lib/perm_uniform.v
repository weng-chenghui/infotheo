(* Uniform Permutation Conditioning (Proposition 4)

   If σ ~ Uniform(S_N) and s_1,...,s_T are distinct in 'I_N, then:
   σ(s_T) | σ(s_1)=v_1,...,σ(s_{T-1})=v_{T-1} ~ Uniform over N-(T-1)
   remaining values.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
Require Import realType_ext ssr_ext fdist proba jfdist_cond entropy.
Require Import entropy_fiber extra_proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope group_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*                    Layer 1: Combinatorial Counting                         *)
(******************************************************************************)

Section prescribed_set.

Variable N : nat.
Hypothesis N_pos : (0 < N)%N.

(* Permutations that map s(i) to v(i) for all i < k *)
Definition prescribed (k : nat) (s v : 'I_k -> 'I_N) : {set {perm 'I_N}} :=
  [set sigma : {perm 'I_N} | [forall i, sigma (s i) == v i]].

Lemma prescribedP k (s v : 'I_k -> 'I_N) (sigma : {perm 'I_N}) :
  reflect (forall i, sigma (s i) = v i) (sigma \in prescribed s v).
Proof.
rewrite inE; apply: (iffP forallP) => H i; by [apply/eqP | apply/eqP].
Qed.

Lemma prescribed0 (s v : 'I_0 -> 'I_N) : prescribed s v = [set: {perm 'I_N}].
Proof.
apply/setP => sigma; rewrite inE in_setT.
by apply/forallP => -[].
Qed.

(* Lemma 1: S_N acts k-transitively: given injective s and v,
   there exists sigma with sigma(s_i) = v_i for all i *)
Lemma Sn_k_transitive (k : nat) (s v : 'I_k -> 'I_N) :
  injective s -> injective v -> (k <= N)%N ->
  exists sigma : {perm 'I_N}, forall i, sigma (s i) = v i.
Proof.
elim: k s v => [s v _ _ _|k IHk s v s_inj v_inj kN].
  by exists 1%g => i; case: (i : 'I_0).
have s'_inj : injective (s \o lift ord_max).
  by move=> i j /(s_inj) /lift_inj.
have v'_inj : injective (v \o lift ord_max).
  by move=> i j /(v_inj) /lift_inj.
have kN' : (k <= N)%N by exact: ltnW.
have [tau0 Htau0] := IHk _ _ s'_inj v'_inj kN'.
set w := tau0 (s ord_max).
case: (boolP (w == v ord_max)) => [/eqP wvk|wvk].
  exists tau0 => -[i Hi].
  case: (unliftP ord_max (Ordinal Hi)) => [j ->|->].
    exact: Htau0.
  exact: wvk.
exists (tau0 * tperm w (v ord_max)) => -[i Hi].
case: (unliftP ord_max (Ordinal Hi)) => [j ->|->].
  have Hj := Htau0 j; rewrite /= in Hj.
  rewrite permM Hj tpermD //.
    (* tau0 (s ord_max) != tau0 (s (lift ord_max j)) *)
    rewrite /w -Hj.
    apply/negP => /eqP/perm_inj/s_inj Habs.
    by move/eqP: (neq_lift ord_max j); apply; exact: Habs.
  (* v ord_max != v (lift ord_max j) *)
  apply/negP => /eqP/v_inj Habs.
  by move/eqP: (neq_lift ord_max j); apply; exact: Habs.
(* s ord_max case *)
by rewrite permM /= /w tpermL.
Qed.

(* Lemma 2: prescribed k s v is a right coset of Sym(~: im s) *)
Lemma prescribed_coset (k : nat) (s v : 'I_k -> 'I_N) (tau : {perm 'I_N}) :
  injective s -> injective v -> (k <= N)%N ->
  tau \in prescribed s v ->
  prescribed s v = Sym (~: (s @: setT)) :* tau.
Proof.
move=> s_inj v_inj kN Htau.
have /prescribedP Htau_sv := Htau.
apply/setP => sigma; rewrite mem_rcoset.
apply/idP/idP.
  (* sigma \in prescribed -> sigma * tau^-1 \in Sym(~: im s) *)
  move/prescribedP => Hsigma.
  rewrite inE; apply/subsetP => x; rewrite !inE.
  apply: contraR; rewrite negbK => /imsetP [i _ ->].
  by rewrite permM Hsigma -(Htau_sv i) permK eqxx.
(* sigma * tau^-1 \in Sym(~: im s) -> sigma \in prescribed *)
rewrite inE => Hpon.
apply/prescribedP => i.
have Hsi : (sigma * tau^-1) (s i) = s i.
  apply: out_perm Hpon _.
  by rewrite inE negbK; apply/imsetP; exists i.
have := congr1 tau Hsi; rewrite permM permKV => ->.
exact: Htau_sv.
Qed.

(* Lemma 3: |prescribed k s v| = (N - k)! *)
Lemma card_prescribed (k : nat) (s v : 'I_k -> 'I_N) :
  injective s -> injective v -> (k <= N)%N ->
  #|prescribed s v| = (N - k)`!.
Proof.
move=> s_inj v_inj kN.
have [tau Htau] := Sn_k_transitive s_inj v_inj kN.
have Htau_in : tau \in prescribed s v.
  by apply/prescribedP.
rewrite (prescribed_coset s_inj v_inj kN Htau_in).
rewrite card_rcoset card_Sym.
congr (_`!).
have Him : #|s @: setT| = k by rewrite card_imset // cardsT card_ord.
have := cardsC (s @: setT : {set 'I_N}).
by rewrite Him card_ord => /(f_equal (subn^~ k)); rewrite addKn.
Qed.

End prescribed_set.

(******************************************************************************)
(*                    Layer 2: Conditional Value Count                         *)
(******************************************************************************)

Section prescribed_value.

Variable N : nat.
Hypothesis N_pos : (0 < N)%N.

Variable k : nat.
Variable s : 'I_k -> 'I_N.
Variable v : 'I_k -> 'I_N.

(* Extending s and v with one more prescribed value *)
Definition s_ext (s_new : 'I_N) : 'I_k.+1 -> 'I_N :=
  fun i => match unlift ord_max i with
           | Some j => s j
           | None => s_new
           end.

Definition v_ext (v_new : 'I_N) : 'I_k.+1 -> 'I_N :=
  fun i => match unlift ord_max i with
           | Some j => v j
           | None => v_new
           end.

Lemma s_ext_inj (s_new : 'I_N) :
  injective s -> s_new \notin s @: setT ->
  injective (s_ext s_new).
Proof.
move=> s_inj Hs_new i j.
rewrite /s_ext.
case: (unliftP ord_max i) => [i' ->|->];
  case: (unliftP ord_max j) => [j' ->|->] //.
- by move/s_inj => ->.
- move=> Heq; exfalso; apply/negP: Hs_new.
  by rewrite negbK; apply/imsetP; exists i'; rewrite ?inE.
- move=> Heq; exfalso; apply/negP: Hs_new.
  by rewrite negbK; apply/imsetP; exists j'; rewrite ?inE.
Qed.

Lemma v_ext_inj (v_new : 'I_N) :
  injective v -> v_new \notin v @: setT ->
  injective (v_ext v_new).
Proof.
move=> v_inj Hv_new i j.
rewrite /v_ext.
case: (unliftP ord_max i) => [i' ->|->];
  case: (unliftP ord_max j) => [j' ->|->] //.
- by move/v_inj => ->.
- move=> Heq; exfalso; apply/negP: Hv_new.
  by rewrite negbK; apply/imsetP; exists i'; rewrite ?inE.
- move=> Heq; exfalso; apply/negP: Hv_new.
  by rewrite negbK; apply/imsetP; exists j'; rewrite ?inE.
Qed.

(* The set of sigma in prescribed(s,v) with sigma(s_new) = v_new
   equals prescribed(s',v') with k+1 constraints *)
Lemma prescribed_extend (s_new v_new : 'I_N) :
  s_new \notin s @: setT -> v_new \notin v @: setT ->
  [set sigma in prescribed s v | sigma s_new == v_new] =
  prescribed (s_ext s_new) (v_ext v_new).
Proof.
move=> Hs Hv; apply/setP => sigma; rewrite !inE.
apply/andP/forallP.
  move=> [/forallP Hall /eqP Hnew] i.
  rewrite /s_ext /v_ext.
  case E: (unlift ord_max i) => [j|] /=.
    exact: Hall.
  by apply/eqP.
move=> Hall; split.
  apply/forallP => i.
  have := Hall (lift ord_max i).
  rewrite /s_ext /v_ext.
  have [j Hlift Hunlift] := unlift_some (neq_lift ord_max i).
  by rewrite Hunlift /=; rewrite (lift_inj Hlift).
have := Hall ord_max.
by rewrite /s_ext /v_ext unlift_none.
Qed.

(* Lemma 4: counting prescribed values *)
Lemma prescribed_value_count (s_new v_new : 'I_N) :
  injective s -> injective v ->
  s_new \notin s @: setT -> v_new \notin v @: setT ->
  (k.+1 <= N)%N ->
  #|[set sigma in prescribed s v | sigma s_new == v_new]| = (N - k.+1)`!.
Proof.
move=> s_inj v_inj Hs Hv kN.
rewrite prescribed_extend //.
apply: card_prescribed => //.
  exact: s_ext_inj.
exact: v_ext_inj.
Qed.

(* Corollary: ratio gives 1/(N-k) *)
Lemma prescribed_ratio :
  injective s -> injective v ->
  (k < N)%N ->
  forall s_new v_new : 'I_N,
    s_new \notin s @: setT -> v_new \notin v @: setT ->
    ((N - k.+1)`! * (N - k) = (N - k)`!)%N.
Proof.
move=> s_inj v_inj kN s_new v_new Hs Hv.
have HNk : (0 < N - k)%N by rewrite subn_gt0.
by rewrite mulnC -[in RHS](prednK HNk) factS subnS prednK.
Qed.

End prescribed_value.

(******************************************************************************)
(*                    Layer 3: Probabilistic Statement                        *)
(******************************************************************************)

Section perm_uniform_prob.
Import GRing.Theory Num.Theory.

Context {R : realType}.
Variable N_minus_1 : nat.
Let N := N_minus_1.+1.

Lemma N_pos : (0 < N)%N. Proof. by []. Qed.

(* Cardinality of S_N *)
Lemma card_permT_N : #|{perm 'I_N}| = (N`!.-1).+1.
Proof.
transitivity (#|perm_on [set: 'I_N]|).
  apply: eq_card => /= sigma.
  by rewrite inE; apply/sym_eq/subsetP.
by rewrite card_perm prednK ?fact_gt0 // cardsT card_ord.
Qed.

Let perm_fdist : R.-fdist {perm 'I_N} := fdist_uniform card_permT_N.

Variable k : nat.
Variable s : 'I_k -> 'I_N.
Variable v : 'I_k -> 'I_N.
Hypothesis s_inj : injective s.
Hypothesis v_inj : injective v.
Hypothesis kN : (k < N)%N.

Let obs_set := prescribed s v.

(* Probability of the prescribed event *)
Lemma Pr_prescribed :
  Pr perm_fdist obs_set = ((N - k)`!%:R / N`!%:R)%R.
Proof.
rewrite /Pr (eq_bigr (fun _ => (#|{perm 'I_N}|%:R^-1 : R)%R)); last first.
  by move=> sigma _; rewrite fdist_uniformE.
rewrite big_const (card_prescribed s_inj v_inj (ltnW kN)) iter_addr addr0.
set c := (#|{perm 'I_N}|%:R^-1 : R)%R.
by rewrite -[LHS]mulr_natr mulrC /c card_permT_N prednK ?fact_gt0.
Qed.

Lemma Pr_prescribed_ne0 : Pr perm_fdist obs_set != (0 : R)%R.
Proof.
rewrite Pr_prescribed mulf_neq0 //.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
by rewrite invr_neq0 // pnatr_eq0 -lt0n fact_gt0.
Qed.

(* Main result: conditional probability *)
Lemma perm_cond_uniform (s_new v_new : 'I_N) :
  s_new \notin s @: setT -> v_new \notin v @: setT ->
  let target := [set sigma : {perm 'I_N} | sigma s_new == v_new] in
  `Pr_perm_fdist[ target | obs_set ] = ((N - k)%:R^-1)%R.
Proof.
move=> Hs_new Hv_new /=.
rewrite /cPr.
(* Numerator: Pr(sigma(s_new) = v_new AND prescribed) *)
set target := [set sigma : {perm 'I_N} | sigma s_new == v_new].
have Hnum : Pr perm_fdist (target :&: obs_set) =
  ((N - k.+1)`!%:R / N`!%:R)%R.
  have -> : target :&: obs_set =
            [set sigma in obs_set | sigma s_new == v_new].
    apply/setP => sigma; rewrite !inE.
    by rewrite andbC.
  rewrite /Pr (eq_bigr (fun _ => (#|{perm 'I_N}|%:R^-1 : R)%R)); last first.
    by move=> sigma _; rewrite fdist_uniformE.
  rewrite big_const prescribed_value_count // iter_addr addr0.
  set c := (#|{perm 'I_N}|%:R^-1 : R)%R.
  by rewrite -[LHS]mulr_natr mulrC /c card_permT_N prednK ?fact_gt0.
rewrite Hnum Pr_prescribed -mulf_div divff; last first.
  by rewrite invr_neq0 // pnatr_eq0 -lt0n fact_gt0.
rewrite mulr1.
have HNk : (0 < N - k)%N by rewrite subn_gt0.
have Hfact : ((N - k)`!%:R = (N - k)%:R * (N - k.+1)`!%:R :> R)%R.
  by rewrite -{1}(prednK HNk) factS subnS natrM prednK.
rewrite Hfact invfM mulrCA divff ?mulr1 //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

(* Conditional probability is zero for already-assigned values *)
Lemma perm_cond_zero (s_new : 'I_N) (v_new : 'I_N) :
  s_new \notin s @: setT -> v_new \in v @: setT ->
  let target := [set sigma : {perm 'I_N} | sigma s_new == v_new] in
  `Pr_perm_fdist[ target | obs_set ] = (0 : R)%R.
Proof.
move=> Hs_new /imsetP [j _ Hvj] /=.
rewrite /cPr.
set target := [set sigma : {perm 'I_N} | sigma s_new == v_new].
suff -> : Pr perm_fdist (target :&: obs_set) = (0 : R)%R.
  by rewrite mul0r.
suff -> : target :&: obs_set = set0 by rewrite Pr_set0.
apply/setP => sigma; rewrite !inE.
apply: negbTE; apply/negP => /andP [/eqP Hnew /forallP Hall].
have /eqP Hsj := Hall j.
have := congr1 sigma^-1 (etrans Hnew (etrans Hvj (esym Hsj))).
rewrite !permK => Heq.
move: Hs_new; rewrite Heq.
by apply/negP/negPn/imsetP; exists j.
Qed.

(* The remaining values are exactly ~: (v @: setT) *)
Definition remaining_values : {set 'I_N} := ~: (v @: setT).

Lemma card_remaining : #|remaining_values| = (N - k)%N.
Proof.
rewrite /remaining_values.
have Hvi : #|v @: setT| = k by rewrite card_imset // cardsT card_ord.
have := cardsC (v @: setT : {set 'I_N}).
rewrite Hvi card_ord.
by move/(f_equal (subn^~ k)); rewrite addKn.
Qed.

Lemma collusion_uniform (s_new : 'I_N) (v_new : 'I_N) :
  s_new \notin s @: setT ->
  v_new \in remaining_values ->
  let target := [set sigma : {perm 'I_N} | sigma s_new == v_new] in
  `Pr_perm_fdist[ target | obs_set ] = ((N - k)%:R^-1)%R.
Proof.
move=> Hs Hv; apply: perm_cond_uniform => //.
by move: Hv; rewrite inE.
Qed.

Lemma collusion_zero (s_new : 'I_N) (v_new : 'I_N) :
  s_new \notin s @: setT ->
  v_new \notin remaining_values ->
  let target := [set sigma : {perm 'I_N} | sigma s_new == v_new] in
  `Pr_perm_fdist[ target | obs_set ] = (0 : R)%R.
Proof.
move=> Hs Hv; apply: perm_cond_zero => //.
by move: Hv; rewrite inE negbK.
Qed.

End perm_uniform_prob.
