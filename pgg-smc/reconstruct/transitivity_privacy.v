(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Transitivity Privacy Bridge                                           *)
(*                                                                            *)
(* A t-transitive monodromy group acting on the deck of N = N'.+1 distinct    *)
(* cards makes every coalition of at most t positions perfectly private: any  *)
(* valid arrangement can be re-dealt to any target secret while agreeing with *)
(* the coalition's exact view. This file proves the reusable bridge over an   *)
(* abstract group, independent of any concrete instance.                      *)
(*                                                                            *)
(* Section 1 -- Fiber counting:                                               *)
(*   rho_tuple_fiber_card == every fiber of the k-tuple orbit map has equal   *)
(*     size #|G| %/ #|dtuple_on k| when k <= t.                               *)
(*                                                                            *)
(* Section 2 -- Re-dealing bridge:                                            *)
(*   ttrans_private == a t-transitive shuffle re-deals any coalition view of  *)
(*     size <= t to either secret.                                            *)
(*                                                                            *)
(* Section 3 -- Distributional corollaries:                                   *)
(*   ttrans_view_indep == the coalition view is independent of the secret.    *)
(*   ttrans_point_uniform == the single-point pushforward is uniform.         *)
(*                                                                            *)
(* Section 4 -- Monotone leakage ramp:                                        *)
(*   view_mutual_info_le == a deterministic reduction of the view has mutual  *)
(*     information with the secret at most that of the full view (DPI at the  *)
(*     random-variable level).                                                *)
(*                                                                            *)
(* Section 5 -- Coalition-general view independence:                          *)
(*   ttrans_view_indep_gen == every coalition of at most t positions has view *)
(*     independent of the secret, by k-tuple fiber counting.                  *)
(*   coalition_view_mutual_info_le == leakage about the secret is monotone    *)
(*     under coalition inclusion.                                             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.

Section product_independence.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (R : realType) (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B).

(** inde_prod_fst == over a product distribution, a random variable whose
    conditional law given the first coordinate is constant is independent of
    the first coordinate.
    @composes: ttrans_view_indep *)
Lemma inde_prod_fst (T : finType) (Z : A * B -> T) (mu : R.-fdist T) :
  (forall a, fdistmap (fun b => Z (a, b)) P2 = mu) ->
  (P1 `x P2) |= (Z : {RV (P1 `x P2) -> T})
    _|_ ((fun ab => ab.1) : {RV (P1 `x P2) -> A}).
Proof.
move=> Hcond.
have HZa : forall (a : A) (z : T),
    Pr (P1 `x P2) (finset (preim [% (Z : {RV (P1 `x P2) -> T}),
       ((fun ab => ab.1) : {RV (P1 `x P2) -> A})] (pred1 (z, a))))
    = P1 a * mu z.
  move=> a z; rewrite /Pr.
  under eq_bigl => ab do rewrite inE /= xpair_eqE.
  rewrite (eq_bigr (fun ab => P1 ab.1 * P2 ab.2)); last first.
    by move=> ab _; rewrite fdist_prodE.
  rewrite (reindex_onto (fun b : B => (a, b)) (fun i => i.2)); last first.
    by move=> [a' b] /= /andP[_ /eqP ->].
  under eq_bigl => b do rewrite /= !eqxx !andbT.
  under eq_bigr => b _ do rewrite /=.
  by rewrite -big_distrr /= -(Hcond a) fdistmapE.
have HfstA : forall a0,
    `Pr[ ((fun ab => ab.1) : {RV (P1 `x P2) -> A}) = a0 ] = P1 a0.
  move=> a0; rewrite pfwd1E.
  have -> : finset (preim ((fun ab : A * B => ab.1)) (pred1 a0))
      = (finset (preim (@id A) (pred1 a0)) `*T).
    by apply/setP => -[a' b]; rewrite !inE.
  rewrite -Pr_fdist_fst fdist_prod1.
  have -> : finset (preim (@id A) (pred1 a0)) = [set a0].
    by apply/setP => x; rewrite !inE.
  by rewrite Pr_set1.
have HZz : forall z0, `Pr[ (Z : {RV (P1 `x P2) -> T}) = z0 ] = mu z0.
  move=> z0; rewrite pfwd1E /Pr.
  under eq_bigl => ab do rewrite inE /=.
  under eq_bigr => ab _ do rewrite fdist_prodE.
  transitivity (\sum_(a' : A) (P1 a' * mu z0)); last first.
    by rewrite -big_distrl /= FDist.f1 mul1r.
  rewrite (partition_big (fun ab => ab.1) xpredT) //=.
  apply: eq_bigr => a' _.
  rewrite -(HZa a' z0) /Pr.
  apply: eq_big => [ab | ab _]; last by rewrite fdist_prodE.
  by rewrite inE /= xpair_eqE andbC.
by move=> z a; rewrite pfwd1E HZa HZz HfstA mulrC.
Qed.

End product_independence.

Section uniform_bijection.
Variables (R : realType) (A : finType) (n : nat).

(** bij_uniform == a bijection pushes the uniform distribution to itself.
    @composes: ttrans_view_indep *)
Lemma bij_uniform (H : #|A| = n.+1) (f : A -> A) : bijective f ->
  fdistmap f (fdist_uniform (R:=R) H) = fdist_uniform H.
Proof.
move=> bijf; have [g fg gf] := bijf.
apply: fdist_ext => a.
rewrite fdistmapE fdist_uniformE.
under eq_bigr => x _ do rewrite fdist_uniformE.
rewrite sumr_const.
have -> : #|[pred x | preim f (pred1 a) x]| = 1%N.
  rewrite -(card1 (g a)); apply: eq_card => x.
  by rewrite !inE -(can_eq gf) fg.
by rewrite mulr1n.
Qed.

End uniform_bijection.

Section transitivity_privacy.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis Htrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.

(** rho_tuple_fiber_card == for k <= t, every fiber of the map sending a group
    element to the k-tuple image of a fixed injective source tuple has size
    #|G| %/ #|dtuple_on k [set: 'I_N'.+1]|.
    @composes: ttrans_view_indep *)
Lemma rho_tuple_fiber_card (k : nat) (p q : k.-tuple 'I_N'.+1) :
  (k <= t)%N -> p \in dtuple_on k [set: 'I_N'.+1] ->
  q \in dtuple_on k [set: 'I_N'.+1] ->
  #|[set g in G | [tuple (rho g) (tnth p i) | i < k] == q]|
  = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
Proof.
move=> Hkt Hp Hq.
have ktrans : [transitive^k rho @* G, on [set: 'I_N'.+1] | 'P].
  exact: (ntransitive_weak Hkt Htrans).
have phiE : forall g, [tuple (rho g) (tnth p i) | i < k] = n_act 'P p (rho g).
  by move=> g; apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_map.
pose Fb := fun r : k.-tuple 'I_N'.+1 => [set g in G | n_act 'P p (rho g) == r].
have goalE : [set g in G | [tuple (rho g) (tnth p i) | i < k] == q] = Fb q.
  by apply/setP => g; rewrite !inE phiE.
rewrite goalE.
have nactM : forall (u : k.-tuple 'I_N'.+1) (a b : {perm 'I_N'.+1}),
    n_act 'P u (a * b) = n_act 'P (n_act 'P u a) b.
  by move=> u a b; exact: (actM (n_act_action 'P k) u a b).
have nact1 : forall (u : k.-tuple 'I_N'.+1), n_act 'P u 1 = u.
  by move=> u; exact: (act1 (n_act_action 'P k) u).
have Heq : forall r, r \in dtuple_on k [set: 'I_N'.+1] -> #|Fb r| = #|Fb q|.
  move=> r Hr.
  have [h hin hqr] := atransP2 ktrans Hq Hr.
  have [g0 g0G _ hg0] := morphimP hin.
  have hr : n_act 'P q (rho g0) = r by rewrite hqr hg0.
  have -> : Fb r = [set (x * g0)%g | x in Fb q].
    apply/setP => x; rewrite inE; apply/idP/imsetP.
    - move=> /andP[xG /eqP xr].
      exists (x * g0^-1)%g; last by rewrite -mulgA mulVg mulg1.
      rewrite inE; apply/andP; split; first by rewrite groupM // groupV.
      apply/eqP.
      by rewrite morphM ?groupV // morphV // nactM xr -hr -nactM mulgV nact1.
    - case=> y; rewrite inE => /andP[yG /eqP yq] ->.
      apply/andP; split; first by rewrite groupM.
      by apply/eqP; rewrite morphM // nactM yq hr.
  exact: (card_imset (Fb q) (mulIg g0)).
have HG0 : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N by apply/card_gt0P; exists q.
have Hpart : #|G| = #|dtuple_on k [set: 'I_N'.+1]| * #|Fb q|.
  transitivity (\sum_(g in G) 1); first by rewrite sum1_card.
  rewrite (partition_big (fun g => n_act 'P p (rho g))
             (mem (dtuple_on k [set: 'I_N'.+1]))); last first.
    by move=> g gG; apply: n_act_dtuple => //; apply/astabsP => x; rewrite !inE.
  rewrite (eq_bigr (fun _ => #|Fb q|)); last first.
    by move=> r Hr; rewrite sum1dep_card -(Heq r Hr).
  by rewrite sum_nat_const.
by rewrite Hpart (mulKn _ HG0).
Qed.

Section redeal.
Variable orbit_class : N'.+1.-tuple 'I_N'.+1 -> bool.
Variable deck_ok : N'.+1.-tuple 'I_N'.+1 -> bool.
Hypothesis Hdeck_uniq : forall sh, deck_ok sh -> uniq sh.
Hypothesis Hinv : forall g sh, g \in G ->
  orbit_class [tuple tnth sh (rho g i) | i < N'.+1] = orbit_class sh.
Hypothesis Hdeck_stable : forall g sh, g \in G ->
  deck_ok [tuple tnth sh (rho g i) | i < N'.+1] = deck_ok sh.
Hypothesis Hpopulated : forall b : bool,
  exists sh, deck_ok sh /\ orbit_class sh = b.

(** ttrans_private == a t-transitive shuffle over a distinct-card deck admits,
    for every coalition of at most t positions and every target secret, a
    re-dealt valid arrangement agreeing with the coalition's exact view.
    @main security: the transitivity privacy bridge discharging ts_private. *)
Theorem ttrans_private (s2 : bool) (sh : N'.+1.-tuple 'I_N'.+1)
    (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> deck_ok sh ->
  exists sh', [/\ deck_ok sh', orbit_class sh' = s2 &
    forall i, i \in C -> tnth sh' i = tnth sh i].
Proof.
move=> HC Hsh.
have [sh2 [Hsh2 Hsh2c]] := Hpopulated s2.
have sh_inj : injective (tnth sh) by apply/tuple_uniqP; exact: Hdeck_uniq.
have sh2_inj : injective (tnth sh2) by apply/tuple_uniqP; exact: Hdeck_uniq.
have [ps psE] : {ps : {perm 'I_N'.+1} | ps =1 tnth sh}.
  by exists (perm sh_inj); exact: permE.
have [ps2 ps2E] : {ps2 : {perm 'I_N'.+1} | ps2 =1 tnth sh2}.
  by exists (perm sh2_inj); exact: permE.
pose pih := (ps * ps2^-1)%g.
pose k := size (enum C).
pose st : k.-tuple 'I_N'.+1 := in_tuple (enum C).
pose tt : k.-tuple 'I_N'.+1 := [tuple pih (tnth st l) | l < k].
have Hk : (k <= t)%N by rewrite /k -cardE.
have Hst : st \in dtuple_on k [set: 'I_N'.+1].
  by rewrite inE; apply/andP; split; [rewrite enum_uniq | apply/subsetP].
have stinj : injective (tnth st) by apply/tuple_uniqP; exact: enum_uniq.
have Htt : tt \in dtuple_on k [set: 'I_N'.+1].
  rewrite inE; apply/andP; split; last by apply/subsetP.
  by apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /perm_inj/stinj->.
have ktrans : [transitive^k rho @* G, on [set: 'I_N'.+1] | 'P].
  exact: (ntransitive_weak Hk Htrans).
have [h hin htt] := atransP2 ktrans Hst Htt.
have [g gG _ hg] := morphimP hin.
have httE : forall l, h (tnth st l) = pih (tnth st l).
  move=> l; move: (congr1 (fun z : k.-tuple _ => tnth z l) htt).
  by rewrite tnth_mktuple tnth_map => ->.
have hpi : forall i, i \in C -> rho g i = pih i.
  move=> i iC.
  have iC2 : i \in st by rewrite mem_enum.
  by case/tnthP: iC2 => l ->; rewrite -hg httE.
exists [tuple tnth sh2 (rho g i) | i < N'.+1]; split.
- by rewrite (Hdeck_stable sh2 gG).
- by rewrite (Hinv sh2 gG).
- move=> i iC.
  by rewrite tnth_mktuple (hpi i iC) -ps2E /pih permM permKV psE.
Qed.

End redeal.

Section point_marginal.
Local Open Scope ring_scope.
Variable R : realType.

(** ttrans_point_uniform == the single-point pushforward of the uniform draw
    over a transitive permutation group is exactly uniform.
    @main security: single-card perfect uniformity of the shuffle. *)
Lemma ttrans_point_uniform (Hpos : (0 < #|G|)%N) (s : 'I_N'.+1) :
  (0 < t)%N ->
  fdistmap (fun g : gT => rho g s) (`U Hpos : R.-fdist gT)
  = fdist_uniform (card_ord N'.+1).
Proof.
move=> t_gt0.
have Ht1 : (1 <= t)%N by [].
have Hs1 : [tuple s] \in dtuple_on 1 [set: 'I_N'.+1].
  by rewrite inE /=; apply/subsetP.
have key : forall (a : 'I_N'.+1) (g : gT),
  ([tuple rho g (tnth [tuple s] i) | i < 1] == [tuple a]) = (rho g s == a).
  move=> a g.
  by rewrite -!(inj_eq val_inj) /= [enum 'I_1]enum_ordSl enum_ord0 /=
    (tnth_nth s) /= eqseq_cons andbT.
set d := #|dtuple_on 1 [set: 'I_N'.+1]|.
set f := (#|G| %/ d)%N.
have fibE : forall a, #|[set g in G | rho g s == a]| = f.
  move=> a.
  have Ha : [tuple a] \in dtuple_on 1 [set: 'I_N'.+1].
    by rewrite inE /=; apply/subsetP.
  rewrite /f /d -(rho_tuple_fiber_card Ht1 Hs1 Ha).
  by apply: eq_card => g; rewrite !inE key.
have Hf : #|G| = (N'.+1 * f)%N.
  rewrite -[LHS]sum1_card (partition_big (fun g => rho g s) xpredT) //=.
  rewrite (eq_bigr (fun=> f)); last first.
    move=> a _; rewrite -(fibE a) sum1dep_card.
    by apply: eq_card => g; rewrite !inE.
  by rewrite sum_nat_const card_ord.
apply: fdist_ext => a.
rewrite fdistmapE fdist_uniformE card_ord.
rewrite (bigID (fun a0 => a0 \in G)) /=.
rewrite [X in (_ + X)%R]big1; last first.
  by move=> a0 /andP[_ Ha0]; rewrite fdist_uniform_supp_notin.
rewrite addr0.
rewrite (eq_bigr (fun=> (#|G|%:R^-1))); last first.
  by move=> i /andP[_ Hi]; rewrite fdist_uniform_supp_in.
rewrite sumr_const.
have -> : #|(fun i : gT =>
    (i \in preim (fun g : gT => rho g s) (pred1 a)) && (i \in G))| = f.
  by rewrite -(fibE a); apply: eq_card => i; rewrite !inE andbC.
have HGR : (#|G|%:R != 0 :> R) by rewrite pnatr_eq0 -lt0n.
have HNR : (N'.+1%:R != 0 :> R) by rewrite pnatr_eq0.
apply: (mulfI HGR).
by rewrite mulrnAr (mulfV HGR) Hf natrM mulrAC (mulfV HNR) mul1r.
Qed.

End point_marginal.

Section view_indep.
Local Open Scope proba_scope.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis HG : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Let P : R.-fdist (bool * gT)%type := secretP `x (`U HG).

(** coalition_view == the dealt card values seen by coalition C at a sample
    (secret, shuffle), and ord0 outside C.
    @intent: coalition observable random variable. *)
Definition coalition_view (C : {set 'I_N'.+1})
    : {RV P -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth (encode u.1) (rho u.2 i) else ord0].

(** dealt_secret == the dealt secret component of a sample.
    @intent: secret random variable. *)
Definition dealt_secret : {RV P -> bool} := fun u => u.1.

(** ttrans_view_indep == a single corrupted position's view of the uniformly
    shuffled dealt arrangement is independent of the secret when the encoding
    is injective per secret and the shuffle group is transitive.
    @main security: distributional corollary of the transitivity bridge. *)
Lemma ttrans_view_indep (i0 : 'I_N'.+1) :
  (0 < t)%N -> (forall b, uniq (encode b)) ->
  P |= coalition_view [set i0] _|_ dealt_secret.
Proof.
move=> t_gt0 Huniq.
pose pf := fun v : 'I_N'.+1 =>
  [ffun i : 'I_N'.+1 => if i \in [set i0] then v else ord0].
pose mu : R.-fdist {ffun 'I_N'.+1 -> 'I_N'.+1} :=
  fdistmap pf (fdist_uniform (card_ord N'.+1)).
apply: (@inde_prod_fst R bool gT secretP (`U HG) _
  (coalition_view [set i0]) mu) => b.
have inj_b : injective (tnth (encode b)) by apply/tuple_uniqP; exact: Huniq.
have -> : (fun b0 : gT => coalition_view [set i0] (b, b0))
        = pf \o (tnth (encode b) \o (fun g0 : gT => rho g0 i0)).
  apply: boolp.funext => g0 /=; apply/ffunP => i.
  rewrite /coalition_view !ffunE.
  case Hi: (i \in [set i0]) => //.
  by move: Hi; rewrite in_set1 => /eqP ->.
rewrite -fdistmap_comp -fdistmap_comp.
rewrite ttrans_point_uniform //.
by rewrite (bij_uniform _ _ (injF_bij inj_b)).
Qed.

End view_indep.

End transitivity_privacy.

From infotheo Require Import entropy.

Section monotone_ramp.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Context {R : realType} {U : finType} (P : R.-fdist U).
Variables (secretT viewT viewT' : finType).
Variables (secret : {RV P -> secretT}) (fullview : {RV P -> viewT}).
Variable proj : viewT -> viewT'.

(** centropy_pair_le == conditioning on a pair of observables cannot exceed
    the conditional entropy given only the second observable.
    @composes: view_mutual_info_le *)
Lemma centropy_pair_le (TX TW TZ : finType)
    (X : {RV P -> TX}) (W : {RV P -> TW}) (Z : {RV P -> TZ}) :
  `H(X | [% W, Z]) <= `H(X | Z).
Proof.
move: (cond_mutual_info_ge0 `p_[% X, W, Z]).
by rewrite /cond_mutual_info fdist_proj13_RV3 fdistA_RV3 subr_ge0.
Qed.

(** view_mutual_info_le == a deterministic reduction of the view cannot
    increase the mutual information shared with the secret; the data-processing
    inequality at the random-variable level.
    @main bound: the monotone leakage ramp making (k, T) well-defined. *)
Lemma view_mutual_info_le :
  `I(secret ; proj `o fullview) <= `I(secret ; fullview).
Proof.
rewrite !mutual_info_RVE lerD2l lerN2.
rewrite -(centropy_RV_contraction secret fullview proj).
exact: centropy_pair_le.
Qed.

End monotone_ramp.

Section transitivity_privacy_gen.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis Htrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis HG : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.

(** ktuple_encode_uniform == the pushforward of the uniform shuffle by the
    coalition's encoded value-tuple map is uniform over injective tuples.
    @composes: ttrans_view_indep_gen *)
Lemma ktuple_encode_uniform (k : nat) (p : k.-tuple 'I_N'.+1) (b : bool)
    (Hdt : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N) :
  (k <= t)%N -> uniq (encode b) ->
  p \in dtuple_on k [set: 'I_N'.+1] ->
  fdistmap (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k])
    (`U HG : R.-fdist gT) = `U Hdt.
Proof.
move=> Hk Hub Hp.
have b_inj : injective (tnth (encode b)) by apply/tuple_uniqP; exact: Hub.
have [eb ebK ebK'] := injF_bij b_inj.
have phi_in : forall g : gT,
    [tuple tnth (encode b) (rho g (tnth p l)) | l < k]
      \in dtuple_on k [set: 'I_N'.+1].
  move=> g; rewrite inE; apply/andP; split.
    apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /b_inj/perm_inj.
    by move: Hp; rewrite inE => /andP[/tuple_uniqP pinj _]; apply: pinj.
  by apply/subsetP => x _; rewrite inE.
have fibeqgen : forall r : k.-tuple 'I_N'.+1,
    r \in dtuple_on k [set: 'I_N'.+1] ->
    #|[set g in G | [tuple tnth (encode b) (rho g (tnth p l)) | l < k] == r]|
    = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
  move=> r Hr.
  have Hr' : [tuple eb (tnth r l) | l < k] \in dtuple_on k [set: 'I_N'.+1].
    rewrite inE; apply/andP; split.
      apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /(can_inj ebK').
      by move: Hr; rewrite inE => /andP[/tuple_uniqP rinj _]; apply: rinj.
    by apply/subsetP => x _; rewrite inE.
  rewrite -(rho_tuple_fiber_card Htrans Hk Hp Hr').
  apply: eq_card => g; rewrite !inE; congr (_ && _).
  apply/idP/idP => /eqP Htup; apply/eqP.
    apply: eq_from_tnth => l.
    move: (congr1 (fun z : k.-tuple _ => tnth z l) Htup).
    rewrite !tnth_mktuple => Hl.
    by rewrite -(ebK (rho g (tnth p l))) Hl.
  apply: eq_from_tnth => l.
  move: (congr1 (fun z : k.-tuple _ => tnth z l) Htup).
  rewrite !tnth_mktuple => Hl.
  by rewrite Hl ebK'.
have Hpart : #|G| = (#|dtuple_on k [set: 'I_N'.+1]|
                     * (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|))%N.
  rewrite -[LHS]sum1_card.
  rewrite (partition_big
    (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k])
    (mem (dtuple_on k [set: 'I_N'.+1]))) /=; last first.
    by move=> g _; exact: phi_in.
  rewrite (eq_bigr (fun=> (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N));
    last first.
    move=> r Hr; rewrite sum1dep_card -(fibeqgen r Hr).
    by apply: eq_card => g; rewrite !inE.
  by rewrite sum_nat_const.
apply: fdist_ext => q.
rewrite fdistmapE.
case: (boolP (q \in dtuple_on k [set: 'I_N'.+1])) => Hq.
  rewrite fdist_uniform_supp_in //.
  rewrite (bigID (fun g : gT => g \in G)) /=.
  rewrite [X in (_ + X)%R]big1; last first.
    by move=> g /andP[_ Hg]; rewrite fdist_uniform_supp_notin.
  rewrite addr0.
  rewrite (eq_bigr (fun=> (#|G|%:R^-1))); last first.
    by move=> g /andP[_ Hg]; rewrite fdist_uniform_supp_in.
  rewrite sumr_const.
  have -> : #|(fun i : gT =>
    (i \in preim (fun g : gT =>
              [tuple tnth (encode b) (rho g (tnth p l)) | l < k]) (pred1 q))
       && (i \in G))|
  = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
    by rewrite -(fibeqgen q Hq); apply: eq_card => i; rewrite !inE andbC.
  have HGR : (#|G|%:R != 0 :> R) by rewrite pnatr_eq0 -lt0n.
  have HdR : (#|dtuple_on k [set: 'I_N'.+1]|%:R != 0 :> R).
    by rewrite pnatr_eq0 -lt0n.
  apply: (mulfI HGR).
  by rewrite mulrnAr (mulfV HGR) {2}Hpart natrM mulrAC (mulfV HdR) mul1r.
rewrite fdist_uniform_supp_notin //.
apply: big1 => g Hg.
case/andP: Hg => _ /eqP Hgq.
by move: (phi_in g); rewrite Hgq (negbTE Hq).
Qed.

(** ttrans_view_indep_gen == a t-transitive shuffle over a distinct-card deck
    makes every coalition view of at most t positions independent of the
    orbit secret.
    @main security: the coalition-general distributional privacy bridge. *)
Lemma ttrans_view_indep_gen (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> (forall b, uniq (encode b)) ->
  secretP `x (`U HG) |= coalition_view rho secretP HG encode C _|_
    @dealt_secret gT G R secretP HG.
Proof.
move=> HC Huniq.
pose k := size (enum C).
pose p : k.-tuple 'I_N'.+1 := in_tuple (enum C).
have Hk : (k <= t)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_N'.+1].
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hdt : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N by apply/card_gt0P; exists p.
pose maskf := fun r : k.-tuple 'I_N'.+1 =>
  [ffun i : 'I_N'.+1 => nth ord0 (val r) (index i (enum C))].
apply: (@inde_prod_fst R bool gT secretP (`U HG) _
  (coalition_view rho secretP HG encode C) (fdistmap maskf (`U Hdt))) => b.
have Hcomp : (fun b0 : gT => coalition_view rho secretP HG encode C (b, b0))
    = maskf \o
      (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /= /maskf ffunE /coalition_view ffunE.
  case Hi: (i \in C).
    have Hmem : i \in enum C by rewrite mem_enum Hi.
    have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
    rewrite -(tnth_nth ord0 _ (Ordinal Hj)) tnth_mktuple.
    have -> : tnth p (Ordinal Hj) = i by rewrite (tnth_nth i) nth_index.
    by [].
  have Hni : i \notin enum C by rewrite mem_enum Hi.
  have Hidx : index i (enum C) = k.
    apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [rewrite /k; exact: index_size | rewrite /k leqNgt index_mem].
  by rewrite Hidx nth_default // size_tuple.
rewrite Hcomp -fdistmap_comp.
by rewrite (@ktuple_encode_uniform k p b Hdt Hk (Huniq b) Hp).
Qed.

Local Open Scope entropy_scope.

(** coalition_view_mutual_info_le == a sub-coalition shares at most the mutual
    information about the secret that the enclosing coalition shares; leakage
    is monotone under coalition inclusion.
    @main bound: leakage is monotone under coalition inclusion (the ramp
    ordering).
    Naming: extends view_mutual_info_le to coalitions; the shared
    _mutual_info_le tail is kept for symmetry with that lemma. *)
Lemma coalition_view_mutual_info_le (C C' : {set 'I_N'.+1}) :
  C' \subset C ->
  `I(dealt_secret secretP HG ;
       coalition_view rho secretP HG encode C')
    <= `I(dealt_secret secretP HG ; coalition_view rho secretP HG encode C).
Proof.
move=> HCC'.
pose restrict := fun v : {ffun 'I_N'.+1 -> 'I_N'.+1} =>
  [ffun i => if i \in C' then v i else ord0].
have Hview : coalition_view rho secretP HG encode C'
    = restrict `o coalition_view rho secretP HG encode C.
  apply: boolp.funext => u; apply/ffunP => i.
  rewrite /comp_RV /restrict /coalition_view !ffunE.
  case: (boolP (i \in C')) => iC' //=.
  by rewrite (subsetP HCC' _ iC').
rewrite Hview.
exact: view_mutual_info_le.
Qed.

End transitivity_privacy_gen.
