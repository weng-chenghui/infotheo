(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Generic Product ThresholdScheme Combinator                                 *)
(*                                                                            *)
(* Given two ThresholdSchemes on 'I_N1 and 'I_N2 with T1 and T2 parties,     *)
(* produces a ThresholdScheme on 'I_(N1+N2) with T1+T2 parties.              *)
(*                                                                            *)
(* Secret encoding: s in 'I_(N1+N2) <-> (s mod N1, s div N1) in 'I_N1*'I_N2 *)
(*   combine uses mod (N1+N2) for totality on all of 'I_N1 * 'I_N2          *)
(*                                                                            *)
(* Privacy: ts_k = min(k1, k2). A coalition of size < min(k1,k2) has         *)
(*   < k_i members in each pile, so per-factor privacy applies.              *)
(*                                                                            *)
(* Application: S_5 x S_5 on 'I_10 with sum_mod per factor gives            *)
(*   (5, 10)-threshold with gap 5 and genus >= 3.                            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Secret Encoding Arithmetic                                  *)
(******************************************************************************)

Section secret_encoding.

Variables N1' N2' : nat.
Let N1 := N1'.+2.
Let N2 := N2'.+2.
Let N := N1 + N2.

(* N1, N2 >= 2 implies N1 + N2 <= N1 * N2 *)
Lemma addn_leq_muln : N <= N1 * N2.
Proof.
rewrite /N /N1 /N2.
elim: N1' => [|n IH].
  by rewrite mul2n -addnn leq_add2r.
rewrite mulSn.
rewrite [n.+3 + _]addnC.
rewrite leq_add2l.
rewrite -[X in X < _]muln1.
by rewrite ltn_pmul2l.
Qed.

(* s div N1 < N2 for any s < N *)
Lemma divn_lt_N2 (s : 'I_N) : s %/ N1 < N2.
Proof.
have HN1 : 0 < N1 by [].
rewrite ltn_divLR // mulnC.
exact: leq_trans addn_leq_muln.
Qed.

Definition split_secret (s : 'I_N) : 'I_N1 * 'I_N2 :=
  (Ordinal (ltn_pmod (val s) (isT : 0 < N1)),
   Ordinal (divn_lt_N2 s)).

(* combine uses mod N for totality *)
Definition combine_secret (s1 : 'I_N1) (s2 : 'I_N2) : 'I_N :=
  Ordinal (ltn_pmod (val s1 + N1 * val s2) (isT : 0 < N)).

Lemma combine_splitK (s : 'I_N) :
  combine_secret (split_secret s).1 (split_secret s).2 = s.
Proof.
apply: val_inj => /=.
by rewrite mulnC addnC -divn_eq modn_small //; exact: ltn_ord.
Qed.

(* Partial cancel: holds when s1 + N1 * s2 < N *)
Lemma split_combineK (s1 : 'I_N1) (s2 : 'I_N2) :
  val s1 + N1 * val s2 < N ->
  split_secret (combine_secret s1 s2) = (s1, s2).
Proof.
move=> Hlt.
congr pair; apply: val_inj => /=.
- have Hlt' : (val s1 + N1 * val s2) %% N = val s1 + N1 * val s2
    by rewrite modn_small.
  by rewrite Hlt' addnC mulnC modnMDl modn_small //; exact: ltn_ord.
- rewrite (modn_small Hlt) addnC mulnC divnMDl // divn_small //.
  by rewrite addn0.
  by exact: ltn_ord.
Qed.

End secret_encoding.

Arguments split_secret {N1' N2'}.
Arguments combine_secret {N1' N2'}.

(******************************************************************************)
(*     Section 2: Product ThresholdScheme                                     *)
(******************************************************************************)

Section product_threshold.

Variables N1' N2' : nat.
Let N1 := N1'.+2.
Let N2 := N2'.+2.
Let N := N1 + N2.

Variable ts1 : ThresholdScheme 'I_N1 'I_N1.
Variable ts2 : ThresholdScheme 'I_N2 'I_N2.

Let T1 := ts_T ts1.   (* = (ts_T' ts1).+1 *)
Let T2 := ts_T ts2.
Let T := T1 + T2.
Let k := minn (ts_k ts1) (ts_k ts2).

(* --- Pile embedding/projection --- *)

Definition embed_pile1 (x : 'I_N1) : 'I_N :=
  Ordinal (ltn_addr N2 (ltn_ord x)).

Lemma embed_pile2_proof (x : 'I_N2) : N1 + val x < N.
Proof. by rewrite ltn_add2l; exact: ltn_ord. Qed.

Definition embed_pile2 (x : 'I_N2) : 'I_N :=
  Ordinal (embed_pile2_proof x).

Definition project_pile1 (x : 'I_N) : 'I_N1 :=
  Ordinal (ltn_pmod (val x) (isT : 0 < N1)).

Definition project_pile2 (x : 'I_N) : 'I_N2 :=
  Ordinal (ltn_pmod (val x - N1) (isT : 0 < N2)).

(* --- Share pile extraction --- *)

(* Index embedding: pile-1 party index i < T1 -> product index i < T *)
Lemma pile1_idx_lt (i : 'I_T1) : val i < T.
Proof. exact: ltn_addr T2 (ltn_ord i). Qed.

(* Index embedding: pile-2 party index i < T2 -> product index T1+i < T *)
Lemma pile2_idx_lt (i : 'I_T2) : T1 + val i < T.
Proof. by rewrite ltn_add2l; exact: ltn_ord. Qed.

Definition pile1_shares (sh : T.-tuple 'I_N) : T1.-tuple 'I_N1 :=
  mktuple (fun i : 'I_T1 =>
    project_pile1 (tnth sh (Ordinal (pile1_idx_lt i)))).

Definition pile2_shares (sh : T.-tuple 'I_N) : T2.-tuple 'I_N2 :=
  mktuple (fun i : 'I_T2 =>
    project_pile2 (tnth sh (Ordinal (pile2_idx_lt i)))).

(* --- Product ThresholdScheme fields --- *)

Definition product_valid (s : 'I_N) (sh : T.-tuple 'I_N) : Prop :=
  let p := @split_secret N1' N2' s in
  ts_valid ts1 p.1 (pile1_shares sh) /\
  ts_valid ts2 p.2 (pile2_shares sh).

Definition product_recon (sh : T.-tuple 'I_N) : 'I_N :=
  @combine_secret N1' N2'
    (ts_recon ts1 (pile1_shares sh))
    (ts_recon ts2 (pile2_shares sh)).

Definition product_encode (s : 'I_N) : T.-tuple 'I_N :=
  let p := @split_secret N1' N2' s in
  let sh1 := ts_encode ts1 p.1 in
  let sh2 := ts_encode ts2 p.2 in
  mktuple (fun i : 'I_T =>
    if val i < T1
    then embed_pile1 (tnth sh1 (inord (val i)))
    else embed_pile2 (tnth sh2 (inord (val i - T1)))).

(* --- Correctness --- *)

Lemma product_correct (s : 'I_N) (sh : T.-tuple 'I_N) :
  product_valid s sh -> product_recon sh = s.
Proof.
rewrite /product_valid /product_recon => -[Hv1 Hv2].
have := @ts_correct _ _ ts1 _ _ Hv1 => ->.
have := @ts_correct _ _ ts2 _ _ Hv2 => ->.
exact: combine_splitK.
Qed.

(* --- Privacy (hardest lemma) --- *)

(* Coalition splitting: C subset of 'I_T splits into pile-1 and pile-2 parts *)
(* Both parts have cardinality bounded by |C| *)

Lemma product_private (s1 s2 : 'I_N) (sh : T.-1.+1.-tuple 'I_N)
    (C : {set 'I_T.-1.+1}) :
  #|C| < k.-1.+1 ->
  product_valid s1 sh ->
  exists sh' : T.-1.+1.-tuple 'I_N,
    product_valid s2 sh' /\
    (forall i : 'I_T.-1.+1, i \in C -> tnth sh' i = tnth sh i).
Proof.
have Hk0 : 0 < k by rewrite /k /ts_k ltn_min.
have HkK : k.-1.+1 = k by rewrite prednK.
have HT1 : 1 < T by rewrite /T /T1 /T2 /ts_T addnS.
have HTT : T.-1.+1 = T by rewrite prednK //; exact: ltn_trans _ HT1.
rewrite HkK => HC [Hv1 Hv2].
(* Pile index embeddings *)
set emb1 : 'I_T1 -> 'I_T.-1.+1 :=
  fun x => cast_ord (esym HTT) (Ordinal (pile1_idx_lt x)).
set emb2 : 'I_T2 -> 'I_T.-1.+1 :=
  fun x => cast_ord (esym HTT) (Ordinal (pile2_idx_lt x)).
have Hemb1_inj : injective emb1.
  move=> x y /cast_ord_inj; rewrite /emb1 => Hxy.
  apply: val_inj; move: Hxy => /= []; done.
have Hemb2_inj : injective emb2.
  move=> x y /cast_ord_inj; rewrite /emb2 => Hxy.
  apply: val_inj; move: Hxy => /= [] /addnI; done.
(* Coalition parts for each pile *)
set C1 := [set x : 'I_T1 | emb1 x \in C].
set C2 := [set x : 'I_T2 | emb2 x \in C].
have HC1_le : #|C1| <= #|C|.
  rewrite -(card_imset _ Hemb1_inj).
  apply: subset_leq_card; apply/subsetP => x /imsetP [y].
  by rewrite inE => Hy ->.
have HC2_le : #|C2| <= #|C|.
  rewrite -(card_imset _ Hemb2_inj).
  apply: subset_leq_card; apply/subsetP => x /imsetP [y].
  by rewrite inE => Hy ->.
have HC1 : #|C1| < ts_k ts1.
  have Hk1 : k <= ts_k ts1 by rewrite /k geq_min leqnn.
  exact: leq_ltn_trans HC1_le (leq_trans HC Hk1).
have HC2 : #|C2| < ts_k ts2.
  have Hk2 : k <= ts_k ts2 by rewrite /k geq_min leqnn orbT.
  exact: leq_ltn_trans HC2_le (leq_trans HC Hk2).
(* Apply per-factor privacy *)
have [sh1' [Hv1' Hag1]] :=
  @ts_private _ _ ts1 _ (split_secret s2).1 _ C1 HC1 Hv1.
have [sh2' [Hv2' Hag2]] :=
  @ts_private _ _ ts2 _ (split_secret s2).2 _ C2 HC2 Hv2.
(* Build combined shares *)
pose sh' : T.-1.+1.-tuple 'I_N := mktuple (fun i : 'I_T.-1.+1 =>
  if i \in C then tnth sh i
  else let j := cast_ord HTT i in
       if val j < T1
       then embed_pile1 (tnth sh1' (inord (val j)))
       else embed_pile2 (tnth sh2' (inord (val j - T1)))).
exists sh'.
split.
  rewrite /product_valid /=; split.
  - suff -> : pile1_shares sh' = sh1' by exact: Hv1'.
    apply: eq_from_tnth => j.
    rewrite /pile1_shares tnth_mktuple /sh' tnth_mktuple /=.
    case: (boolP (Ordinal (pile1_idx_lt j) \in C)) => HjC.
    + rewrite /project_pile1 /=.
      have HjC1 : j \in C1.
        rewrite /C1 inE /emb1.
        suff -> : cast_ord (esym HTT) (Ordinal (pile1_idx_lt j)) =
                  Ordinal (pile1_idx_lt j) by exact: HjC.
        by apply: val_inj.
      rewrite (Hag1 _ HjC1).
      by rewrite /pile1_shares tnth_mktuple.
    + have -> : (val j < T1) = true by rewrite ltn_ord.
      rewrite /project_pile1 /embed_pile1 /=.
      apply: val_inj => /=.
      rewrite modn_small; last exact: ltn_ord.
      congr (val (tnth _ _)).
      apply: val_inj => /=.
      by rewrite inordK //; exact: ltn_ord.
  - suff -> : pile2_shares sh' = sh2' by exact: Hv2'.
    apply: eq_from_tnth => j.
    rewrite /pile2_shares tnth_mktuple /sh' tnth_mktuple /=.
    case: (boolP (Ordinal (pile2_idx_lt j) \in C)) => HjC.
    + have HjC2 : j \in C2.
        rewrite /C2 inE /emb2.
        suff -> : cast_ord (esym HTT) (Ordinal (pile2_idx_lt j)) =
                  Ordinal (pile2_idx_lt j) by exact: HjC.
        by apply: val_inj.
      rewrite (Hag2 _ HjC2).
      by rewrite /pile2_shares tnth_mktuple.
    + have -> : (val (Ordinal (pile2_idx_lt j)) < T1) = false.
        apply/negbTE/negP => /=.
        by rewrite ltnNge leq_addr.
      rewrite /project_pile2 /embed_pile2 /=.
      apply: val_inj => /=.
      rewrite addKn modn_small; last exact: ltn_ord.
      congr (val (tnth _ _)).
      apply: val_inj => /=.
      by rewrite addKn inordK //; exact: ltn_ord.
move=> i Hi.
by rewrite /sh' tnth_mktuple /= Hi.
Qed.

(* --- Encode validity --- *)

Lemma product_encode_valid (s : 'I_N) :
  product_valid s (product_encode s).
Proof.
rewrite /product_valid /product_encode /=.
set sh := [tuple _ | i < T].
split.
- suff -> : pile1_shares sh = ts_encode ts1 (split_secret s).1
    by exact: ts_encode_valid.
  apply: eq_from_tnth => i.
  rewrite /pile1_shares tnth_mktuple /sh tnth_mktuple.
  have -> : (val (Ordinal (pile1_idx_lt i)) < T1) = true
    by rewrite /= ltn_ord.
  rewrite /project_pile1 /embed_pile1 /=.
  apply: val_inj => /=.
  rewrite modn_small; last exact: ltn_ord.
  congr (val (tnth _ _)).
  apply: val_inj => /=.
  by rewrite inordK //; exact: ltn_ord.
- suff -> : pile2_shares sh = ts_encode ts2 (split_secret s).2
    by exact: ts_encode_valid.
  apply: eq_from_tnth => i.
  rewrite /pile2_shares tnth_mktuple /sh tnth_mktuple.
  have -> : (val (Ordinal (pile2_idx_lt i)) < T1) = false.
    apply/negbTE/negP => /=.
    by rewrite ltnNge leq_addr.
  rewrite /project_pile2 /embed_pile2 /=.
  apply: val_inj => /=.
  rewrite addKn modn_small; last exact: ltn_ord.
  congr (val (tnth _ _)).
  apply: val_inj => /=.
  by rewrite addKn inordK //; exact: ltn_ord.
Qed.

(* --- Product ThresholdScheme --- *)

(* T >= 2 since T1, T2 >= 1 *)
Lemma T_gt1 : 1 < T.
Proof. by rewrite /T /T1 /T2 /ts_T addnS. Qed.

(* k >= 1 since k1, k2 >= 1 *)
Lemma k_gt0 : 0 < k.
Proof. by rewrite /k /ts_k ltn_min. Qed.

Definition product_scheme : ThresholdScheme 'I_N 'I_N :=
  @MkThresholdScheme 'I_N 'I_N T.-1 k.-1
    product_valid
    product_recon
    product_encode
    product_correct
    product_private
    product_encode_valid.

End product_threshold.

Arguments product_scheme {N1' N2'}.

(******************************************************************************)
(*     Section 3: Perm Compatibility for Sum-Mod Product                      *)
(*                                                                            *)
(* When both factors are sum_mod_scheme, perm_compatible reduces to:          *)
(* permuting summands preserves the sum. This avoids the need for per-factor  *)
(* code automorphisms entirely.                                               *)
(******************************************************************************)

Section product_sum_mod_perm_compatible.

Variables N1' N2' T1' T2' : nat.
Let N1 := N1'.+2.
Let N2 := N2'.+2.
Let N := N1 + N2.
Let T1 := T1'.+1.
Let T2 := T2'.+1.

Let ts1 : ThresholdScheme 'I_N1 'I_N1 := @sum_mod_scheme N1' T1'.
Let ts2 : ThresholdScheme 'I_N2 'I_N2 := @sum_mod_scheme N2' T2'.

Let pts := @product_scheme N1' N2' ts1 ts2.

Variable (gT : finGroupType) (G : {group gT}).

(* The permutation on 'I_(T1+T2) = 'I_N when T = N *)
Variable sigma : gT -> {perm 'I_(T1 + T2)}.

(* Pile preservation: sigma g maps pile-1 indices to pile-1 indices *)
Hypothesis preserves_pile1 :
  forall g, g \in G ->
  forall i : 'I_(T1 + T2), val i < T1 -> val (sigma g i) < T1.

(* When T1 + T2 = N (parties = sheets), perm_compatible holds because:
   1. sigma preserves piles (preserves_pile1)
   2. permuting shares within a pile preserves the pile sum
   3. sum_mod_recon only depends on the pile sum *)
Lemma product_sum_mod_perm_compatible :
  @ts_perm_compatible _ G _ _ pts sigma.
Proof.
move=> g s shares Hg Hvalid.
apply product_correct.
case: Hvalid => Hv1 Hv2.
rewrite /product_valid; split.
- (* pile1: sum of permuted pile1 shares = sum of original *)
  rewrite /ts_valid /= /sum_mod_valid_pred.
  rewrite /ts_valid /= /sum_mod_valid_pred in Hv1.
  rewrite -Hv1; congr (_ %% _).
  under eq_bigr do rewrite /pile1_shares tnth_mktuple.
  under [RHS]eq_bigr do rewrite /pile1_shares tnth_mktuple.
  under eq_bigr do rewrite tnth_mktuple.
  change (ts_T ts1) with T1 in *; change (ts_T ts2) with T2 in *.
  set F := fun (j : 'I_(T1 + T2)) => project_pile1 (tnth shares j) : nat.
  transitivity (\sum_(i < T1) F (@Ordinal (T1 + T2) (val i)
    (@pile1_idx_lt N1' N2' ts1 ts2 i))); last by [].
  transitivity (\sum_(i < T1) F (sigma g (@Ordinal (T1 + T2) (val i)
    (@pile1_idx_lt N1' N2' ts1 ts2 i)))); first by [].
  pose emb := fun (i : 'I_T1) =>
    @Ordinal (T1 + T2) (val i) (@pile1_idx_lt N1' N2' ts1 ts2 i).
  have Hemb_lt : forall i : 'I_T1, val (emb i) < T1
    by move=> i /=; exact: ltn_ord.
  pose sigma_r (i : 'I_T1) : 'I_T1 :=
    Ordinal (preserves_pile1 Hg (Hemb_lt i)).
  have Hemb_sigma : forall i, emb (sigma_r i) = sigma g (emb i)
    by move=> i; apply val_inj.
  have Hsigma_r_inj : injective sigma_r.
    move=> x y Hxy.
    have := congr1 val (Hemb_sigma x); have := congr1 val (Hemb_sigma y).
    rewrite /emb /sigma_r /= => Hy Hx.
    move: Hxy => /(congr1 val) /= Hval.
    have Hsg : sigma g (emb x) = sigma g (emb y) by apply: val_inj.
    have := @perm_inj _ (sigma g) _ _ Hsg => /(congr1 val) /=.
    exact: val_inj.
  symmetry; rewrite (reindex_inj Hsigma_r_inj).
  by apply eq_bigr => i _; rewrite /emb; congr (F _); exact: Hemb_sigma.
- (* pile2: derive preserves_pile2, then same reindexing argument *)
  have preserves_pile2 : forall i : 'I_(T1 + T2),
      T1 <= val i -> T1 <= val (sigma g i).
    move=> i Hi; rewrite leqNgt; apply/negP => Hlt.
    pose emb1 (j : 'I_T1) : 'I_(T1 + T2) := Ordinal (ltn_addr T2 (ltn_ord j)).
    have Hemb1_lt : forall j, val (emb1 j) < T1
      by move=> j; rewrite /emb1 /=; exact: ltn_ord.
    pose sigma1 (j : 'I_T1) : 'I_T1 := Ordinal (preserves_pile1 Hg (Hemb1_lt j)).
    have Hinj1 : injective sigma1.
      move=> a b /= Hab; apply val_inj; move: Hab => /(congr1 val) /= Hv.
      exact: (congr1 val (@perm_inj _ (sigma g) _ _ (val_inj Hv))).
    have [sigma1_inv Hcancel1 Hcancel2] := injF_bij Hinj1.
    pose k : 'I_T1 := Ordinal Hlt.
    have Hk : sigma g (emb1 (sigma1_inv k)) = sigma g i.
      apply val_inj => /=; have := Hcancel2 k => /(congr1 val) /=; by [].
    have Hemb_eq := @perm_inj _ (sigma g) _ _ Hk.
    have : val (emb1 (sigma1_inv k)) < T1 by exact: Hemb1_lt.
    by rewrite Hemb_eq ltnNge Hi.
  rewrite /ts_valid /= /sum_mod_valid_pred.
  rewrite /ts_valid /= /sum_mod_valid_pred in Hv2.
  rewrite -Hv2; congr (_ %% _).
  under eq_bigr do rewrite /pile2_shares tnth_mktuple.
  under [RHS]eq_bigr do rewrite /pile2_shares tnth_mktuple.
  under eq_bigr do rewrite tnth_mktuple.
  change (ts_T ts1) with T1 in *; change (ts_T ts2) with T2 in *.
  set F2 := fun (j : 'I_(T1 + T2)) => project_pile2 (tnth shares j) : nat.
  transitivity (\sum_(i < T2) F2 (@Ordinal (T1 + T2) (T1 + val i)
    (@pile2_idx_lt N1' N2' ts1 ts2 i))); last by [].
  transitivity (\sum_(i < T2) F2 (sigma g (@Ordinal (T1 + T2) (T1 + val i)
    (@pile2_idx_lt N1' N2' ts1 ts2 i)))); first by [].
  pose emb2 (j : 'I_T2) : 'I_(T1 + T2) :=
    @Ordinal (T1 + T2) (T1 + val j) (@pile2_idx_lt N1' N2' ts1 ts2 j).
  have Hemb2_ge : forall j, T1 <= val (emb2 j)
    by move=> j; rewrite /emb2 /= leq_addr.
  have Hsr2_lt : forall (j : 'I_T2), val (sigma g (emb2 j)) - T1 < T2.
    move=> j; have Hge := preserves_pile2 (emb2 j) (Hemb2_ge j).
    have Hord := ltn_ord (sigma g (emb2 j)); rewrite /= in Hord.
    have : val (sigma g (emb2 j)) - T1 + T1 < T1 + T2 by rewrite subnK.
    by move=> H; rewrite ltn_subLR.
  pose sigma_r2 (j : 'I_T2) : 'I_T2 := Ordinal (Hsr2_lt j).
  have Hemb2_sigma : forall i, emb2 (sigma_r2 i) = sigma g (emb2 i).
    move=> i; apply val_inj => /=.
    by rewrite addnC subnK //; exact: preserves_pile2 _ (Hemb2_ge i).
  have Hsigma_r2_inj : injective sigma_r2.
    move=> a b /(congr1 val) /= Hab; apply val_inj => /=.
    have Hsg : sigma g (emb2 a) = sigma g (emb2 b).
      apply val_inj => /=.
      by rewrite -(subnK (preserves_pile2 _ (Hemb2_ge a)))
                 -(subnK (preserves_pile2 _ (Hemb2_ge b))) Hab.
    have := @perm_inj _ (sigma g) _ _ Hsg => /(congr1 val) /=.
    by move/addnI => ->.
  symmetry; rewrite (reindex_inj Hsigma_r2_inj).
  by apply eq_bigr => i _; congr (F2 _); exact: Hemb2_sigma.
Qed.

End product_sum_mod_perm_compatible.
