(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop path binomial.
From Stdlib Require Import Wf_nat.
From pgg_smc Require Import pgg_lfree pgg_raag pgg_raag_clique.

(******************************************************************************)
(* PGG-SMC: Cartier-Foata Theorem Infrastructure                             *)
(*                                                                            *)
(* Re-proves infrastructure lemmas about foata_pairs/foata_nf that are        *)
(* section-local in pgg_raag.v, plus new NF properties:                       *)
(*                                                                            *)
(* Section foata_infrastructure:                                              *)
(*   foata_pairs_split' == foata_pairs distributes over concatenation         *)
(*   foata_pairs_vals == values of foata_pairs = prev values ++ w             *)
(*   size_foata_pairs == size of foata_pairs = size prev + size w             *)
(*   dv_leq_trans/anti/total == dv_leq is a total order                      *)
(*   sort_perm_eq_dv == perm_eq inputs give equal sorted outputs              *)
(*   foata_depth_at_bigop == depth as bigop (perm invariant)                  *)
(*   foata_depth_at_perm == depth invariant under prefix permutation          *)
(*   foata_depth_comm_rcons == commuting element doesn't affect depth         *)
(*   foata_pairs_perm_prefix == permuted prefix gives permuted output         *)
(*   foata_pairs_swap_adj == adjacent commuting swap preserves multiset       *)
(*   foata_nf_swap_adj == adjacent commuting swap preserves NF                *)
(*   foata_nf_sorted == sorted pairs implies NF = identity                    *)
(*   foata_nf_sound == NF reachable via adjacent commuting swaps             *)
(*                                                                            *)
(* Section foata_nf_properties:                                               *)
(*   size_foata_nf == size (foata_nf comm w) = size w                         *)
(*   foata_nf_perm_eq == perm_eq (foata_nf comm w) w                          *)
(*   foata_nf_idempotent == foata_nf (foata_nf w) = foata_nf w               *)
(*   foata_nf_prepend_compat == equal NFs imply equal NFs after prepend       *)
(*                                                                            *)
(* Section cartier_foata:                                                     *)
(*   foata_first_layer/rest infrastructure with Tg and comm_sym               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Infrastructure lemmas about foata_pairs / foata_nf (no Tg needed)          *)
(* ========================================================================== *)

Section foata_infrastructure.

(* --- foata_pairs structural lemmas --- *)

Lemma foata_pairs_split' (crel : nat -> nat -> bool) prev w1 w2 :
  foata_pairs crel prev (w1 ++ w2) =
  foata_pairs crel (foata_pairs crel prev w1) w2.
Proof. by elim: w1 prev => [|x w1 IH] prev //=. Qed.

Lemma foata_pairs_vals (crel : nat -> nat -> bool) prev w :
  map snd (foata_pairs crel prev w) = map snd prev ++ w.
Proof.
elim: w prev => [|x w IH] prev /=; first by rewrite cats0.
by rewrite IH map_rcons -cats1 -catA.
Qed.

Lemma size_foata_pairs (crel : nat -> nat -> bool) prev w :
  size (foata_pairs crel prev w) = size prev + size w.
Proof.
elim: w prev => [|x w IH] prev /=; first by rewrite addn0.
by rewrite IH size_rcons addSnnS.
Qed.

(* --- dv_leq properties --- *)

Lemma dv_leq_trans : transitive dv_leq.
Proof.
move=> [d2 v2] [d1 v1] [d3 v3]; rewrite /dv_leq /=.
move/orP => [H1|/andP [/eqP H1 H2]]; move/orP => [H3|/andP [/eqP H3 H4]].
- by apply/orP; left; exact: ltn_trans H1 H3.
- by apply/orP; left; rewrite -H3.
- by apply/orP; left; rewrite H1.
- by apply/orP; right; apply/andP; split;
    [rewrite H1 H3|exact: leq_trans H2 H4].
Qed.

Lemma dv_leq_anti : antisymmetric dv_leq.
Proof.
move=> [d1 v1] [d2 v2]; rewrite /dv_leq /=.
move/andP => [/orP [H1|/andP [/eqP H1 H2]] /orP [H3|/andP [/eqP H3 H4]]].
- by have := ltn_trans H1 H3; rewrite ltnn.
- by exfalso; rewrite H3 ltnn in H1.
- by exfalso; rewrite H1 ltnn in H3.
- by congr pair; [rewrite H1 | apply/anti_leq/andP].
Qed.

Lemma dv_leq_total : total dv_leq.
Proof.
move=> [d1 v1] [d2 v2]; rewrite /dv_leq /=.
by case: ltngtP => //= E; rewrite ?E ?eqxx /= ?leq_total ?orbT.
Qed.

Lemma sort_perm_eq_dv (s1 s2 : seq (nat * nat)) :
  perm_eq s1 s2 -> sort dv_leq s1 = sort dv_leq s2.
Proof.
move=> Hp.
have Hs1 := sort_sorted dv_leq_total s1.
have Hs2 := sort_sorted dv_leq_total s2.
have Hp' : perm_eq (sort dv_leq s1) (sort dv_leq s2).
  by rewrite (perm_sort _ s1) perm_sym (perm_sort _ s2) perm_sym.
exact: (sorted_eq dv_leq_trans dv_leq_anti Hs1 Hs2 Hp').
Qed.

(* --- foata_depth_at as bigop --- *)

Let foldl_maxn_shift (s : seq nat) (a : nat) :
  foldl maxn a s = maxn a (foldl maxn 0 s).
Proof.
elim: s a => [|b s IH] a /=; first by rewrite maxn0.
by rewrite (IH (maxn a b)) (IH (maxn 0 b)) max0n maxnA.
Qed.

Lemma foata_depth_at_bigop (crel : nat -> nat -> bool) prev x :
  foata_depth_at crel prev x =
  \max_(dv <- prev | ~~ crel dv.2 x) dv.1.+1.
Proof.
rewrite /foata_depth_at.
suff Hgen : forall acc,
  foldl (fun a dv => if crel dv.2 x then a else maxn a dv.1.+1) acc prev =
  maxn acc (\max_(dv <- prev | ~~ crel dv.2 x) dv.1.+1).
  by rewrite Hgen max0n.
elim: prev => [|dv prev IH] acc /=; first by rewrite big_nil maxn0.
by rewrite big_cons; case: (crel dv.2 x) => /=; rewrite IH -?maxnA.
Qed.

Lemma foata_depth_at_perm (crel : nat -> nat -> bool) prev1 prev2 x :
  perm_eq prev1 prev2 ->
  foata_depth_at crel prev1 x = foata_depth_at crel prev2 x.
Proof. by move=> Hp; rewrite !foata_depth_at_bigop; apply: perm_big. Qed.

(* --- Commuting element doesn't affect depth --- *)

Lemma foata_depth_comm_rcons (crel : nat -> nat -> bool) prev d a b :
  crel a b ->
  foata_depth_at crel (rcons prev (d, a)) b =
  foata_depth_at crel prev b.
Proof.
move=> Hab; rewrite !foata_depth_at_bigop -cats1 big_cat /=.
by rewrite big_cons big_nil Hab /= maxn0.
Qed.

(* --- Prefix preservation --- *)

Lemma foata_pairs_prefix (crel : nat -> nat -> bool) prev w :
  take (size prev) (foata_pairs crel prev w) = prev.
Proof.
elim: w prev => [|x w IH] prev //=.
  by rewrite take_size.
have := IH (rcons prev (foata_depth_at crel prev x, x)).
rewrite size_rcons => HIH.
rewrite -(take_takel _ (leqnSn (size prev))) HIH.
by rewrite -cats1 take_size_cat.
Qed.

(* --- nth access into foata_pairs --- *)

Lemma nth_foata_pairs_val (crel : nat -> nat -> bool) prev w k :
  k < size w ->
  (nth (0, 0) (foata_pairs crel prev w) (size prev + k)).2 = nth 0 w k.
Proof.
elim: w prev k => [|x w IH] prev k //=.
case: k => [|k] Hk /=.
  rewrite addn0; set prev' := rcons prev _.
  have Hlt : size prev < size prev' by rewrite /prev' size_rcons.
  rewrite -(nth_take (0,0) Hlt) (foata_pairs_prefix crel prev' w).
  by rewrite /prev' nth_rcons ltnn eqxx.
by rewrite -(IH (rcons prev (foata_depth_at crel prev x, x)) k Hk)
           size_rcons addSnnS.
Qed.

Lemma nth_foata_pairs_depth (crel : nat -> nat -> bool) prev w k :
  k < size w ->
  (nth (0, 0) (foata_pairs crel prev w) (size prev + k)).1 =
  foata_depth_at crel (foata_pairs crel prev (take k w)) (nth 0 w k).
Proof.
elim: w prev k => [|x w IH] prev k //=.
case: k => [|k] Hk /=.
  rewrite addn0 /=; set prev' := rcons prev _.
  have Hlt : size prev < size prev' by rewrite /prev' size_rcons.
  rewrite -(nth_take (0,0) Hlt) (foata_pairs_prefix crel prev' w).
  by rewrite /prev' nth_rcons ltnn eqxx.
by rewrite -(IH (rcons prev (foata_depth_at crel prev x, x)) k Hk)
           size_rcons addSnnS.
Qed.

(* --- Permuted prefix gives permuted foata_pairs --- *)

Lemma foata_pairs_perm_prefix (crel : nat -> nat -> bool) p1 p2 w :
  perm_eq p1 p2 ->
  perm_eq (foata_pairs crel p1 w) (foata_pairs crel p2 w).
Proof.
elim: w p1 p2 => [|x w IH] p1 p2 Hp //=.
apply: IH; rewrite (foata_depth_at_perm _ _ Hp) -!cats1.
exact: perm_cat Hp (perm_refl _).
Qed.

(* --- Swapping adjacent commuting elements preserves foata_pairs multiset --- *)

Lemma foata_pairs_swap_adj (crel : nat -> nat -> bool) prev a b w :
  crel a b -> crel b a ->
  perm_eq (foata_pairs crel prev (a :: b :: w))
          (foata_pairs crel prev (b :: a :: w)).
Proof.
move=> Hab Hba /=.
rewrite (foata_depth_comm_rcons _ _ Hab) (foata_depth_comm_rcons _ _ Hba).
apply: foata_pairs_perm_prefix.
by rewrite -!cats1 -!catA perm_cat2l perm_catC.
Qed.

(* --- foata_nf invariant under adjacent commuting swap --- *)

Lemma foata_nf_swap_adj (crel : nat -> nat -> bool) a b (w1 w2 : seq nat) :
  crel a b -> crel b a ->
  foata_nf crel (w1 ++ a :: b :: w2) = foata_nf crel (w1 ++ b :: a :: w2).
Proof.
move=> Hab Hba; rewrite /foata_nf !foata_pairs_split'.
congr (map snd); apply: sort_perm_eq_dv.
exact: foata_pairs_swap_adj.
Qed.

(* --- Depth lower bound from non-commuting predecessor --- *)

Lemma foata_depth_noncomm_lb (crel : nat -> nat -> bool) prev d v x :
  ~~ crel v x -> (d, v) \in prev ->
  d.+1 <= foata_depth_at crel prev x.
Proof.
move=> Hnc Hin; rewrite foata_depth_at_bigop.
exact: (leq_bigmax_seq (d, v) Hin Hnc).
Qed.

(* --- Adjacent descent implies commutativity --- *)

Lemma foata_descent_comm (crel : nat -> nat -> bool) prev w k :
  k.+1 < size w ->
  ~~ dv_leq (nth (0, 0) (foata_pairs crel prev w) (size prev + k))
             (nth (0, 0) (foata_pairs crel prev w) (size prev + k.+1)) ->
  crel (nth 0 w k) (nth 0 w k.+1).
Proof.
move=> Hk; rewrite /dv_leq negb_or -!ltnNge => /andP [Hlt _].
apply/negPn/negP => Hnc.
have Hk' := ltn_trans (ltnSn k) Hk.
have Hdep : (nth (0, 0) (foata_pairs crel prev w) (size prev + k.+1)).1 >=
  ((nth (0, 0) (foata_pairs crel prev w) (size prev + k)).1).+1.
  rewrite (nth_foata_pairs_depth crel prev Hk).
  rewrite (nth_foata_pairs_depth crel prev Hk').
  rewrite (take_nth 0 Hk') -cats1 (foata_pairs_split' crel) /=.
  apply: foata_depth_noncomm_lb; first exact: Hnc.
  by rewrite mem_rcons inE eqxx.
by have := leq_ltn_trans Hdep Hlt; rewrite ltnn.
Qed.

(* --- When foata_pairs is sorted, foata_nf = identity --- *)

Lemma foata_nf_sorted (crel : nat -> nat -> bool) w :
  sorted dv_leq (foata_pairs crel [::] w) -> foata_nf crel w = w.
Proof.
move=> Hs; rewrite /foata_nf.
set ps := foata_pairs crel [::] w.
have Hpe : perm_eq ps (sort dv_leq ps) by rewrite perm_sym perm_sort.
have Heq := sorted_eq dv_leq_trans dv_leq_anti Hs
               (sort_sorted dv_leq_total ps) Hpe.
rewrite -Heq; exact: foata_pairs_vals.
Qed.

(* --- Unsorted seq has adjacent descent --- *)

Lemma not_sorted_descent (s : seq (nat * nat)) :
  1 < size s -> ~~ sorted dv_leq s ->
  exists k : nat, k.+1 < size s /\
    ~~ dv_leq (nth (0, 0) s k) (nth (0, 0) s k.+1).
Proof.
elim: s => [|a [|b s'] IH] //= _.
rewrite negb_and => /orP [H|H].
  by exists 0; rewrite H.
have Hs : 1 < size (b :: s').
  by case: (s') H => //= c s'' _; rewrite ltnS.
have [k [Hk Hd]] := IH Hs H.
by exists k.+1.
Qed.

(* --- Word split at nat level --- *)

Lemma w_split_nat (k : nat) (w : seq nat) :
  k.+1 < size w ->
  w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
Proof.
move=> Hk.
have Hk' : k < size w := ltn_trans (ltnSn k) Hk.
rewrite -{1}[w](cat_take_drop k).
rewrite (drop_nth 0 Hk').
by rewrite (drop_nth 0 Hk).
Qed.

(* --- Foata inversion count --- *)

Definition foata_inv (crel : nat -> nat -> bool) (w : seq nat) : nat :=
  let ps := foata_pairs crel [::] w in
  \sum_(i < size w) \sum_(j < size w | i < j)
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).

Lemma foata_inv_zero (crel : nat -> nat -> bool) w :
  foata_inv crel w = 0 ->
  sorted dv_leq (foata_pairs crel [::] w).
Proof.
rewrite /foata_inv => Hzero.
apply/(sortedP (0,0)) => i; rewrite size_foata_pairs /= add0n => Hi.
apply/negPn/negP => Hneg.
suff : 0 < \sum_(i0 < size w) \sum_(j0 < size w | i0 < j0)
  (~~ dv_leq (nth (0, 0) (foata_pairs crel [::] w) i0)
             (nth (0, 0) (foata_pairs crel [::] w) j0)) by rewrite Hzero.
have Hi' : i < size w := ltn_trans (ltnSn i) Hi.
rewrite (bigD1 (Ordinal Hi')) //=.
apply: leq_trans; last exact: leq_addr.
rewrite (bigD1 (Ordinal Hi)) //=.
apply: leq_trans; last exact: leq_addr.
by rewrite Hneg.
Qed.

(* --- foata_pairs structure after swap --- *)

Lemma foata_pairs_swap_nth (crel : nat -> nat -> bool) w k :
  (forall a b, crel a b -> crel b a) ->
  k.+1 < size w ->
  crel (nth 0 w k) (nth 0 w k.+1) ->
  let sw := take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w in
  let ps := foata_pairs crel [::] w in
  let ps' := foata_pairs crel [::] sw in
  (forall i, i < size w ->
    nth (0, 0) ps' i =
    if i == k then nth (0, 0) ps k.+1
    else if i == k.+1 then nth (0, 0) ps k
    else nth (0, 0) ps i) /\
  size sw = size w.
Proof.
move=> Hcsym Hk Hc /=.
set sw := take k w ++ _ :: _ :: _.
set ps := foata_pairs crel [::] w.
set ps' := foata_pairs crel [::] sw.
have Hsz : size sw = size w.
  rewrite /sw size_cat /= size_drop (size_takel (ltnW (ltn_trans (ltnSn k) Hk))).
  by rewrite -addn2 addnCA addn2 subnK.
split => // i Hi.
have Hw : w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
  exact: w_split_nat.
set P := foata_pairs crel [::] (take k w).
set a := nth 0 w k.
set b := nth 0 w k.+1.
set suffix := drop k.+2 w.
have Hps : ps = foata_pairs crel P (a :: b :: suffix).
  by rewrite /ps Hw foata_pairs_split'.
have Hps' : ps' = foata_pairs crel P (b :: a :: suffix).
  by rewrite /ps' /sw foata_pairs_split'.
set da := foata_depth_at crel P a.
set db := foata_depth_at crel P b.
have Hdb' : foata_depth_at crel (rcons P (da, a)) b = db.
  by rewrite foata_depth_comm_rcons.
have Hda' : foata_depth_at crel (rcons P (db, b)) a = da.
  by rewrite foata_depth_comm_rcons // Hcsym.
set P_ab := rcons (rcons P (da, a)) (db, b).
set P_ba := rcons (rcons P (db, b)) (da, a).
have Hpab : perm_eq P_ab P_ba.
  rewrite /P_ab /P_ba; apply/seq.permP => p.
  rewrite -cats1 -[rcons P (da, a)]cats1 -cats1 -[rcons P (db, b)]cats1.
  by rewrite count_cat count_cat count_cat count_cat /= addn0 addn0 addnAC.
have HszP : size P = k.
  by rewrite size_foata_pairs /= add0n size_take (ltn_trans (ltnSn k) Hk).
have Hsuffix_eq : forall j, j < size suffix ->
  nth (0, 0) (foata_pairs crel P_ab suffix) (size P_ab + j) =
  nth (0, 0) (foata_pairs crel P_ba suffix) (size P_ba + j).
  elim: suffix P_ab P_ba Hpab {Hps Hps'} => [|x suf IH] Pab Pba Hpab j Hj //.
  case: j Hj => [|j] Hj /=.
    rewrite addn0 addn0.
    set dab := foata_depth_at crel Pab x.
    set dba := foata_depth_at crel Pba x.
    set Pab' := rcons Pab (dab, x).
    set Pba' := rcons Pba (dba, x).
    have Hlt_ab : size Pab < size Pab' by rewrite /Pab' size_rcons.
    have Hlt_ba : size Pba < size Pba' by rewrite /Pba' size_rcons.
    rewrite -(nth_take (0,0) Hlt_ab) (foata_pairs_prefix crel Pab' suf).
    rewrite -(nth_take (0,0) Hlt_ba) (foata_pairs_prefix crel Pba' suf).
    rewrite /Pab' /Pba' nth_rcons nth_rcons ltnn ltnn eqxx eqxx.
    by rewrite /dab /dba (foata_depth_at_perm _ _ Hpab).
  have Hpab' : perm_eq (rcons Pab (foata_depth_at crel Pab x, x))
                       (rcons Pba (foata_depth_at crel Pba x, x)).
    rewrite (foata_depth_at_perm _ _ Hpab) -cats1 -(cats1 Pba).
    exact: perm_cat Hpab _.
  have -> : size Pab + j.+1 =
    size (rcons Pab (foata_depth_at crel Pab x, x)) + j
    by rewrite size_rcons addSnnS.
  have -> : size Pba + j.+1 =
    size (rcons Pba (foata_depth_at crel Pba x, x)) + j
    by rewrite size_rcons addSnnS.
  exact: IH.
case: (ltnP i k) => Hik.
  have -> : (i == k) = false by apply/negbTE; rewrite ltn_eqF.
  have -> : (i == k.+1) = false by apply/negbTE; rewrite ltn_eqF // ltnS ltnW.
  have Hi_lt_P : i < size P by rewrite HszP.
  transitivity (nth (0, 0) P i); last first.
    have -> : nth (0,0) ps i = nth (0,0) (take (size P) ps) i by rewrite nth_take.
    by rewrite Hps (foata_pairs_prefix crel P (a :: b :: suffix)).
  have -> : nth (0,0) ps' i = nth (0,0) (take (size P) ps') i by rewrite nth_take.
  by rewrite Hps' (foata_pairs_prefix crel P (b :: a :: suffix)).
case Heqk : (i == k).
  rewrite (eqP Heqk).
  have HszPba : k < size P_ba by rewrite /P_ba !size_rcons HszP.
  have HszPab : k.+1 < size P_ab by rewrite /P_ab !size_rcons HszP.
  rewrite Hps' /= Hda'.
  rewrite -(nth_take (0,0) HszPba) (foata_pairs_prefix crel P_ba suffix).
  rewrite /P_ba !nth_rcons !size_rcons HszP ltnSn ltnn eqxx /=.
  rewrite Hps /= Hdb'.
  rewrite -(nth_take (0,0) HszPab) (foata_pairs_prefix crel P_ab suffix).
  by rewrite /P_ab !nth_rcons !size_rcons HszP ltnn eqxx.
have Hik' : k < i by rewrite ltn_neqAle eq_sym Heqk Hik.
case Heqk1 : (i == k.+1).
  rewrite (eqP Heqk1).
  have HszPba1 : k.+1 < size P_ba by rewrite /P_ba !size_rcons HszP.
  have HszPabk : k < size P_ab by rewrite /P_ab !size_rcons HszP.
  rewrite Hps' /= Hda'.
  rewrite -(nth_take (0,0) HszPba1) (foata_pairs_prefix crel P_ba suffix).
  rewrite /P_ba !nth_rcons !size_rcons HszP ltnn eqxx /=.
  rewrite Hps /= Hdb'.
  rewrite -(nth_take (0,0) HszPabk) (foata_pairs_prefix crel P_ab suffix).
  by rewrite /P_ab !nth_rcons !size_rcons HszP ltnSn ltnn eqxx.
have Hik1 : k.+1 < i by rewrite ltn_neqAle eq_sym Heqk1 Hik'.
have Hsuf_i : i - k.+2 < size suffix.
  by rewrite size_drop ltn_sub2rE.
have HszPab2 : size P_ab = k.+2 by rewrite /P_ab !size_rcons HszP.
have HszPba2 : size P_ba = k.+2 by rewrite /P_ba !size_rcons HszP.
have Hi_eq : i = size P_ab + (i - k.+2).
  by rewrite HszPab2 addnC subnK.
have Hi_ba : i = size P_ba + (i - k.+2).
  by rewrite HszPba2 addnC subnK.
have Hps_ab : ps = foata_pairs crel P_ab suffix.
  by rewrite Hps /= Hdb'.
have Hps'_ba : ps' = foata_pairs crel P_ba suffix.
  by rewrite Hps' /= Hda'.
have Hsuf_eq_i := Hsuffix_eq _ Hsuf_i.
have Hki : k.+2 <= i by [].
have Hki2 : k.+2 + (i - k.+2) = i by rewrite addnC subnK.
rewrite HszPab2 HszPba2 Hki2 in Hsuf_eq_i.
by rewrite Hps'_ba Hps_ab.
Qed.

(* --- Inversion count decreases under swap --- *)

Lemma foata_inv_swap_lt (crel : nat -> nat -> bool) w k :
  (forall a b, crel a b -> crel b a) ->
  k.+1 < size w ->
  crel (nth 0 w k) (nth 0 w k.+1) ->
  ~~ dv_leq (nth (0, 0) (foata_pairs crel [::] w) k)
             (nth (0, 0) (foata_pairs crel [::] w) k.+1) ->
  foata_inv crel (take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w) <
  foata_inv crel w.
Proof.
move=> Hcsym Hk Hc Hdesc.
set sw := take k w ++ _ :: _ :: _.
have [Hnth Hsz] := foata_pairs_swap_nth Hcsym Hk Hc.
set ps := foata_pairs crel [::] w.
set ps' := foata_pairs crel [::] sw.
rewrite /foata_inv Hsz.
have Hk' : k < size w := ltn_trans (ltnSn k) Hk.
have Hk1 : k.+1 < size w := Hk.
suff Hlt_sum : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps' i) (nth (0, 0) ps' j)) <
  \sum_(i < size w) \sum_(j < size w | i < j)
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).
  exact: Hlt_sum.
have Hnth_eq : forall i : 'I_(size w),
  nth (0, 0) ps' i =
  nth (0, 0) ps (if val i == k then k.+1 else if val i == k.+1 then k else val i).
  move=> [i Hi] /=; rewrite Hnth //.
  case: (i == k) => //; case: (i == k.+1) => //.
set tp := fun i : nat => if i == k then k.+1 else if i == k.+1 then k else i.
have Htp_inv : forall i, tp (tp i) = i.
  move=> i; rewrite /tp.
  case Hi : (i == k).
    by rewrite (eqP Hi) gtn_eqF // eqxx.
  case Hi1 : (i == k.+1).
    by rewrite (eqP Hi1) eqxx.
  by rewrite Hi Hi1.
have Htp_inj : injective tp.
  by move=> i j Hij; rewrite -(Htp_inv i) -(Htp_inv j) Hij.
have Heq_tp : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps' i) (nth (0, 0) ps' j)) =
  \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps (tp i)) (nth (0, 0) ps (tp j))).
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite !Hnth_eq.
rewrite Heq_tp.
have Hfix : dv_leq (nth (0, 0) ps k.+1) (nth (0, 0) ps k).
  by move: (dv_leq_total (nth (0, 0) ps k) (nth (0, 0) ps k.+1));
     rewrite (negbTE Hdesc).
set ik : 'I_(size w) := Ordinal Hk'.
set ik1 : 'I_(size w) := Ordinal Hk.
have Hik_ne : ik != ik1.
  by apply/eqP => /(congr1 val) /= /n_Sn.
have Htp_bnd : forall i, i < size w -> tp i < size w.
  move=> i Hi; rewrite /tp.
  case: (i == k) => //; case: (i == k.+1) => //.
set tp_ord := fun i : 'I_(size w) => Ordinal (Htp_bnd _ (ltn_ord i)) : 'I_(size w).
have Htp_ord_val : forall i : 'I_(size w), val (tp_ord i) = tp (val i).
  by move=> [i Hi].
have Htp_ord_inv : forall i, tp_ord (tp_ord i) = i.
  move=> i; apply: ord_inj; rewrite !Htp_ord_val; exact: Htp_inv.
have Htp_ord_inj : injective tp_ord.
  by move=> i j Hij; rewrite -(Htp_ord_inv i) -(Htp_ord_inv j) Hij.
have Htp_ik : tp_ord ik = ik1.
  by apply: ord_inj; rewrite Htp_ord_val /tp /= eqxx.
have Htp_ik1 : tp_ord ik1 = ik.
  by apply: ord_inj; rewrite Htp_ord_val /tp /= gtn_eqF // eqxx.
have Hreindex : \sum_(i < size w) \sum_(j < size w | i < j)
  (~~ dv_leq (nth (0, 0) ps (tp i)) (nth (0, 0) ps (tp j))) =
  \sum_(i < size w) \sum_(j < size w | tp (val i) < tp (val j))
    (~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j)).
  have Htp_tp_ord : forall i : 'I_(size w),
    tp (val (tp_ord i)) = val i.
    by move=> i0; rewrite Htp_ord_val Htp_inv.
  rewrite (reindex_inj Htp_ord_inj).
  apply: eq_bigr => i _.
  rewrite (reindex_inj Htp_ord_inj).
  apply: eq_bigr => j _.
  congr (~~ dv_leq (nth _ ps _) (nth _ ps _)); exact: Htp_tp_ord.
rewrite Hreindex.
have tpk : tp k = k.+1 by rewrite /tp eqxx.
have tpk1 : tp k.+1 = k by rewrite /tp (gtn_eqF (ltnSn k)) eqxx.
have tp_oth : forall m, m != k -> m != k.+1 -> tp m = m.
  by move=> m /negbTE Hm /negbTE Hm1; rewrite /tp Hm Hm1.
have tp_swap_only : forall i j : nat,
    tp i < tp j -> ~~ (i < j) -> i = k.+1 /\ j = k.
  move=> i0 j0 Htp0 Horig0.
  have [Hik0|Hik0] := boolP (i0 == k); have [Hjk0|Hjk0] := boolP (j0 == k).
  - by move: Htp0; rewrite (eqP Hik0) (eqP Hjk0) tpk ltnn.
  - have [Hjk1|Hjk1] := boolP (j0 == k.+1).
    + by move: Htp0; rewrite (eqP Hik0) (eqP Hjk1) tpk tpk1 ltnNge leqnSn.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hik0).
      move: Htp0; rewrite (eqP Hik0) tpk (@tp_oth j0 Hjk0 Hjk1) => Hlt0.
      exact: ltn_trans (ltnSn k) Hlt0.
  - have [Hik10|Hik10] := boolP (i0 == k.+1).
    + by rewrite (eqP Hik10) (eqP Hjk0).
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hjk0).
      move: Htp0; rewrite (eqP Hjk0) tpk (@tp_oth i0 Hik0 Hik10) => Hlt0.
      by rewrite ltn_neqAle Hik0 -ltnS.
  - have [Hik10|Hik10] := boolP (i0 == k.+1); have [Hjk1|Hjk1] := boolP (j0 == k.+1).
    + by move: Htp0; rewrite (eqP Hik10) (eqP Hjk1) tpk1 ltnn.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hik10).
      move: Htp0; rewrite (eqP Hik10) tpk1 (@tp_oth j0 Hjk0 Hjk1) => Hlt0.
      rewrite ltn_neqAle eq_sym Hjk1 /=.
      exact: Hlt0.
    + exfalso; move/negP: Horig0; apply.
      rewrite (eqP Hjk1).
      move: Htp0; rewrite (eqP Hjk1) tpk1 (@tp_oth i0 Hik0 Hik10) => Hlt0.
      exact: ltn_trans Hlt0 (ltnSn k).
    + exfalso; move/negP: Horig0; apply.
      by move: Htp0; rewrite (@tp_oth i0 Hik0 Hik10) (@tp_oth j0 Hjk0 Hjk1).
have Hpw : forall i j : 'I_(size w),
  (if tp (val i) < tp (val j)
   then ~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j) : nat else 0) <=
  (if val i < val j
   then ~~ dv_leq (nth (0, 0) ps i) (nth (0, 0) ps j) : nat else 0).
  move=> i0 j0.
  case Horig0 : (val i0 < val j0) => /=.
    by case : (tp (val i0) < tp (val j0)).
  have [Htp0|Htp0] := boolP (tp (val i0) < tp (val j0)) => //.
  have [Hi0 Hj0] := @tp_swap_only (val i0) (val j0) Htp0 (negbT Horig0).
  have -> : i0 = ik1 by apply: ord_inj.
  have -> : j0 = ik by apply: ord_inj.
  by rewrite /= Hfix.
have Hstrict : (if tp (val ik) < tp (val ik1)
    then ~~ dv_leq (nth (0, 0) ps ik) (nth (0, 0) ps ik1) : nat else 0) <
  (if val ik < val ik1
    then ~~ dv_leq (nth (0, 0) ps ik) (nth (0, 0) ps ik1) : nat else 0).
  rewrite /= tpk tpk1 ltnSn (negbTE Hdesc) /=.
  by have -> : k.+1 < k = false by rewrite ltnNge leqnSn.
have ltn_sum_aux : forall (I : finType) (f0 g0 : I -> nat) (i0 : I),
    (forall i, f0 i <= g0 i) -> f0 i0 < g0 i0 ->
    \sum_i f0 i < \sum_i g0 i.
  move=> I f0 g0 i0 Hle Hlt.
  rewrite (bigD1 i0) // [X in _ < X](bigD1 i0) //.
  have Hle_rest : \sum_(i | i != i0) f0 i <= \sum_(i | i != i0) g0 i.
    by apply: leq_sum => i _; exact: Hle.
  apply: (@leq_ltn_trans (f0 i0 + \sum_(i | i != i0) g0 i)).
    by rewrite leq_add2l.
  by rewrite ltn_add2r.
rewrite [X in X < _]big_mkcond [X in _ < X]big_mkcond.
apply: (@ltn_sum_aux _ _ _ ik).
  move=> i0.
  rewrite [X in X <= _]big_mkcond [X in _ <= X]big_mkcond.
  exact: leq_sum (fun j0 _ => Hpw i0 j0).
rewrite [X in X < _]big_mkcond [X in _ < X]big_mkcond.
apply: (@ltn_sum_aux _ _ _ ik1).
  move=> j0.
  exact: Hpw ik j0.
exact: Hstrict.
Qed.

(* --- Soundness: foata_nf(w) reachable via adjacent commuting swaps --- *)

Lemma foata_nf_sound (crel : nat -> nat -> bool) w :
  (forall a b, crel a b -> crel b a) ->
  exists ws : seq (seq nat),
    last w ws = foata_nf crel w /\
    forall i, i < size ws ->
      let w0 := nth [::] (w :: ws) i in
      let w1 := nth [::] (w :: ws) i.+1 in
      exists k, k.+1 < size w0 /\
        crel (nth 0 w0 k) (nth 0 w0 k.+1) /\
        crel (nth 0 w0 k.+1) (nth 0 w0 k) /\
        w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0.
Proof.
move=> Hcsym.
move: w.
apply: (well_founded_induction_type
  (Wf_nat.well_founded_ltof _ (foata_inv crel))).
move=> w IH.
case Hs : (sorted dv_leq (foata_pairs crel [::] w)).
  exists [::]; split; first by rewrite /= foata_nf_sorted.
  by move=> i.
have Hsz : 1 < size w.
  case Hw : (size w) => [|[|n]] //.
  1,2: exfalso; move/negP: Hs; apply;
       by case: w Hw IH => [|a [|b w']] //=.
have Hszfp : 1 < size (foata_pairs crel [::] w)
  by rewrite size_foata_pairs /= add0n.
have [k0 [Hk0 Hk0d]] := not_sorted_descent Hszfp (negbT Hs).
rewrite size_foata_pairs /= add0n in Hk0.
have Hcomm : crel (nth 0 w k0) (nth 0 w k0.+1).
  exact: foata_descent_comm Hk0 Hk0d.
set sw := take k0 w ++ nth 0 w k0.+1 :: nth 0 w k0 :: drop k0.+2 w.
have Hnf : foata_nf crel sw = foata_nf crel w.
  rewrite /sw.
  transitivity (foata_nf crel (take k0 w ++ nth 0 w k0 :: nth 0 w k0.+1 :: drop k0.+2 w)).
    apply foata_nf_swap_adj; [exact: Hcsym | exact: Hcomm].
  congr (foata_nf crel). symmetry; exact: w_split_nat.
have Hlt : @Wf_nat.ltof _ (foata_inv crel) sw w.
  rewrite /Wf_nat.ltof /sw; apply/ltP.
  exact: foata_inv_swap_lt Hcsym Hk0 Hcomm Hk0d.
have [ws [Hlast Hsteps]] := IH sw Hlt.
exists (sw :: ws); split.
  by rewrite /= Hlast Hnf.
case => [|i] Hi /=.
  exists k0; repeat split => //; exact: Hcsym.
exact: Hsteps.
Qed.

End foata_infrastructure.

(* ========================================================================== *)
(* New NF properties                                                          *)
(* ========================================================================== *)

Section foata_nf_properties.

(* --- size_foata_nf --- *)

Lemma size_foata_nf (crel : nat -> nat -> bool) w :
  size (foata_nf crel w) = size w.
Proof.
rewrite /foata_nf size_map size_sort size_foata_pairs /=.
by rewrite add0n.
Qed.

(* --- foata_nf_perm_eq --- *)

Lemma foata_nf_perm_eq (crel : nat -> nat -> bool) w :
  perm_eq (foata_nf crel w) w.
Proof.
rewrite /foata_nf.
have Hvals : [seq p.2 | p <- foata_pairs crel [::] w] = w.
  by rewrite foata_pairs_vals.
have Hpe : perm_eq [seq p.2 | p <- sort dv_leq (foata_pairs crel [::] w)]
                    [seq p.2 | p <- foata_pairs crel [::] w].
  apply: perm_map.
  by rewrite perm_sort.
by rewrite Hvals in Hpe.
Qed.

(* --- swap chain preserves size --- *)

Lemma swap_chain_size (crel : nat -> nat -> bool) w ws :
  (forall i, i < size ws ->
    let w0 := nth [::] (w :: ws) i in
    let w1 := nth [::] (w :: ws) i.+1 in
    exists k, k.+1 < size w0 /\
      crel (nth 0 w0 k) (nth 0 w0 k.+1) /\
      crel (nth 0 w0 k.+1) (nth 0 w0 k) /\
      w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0) ->
  forall i, i <= size ws -> size (nth [::] (w :: ws) i) = size w.
Proof.
move=> Hsteps i; elim: i => [|i IH] Hi //=.
have Hi' : i < size ws by [].
have Hisz := IH (ltnW Hi').
have /= [k [Hk [_ [_ Heq]]]] := Hsteps i Hi'.
rewrite Heq size_cat /= size_drop.
have Hksz : k < size (nth [::] (w :: ws) i) := ltn_trans (ltnSn k) Hk.
by rewrite (size_takel (ltnW Hksz)) -addn2 addnCA addn2 subnK.
Qed.

(* --- swap chain preserves foata_nf --- *)

Lemma swap_chain_nf (crel : nat -> nat -> bool) w ws :
  (forall a b, crel a b -> crel b a) ->
  (forall i, i < size ws ->
    let w0 := nth [::] (w :: ws) i in
    let w1 := nth [::] (w :: ws) i.+1 in
    exists k, k.+1 < size w0 /\
      crel (nth 0 w0 k) (nth 0 w0 k.+1) /\
      crel (nth 0 w0 k.+1) (nth 0 w0 k) /\
      w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0) ->
  forall i, i <= size ws ->
    foata_nf crel (nth [::] (w :: ws) i) = foata_nf crel w.
Proof.
move=> Hcsym Hsteps i; elim: i => [|i IH] Hi //=.
have Hi' : i < size ws by [].
have /= [k [Hk [Hc1 [Hc2 Heq]]]] := Hsteps i Hi'.
set w0 := nth [::] (w :: ws) i in Hk Hc1 Hc2 Heq *.
set a := nth 0 w0 k in Hc1 Hc2 Heq *.
set b := nth 0 w0 k.+1 in Hc1 Hc2 Heq *.
rewrite Heq (@foata_nf_swap_adj _ b a _ _ Hc2 Hc1).
have Hw0 := @w_split_nat k w0 Hk; rewrite -{}Hw0.
exact: IH (ltnW Hi').
Qed.

(* --- foata_nf_idempotent --- *)

Lemma foata_nf_idempotent (crel : nat -> nat -> bool) w :
  (forall a b, crel a b -> crel b a) ->
  foata_nf crel (foata_nf crel w) = foata_nf crel w.
Proof.
move=> Hcsym.
(* foata_nf_sound gives swap chain w → foata_nf w *)
have [ws [Hlast Hsteps]] := foata_nf_sound w Hcsym.
(* All words in the chain have the same NF *)
have Hnf_eq : foata_nf crel (last w ws) = foata_nf crel w.
  have := swap_chain_nf Hcsym Hsteps (leqnn (size ws)).
  by rewrite nth_last /= Hlast.
(* foata_nf(foata_nf(w)) = foata_nf(last w ws) = foata_nf(w) *)
by rewrite -Hlast Hnf_eq.
Qed.

(* --- foata_nf_prepend_compat --- *)

(* Helper: a single swap at position k in w becomes a swap at position
   |u| + k in u ++ w *)
Lemma foata_nf_prepend_swap (crel : nat -> nat -> bool) u w k :
  (forall a b, crel a b -> crel b a) ->
  k.+1 < size w ->
  crel (nth 0 w k) (nth 0 w k.+1) ->
  crel (nth 0 w k.+1) (nth 0 w k) ->
  let sw := take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w in
  foata_nf crel (u ++ sw) = foata_nf crel (u ++ w).
Proof.
move=> Hcsym Hk Hc1 Hc2 /=.
set sw := take k w ++ _ :: _ :: _.
have Hw : w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
  exact: w_split_nat.
set u' := u ++ take k w.
have -> : u ++ sw = u' ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w.
  by rewrite /u' /sw catA.
have -> : u ++ w = u' ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
  by rewrite /u' {1}Hw catA.
exact: foata_nf_swap_adj.
Qed.

Lemma foata_nf_prepend_compat (crel : nat -> nat -> bool) u w1 w2 :
  (forall a b, crel a b -> crel b a) ->
  foata_nf crel w1 = foata_nf crel w2 ->
  foata_nf crel (u ++ w1) = foata_nf crel (u ++ w2).
Proof.
move=> Hcsym Hnf12.
(* Get swap chain from w1 to foata_nf(w1) *)
have [ws1 [Hlast1 Hsteps1]] := foata_nf_sound w1 Hcsym.
(* Get swap chain from w2 to foata_nf(w2) *)
have [ws2 [Hlast2 Hsteps2]] := foata_nf_sound w2 Hcsym.
(* Apply each swap from w1-chain to u ++ w1 *)
(* Each swap at position k in w_i becomes swap at position |u|+k in u++w_i *)
(* So foata_nf(u ++ w1) = foata_nf(u ++ last w1 ws1) = foata_nf(u ++ foata_nf(w1)) *)
suff Hchain : forall v ws,
  (forall i, i < size ws ->
    let w0 := nth [::] (v :: ws) i in
    let w1 := nth [::] (v :: ws) i.+1 in
    exists k, k.+1 < size w0 /\
      crel (nth 0 w0 k) (nth 0 w0 k.+1) /\
      crel (nth 0 w0 k.+1) (nth 0 w0 k) /\
      w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0) ->
  foata_nf crel (u ++ last v ws) = foata_nf crel (u ++ v).
  by rewrite -(Hchain _ _ Hsteps1) -(Hchain _ _ Hsteps2) Hlast1 Hlast2 Hnf12.
move=> v ws Hsteps.
elim: ws v Hsteps => [|w' ws' IH] v Hsteps //=.
have [k [Hk [Hc1 [Hc2 Heq]]]] := Hsteps 0 (ltn0Sn _).
rewrite /= in Heq.
have Hsteps' : forall i, i < size ws' ->
  let w0 := nth [::] (w' :: ws') i in
  let w1' := nth [::] (w' :: ws') i.+1 in
  exists k0, k0.+1 < size w0 /\
    crel (nth 0 w0 k0) (nth 0 w0 k0.+1) /\
    crel (nth 0 w0 k0.+1) (nth 0 w0 k0) /\
    w1' = take k0 w0 ++ nth 0 w0 k0.+1 :: nth 0 w0 k0 :: drop k0.+2 w0.
  by move=> i Hi; exact: (Hsteps i.+1 Hi).
rewrite (IH w' Hsteps') Heq.
exact: foata_nf_prepend_swap.
Qed.

End foata_nf_properties.

(* ========================================================================== *)
(* Phase A: Foata first-layer infrastructure                                  *)
(* ========================================================================== *)

Section cartier_foata.

Variable Tg : nat.
Variable comm : nat -> nat -> bool.

(* Hypothesis: comm is symmetric and irreflexive on {0,...,Tg-1} *)
Hypothesis comm_sym : forall a b, a < Tg -> b < Tg -> comm a b -> comm b a.
Hypothesis comm_irrefl : forall a, ~~ comm a a.

(* --- First layer: depth-0 elements of Foata pairs --- *)

Definition foata_first_layer_pairs (w : seq nat) : seq (nat * nat) :=
  [seq dv <- foata_pairs comm [::] w | dv.1 == 0].

Definition foata_first_layer (w : seq nat) : seq nat :=
  [seq dv.2 | dv <- foata_first_layer_pairs w].

Definition foata_rest_pairs (w : seq nat) : seq (nat * nat) :=
  [seq dv <- foata_pairs comm [::] w | dv.1 != 0].

Definition foata_rest (w : seq nat) : seq nat :=
  [seq dv.2 | dv <- foata_rest_pairs w].

(* --- Size lemmas --- *)

Lemma size_foata_pairs_nil w :
  size (foata_pairs comm [::] w) = size w.
Proof. by rewrite size_foata_pairs /= add0n. Qed.

Lemma foata_first_layer_rest_size w :
  size (foata_first_layer_pairs w) + size (foata_rest_pairs w) = size w.
Proof.
rewrite /foata_first_layer_pairs /foata_rest_pairs.
rewrite -size_foata_pairs_nil.
rewrite -(count_predC (fun dv : nat * nat => dv.1 == 0) (foata_pairs comm [::] w)).
by rewrite !size_filter; congr (_ + _); apply: eq_count => dv /=;
  rewrite ?negbK.
Qed.

Lemma foata_pairs_vals_nil w :
  [seq dv.2 | dv <- foata_pairs comm [::] w] = w.
Proof. by rewrite foata_pairs_vals /=. Qed.

End cartier_foata.

(* ========================================================================== *)
(* Phase B: Krattenthaler/Viennot Sign-Reversing Involution (SRI)             *)
(* ========================================================================== *)

Section sri_krattenthaler.

Variable Tg : nat.
Variable comm : nat -> nat -> bool.
Hypothesis comm_sym : forall a b, comm a b -> comm b a.
Hypothesis comm_irrefl : forall a, ~~ comm a a.

(* Remove the first occurrence of b from a list *)
Fixpoint rem_first_occ (b : nat) (s : seq nat) : seq nat :=
  match s with
  | [::] => [::]
  | x :: s' => if x == b then s' else x :: rem_first_occ b s'
  end.

(* Insert b into a sorted list, maintaining sorted order *)
Fixpoint insort (b : nat) (s : seq nat) : seq nat :=
  match s with
  | [::] => [:: b]
  | x :: s' => if b <= x then b :: x :: s' else x :: insort b s'
  end.

Lemma perm_rem_first_occ b s :
  b \in s -> perm_eq s (b :: rem_first_occ b s).
Proof.
elim: s => [|x s IH] //=.
rewrite inE => /orP [/eqP -> | Hb].
  by rewrite eqxx.
case: ifP => [/eqP -> | Hneq].
  by rewrite perm_cons.
apply: (perm_trans (y := x :: b :: rem_first_occ b s)).
  by rewrite perm_cons IH.
by rewrite -(cat1s x) -(cat1s b) -(cat1s x (rem_first_occ _ _))
           perm_catCA /= perm_refl.
Qed.

Lemma size_rem_first_occ b s :
  b \in s -> size (rem_first_occ b s) = (size s).-1.
Proof.
elim: s => [|x s IH] //=.
case Hxb: (x == b) => /=; first by move=> _.
rewrite inE eq_sym Hxb /= => Hb.
rewrite IH //.
by case: (s) Hb.
Qed.

Lemma mem_rem_first_occ b s x :
  x \in rem_first_occ b s -> x \in s.
Proof.
elim: s => [|y s IH] //=.
case: ifP => [/eqP -> Hx | _].
  by rewrite inE Hx orbT.
rewrite inE => /orP [Hxy | /IH Hx].
  by rewrite inE Hxy.
by rewrite inE Hx orbT.
Qed.

Lemma perm_insort b s : perm_eq (insort b s) (b :: s).
Proof.
elim: s => [|x s IH] //=.
case: ifP => [_ | _] //.
apply: (perm_trans (y := x :: b :: s)).
  by rewrite perm_cons.
by rewrite -(cat1s x) -(cat1s b) -(cat1s x s) perm_catCA.
Qed.

Lemma size_insort b s : size (insort b s) = (size s).+1.
Proof.
by have /= := perm_size (perm_insort b s).
Qed.

Lemma mem_insort b s x : x \in insort b s = (x == b) || (x \in s).
Proof.
by have := perm_mem (perm_insort b s) x; rewrite inE.
Qed.

Lemma path_insort a b s :
  path ltn a s -> a < b -> b \notin s -> path ltn a (insort b s).
Proof.
elim: s a => [|x s' IH] a /=.
  by move=> _ -> _.
move=> /andP [Hax Hpath] Hab.
rewrite inE negb_or => /andP [Hbx Hnotin].
case Hle : (b <= x) => /=.
  by rewrite Hab /= ltn_neqAle (negbTE Hbx) Hle /= Hpath.
have Hxb : x < b by rewrite ltnNge Hle.
by rewrite Hax /= IH.
Qed.

Lemma sorted_insort b s :
  sorted ltn s -> b \notin s -> sorted ltn (insort b s).
Proof.
case: s => [|x s'] //= Hpath Hnotin.
rewrite inE negb_or in Hnotin; case/andP: Hnotin => Hbx Hnotin.
case Hle : (b <= x) => /=.
  by rewrite /sorted /= ltn_neqAle (negbTE Hbx) Hle /= Hpath.
have Hxb : x < b by rewrite ltnNge Hle.
exact: path_insort Hpath Hxb Hnotin.
Qed.

(* --- The Krattenthaler/Viennot SRI --- *)

Definition composed_nf (S nf : seq nat) : seq nat :=
  foata_nf comm (S ++ nf).

Definition sri_pivot (S nf : seq nat) : nat :=
  head 0 (composed_nf S nf).

Definition sri_map (S nf : seq nat) : seq nat * seq nat :=
  let b := sri_pivot S nf in
  if b \in S then
    (rem_first_occ b S, foata_nf comm (b :: nf))
  else
    (insort b S, foata_nf comm (rem_first_occ b nf)).

(* --- Pivot membership --- *)

Lemma sri_pivot_mem S nf :
  0 < size S + size nf ->
  sri_pivot S nf \in S ++ nf.
Proof.
move=> Hpos.
rewrite /sri_pivot /composed_nf.
have Hpe := foata_nf_perm_eq comm (S ++ nf).
have Hpos' : 0 < size (foata_nf comm (S ++ nf)).
  by rewrite size_foata_nf size_cat.
case Hcnf : (foata_nf comm (S ++ nf)) Hpos' => [|b cnf'] // _ /=.
have Hb : b \in foata_nf comm (S ++ nf) by rewrite Hcnf inE eqxx.
by rewrite (perm_mem Hpe) in Hb.
Qed.

Lemma sri_pivot_in_nf S nf :
  0 < size S + size nf ->
  sri_pivot S nf \notin S ->
  sri_pivot S nf \in nf.
Proof.
move=> Hpos HnS; have := sri_pivot_mem Hpos.
by rewrite mem_cat => /orP [|//]; rewrite (negbTE HnS).
Qed.

(* --- Total size preservation --- *)

Lemma sri_map_total_size S nf :
  0 < size S + size nf ->
  let '(S', nf') := sri_map S nf in
  size S' + size nf' = size S + size nf.
Proof.
move=> Hpos; rewrite /sri_map.
case HbS : (sri_pivot S nf \in S).
- rewrite size_rem_first_occ // size_foata_nf /=.
  have Hgt : 0 < size S by move: HbS; case: (S) => //=; rewrite in_nil.
  by rewrite -addSnnS prednK.
- have HbS' : sri_pivot S nf \notin S by move: HbS; case: (_ \in S).
  have Hb : sri_pivot S nf \in nf := sri_pivot_in_nf Hpos HbS'.
  rewrite size_insort size_foata_nf size_rem_first_occ //.
  have Hgt : 0 < size nf by move: Hb; case: (nf) => //=; rewrite in_nil.
  by rewrite addSnnS prednK.
Qed.

(* --- Sign-reversing property --- *)

Lemma sri_map_sign S nf :
  0 < size S + size nf ->
  let '(S', nf') := sri_map S nf in
  (size S' == (size S).+1) || (size S' == (size S).-1).
Proof.
move=> Hpos; rewrite /sri_map.
case HbS : (sri_pivot S nf \in S).
- by rewrite size_rem_first_occ // eqxx orbT.
- by rewrite size_insort eqxx.
Qed.

(* --- Helper: bubble element to front via commuting swaps --- *)

Lemma foata_nf_bubble_front (prefix : seq nat) (a : nat) (rest : seq nat) :
  (forall x, x \in prefix -> x != a -> comm x a) ->
  foata_nf comm (prefix ++ a :: rest) =
  foata_nf comm (a :: prefix ++ rest).
Proof.
elim: prefix => [|x prefix IH] //= Hcomm1.
have Hcomm1' : forall y, y \in prefix -> y != a -> comm y a.
  by move=> y Hy; apply: Hcomm1; rewrite inE Hy orbT.
have -> : x :: prefix ++ a :: rest = [:: x] ++ (prefix ++ a :: rest) by [].
rewrite (@foata_nf_prepend_compat comm [:: x] _ _ comm_sym (IH Hcomm1')).
have -> : [:: x] ++ (a :: prefix ++ rest) = [::] ++ x :: a :: (prefix ++ rest) by [].
have -> : a :: x :: prefix ++ rest = [::] ++ a :: x :: (prefix ++ rest) by [].
case Hxa_eq : (x == a).
  by rewrite (eqP Hxa_eq).
have Hxa' : comm x a := Hcomm1 x (mem_head x prefix) (negbT Hxa_eq).
exact: (foata_nf_swap_adj [::] (prefix ++ rest) Hxa' (comm_sym Hxa')).
Qed.

(* --- Clique NF permutation lemma --- *)
(* When all elements of a prefix commute pairwise, any permutation of
   that prefix produces the same foata_nf. *)

Lemma foata_nf_clique_perm (w1 w2 suffix : seq nat) :
  perm_eq w1 w2 ->
  (forall a b, a \in w1 -> b \in w1 -> a != b -> comm a b) ->
  foata_nf comm (w1 ++ suffix) = foata_nf comm (w2 ++ suffix).
Proof.
elim: w1 w2 => [|a w1 IH] w2 Hperm Hclique.
  have -> : w2 = [::] by apply/eqP; rewrite -size_eq0 -(perm_size Hperm).
  by [].
have Ha2 : a \in w2 by rewrite -(perm_mem Hperm) inE eqxx.
set k := index a w2.
have Hk : k < size w2 by rewrite /k index_mem.
set prefix := take k w2.
set rest := drop k.+1 w2.
have Hnth : nth 0 w2 k = a by rewrite /k nth_index.
have Hw2 : w2 = prefix ++ a :: rest.
  by rewrite /prefix /rest -Hnth -drop_nth // cat_take_drop.
have Hperm2 : perm_eq (a :: w1) (prefix ++ a :: rest) by rewrite -Hw2.
have Hclique2 : forall x y, x \in w2 -> y \in w2 -> x != y -> comm x y.
  move=> x y Hx Hy Hne; apply: Hclique => //.
  - by rewrite (perm_mem Hperm).
  - by rewrite (perm_mem Hperm).
have Hclique' : forall x, x \in prefix -> x != a -> comm x a.
  move=> x Hx Hne.
  by apply: Hclique2; rewrite ?Hw2 ?mem_cat ?inE ?eqxx ?Hx ?orbT.
rewrite Hw2 -catA.
rewrite (@foata_nf_bubble_front prefix a (rest ++ suffix) Hclique').
symmetry.
have -> : a :: prefix ++ (rest ++ suffix) = [:: a] ++ ((prefix ++ rest) ++ suffix).
  by rewrite /= catA.
symmetry.
have -> : (a :: w1) ++ suffix = [:: a] ++ (w1 ++ suffix) by [].
apply: (@foata_nf_prepend_compat comm [:: a] _ _ comm_sym).
apply: IH.
- have : perm_eq (a :: w1) (a :: prefix ++ rest).
    rewrite (perm_trans Hperm2) //.
    by rewrite perm_sym -cat1s perm_catCA cat1s.
  by rewrite perm_cons.
- move=> x y Hx Hy Hne.
  apply: Hclique => //; by rewrite in_cons ?Hx ?Hy orbT.
Qed.

(* --- Sorted head is minimum --- *)

Lemma sorted_head_leq (s : seq (nat * nat)) (dv : nat * nat) :
  sorted dv_leq s -> dv \in s -> dv_leq (head (0,0) s) dv.
Proof.
case: s => [|h t] //= Hsorted Hdv.
have Hmin := order_path_min dv_leq_trans Hsorted.
rewrite inE in Hdv; case/orP: Hdv => [/eqP -> | Hdv].
- by case/orP: (dv_leq_total h h).
- by have /allP := Hmin; apply.
Qed.

(* --- Depth bound from non-commuting predecessor --- *)

Lemma depth_noncomm_ge (w : seq nat) (j k : nat) :
  j < k -> k < size w ->
  ~~ comm (nth 0 w j) (nth 0 w k) ->
  (nth (0,0) (foata_pairs comm [::] w) j).1.+1 <=
  (nth (0,0) (foata_pairs comm [::] w) k).1.
Proof.
move=> Hjk Hk Hnc.
have Hj : j < size w := ltn_trans Hjk Hk.
(* The depth at position k equals foata_depth_at on the prefix *)
rewrite -{1}(add0n k) (nth_foata_pairs_depth comm [::] Hk).
(* Now goal: (nth (0,0) (foata_pairs comm [::] w) j).1.+1 <=
             foata_depth_at comm (foata_pairs comm [::] (take k w)) (nth 0 w k) *)
(* The pair at position j in the full word equals the pair at position j in take k w
   (since j < k, and foata_pairs only depends on the prefix) *)
(* We show that nth (0,0) (foata_pairs comm [::] w) j \in foata_pairs comm [::] (take k w) *)
set prev_k := foata_pairs comm [::] (take k w).
set pair_j := nth (0,0) (foata_pairs comm [::] w) j.
apply: (@foata_depth_noncomm_lb comm prev_k pair_j.1 pair_j.2 (nth 0 w k)).
- (* ~~ comm pair_j.2 (nth 0 w k) *)
  rewrite /pair_j -{1}(add0n j) (nth_foata_pairs_val comm [::] Hj).
  exact: Hnc.
- (* (pair_j.1, pair_j.2) \in prev_k *)
  rewrite -surjective_pairing /pair_j /prev_k.
  have Hjsz : j < size (foata_pairs comm [::] (take k w)).
    by rewrite size_foata_pairs /= add0n size_take Hk.
  (* foata_pairs comm [::] (take k w) is a prefix of foata_pairs comm [::] w *)
  (* The full pairs = prefix_pairs ++ suffix_pairs *)
  set pk := foata_pairs comm [::] (take k w).
  have Hcat : foata_pairs comm [::] w = foata_pairs comm pk (drop k w).
    by rewrite /pk -{1}(cat_take_drop k w) foata_pairs_split'.
  have Hprefix : take (size pk) (foata_pairs comm pk (drop k w)) = pk.
    exact: foata_pairs_prefix.
  have Hjsz' : j < size (take (size pk) (foata_pairs comm pk (drop k w))).
    have Hle : size pk <= size (foata_pairs comm pk (drop k w)).
      by rewrite size_foata_pairs; apply: leq_addr.
    by rewrite (size_takel Hle).
  have Hnth_pk : nth (0,0) (foata_pairs comm [::] w) j = nth (0,0) pk j.
    rewrite Hcat -(cat_take_drop (size pk) (foata_pairs comm pk (drop k w))).
    by rewrite nth_cat Hjsz' Hprefix.
  rewrite Hnth_pk. exact: mem_nth.
Qed.

(* --- Pivot commutes with all predecessors in the original word --- *)

Lemma pivot_comm_predecessor (w : seq nat) (j : nat) :
  0 < size w ->
  let b := head 0 (foata_nf comm w) in
  let ps := foata_pairs comm [::] w in
  let sorted_ps := sort dv_leq ps in
  let b_pair := head (0,0) sorted_ps in
  (* b_pair is in ps at some position pos *)
  let pos := index b_pair ps in
  j < pos ->
  comm b (nth 0 w j).
Proof.
move=> Hpos /=.
set b := head 0 (foata_nf comm w).
set ps := foata_pairs comm [::] w.
set sorted_ps := sort dv_leq ps.
set b_pair := head (0,0) sorted_ps.
set pos := index b_pair ps.
move=> Hjp.
apply/negPn/negP => Hnc.
have Hnc' : ~~ comm (nth 0 w j) b.
  by apply/negP => Hc; move/negP: Hnc; apply; exact: comm_sym.
have Hpos_sp : 0 < size sorted_ps.
  by rewrite /sorted_ps (perm_size (permEl (perm_sort dv_leq ps))) /ps size_foata_pairs /= add0n.
have Hb_eq : b = (head (0,0) sorted_ps).2.
  rewrite /b /foata_nf /sorted_ps /ps.
  by case: (sort dv_leq (foata_pairs comm [::] w)) Hpos_sp => [|[d v] t] //=.
have Hbp_in : b_pair \in ps.
  rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps))).
  have := Hpos_sp; rewrite /sorted_ps.
  by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
have Hpos_lt : pos < size ps by rewrite /pos index_mem.
have Hnth_pos : nth (0,0) ps pos = b_pair by rewrite /pos nth_index.
have Hpos_w : pos < size w.
  by move: Hpos_lt; rewrite /ps size_foata_pairs /= add0n.
have Hj : j < size w := ltn_trans Hjp Hpos_w.
(* Depth bound *)
have Hnth_b : nth 0 w pos = b.
  have Hval := nth_foata_pairs_val comm [::] Hpos_w.
  rewrite /= add0n /ps in Hval.
  by rewrite -Hval Hnth_pos /b_pair -Hb_eq.
have Hdepth : (nth (0,0) ps j).1.+1 <= (nth (0,0) ps pos).1.
  by apply: depth_noncomm_ge => //; rewrite Hnth_b.
rewrite Hnth_pos in Hdepth.
(* b_pair is minimum *)
set s_pair := nth (0,0) ps j.
have Hmin : dv_leq b_pair s_pair.
  apply: (sorted_head_leq (sort_sorted dv_leq_total ps)).
  rewrite (perm_mem (permEl (perm_sort dv_leq ps))).
  by apply: mem_nth; rewrite /ps size_foata_pairs /= add0n.
rewrite /dv_leq in Hmin; case/orP: Hmin => [Hlt | /andP [/eqP Heq _]].
- by have := ltnW (leq_ltn_trans Hdepth Hlt); rewrite ltnn.
- by have := Hdepth; rewrite Heq ltnn.
Qed.

Lemma rem_first_occ_take_drop (b : nat) (s : seq nat) :
  b \in s ->
  rem_first_occ b s = take (index b s) s ++ drop (index b s).+1 s.
Proof.
elim: s => [|x s IH] //=.
case Hbx : (b == x) => /=.
- by move=> _; rewrite eq_sym Hbx /= drop0.
- rewrite inE Hbx /=; have -> : (x == b) = false by rewrite eq_sym Hbx.
  by move=> /= Hb; congr (x :: _); exact: IH.
Qed.

(* --- Composed NF invariant for the SRI map --- *)
(* Requires S to be a clique (all elements pairwise commute) *)

Definition all_pairs_comm (s : seq nat) : bool :=
  all (fun i => all (fun j => (i == j) || comm i j) s) s.

Lemma all_pairs_commP s :
  reflect (forall a b, a \in s -> b \in s -> a != b -> comm a b) (all_pairs_comm s).
Proof.
apply: (iffP idP).
- rewrite /all_pairs_comm => /allP Hs a b Ha Hb Hne.
  have /allP := Hs a Ha.
  move=> /(_ b Hb) /orP [/eqP Hab | //].
  by rewrite Hab eqxx in Hne.
- move=> H; apply/allP => a Ha; apply/allP => b Hb.
  case Hab : (a == b) => //=.
  by apply: H => //; rewrite Hab.
Qed.

Lemma sri_composed_nf_invariant S nf :
  0 < size S + size nf ->
  all_pairs_comm S ->
  let '(S', nf') := sri_map S nf in
  composed_nf S' nf' = composed_nf S nf.
Proof.
move=> Hpos Hapc; rewrite /sri_map /composed_nf.
set b := sri_pivot S nf.
have Hclique : forall a b, a \in S -> b \in S -> a != b -> comm a b.
  by move/all_pairs_commP: Hapc.
case HbS : (b \in S).
- (* REMOVE case: b ∈ S *)
  rewrite (@foata_nf_prepend_compat comm (rem_first_occ b S) _ _ comm_sym
    (foata_nf_idempotent (b :: nf) comm_sym)).
  have -> : rem_first_occ b S ++ b :: nf = (rem_first_occ b S ++ [:: b]) ++ nf.
    by rewrite -catA.
  apply: foata_nf_clique_perm.
  + by rewrite perm_catC /= perm_sym; exact: perm_rem_first_occ.
  + move=> x y Hx Hy Hne.
    have Hpe := perm_rem_first_occ HbS.
    have Hx' : x \in S.
      rewrite (perm_mem Hpe) inE.
      by move: Hx; rewrite mem_cat mem_seq1 orbC.
    have Hy' : y \in S.
      rewrite (perm_mem Hpe) inE.
      by move: Hy; rewrite mem_cat mem_seq1 orbC.
    exact: Hclique.
- (* ADD case: b ∉ S *)
  have HbS' : b \notin S by move: HbS; case: (b \in S).
  have Hb_nf : b \in nf.
    have := sri_pivot_mem Hpos.
    by rewrite -/b mem_cat (negbTE HbS') /=.
  rewrite (@foata_nf_prepend_compat comm (insort b S) _ _ comm_sym
    (foata_nf_idempotent (rem_first_occ b nf) comm_sym)).
  (* Goal: foata_nf comm (insort b S ++ rem_first_occ b nf) = foata_nf comm (S ++ nf) *)
  (* Set up foata_pairs infrastructure for pivot_comm_predecessor *)
  set w := S ++ nf.
  have Hpos_w : 0 < size w by rewrite /w size_cat.
  set ps := foata_pairs comm [::] w.
  set sorted_ps := sort dv_leq ps.
  set b_pair := head (0,0) sorted_ps.
  set pos := index b_pair ps.
  have Hpos_sp : 0 < size sorted_ps.
    by rewrite /sorted_ps (perm_size (permEl (perm_sort dv_leq ps))) /ps size_foata_pairs /= add0n.
  have Hbp_in : b_pair \in ps.
    rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps))).
    have := Hpos_sp; rewrite /sorted_ps.
    by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
  have Hpos_lt : pos < size ps by rewrite /pos index_mem.
  have Hnth_pos : nth (0,0) ps pos = b_pair by rewrite /pos nth_index.
  have Hpos_w2 : pos < size w.
    by move: Hpos_lt; rewrite /ps size_foata_pairs /= add0n.
  (* b = head 0 (foata_nf comm w) = b_pair.2 *)
  have Hb_eq : b = b_pair.2.
    rewrite /b /sri_pivot /composed_nf /b_pair /sorted_ps /ps /w.
    rewrite /foata_nf.
    by case: (sort dv_leq (foata_pairs comm [::] (S ++ nf))) Hpos_sp => [|[d v] t] //=.
  (* nth 0 w pos = b *)
  have Hnth_pos_b : nth 0 w pos = b.
    rewrite Hb_eq -(nth_foata_pairs_val comm [::] (k := pos) Hpos_w2).
    by rewrite /= add0n Hnth_pos.
  (* Key: pos >= size S (since b ∉ S) *)
  have Hpos_geS : size S <= pos.
    apply/negPn/negP; rewrite -ltnNge => Hlt.
    have : nth 0 w pos \in S.
      rewrite /w nth_cat Hlt; exact: mem_nth.
    by rewrite Hnth_pos_b (negbTE HbS').
  (* Key: pos >= size S + index b nf *)
  set i := index b nf.
  have Hi : i < size nf by rewrite /i index_mem.
  (* pos >= size S + i *)
  have Hpos_geSi : size S + i <= pos.
    apply/negPn/negP; rewrite -ltnNge => Hlt.
    have HposgS : size S <= pos := Hpos_geS.
    have Hpmi : pos - size S < i by rewrite ltn_subLR.
    have Hpmi_sz : pos - size S < size nf.
      by rewrite -(ltn_add2l (size S)) subnKC // -(size_cat S nf).
    have Hnth_b : nth 0 nf (pos - size S) = b.
      have := Hnth_pos_b; rewrite /w nth_cat ltnNge HposgS /=.
      by [].
    have Hidx : index b nf <= pos - size S.
      by rewrite -Hnth_b; exact: index_nth.
    by have := leq_ltn_trans Hidx Hpmi; rewrite ltnn.
  (* Now derive commutativity facts using pivot_comm_predecessor *)
  have Hb_comm_S : forall s, s \in S -> comm b s.
    move=> s Hs.
    set j := index s S.
    have Hj : j < size S by rewrite /j index_mem.
    have Hnth_j : nth 0 w j = s by rewrite /w nth_cat Hj /j nth_index.
    rewrite -Hnth_j.
    apply: (@pivot_comm_predecessor w j Hpos_w).
    exact: (leq_trans Hj Hpos_geS).
  have Hnf_eq : nf = take i nf ++ b :: drop i.+1 nf.
    rewrite -{1}(cat_take_drop i nf); congr (_ ++ _).
    rewrite (drop_nth 0); last by rewrite /i index_mem.
    by congr (_ :: _); rewrite /i nth_index.
  have Hrem_eq : rem_first_occ b nf = take i nf ++ drop i.+1 nf.
    exact: rem_first_occ_take_drop.
  have Hb_comm_nf : forall x, x \in take i nf -> comm b x.
    move=> x Hx.
    have Hx_idx : index x (take i nf) < i.
      have := index_mem x (take i nf); rewrite Hx size_takel //.
      exact: ltnW.
    set j := size S + index x (take i nf).
    have Hnth_j : nth 0 w j = x.
      rewrite /w /j nth_cat ltnNge leq_addr /= addnC addnK.
      by rewrite -(nth_take _ Hx_idx) nth_index.
    rewrite -Hnth_j.
    apply: (@pivot_comm_predecessor w j Hpos_w).
    apply: (leq_trans _ Hpos_geSi).
    by rewrite /j ltn_add2l.
  (* Main chain of equalities *)
  transitivity (foata_nf comm ((b :: S) ++ rem_first_occ b nf)).
    apply: foata_nf_clique_perm.
    + exact: perm_insort.
    + move=> x y Hx Hy Hne.
      have Hx_in : x \in b :: S by rewrite -(perm_mem (perm_insort b S)).
      have Hy_in : y \in b :: S by rewrite -(perm_mem (perm_insort b S)).
      rewrite inE in Hx_in; rewrite inE in Hy_in.
      case/orP: Hx_in => [/eqP Hxb |Hx_S]; case/orP: Hy_in => [/eqP Hyb |Hy_S].
      * by rewrite Hxb Hyb eqxx in Hne.
      * by rewrite Hxb; exact: Hb_comm_S.
      * by rewrite Hyb; exact: comm_sym (Hb_comm_S _ Hx_S).
      * exact: Hclique Hx_S Hy_S Hne.
  (* Goal: foata_nf comm ((b :: S) ++ rem_first_occ b nf) = foata_nf comm (S ++ nf) *)
  transitivity (foata_nf comm (b :: (S ++ take i nf) ++ drop i.+1 nf)).
    congr (foata_nf comm); rewrite Hrem_eq /= catA //.
  transitivity (foata_nf comm ((S ++ take i nf) ++ b :: drop i.+1 nf)).
    symmetry; apply: foata_nf_bubble_front.
    move=> x Hx Hne.
    rewrite mem_cat in Hx; case/orP: Hx => [Hx_S | Hx_nf].
    + exact: comm_sym (Hb_comm_S x Hx_S).
    + exact: comm_sym (Hb_comm_nf x Hx_nf).
  congr (foata_nf comm); rewrite -catA -Hnf_eq //.
Qed.

(* --- Helper lemmas for the involution --- *)

Lemma ltn_trans' : transitive ltn.
Proof. by move=> b a c; exact: ltn_trans. Qed.

Lemma sorted_ltn_not_dup x s :
  path ltn x s -> x \notin s.
Proof.
elim: s x => [|y s IH] x //= /andP [Hxy Hpath].
rewrite inE negb_or.
apply/andP; split.
- by apply/eqP => Heq; subst y; rewrite ltnn in Hxy.
- apply/negP => Hxs.
  have := order_path_min ltn_trans' Hpath.
  move/allP/(_ x Hxs) => Hyx.
  by have := ltn_trans Hxy Hyx; rewrite ltnn.
Qed.

Lemma rem_insort_cancel b s :
  b \notin s -> rem_first_occ b (insort b s) = s.
Proof.
elim: s => [|x s IH] //=.
- by rewrite eqxx.
- rewrite inE negb_or => /andP [Hbx Hbs].
  case: ifP => Hle /=.
  + by rewrite eqxx.
  + have -> : (x == b) = false by apply/eqP => Heq; rewrite Heq eqxx in Hbx.
    by rewrite IH.
Qed.

Lemma insort_rem_cancel b s :
  sorted ltn s -> b \in s -> insort b (rem_first_occ b s) = s.
Proof.
elim: s => [|x s IH] //=.
rewrite /sorted /= => Hpath; rewrite inE => /orP [/eqP -> | Hbs].
- rewrite eqxx.
  case: s IH Hpath => [|y s'] _ //= /andP [Hby _].
  by rewrite (ltnW Hby).
- case Hxb : (x == b) => /=.
  + exfalso; move/eqP: Hxb => ?; subst x.
    by have := sorted_ltn_not_dup Hpath; rewrite Hbs.
  + have Hsorted' : sorted ltn s := path_sorted Hpath.
    rewrite IH //.
    case Hle : (b <= x) => //.
    exfalso.
    have := order_path_min ltn_trans' Hpath.
    move/allP/(_ b Hbs) => Hxb'.
    by have := leq_ltn_trans Hle Hxb'; rewrite ltnn.
Qed.

Lemma mem_rem_sorted_notin b s :
  sorted ltn s -> b \in s -> b \notin rem_first_occ b s.
Proof.
elim: s => [|x s IH] //=.
rewrite /sorted /= => Hpath; rewrite inE => /orP [/eqP -> | Hbs].
- rewrite eqxx. exact: sorted_ltn_not_dup Hpath.
- case Hxb : (x == b).
  + exfalso; move/eqP: Hxb => ?; subst x.
    by have := sorted_ltn_not_dup Hpath; rewrite Hbs.
  + rewrite /= inE.
    have Hsorted' : sorted ltn s := path_sorted Hpath.
    have Hbr := IH Hsorted' Hbs.
    by rewrite (negbTE Hbr) orbF; apply/eqP => Heq; rewrite Heq eqxx in Hxb.
Qed.

Lemma mem_insort_head b s : b \in insort b s.
Proof.
elim: s => [|x s IH] //=.
- by rewrite inE eqxx.
- case: ifP => _ /=; by rewrite inE ?eqxx // IH orbT.
Qed.

Lemma all_pairs_comm_sub s1 s2 :
  (forall x, x \in s1 -> x \in s2) ->
  all_pairs_comm s2 -> all_pairs_comm s1.
Proof.
move=> Hsub /allP Hall.
apply/allP => x Hx.
have := Hall _ (Hsub _ Hx).
move/allP => Hallx.
apply/allP => y Hy.
exact: Hallx (Hsub _ Hy).
Qed.

Lemma all_pairs_comm_rem b s :
  all_pairs_comm s -> all_pairs_comm (rem_first_occ b s).
Proof. exact: all_pairs_comm_sub (fun x => @mem_rem_first_occ b s x). Qed.

(* Swap chain projection: removing b from a swap chain yields a swap chain *)
(* Key property: adjacent commuting swaps preserve foata_nf after removing b *)
Lemma foata_nf_rem_swap b w k :
  k.+1 < size w ->
  comm (nth 0 w k) (nth 0 w k.+1) ->
  comm (nth 0 w k.+1) (nth 0 w k) ->
  b \in w ->
  let sw := take k w ++ nth 0 w k.+1 :: nth 0 w k :: drop k.+2 w in
  foata_nf comm (rem_first_occ b sw) = foata_nf comm (rem_first_occ b w).
Proof.
move=> Hk Hc1 Hc2 Hb /=.
set sw := take k w ++ _ :: _ :: _.
have Hw : w = take k w ++ nth 0 w k :: nth 0 w k.+1 :: drop k.+2 w.
  exact: w_split_nat.
(* Case analysis on whether b appears in take k w *)
set a1 := nth 0 w k.
set a2 := nth 0 w k.+1.
rewrite -/a1 -/a2 in Hc1 Hc2.
have Hk' : k < size w := ltn_trans (ltnSn k) Hk.
have Hsw : sw = take k w ++ a2 :: a1 :: drop k.+2 w by [].
(* b appears somewhere in w = take k w ++ a1 :: a2 :: drop k.+2 w *)
have Hb_w : b \in take k w ++ a1 :: a2 :: drop k.+2 w by rewrite -Hw.
rewrite mem_cat in Hb_w.
have [Hb_take | Hb_ntake] := boolP (b \in take k w).
  (* Case 1: b appears in take k w, at position < k *)
  (* rem_first_occ b (take k w) is the same for both sw and w *)
  (* rem_first_occ b w = rem_first_occ b (take k w) ++ a1 :: a2 :: drop k.+2 w *)
  (* rem_first_occ b sw = rem_first_occ b (take k w) ++ a2 :: a1 :: drop k.+2 w *)
  have Hrem_w : rem_first_occ b w =
    rem_first_occ b (take k w) ++ a1 :: a2 :: drop k.+2 w.
    rewrite {1}Hw -/a1 -/a2.
    elim: (take k w) Hb_take => [|x s IH] //=.
    rewrite inE => /orP [/eqP -> | Hbs] /=.
      by rewrite eqxx.
    by case: ifP => [_ | _] //=; rewrite IH.
  have Hrem_sw : rem_first_occ b sw =
    rem_first_occ b (take k w) ++ a2 :: a1 :: drop k.+2 w.
    rewrite Hsw -/a1 -/a2.
    elim: (take k w) Hb_take => [|x s IH] //=.
    rewrite inE => /orP [/eqP -> | Hbs] /=.
      by rewrite eqxx.
    by case: ifP => [_ | _] //=; rewrite IH.
  rewrite Hrem_w Hrem_sw.
  exact: foata_nf_swap_adj _ _ Hc2 Hc1.
(* Case 2: b not in take k w, so first occurrence is at k or later *)
move: Hb_w; rewrite (negbTE Hb_ntake) /= inE inE => /orP [/eqP Hba1 | Hb_rest].
  (* Case 2a: b = a1 = nth 0 w k *)
  (* In w: first occurrence of b is at position k, rem gives take k w ++ a2 :: drop k.+2 w *)
  (* In sw: sw = take k w ++ a2 :: a1 :: drop k.+2 w
     a2 is at position k. Is a2 = b? If so, a2 = a1 = b, contradicting comm_irrefl.
     Otherwise, a1 = b at position k+1. *)
  have Ha2_ne : a2 != b.
    apply/eqP => Ha2b; rewrite Ha2b -Hba1 in Hc1.
    by move: (comm_irrefl b); rewrite Hc1.
  have Hrem_w : rem_first_occ b w = take k w ++ a2 :: drop k.+2 w.
    rewrite {1}Hw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite /a1 Hba1 eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  have Hrem_sw : rem_first_occ b sw = take k w ++ a2 :: drop k.+2 w.
    rewrite Hsw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite (negbTE Ha2_ne) /= Hba1 eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  by rewrite Hrem_w Hrem_sw.
case/orP: Hb_rest => [/eqP Hba2 | Hb_drop].
  (* Case 2b: b = a2 = nth 0 w k.+1 *)
  have Ha1_ne : a1 != b.
    apply/eqP => Ha1b; rewrite Ha1b -Hba2 in Hc1.
    by move: (comm_irrefl b); rewrite Hc1.
  have Hrem_w : rem_first_occ b w = take k w ++ a1 :: drop k.+2 w.
    rewrite {1}Hw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite (negbTE Ha1_ne) /= Hba2 eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  have Hrem_sw : rem_first_occ b sw = take k w ++ a1 :: drop k.+2 w.
    rewrite Hsw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite Hba2 eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  by rewrite Hrem_w Hrem_sw.
(* Case 3: b in drop k.+2 w *)
(* Sub-case: a1 = b or a2 = b needs special treatment *)
have Ha12_ne : a1 != a2.
  apply/eqP => Ha12; move: (comm_irrefl a1).
  by rewrite {2}Ha12 Hc1.
have [/eqP Ha1b | Ha1_ne] := boolP (a1 == b).
  (* a1 = b: same as Case 2a but we're also in Hb_drop *)
  have Ha2_ne : a2 != b.
    by apply/eqP => Ha2b; move: Ha12_ne; rewrite Ha1b Ha2b eqxx.
  have Hrem_w : rem_first_occ b w = take k w ++ a2 :: drop k.+2 w.
    rewrite {1}Hw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite Ha1b eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  have Hrem_sw : rem_first_occ b sw = take k w ++ a2 :: drop k.+2 w.
    rewrite Hsw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite (negbTE Ha2_ne) /= Ha1b eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  by rewrite Hrem_w Hrem_sw.
have [/eqP Ha2b | Ha2_ne] := boolP (a2 == b).
  (* a2 = b: same as Case 2b but we're also in Hb_drop *)
  have Hrem_w : rem_first_occ b w = take k w ++ a1 :: drop k.+2 w.
    rewrite {1}Hw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite (negbTE Ha1_ne) /= Ha2b eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  have Hrem_sw : rem_first_occ b sw = take k w ++ a1 :: drop k.+2 w.
    rewrite Hsw -/a1 -/a2.
    elim: (take k w) Hb_ntake => [|x s IH] //=.
      by rewrite Ha2b eqxx.
    rewrite inE negb_or => /andP [Hxb Hbs].
    by rewrite eq_sym (negbTE Hxb) /= IH.
  by rewrite Hrem_w Hrem_sw.
(* Neither a1 nor a2 is b *)
have Hrem_w : rem_first_occ b w =
  take k w ++ a1 :: a2 :: rem_first_occ b (drop k.+2 w).
  rewrite {1}Hw -/a1 -/a2.
  elim: (take k w) Hb_ntake => [|x s IH] //=.
    by rewrite (negbTE Ha1_ne) /= (negbTE Ha2_ne) /=.
  rewrite inE negb_or => /andP [Hxb Hbs].
  by rewrite eq_sym (negbTE Hxb) /= IH.
have Hrem_sw : rem_first_occ b sw =
  take k w ++ a2 :: a1 :: rem_first_occ b (drop k.+2 w).
  rewrite Hsw -/a1 -/a2.
  elim: (take k w) Hb_ntake => [|x s IH] //=.
    by rewrite (negbTE Ha2_ne) /= (negbTE Ha1_ne) /=.
  rewrite inE negb_or => /andP [Hxb Hbs].
  by rewrite eq_sym (negbTE Hxb) /= IH.
rewrite Hrem_w Hrem_sw.
exact: foata_nf_swap_adj _ _ Hc2 Hc1.
Qed.

(* Core NF roundtrip: removing b from foata_nf(b :: nf) and renormalizing gives nf *)
Lemma foata_nf_rem_head_cancel b nf0 :
  foata_nf comm nf0 = nf0 ->
  foata_nf comm (rem_first_occ b (foata_nf comm (b :: nf0))) = nf0.
Proof.
move=> Hnf0.
(* foata_nf(b :: nf0) is reached from b :: nf0 via adjacent commuting swaps *)
have [ws [Hlast Hsteps]] := foata_nf_sound (b :: nf0) comm_sym.
(* Each swap preserves foata_nf after removing b *)
(* So foata_nf(rem b (foata_nf(b :: nf0))) = foata_nf(rem b (b :: nf0)) = foata_nf(nf0) = nf0 *)
suff Hchain : forall v ws0,
  b \in v ->
  (forall i, i < size ws0 ->
    let w0 := nth [::] (v :: ws0) i in
    let w1 := nth [::] (v :: ws0) i.+1 in
    exists k, k.+1 < size w0 /\
      comm (nth 0 w0 k) (nth 0 w0 k.+1) /\
      comm (nth 0 w0 k.+1) (nth 0 w0 k) /\
      w1 = take k w0 ++ nth 0 w0 k.+1 :: nth 0 w0 k :: drop k.+2 w0) ->
  foata_nf comm (rem_first_occ b (last v ws0)) =
  foata_nf comm (rem_first_occ b v).
  rewrite -Hlast (Hchain _ _ _ Hsteps) /=; first by rewrite eqxx.
  by rewrite inE eqxx.
move=> v ws0 Hbv Hsteps0.
elim: ws0 v Hbv Hsteps0 => [|w' ws' IH] v Hbv Hsteps0 //=.
have [k [Hk [Hc1 [Hc2 Heq]]]] := Hsteps0 0 (ltn0Sn _).
rewrite /= in Heq.
have Hsteps' : forall i, i < size ws' ->
  let w0 := nth [::] (w' :: ws') i in
  let w1 := nth [::] (w' :: ws') i.+1 in
  exists k0, k0.+1 < size w0 /\
    comm (nth 0 w0 k0) (nth 0 w0 k0.+1) /\
    comm (nth 0 w0 k0.+1) (nth 0 w0 k0) /\
    w1 = take k0 w0 ++ nth 0 w0 k0.+1 :: nth 0 w0 k0 :: drop k0.+2 w0.
  by move=> i Hi; exact: (Hsteps0 i.+1 Hi).
have Hbw' : b \in w'.
  have Hpe : perm_eq v w'.
    have Hv := @w_split_nat k v Hk.
    rewrite Hv Heq perm_cat2l /= -(cat1s (nth 0 v k.+1)) -(cat1s (nth 0 v k)).
    by rewrite perm_catCA perm_refl.
  by rewrite -(perm_mem Hpe).
rewrite (IH w' Hbw' Hsteps') Heq.
exact: foata_nf_rem_swap Hk Hc1 Hc2 Hbv.
Qed.

(* Dual: adding b to nf and renormalizing after removing b gives nf *)
(* Requires that b commutes with all elements before it in nf0 (depth-0 condition) *)
Lemma foata_nf_add_head_cancel b nf0 :
  foata_nf comm nf0 = nf0 ->
  b \in nf0 ->
  (forall j, j < index b nf0 -> comm b (nth 0 nf0 j)) ->
  foata_nf comm (b :: foata_nf comm (rem_first_occ b nf0)) = nf0.
Proof.
move=> Hnf0 Hb Hcomm_pre.
(* Step 1: foata_nf(b :: foata_nf(rem b nf0)) = foata_nf(b :: rem b nf0) *)
have Hstep1 : foata_nf comm (b :: foata_nf comm (rem_first_occ b nf0)) =
              foata_nf comm (b :: rem_first_occ b nf0).
  apply: (@foata_nf_prepend_compat comm [:: b] _ _ comm_sym).
  exact: foata_nf_idempotent.
rewrite Hstep1.
(* Step 2: foata_nf(b :: rem b nf0) = foata_nf(nf0) = nf0 *)
(* b :: rem b nf0 = b :: (take i nf0 ++ drop i.+1 nf0) *)
(* nf0 = take i nf0 ++ b :: drop i.+1 nf0 *)
(* b commutes with all of take i nf0 by hypothesis *)
set i := index b nf0.
have Hi : i < size nf0 by rewrite /i index_mem.
have Hnf0_split : nf0 = take i nf0 ++ b :: drop i.+1 nf0.
  rewrite -{1}(cat_take_drop i nf0); congr (_ ++ _).
  rewrite (drop_nth 0); last by rewrite /i index_mem.
  by congr (_ :: _); rewrite /i nth_index.
have Hrem : rem_first_occ b nf0 = take i nf0 ++ drop i.+1 nf0.
  exact: rem_first_occ_take_drop.
rewrite Hrem.
(* Goal: foata_nf comm (b :: take i nf0 ++ drop i.+1 nf0) = nf0 *)
transitivity (foata_nf comm (take i nf0 ++ b :: drop i.+1 nf0)).
  symmetry; apply: foata_nf_bubble_front.
  move=> x Hx Hxb.
  set j := index x (take i nf0).
  have Hj : j < i.
    have := Hx; rewrite /j -index_mem size_takel //; exact: ltnW.
  have Hnth_j : nth 0 nf0 j = x.
    rewrite -(nth_take 0 Hj) /j nth_index //.
  have := Hcomm_pre j Hj.
  by rewrite Hnth_j; exact: comm_sym.
by rewrite -Hnf0_split Hnf0.
Qed.

(* --- Involution property --- *)

Lemma sri_involution S nf :
  0 < size S + size nf ->
  all_pairs_comm S ->
  sorted ltn S ->
  foata_nf comm nf = nf ->
  sri_map (sri_map S nf).1 (sri_map S nf).2 = (S, nf).
Proof.
move=> Hpos Hapc Hsorted Hnf_idem.
set b := sri_pivot S nf.
set p := sri_map S nf.
have /all_pairs_commP Hclique := Hapc.
(* Extract the composed NF invariant *)
have Hinv : composed_nf p.1 p.2 = composed_nf S nf.
  have := @sri_composed_nf_invariant S nf Hpos Hapc.
  by rewrite -/p; case: p.
(* The total size is preserved *)
have Htotal : size p.1 + size p.2 = size S + size nf.
  move: (@sri_map_total_size S nf Hpos).
  by rewrite -/p; case: (p) => s1 s2.
have Hpos' : 0 < size p.1 + size p.2 by rewrite Htotal.
(* The pivot is the same *)
have Hpivot : sri_pivot p.1 p.2 = b.
  rewrite /sri_pivot /b Hinv //.
(* Now case split on whether b ∈ S *)
rewrite /p /sri_map -/b.
case HbS : (b \in S).
- (* REMOVE case: b ∈ S *)
  set S' := rem_first_occ b S.
  set nf' := foata_nf comm (b :: nf).
  (* The second application *)
  rewrite /= -/b.
  (* pivot for second application *)
  have Hinv' : composed_nf S' nf' = composed_nf S nf.
    have := @sri_composed_nf_invariant S nf Hpos Hapc.
    by rewrite /sri_map -/b HbS -/S' -/nf'.
  have Hpivot' : sri_pivot S' nf' = b by rewrite /sri_pivot Hinv'.
  rewrite /sri_map Hpivot'.
  (* b ∉ S' *)
  have HbS' : b \notin S' by exact: mem_rem_sorted_notin Hsorted HbS.
  rewrite (negbTE HbS').
  (* Need: (insort b S', foata_nf (rem_first_occ b nf')) = (S, nf) *)
  congr pair.
  + (* insort b (rem_first_occ b S) = S *)
    exact: insort_rem_cancel Hsorted HbS.
  + (* foata_nf (rem_first_occ b (foata_nf (b :: nf))) = nf *)
    exact: foata_nf_rem_head_cancel Hnf_idem.
- (* ADD case: b ∉ S *)
  set S' := insort b S.
  have HbS' : b \notin S by move: HbS; case: (b \in S).
  have Hb_nf : b \in nf := sri_pivot_in_nf Hpos HbS'.
  set nf' := foata_nf comm (rem_first_occ b nf).
  rewrite /= -/b.
  have Hinv' : composed_nf S' nf' = composed_nf S nf.
    have := @sri_composed_nf_invariant S nf Hpos Hapc.
    by rewrite /sri_map -/b (negbTE HbS') -/S' -/nf'.
  have Hpivot' : sri_pivot S' nf' = b by rewrite /sri_pivot Hinv'.
  rewrite /sri_map Hpivot'.
  (* b ∈ S' = insort b S *)
  have HbS'' : b \in S' := mem_insort_head b S.
  rewrite HbS''.
  congr pair.
  + (* rem_first_occ b (insort b S) = S *)
    exact: rem_insort_cancel HbS'.
  + (* foata_nf (b :: foata_nf (rem_first_occ b nf)) = nf *)
    apply: foata_nf_add_head_cancel Hnf_idem Hb_nf _.
    (* Need: forall j, j < index b nf -> comm b (nth 0 nf j) *)
    (* Use pivot_comm_predecessor on w = S ++ nf *)
    set w := S ++ nf.
    have Hpos_w : 0 < size w by rewrite /w size_cat.
    set ps := foata_pairs comm [::] w.
    set sorted_ps := sort dv_leq ps.
    set b_pair := head (0,0) sorted_ps.
    set pos := index b_pair ps.
    have Hpos_sp : 0 < size sorted_ps.
      by rewrite /sorted_ps (perm_size (permEl (perm_sort dv_leq ps))) /ps size_foata_pairs /= add0n.
    have Hpos_lt : pos < size ps by rewrite /pos index_mem;
      rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps)));
      have := Hpos_sp; rewrite /sorted_ps;
      by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
    have Hpos_w2 : pos < size w.
      by move: Hpos_lt; rewrite /ps size_foata_pairs /= add0n.
    have Hb_eq : b = b_pair.2.
      rewrite /b /sri_pivot /composed_nf /b_pair /sorted_ps /ps /w /foata_nf.
      by case: (sort dv_leq (foata_pairs comm [::] (S ++ nf))) Hpos_sp => [|[d v] t] //=.
    have Hnth_pos_b : nth 0 w pos = b.
      rewrite Hb_eq -(nth_foata_pairs_val comm [::] (k := pos) Hpos_w2).
      by rewrite /= add0n /ps /pos nth_index //;
         rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps)));
         have := Hpos_sp; rewrite /sorted_ps;
         by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
    have Hpos_geS : size S <= pos.
      apply/negPn/negP; rewrite -ltnNge => Hlt.
      have : nth 0 w pos \in S.
        rewrite /w nth_cat Hlt; exact: mem_nth.
      by rewrite Hnth_pos_b (negbTE HbS').
    have Hb_nf' : b \in nf := sri_pivot_in_nf Hpos HbS'.
    have Hi_nf : index b nf < size nf by rewrite index_mem.
    have Hpos_geSi : size S + index b nf <= pos.
      apply/negPn/negP; rewrite -ltnNge => Hlt.
      have HposgS : size S <= pos := Hpos_geS.
      have Hpmi : pos - size S < index b nf by rewrite ltn_subLR.
      have Hpmi_sz : pos - size S < size nf.
        by rewrite -(ltn_add2l (size S)) subnKC // -(size_cat S nf).
      have Hnth_b : nth 0 nf (pos - size S) = b.
        have := Hnth_pos_b; rewrite /w nth_cat ltnNge HposgS /=.
        by [].
      have Hidx : index b nf <= pos - size S.
        by rewrite -Hnth_b; exact: index_nth.
      by have := leq_ltn_trans Hidx Hpmi; rewrite ltnn.
    move=> j Hj.
    set jw := size S + j.
    have Hnth_jw : nth 0 w jw = nth 0 nf j.
      by rewrite /w /jw nth_cat ltnNge leq_addr /= addnC addnK.
    rewrite -Hnth_jw.
    apply: (@pivot_comm_predecessor w jw Hpos_w).
    apply: (leq_trans _ Hpos_geSi).
    by rewrite /jw ltn_add2l.
Qed.

(* --- No fixed points --- *)

Lemma Sn_neq_n n : n.+1 <> n.
Proof. by move/eqP; rewrite eqn_leq leqNgt ltnSn /=. Qed.

Lemma sri_no_fixpoints S nf :
  0 < size S + size nf ->
  sri_map S nf <> (S, nf).
Proof.
move=> Hpos; rewrite /sri_map.
case HbS : (sri_pivot S nf \in S) => [] [HS _].
- have Hgt : 0 < size S by move: HbS; case: (S) => //=; rewrite in_nil.
  have := congr1 size HS; rewrite size_rem_first_occ // => Hsz.
  have := prednK Hgt; rewrite Hsz; exact: Sn_neq_n.
- have := congr1 size HS; rewrite size_insort; exact: Sn_neq_n.
Qed.

(* --- Pivot commutes with clique elements (when pivot not in S) --- *)

Lemma sri_pivot_comm_clique S nf :
  0 < size S + size nf ->
  all_pairs_comm S ->
  sri_pivot S nf \notin S ->
  forall s, s \in S -> comm (sri_pivot S nf) s.
Proof.
move=> Hpos Hapc HbS' s Hs.
set b := sri_pivot S nf.
have Hb_nf : b \in nf := sri_pivot_in_nf Hpos HbS'.
set w := S ++ nf.
have Hpos_w : 0 < size w by rewrite /w size_cat.
set ps := foata_pairs comm [::] w.
set sorted_ps := sort dv_leq ps.
set b_pair := head (0,0) sorted_ps.
set pos := index b_pair ps.
have Hpos_sp : 0 < size sorted_ps
  by rewrite /sorted_ps (perm_size (permEl (perm_sort dv_leq ps))) /ps
     size_foata_pairs /= add0n.
have Hbp_in : b_pair \in ps.
  rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps))).
  have := Hpos_sp; rewrite /sorted_ps.
  by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
have Hpos_lt : pos < size ps by rewrite /pos index_mem.
have Hpos_w2 : pos < size w
  by move: Hpos_lt; rewrite /ps size_foata_pairs /= add0n.
have Hb_eq : b = b_pair.2.
  rewrite /b /sri_pivot /composed_nf /b_pair /sorted_ps /ps /w /foata_nf.
  by case: (sort dv_leq (foata_pairs comm [::] (S ++ nf))) Hpos_sp => [|[d v] t] //=.
have Hnth_pos_b : nth 0 w pos = b.
  rewrite Hb_eq -(nth_foata_pairs_val comm [::] (k := pos) Hpos_w2).
  by rewrite /= add0n /ps /pos nth_index //;
     rewrite /b_pair -(perm_mem (permEl (perm_sort dv_leq ps)));
     have := Hpos_sp; rewrite /sorted_ps;
     by case: (sort dv_leq ps) => [|h t] //= _; rewrite inE eqxx.
have Hpos_geS : size S <= pos.
  apply/negPn/negP; rewrite -ltnNge => Hlt.
  have : nth 0 w pos \in S.
    rewrite /w nth_cat Hlt; exact: mem_nth.
  by rewrite Hnth_pos_b (negbTE HbS').
set j := index s S.
have Hj : j < size S by rewrite /j index_mem.
have Hnth_j : nth 0 w j = s by rewrite /w nth_cat Hj /j nth_index.
rewrite -Hnth_j.
apply: (@pivot_comm_predecessor w j Hpos_w).
exact: (leq_trans Hj Hpos_geS).
Qed.

(* --- SRI map preserves validity --- *)

Lemma sri_map_valid S nf :
  0 < size S + size nf ->
  all_pairs_comm S ->
  sorted ltn S ->
  foata_nf comm nf = nf ->
  let '(S', nf') := sri_map S nf in
  all_pairs_comm S' /\ sorted ltn S' /\ foata_nf comm nf' = nf'.
Proof.
move=> Hpos Hapc Hsorted Hnf.
rewrite /sri_map.
set b := sri_pivot S nf.
have /all_pairs_commP Hclique := Hapc.
case HbS : (b \in S).
- (* REMOVE case *)
  set S' := rem_first_occ b S.
  set nf' := foata_nf comm (b :: nf).
  repeat split.
  + (* S' is a clique *)
    apply/all_pairs_commP => a' b' Ha' Hb' Hne.
    apply: Hclique => //.
    * exact: mem_rem_first_occ Ha'.
    * exact: mem_rem_first_occ Hb'.
  + (* S' is sorted: rem_first_occ gives subseq *)
    have Hsubseq : forall (c : nat) (t : seq nat), subseq (rem_first_occ c t) t.
      move=> c; elim => [|y t' IHt] //=.
      case: (y == c) => /=.
        exact: subseq_cons.
      have Hss : subseq (y :: rem_first_occ c t') (y :: t').
        by rewrite /= eqxx.
      exact: Hss.
    exact: (subseq_sorted ltn_trans' (Hsubseq b S) Hsorted).
  + (* nf' is a normal form *)
    exact: foata_nf_idempotent.
- (* ADD case *)
  have HbS' : b \notin S by move: HbS; case: (b \in S).
  set S' := insort b S.
  set nf' := foata_nf comm (rem_first_occ b nf).
  have Hb_comm_S : forall s, s \in S -> comm b s.
    exact: sri_pivot_comm_clique Hpos Hapc HbS'.
  repeat split.
  + (* S' = insort b S is a clique *)
    apply/all_pairs_commP => a' b' Ha' Hb' Hne.
    rewrite mem_insort in Ha'; rewrite mem_insort in Hb'.
    case/orP: Ha' => [/eqP Ha_eq | Ha']; case/orP: Hb' => [/eqP Hb_eq | Hb'].
    * by rewrite Ha_eq Hb_eq eqxx in Hne.
    * by rewrite Ha_eq; exact: Hb_comm_S.
    * by rewrite Hb_eq; exact: comm_sym (Hb_comm_S _ Ha').
    * exact: Hclique Ha' Hb' Hne.
  + (* S' is sorted *)
    exact: sorted_insort Hsorted HbS'.
  + (* nf' is a normal form *)
    exact: foata_nf_idempotent.
Qed.

End sri_krattenthaler.

(* ========================================================================== *)
(* Phase C: Main theorem infrastructure                                       *)
(* ========================================================================== *)

(* --- Basic lemmas about all_words --- *)

Lemma all_words_bounded Tg L w :
  w \in all_words Tg L -> all (fun i => i < Tg) w.
Proof.
elim: L w => [|L IH] w /=.
  by rewrite mem_seq1 => /eqP ->.
move/flattenP => [s /mapP [i Hi ->] /mapP [w' Hw' ->]] /=.
by rewrite mem_iota /= add0n in Hi; rewrite Hi IH.
Qed.

Lemma all_words_size Tg L w :
  w \in all_words Tg L -> size w = L.
Proof.
elim: L w => [|L IH] w /=.
  by rewrite mem_seq1 => /eqP ->.
move/flattenP => [s /mapP [i Hi ->] /mapP [w' Hw' ->]] /=.
by rewrite IH.
Qed.

Lemma all_words_uniq Tg L : uniq (all_words Tg L).
Proof.
elim: L => [|L IH] //=.
apply: allpairs_uniq; first exact: iota_uniq.
- exact: IH.
- by move=> [a1 b1] [a2 b2] /= _ _ [-> ->].
Qed.

(* --- Bounded comm relation --- *)

Definition comm_b (Tg : nat) (comm : nat -> nat -> bool) (a b : nat) : bool :=
  (a < Tg) && (b < Tg) && comm a b.

Lemma comm_b_sym (Tg : nat) (crel : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> crel a b -> crel b a) ->
  forall a b, comm_b Tg crel a b -> comm_b Tg crel b a.
Proof.
move=> Hsym a b; rewrite /comm_b.
by move/andP => [/andP [Ha Hb] Hab]; rewrite Ha Hb /= Hsym.
Qed.

Lemma comm_b_irrefl (Tg : nat) (crel : nat -> nat -> bool) :
  (forall a, ~~ crel a a) ->
  forall a, ~~ comm_b Tg crel a a.
Proof.
move=> Hirr a; rewrite /comm_b.
by case: (a < Tg) => //=; rewrite Hirr.
Qed.

Lemma foata_nf_comm_b (Tg : nat) (crel : nat -> nat -> bool) (w : seq nat) :
  all (fun i => i < Tg) w ->
  foata_nf crel w = foata_nf (comm_b Tg crel) w.
Proof.
move=> Hbd; apply: foata_nf_ext => a b Ha Hb.
rewrite /comm_b.
have HaTg : a < Tg by exact: (allP Hbd _ Ha).
have HbTg : b < Tg by exact: (allP Hbd _ Hb).
by rewrite HaTg HbTg.
Qed.

Lemma n_traces_natB_comm_b (Tg L : nat) (crel : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> crel a b -> crel b a) ->
  (forall a, ~~ crel a a) ->
  n_traces_natB Tg L crel = n_traces_natB Tg L (comm_b Tg crel).
Proof.
move=> Hsym Hirr; rewrite /n_traces_natB.
congr (size (undup _)).
apply/eq_in_map => w Hw.
exact: foata_nf_comm_b (all_words_bounded Hw).
Qed.

Lemma all_pairs_comm_sorted_comm_b (Tg : nat) (crel : nat -> nat -> bool) (s : seq nat) :
  all (fun i => i < Tg) s ->
  all_pairs_comm_sorted crel s = all_pairs_comm_sorted (comm_b Tg crel) s.
Proof.
move=> Hbd; rewrite /all_pairs_comm_sorted.
apply: eq_in_all => i Hi.
apply: eq_in_all => j Hj.
case Hij : (i == j) => //=.
rewrite /comm_b.
have HiTg : i < Tg by exact: (allP Hbd _ Hi).
have HjTg : j < Tg by exact: (allP Hbd _ Hj).
by rewrite HiTg HjTg.
Qed.

Lemma clique_count_comm_b (Tg k : nat) (crel : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> crel a b -> crel b a) ->
  (forall a, ~~ crel a a) ->
  clique_count Tg k crel = clique_count Tg k (comm_b Tg crel).
Proof.
move=> Hsym Hirr; rewrite /clique_count /cliques_of_size.
congr size; apply: eq_in_filter => s Hs.
apply: all_pairs_comm_sorted_comm_b.
have Hsub : subseq s (iota 0 Tg) by exact: subseqs_k_subseq Hs.
apply/allP => x Hx.
have : x \in iota 0 Tg by exact: (mem_subseq Hsub Hx).
by rewrite mem_iota add0n.
Qed.

(* --- Involution counting principle --- *)
(* If f is a fixpoint-free involution on a list, and sign flips on each pair,
   then the two halves have equal count. *)

Lemma perm_count_pred (T : eqType) (p : pred T) (s1 s2 : seq T) :
  perm_eq s1 s2 -> count p s1 = count p s2.
Proof.
move=> Hpe; rewrite -!size_filter.
exact: perm_size (perm_filter p Hpe).
Qed.

Section involution_counting.

Variable A : eqType.
Variable f : A -> A.
Variable sign : A -> bool.
Hypothesis f_invol : forall x, f (f x) = x.
Hypothesis f_no_fix : forall x, f x != x.
Hypothesis f_flip : forall x, sign (f x) = ~~ sign x.

Lemma f_inj : injective f.
Proof. by move=> x y Hxy; rewrite -(f_invol x) -(f_invol y) Hxy. Qed.

Lemma involution_sign_count (s : seq A) :
  uniq s ->
  (forall x, x \in s -> f x \in s) ->
  count sign s = count (predC sign) s.
Proof.
move: s; apply: (well_founded_induction_type
  (Wf_nat.well_founded_ltof _ (@size A))) => s IH Huniq Hclosed.
case: s Huniq Hclosed IH => [|a s0] //= /andP [Ha Hs0] Hclosed IH.
have Hfa_ne : f a != a := f_no_fix a.
have Hfa_in : f a \in a :: s0.
  by apply: Hclosed; rewrite inE eqxx.
have Hfa_s0 : f a \in s0.
  by rewrite inE (negbTE Hfa_ne) in Hfa_in.
set s' := rem (f a) s0.
have Hs'_uniq : uniq s' by exact: rem_uniq _ Hs0.
have Hpe_s0 : perm_eq s0 (f a :: s') := perm_to_rem Hfa_s0.
have Hs'_sz : Wf_nat.ltof _ (@size A) s' (a :: s0).
  rewrite /Wf_nat.ltof; apply/ltP.
  by rewrite /s' (size_rem Hfa_s0) /=; case: (size s0).
have Hfa_sign : sign (f a) = ~~ sign a := f_flip a.
have Hc_sign : count sign s0 = sign (f a) + count sign s' by
  rewrite (perm_count_pred sign Hpe_s0).
have Hc_comp : count (predC sign) s0 = (~~ sign (f a)) + count (predC sign) s' by
  rewrite (perm_count_pred (predC sign) Hpe_s0).
rewrite /= Hc_sign Hc_comp Hfa_sign.
have Hclosed' : forall x, x \in s' -> f x \in s'.
  move=> x Hx.
  have Hx_s0 : x \in s0 := mem_rem Hx.
  have Hx_cons : x \in a :: s0 by rewrite inE Hx_s0 orbT.
  have Hfx := Hclosed _ Hx_cons.
  rewrite inE in Hfx.
  case/orP: Hfx => [/eqP Hfxa | Hfx_s0].
  - exfalso; have : x = f a by rewrite -Hfxa f_invol.
    move=> Hxfa; move: Hx; rewrite /s' Hxfa (mem_rem_uniqF _ Hs0) //.
  - rewrite /s' (mem_rem_uniq _ Hs0) inE Hfx_s0 andbT.
    apply/eqP => Hfxfa.
    have : x = a by exact: f_inj.
    by move=> Hxa; move: Ha; rewrite -Hxa Hx_s0.
have := IH s' Hs'_sz Hs'_uniq Hclosed'.
case: (sign a) => /= ->.
- by rewrite addnS.
- by rewrite addSn.
Qed.

End involution_counting.

(* Localized version: properties only required for elements of s *)
Lemma involution_sign_count_local (A : eqType) (f : A -> A) (sign : A -> bool) (s : seq A) :
  uniq s ->
  (forall x, x \in s -> f (f x) = x) ->
  (forall x, x \in s -> f x != x) ->
  (forall x, x \in s -> sign (f x) = ~~ sign x) ->
  (forall x, x \in s -> f x \in s) ->
  count sign s = count (predC sign) s.
Proof.
move: s; apply: (well_founded_induction_type
  (Wf_nat.well_founded_ltof _ (@size A))) => s IH Huniq Hinvol Hnofix Hflip Hclosed.
case: s Huniq Hinvol Hnofix Hflip Hclosed IH => [|a s0] //=
  /andP [Ha Hs0] Hinvol Hnofix Hflip Hclosed IH.
have Ha_in : a \in a :: s0 by rewrite inE eqxx.
have Hfa_ne : f a != a := Hnofix a Ha_in.
have Hfa_in : f a \in a :: s0 := Hclosed a Ha_in.
have Hfa_s0 : f a \in s0 by rewrite inE (negbTE Hfa_ne) in Hfa_in.
set s' := rem (f a) s0.
have Hs'_uniq : uniq s' by exact: rem_uniq _ Hs0.
have Hpe_s0 : perm_eq s0 (f a :: s') := perm_to_rem Hfa_s0.
have Hs'_sz : Wf_nat.ltof _ (@size A) s' (a :: s0).
  rewrite /Wf_nat.ltof; apply/ltP.
  by rewrite /s' (size_rem Hfa_s0) /=; case: (size s0).
have Hfa_sign : sign (f a) = ~~ sign a := Hflip a Ha_in.
have Hc_sign : count sign s0 = sign (f a) + count sign s' by
  rewrite (perm_count_pred sign Hpe_s0).
have Hc_comp : count (predC sign) s0 = (~~ sign (f a)) + count (predC sign) s' by
  rewrite (perm_count_pred (predC sign) Hpe_s0).
rewrite /= Hc_sign Hc_comp Hfa_sign.
have Hs'_sub : forall x, x \in s' -> x \in a :: s0.
  by move=> x Hx; rewrite inE (mem_rem Hx) orbT.
have Hinvol_fa : f (f a) = a := Hinvol a Ha_in.
have Hf_inj : forall x y, x \in a :: s0 -> y \in a :: s0 -> f x = f y -> x = y.
  move=> x y Hx Hy Hfxy.
  by rewrite -(Hinvol x Hx) -(Hinvol y Hy) Hfxy.
have Hclosed' : forall x, x \in s' -> f x \in s'.
  move=> x Hx.
  have Hx_s0 : x \in s0 := mem_rem Hx.
  have Hx_cons := Hs'_sub _ Hx.
  have Hfx := Hclosed _ Hx_cons.
  rewrite inE in Hfx.
  case/orP: Hfx => [/eqP Hfxa | Hfx_s0].
  - exfalso; have : x = f a by rewrite -Hfxa (Hinvol _ Hx_cons).
    move=> Hxfa; move: Hx; rewrite /s' Hxfa (mem_rem_uniqF _ Hs0) //.
  - rewrite /s' (mem_rem_uniq _ Hs0) inE Hfx_s0 andbT.
    apply/eqP => Hfxfa.
    have : x = a := Hf_inj _ _ Hx_cons Ha_in Hfxfa.
    by move=> Hxa; move: Ha; rewrite -Hxa Hx_s0.
have := IH s' Hs'_sz Hs'_uniq
  (fun x Hx => Hinvol x (Hs'_sub _ Hx))
  (fun x Hx => Hnofix x (Hs'_sub _ Hx))
  (fun x Hx => Hflip x (Hs'_sub _ Hx))
  Hclosed'.
case: (sign a) => /= ->.
- by rewrite addnS.
- by rewrite addSn.
Qed.

(* --- The recurrence for n_traces_natB --- *)

Lemma n_traces_natB_0 (Tg : nat) (crel : nat -> nat -> bool) :
  n_traces_natB Tg 0 crel = 1.
Proof.
by rewrite /n_traces_natB /all_words /= /foata_nf /=.
Qed.

(* --- SRI alternating identity via involution counting --- *)

Section sri_alternating.

Variable Tg : nat.
Variable crel : nat -> nat -> bool.
Hypothesis crel_sym : forall a b, crel a b -> crel b a.
Hypothesis crel_irrefl : forall a, ~~ crel a a.

(* An SRI pair is (clique, normal_form) — use seq nat * seq nat for eqType *)
Definition sri_pair := (seq nat * seq nat)%type.

Definition sp_clique (p : sri_pair) : seq nat := p.1.
Definition sp_nf (p : sri_pair) : seq nat := p.2.

Definition sri_pair_valid (p : sri_pair) (L : nat) : bool :=
  let cl := sp_clique p in
  let nf := sp_nf p in
  (size cl + size nf == L) &&
  all_pairs_comm_sorted crel cl &&
  sorted ltn cl &&
  (foata_nf crel nf == nf) &&
  all (fun i => i < Tg) cl &&
  all (fun i => i < Tg) nf.

(* Enumerate all valid pairs for a given L *)
Definition all_sri_pairs (L : nat) : seq sri_pair :=
  [seq (cl, nf)
  | cl <- flatten [seq cliques_of_size Tg k crel | k <- iota 0 L.+1],
    nf <- undup (map (foata_nf crel) (all_words Tg (L - size cl)))].

(* The SRI map lifted to sri_pair *)
Definition sri_pair_map (p : sri_pair) : sri_pair :=
  @sri_map crel (sp_clique p) (sp_nf p).

(* Sign of a pair: even |S| = positive *)
Definition sri_pair_sign (p : sri_pair) : bool :=
  ~~ odd (size (sp_clique p)).

(* The alternating identity: for L > 0, the signed sum over valid pairs = 0 *)
(* This means: count positive = count negative *)

(* To prove this, we need:
   1. sri_pair_map is an involution on valid pairs
   2. It has no fixed points
   3. It flips the sign *)

(* 1. sri_map preserves validity *)
Lemma sri_map_preserves_valid (p : sri_pair) (L : nat) :
  0 < L ->
  sri_pair_valid p L ->
  sri_pair_valid (sri_pair_map p) L.
Proof.
move=> HL Hv.
rewrite /sri_pair_valid /sri_pair_map /sp_clique /sp_nf.
move: Hv; rewrite /sri_pair_valid /sp_clique /sp_nf.
case: p => [cl nf] /=.
move/andP => [/andP [/andP [/andP [/andP [/eqP Hsz Hapc] Hsorted] /eqP Hnf] HbdS] HbdNf].
have Hpos : 0 < size cl + size nf by rewrite Hsz.
(* Get validity from sri_map_valid *)
have Hvalid := @sri_map_valid crel crel_sym cl nf Hpos Hapc Hsorted Hnf.
(* Get size preservation *)
have Htotal := @sri_map_total_size crel cl nf Hpos.
case Hmap : (@sri_map crel cl nf) => [cl' nf'] /=.
rewrite Hmap /= in Hvalid Htotal.
case: Hvalid => [Hapc' [Hsorted' Hnf']].
(* Size *)
apply/andP; split; last first.
  (* Boundedness of nf' *)
  have Hpe_nf' := foata_nf_perm_eq crel.
  rewrite /sri_map -/(@sri_pivot crel) in Hmap.
  set b := @sri_pivot crel cl nf in Hmap.
  have Hb_mem : b \in cl ++ nf.
    exact: (@sri_pivot_mem crel cl nf Hpos).
  have Hb_bd : b < Tg.
    rewrite mem_cat in Hb_mem; case/orP: Hb_mem => Hmem.
    - exact: (allP HbdS _ Hmem).
    - exact: (allP HbdNf _ Hmem).
  case HbS : (b \in cl) Hmap => [] [Hcl' Hnf''].
  - (* REMOVE: cl' = rem b cl, nf' = foata_nf (b :: nf) *)
    rewrite -Hnf''.
    apply/allP => x Hx.
    have := perm_mem (foata_nf_perm_eq crel (b :: nf)) x.
    rewrite Hx => /esym; rewrite inE => /orP [/eqP -> | Hx_nf].
    + exact: Hb_bd.
    + exact: (allP HbdNf _ Hx_nf).
  - (* ADD: cl' = insort b cl, nf' = foata_nf (rem b nf) *)
    rewrite -Hnf''.
    apply/allP => x Hx.
    have := perm_mem (foata_nf_perm_eq crel (rem_first_occ b nf)) x.
    rewrite Hx => /esym => Hx_rem.
    exact: (allP HbdNf _ (mem_rem_first_occ Hx_rem)).
apply/andP; split; last first.
  (* Boundedness of cl' *)
  rewrite /sri_map -/(@sri_pivot crel) in Hmap.
  set b := @sri_pivot crel cl nf in Hmap.
  have Hb_mem : b \in cl ++ nf.
    exact: (@sri_pivot_mem crel cl nf Hpos).
  have Hb_bd : b < Tg.
    rewrite mem_cat in Hb_mem; case/orP: Hb_mem => Hmem.
    - exact: (allP HbdS _ Hmem).
    - exact: (allP HbdNf _ Hmem).
  case HbS : (b \in cl) Hmap => [] [Hcl' Hnf''].
  - (* REMOVE: cl' = rem b cl *)
    rewrite -Hcl'.
    apply/allP => x Hx.
    exact: (allP HbdS _ (mem_rem_first_occ Hx)).
  - (* ADD: cl' = insort b cl *)
    rewrite -Hcl'.
    apply/allP => x Hx.
    have := perm_mem (perm_insort b cl) x.
    rewrite Hx => /esym; rewrite inE => /orP [/eqP -> | Hx_cl].
    + exact: Hb_bd.
    + exact: (allP HbdS _ Hx_cl).
apply/andP; split; last first.
  by rewrite Hnf' eqxx.
apply/andP; split; last first.
  exact: Hsorted'.
apply/andP; split; last first.
  exact: Hapc'.
by rewrite Htotal Hsz.
Qed.

(* Common tactic for extracting fields from sri_pair_valid *)
(* 2. sri_map is an involution on valid pairs *)
Lemma sri_pair_map_invol (p : sri_pair) (L : nat) :
  0 < L ->
  sri_pair_valid p L ->
  sri_pair_map (sri_pair_map p) = p.
Proof.
move=> HL Hv.
rewrite /sri_pair_map /sp_clique /sp_nf.
move: Hv; rewrite /sri_pair_valid /sp_clique /sp_nf.
case: p => [cl nf] /=.
move/andP => [/andP [/andP [/andP [/andP [/eqP Hsz Hapc] Hsorted] /eqP Hnf] HbdS] HbdNf].
have Hpos : 0 < size cl + size nf by rewrite Hsz.
have Hapc' : @all_pairs_comm crel cl.
  exact: Hapc.
have := @sri_involution crel crel_sym crel_irrefl cl nf Hpos Hapc' Hsorted Hnf.
by case: (@sri_map crel cl nf) => [cl' nf'] /= ->.
Qed.

(* 3. sri_map has no fixed points *)
Lemma sri_pair_map_no_fix (p : sri_pair) (L : nat) :
  0 < L ->
  sri_pair_valid p L ->
  sri_pair_map p != p.
Proof.
move=> HL Hv.
rewrite /sri_pair_map /sp_clique /sp_nf.
move: Hv; rewrite /sri_pair_valid /sp_clique /sp_nf.
case: p => [cl nf] /=.
move/andP => [/andP [/andP [/andP [/andP [/eqP Hsz _] _] _] _] _].
have Hpos : 0 < size cl + size nf by rewrite Hsz.
have := @sri_no_fixpoints crel cl nf Hpos.
case: (@sri_map crel cl nf) => [cl' nf'] /= Hne.
apply/eqP => /= [] [Hcl Hnf].
by apply: Hne; congr pair.
Qed.

(* 4. sri_map flips sign *)
Lemma sri_pair_map_flip (p : sri_pair) (L : nat) :
  0 < L ->
  sri_pair_valid p L ->
  sri_pair_sign (sri_pair_map p) = ~~ sri_pair_sign p.
Proof.
move=> HL Hv.
rewrite /sri_pair_map /sri_pair_sign /sp_clique /sp_nf.
move: Hv; rewrite /sri_pair_valid /sp_clique /sp_nf.
case: p => [cl nf] /=.
move/andP => [/andP [/andP [/andP [/andP [/eqP Hsz _] _] _] _] _].
have Hpos : 0 < size cl + size nf by rewrite Hsz.
rewrite /sri_map.
case HbS : (@sri_pivot crel cl nf \in cl).
- (* REMOVE case: size decreases by 1 *)
  rewrite /= size_rem_first_occ //.
  have Hgt : 0 < size cl by case: (cl) HbS => //; rewrite in_nil.
  by rewrite -{2}(prednK Hgt) oddS negbK.
- (* ADD case: size increases by 1 *)
  by rewrite /= size_insort oddS negbK.
Qed.

(* --- Helper lemmas for alternating count proof --- *)

(* Completeness of all_words: if size and bounds match, word is in all_words *)
Lemma all_words_complete (Tg' L : nat) (w : seq nat) :
  size w = L -> all (fun i => i < Tg') w -> w \in all_words Tg' L.
Proof.
elim: L w => [|L IH] w /=.
  by move=> /size0nil ->.
case: w => [|a w'] //= [Hsz] /andP [Ha Hbd].
apply/flattenP; exists (map (cons a) (all_words Tg' L)).
  by apply/mapP; exists a => //; rewrite mem_iota add0n.
by apply/mapP; exists w' => //; exact: IH.
Qed.

(* subseqs_k produces unique lists when the input is unique *)
Lemma subseqs_k_notin a k s :
  a \notin s -> forall t, t \in subseqs_k k s -> a \notin t.
Proof.
move=> Ha t Ht.
have Hsub := subseqs_k_subseq Ht.
apply/negP => Hin.
by move/negP: Ha; apply; exact: (mem_subseq Hsub).
Qed.

Lemma subseqs_k_uniq k s : uniq s -> uniq (subseqs_k k s).
Proof.
elim: s k => [|a s IHs] [|k] //= /andP [Ha Hs].
rewrite cat_uniq (map_inj_uniq (f := cons a)); last first.
  by move=> x y [] ->.
rewrite IHs // IHs //= andbT.
apply/hasPn => x Hx.
(* x \in subseqs_k k.+1 s, so a \notin x *)
have Hx_no_a := subseqs_k_notin Ha Hx.
(* x \notin [seq a :: t | ...] because x doesn't start with a *)
apply/negP => /mapP [t _ Hxt].
by rewrite Hxt /= inE eqxx in Hx_no_a.
Qed.

(* cliques_of_size produces unique lists *)
Lemma cliques_of_size_uniq (Tg' k : nat) (comm : nat -> nat -> bool) :
  uniq (cliques_of_size Tg' k comm).
Proof.
rewrite /cliques_of_size; apply: filter_uniq.
exact: subseqs_k_uniq (iota_uniq 0 Tg').
Qed.

(* Elements of cliques_of_size have the right size *)
Lemma cliques_of_size_size (Tg' k : nat) (comm : nat -> nat -> bool) cl :
  cl \in cliques_of_size Tg' k comm -> size cl = k.
Proof.
rewrite /cliques_of_size mem_filter => /andP [_ Hcl].
exact: subseqs_k_size Hcl.
Qed.

(* Helper: membership in flatten of mapped cliques *)
Lemma mem_cliques_flat cl ks :
  cl \in flatten [seq cliques_of_size Tg k crel | k <- ks] ->
  exists2 k, k \in ks & cl \in cliques_of_size Tg k crel.
Proof.
elim: ks => [|k ks IH] //=.
rewrite mem_cat => /orP [Hcl | /IH [k' Hk' Hcl']].
- by exists k => //; rewrite inE eqxx.
- by exists k' => //; rewrite inE Hk' orbT.
Qed.

(* The flat list of all cliques is unique *)
Lemma cliques_flat_uniq (L : nat) :
  uniq (flatten [seq cliques_of_size Tg k crel | k <- iota 0 L.+1]).
Proof.
elim: L => [|L IH].
  by rewrite /= cats0; exact: cliques_of_size_uniq.
have Hiota : iota 0 L.+2 = iota 0 L.+1 ++ [:: L.+1].
  by rewrite -addn1 iotaD add0n /=.
rewrite Hiota map_cat flatten_cat.
have Hflat_cats0 : flatten [seq cliques_of_size Tg k crel | k <- [:: L.+1]] =
  cliques_of_size Tg L.+1 crel by rewrite /= cats0.
rewrite Hflat_cats0.
rewrite cat_uniq IH cliques_of_size_uniq !andbT.
apply/hasPn => cl Hcl1.
have Hsz1 : size cl = L.+1 := cliques_of_size_size Hcl1.
apply/negP => Hcl2.
have [k Hk Hcl_k] := mem_cliques_flat Hcl2.
have Hsz2 : size cl = k := cliques_of_size_size Hcl_k.
rewrite mem_iota in Hk; case/andP: Hk => _ Hk.
by rewrite Hsz1 in Hsz2; rewrite Hsz2 ltnn in Hk.
Qed.

(* Every element of all_sri_pairs is valid *)
Lemma all_sri_pairs_valid p (L : nat) :
  p \in all_sri_pairs L -> sri_pair_valid p L.
Proof.
move=> Hp; rewrite /sri_pair_valid /sp_clique /sp_nf.
case Hpair : p Hp => [cl nf] /=.
rewrite /all_sri_pairs => Hp.
(* The comprehension is flatten [seq [seq (c, n) | n <- ...] | c <- ...] *)
(* Destruct membership in this flatten *)
have /flattenP [sub Hsub Hpin] := Hp.
have /mapP [cl' Hcl' Hsub_eq] := Hsub.
rewrite Hsub_eq in Hpin.
have /mapP [nf' Hnf' [Hcl_eq Hnf_eq]] := Hpin.
subst cl nf.
(* Now cl' is in cls, nf' is in nfs cl' *)
have [k Hk Hcl_k] := mem_cliques_flat Hcl'.
rewrite mem_iota in Hk; case/andP: Hk => [_ Hk].
have Hcl_comm : all_pairs_comm_sorted crel cl'.
  by move: Hcl_k; rewrite /cliques_of_size mem_filter => /andP [].
have Hcl_sub : subseq cl' (iota 0 Tg).
  move: Hcl_k; rewrite /cliques_of_size mem_filter => /andP [_ Hs].
  exact: subseqs_k_subseq Hs.
have Hcl_sorted : sorted ltn cl'.
  have Htrans : transitive ltn by move=> b a c; exact: ltn_trans.
  exact: (subseq_sorted Htrans Hcl_sub (iota_ltn_sorted 0 Tg)).
have Hcl_bd : all (fun i => i < Tg) cl'.
  apply/allP => x Hx; have := mem_subseq Hcl_sub Hx.
  by rewrite mem_iota add0n.
have Hcl_sz : size cl' = k := cliques_of_size_size Hcl_k.
(* nf' is in undup, so it's a foata_nf of some word *)
move: Hnf'; rewrite mem_undup => /mapP [w Hw ->].
have Hw_sz := all_words_size Hw.
have Hw_bd := all_words_bounded Hw.
have Hnf_sz := size_foata_nf crel w.
have Hnf_bd : all (fun i => i < Tg) (foata_nf crel w).
  apply/allP => x Hx.
  have := perm_mem (foata_nf_perm_eq crel w) x; rewrite Hx => /esym Hxw.
  exact: (allP Hw_bd _ Hxw).
have Hnf_idem : foata_nf crel (foata_nf crel w) = foata_nf crel w.
  exact: foata_nf_idempotent.
(* Now assemble the validity *)
apply/andP; split; last exact: Hnf_bd.
apply/andP; split; last exact: Hcl_bd.
apply/andP; split; last by rewrite Hnf_idem eqxx.
apply/andP; split; last exact: Hcl_sorted.
apply/andP; split; last exact: Hcl_comm.
by rewrite Hnf_sz Hw_sz Hcl_sz subnKC // -ltnS.
Qed.

(* Membership in cliques_of_size: a sequence is a clique iff it passes the filter *)
Lemma mem_cliques_of_size cl k :
  cl \in cliques_of_size Tg k crel =
  (cl \in subseqs_k k (iota 0 Tg)) && all_pairs_comm_sorted crel cl.
Proof. by rewrite /cliques_of_size mem_filter andbC. Qed.

(* Sorted ltn sequence with bounded elements is subseq of iota *)
Lemma sorted_ltn_subseq_iota (s : seq nat) (n : nat) :
  sorted ltn s -> all (fun i => i < n) s -> subseq s (iota 0 n).
Proof.
move=> Hsorted Hbd.
apply/subseq_uniqP; first exact: iota_uniq.
(* Goal: s = [seq x <- iota 0 n | x \in s] *)
have Htrans : transitive ltn by move=> b a c; exact: ltn_trans.
have Hirr : irreflexive ltn by move=> x; exact: ltnn.
have Hsorted2 : sorted ltn [seq x <- iota 0 n | x \in s].
  apply: (subseq_sorted Htrans (filter_subseq _ _)).
  exact: iota_ltn_sorted.
have Hmem : s =i [seq x <- iota 0 n | x \in s].
  move=> x; rewrite mem_filter mem_iota add0n.
  case Hxs : (x \in s) => //=.
  by rewrite (allP Hbd _ Hxs).
exact: (irr_sorted_eq Htrans Hirr Hsorted Hsorted2 Hmem).
Qed.

(* Completeness: every valid pair is in all_sri_pairs *)
Lemma valid_in_all_sri_pairs p (L : nat) :
  sri_pair_valid p L -> p \in all_sri_pairs L.
Proof.
rewrite /sri_pair_valid /sp_clique /sp_nf.
case: p => [cl nf] /=.
move/andP => [/andP [/andP [/andP [/andP [/eqP Hsz Hapc] Hsorted] /eqP Hnf] HbdS] HbdNf].
rewrite /all_sri_pairs.
apply: allpairs_f_dep.
- (* cl is in the flat list of cliques *)
  apply/flattenP.
  exists (cliques_of_size Tg (size cl) crel).
    apply/mapP; exists (size cl) => //.
    rewrite mem_iota /= add0n -Hsz; exact: leq_addr.
  rewrite mem_cliques_of_size Hapc andbT.
  apply: mem_subseqs_k => //.
  exact: sorted_ltn_subseq_iota Hsorted HbdS.
- (* nf is in the undup list *)
  rewrite mem_undup; apply/mapP; exists nf; last by rewrite Hnf.
  apply: all_words_complete; last exact: HbdNf.
  by rewrite -[LHS](@addKn (size cl)) Hsz.
Qed.

(* Uniqueness of all_sri_pairs *)
Lemma all_sri_pairs_uniq (L : nat) : uniq (all_sri_pairs L).
Proof.
rewrite /all_sri_pairs.
apply: allpairs_uniq_dep.
- exact: cliques_flat_uniq.
- move=> cl _; exact: undup_uniq.
- move=> [cl1 nf1] [cl2 nf2] _ _ /= [-> ->]; exact: erefl.
Qed.

(* Closure: sri_pair_map maps valid pairs to the enumerated list *)
Lemma sri_pair_map_closed p (L : nat) :
  0 < L -> p \in all_sri_pairs L -> sri_pair_map p \in all_sri_pairs L.
Proof.
move=> HL Hp.
apply: valid_in_all_sri_pairs.
exact: sri_map_preserves_valid HL (all_sri_pairs_valid Hp).
Qed.

(* The alternating identity in terms of counts over the pair list *)
Lemma sri_alternating_count (L : nat) :
  0 < L ->
  let pairs := all_sri_pairs L in
  count sri_pair_sign pairs = count (predC sri_pair_sign) pairs.
Proof.
move=> HL /=.
apply: involution_sign_count_local.
- exact: all_sri_pairs_uniq.
- move=> x Hx; exact: sri_pair_map_invol HL (all_sri_pairs_valid Hx).
- move=> x Hx; exact: sri_pair_map_no_fix HL (all_sri_pairs_valid Hx).
- move=> x Hx; exact: sri_pair_map_flip HL (all_sri_pairs_valid Hx).
- move=> x Hx; exact: sri_pair_map_closed HL Hx.
Qed.

(* --- Helper lemmas for count decomposition --- *)

(* Count over allpairs with sign depending only on first component *)
Lemma count_allpairs_dep (T1 T2 : eqType) (f : T1 -> seq T2)
  (g : T1 * T2 -> bool) (s : seq T1) :
  count g [seq (x, y) | x <- s, y <- f x] =
  sumn [seq count g [seq (x, y) | y <- f x] | x <- s].
Proof.
by rewrite count_flatten -map_comp.
Qed.

(* When the predicate depends only on the first component *)
Lemma count_pair_fst (T1 T2 : Type) (p : T1 -> bool) (x : T1)
  (ys : seq T2) :
  count (fun q : T1 * T2 => p q.1) [seq (x, y) | y <- ys] =
  if p x then size ys else 0.
Proof.
rewrite count_map /preim /=.
by case: (p x); [rewrite count_predT | rewrite count_pred0].
Qed.

(* Convert the count identity to the nat-level alternating sum *)
(* Decomposition of pair count by sign *)
(* count positive = sum_{k even} c_k * m_{L-k} *)
(* count negative = sum_{k odd} c_k * m_{L-k} *)
Lemma count_sign_decomp (L : nat) :
  0 < L ->
  count sri_pair_sign (all_sri_pairs L) =
  sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel
       | k <- iota 0 L.+1 & ~~ odd k].
Proof.
move=> HL.
rewrite /all_sri_pairs count_allpairs_dep.
(* Step 1: Simplify count over pairs to size-based condition *)
transitivity (sumn [seq (if ~~ odd (size cl) then
  size (undup (map (foata_nf crel) (all_words Tg (L - size cl))))
  else 0) | cl <- flatten [seq cliques_of_size Tg k crel | k <- iota 0 L.+1]]).
  congr sumn; apply: eq_map => cl /=.
  rewrite /sri_pair_sign /sp_clique count_map /preim /=.
  by case: (~~ odd (size cl)); [rewrite count_predT | rewrite count_pred0].
(* Step 2: Group by k using induction on iota list *)
have map_const_nseq : forall (T : Type) (c : nat) (s : seq T),
  [seq c | _ <- s] = nseq (size s) c.
  by move=> T' c; elim=> //= a s'' ->.
have sumn_map_const : forall (T : Type) (c : nat) (s : seq T),
  sumn [seq c | _ <- s] = size s * c.
  by move=> T' c s'; rewrite map_const_nseq sumn_nseq mulnC.
set h := fun cl : seq nat => if ~~ odd (size cl) then
  size (undup (map (foata_nf crel) (all_words Tg (L - size cl)))) else 0.
transitivity (sumn [seq (if ~~ odd k then
  clique_count Tg k crel * n_traces_natB Tg (L - k) crel
  else 0) | k <- iota 0 L.+1]).
  elim: (iota 0 L.+1) => [|k ks IH] //=.
  rewrite map_cat sumn_cat IH; congr (_ + _).
  case Hodd : (~~ odd k).
  - rewrite /clique_count.
    transitivity (sumn [seq n_traces_natB Tg (L - k) crel
      | _ <- cliques_of_size Tg k crel]).
      congr sumn; apply/eq_in_map => cl Hcl /=.
      rewrite /h (cliques_of_size_size Hcl) Hodd /n_traces_natB //.
    by rewrite sumn_map_const /clique_count mulnC.
  - transitivity (sumn [seq 0 | _ <- cliques_of_size Tg k crel]).
      congr sumn; apply/eq_in_map => cl Hcl /=.
      by rewrite /h (cliques_of_size_size Hcl) Hodd.
    by rewrite sumn_map_const muln0.
(* Step 3: Filter out zero terms *)
(* sumn [seq if p k then f k else 0 | k <- s] = sumn [seq f k | k <- s & p k] *)
have sumn_if_filter : forall (p : pred nat) (f : nat -> nat) (s : seq nat),
  sumn [seq (if p x then f x else 0) | x <- s] = sumn [seq f x | x <- s & p x].
  move=> p' f'; elim=> [|x' s'' IHs''] //.
  rewrite /sumn /= -/(sumn _) -/(sumn _) IHs''.
  by case: (p' x').
exact: sumn_if_filter.
Qed.

Lemma count_nsign_decomp (L : nat) :
  0 < L ->
  count (predC sri_pair_sign) (all_sri_pairs L) =
  sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel
       | k <- iota 0 L.+1 & odd k].
Proof.
move=> HL.
rewrite /all_sri_pairs count_allpairs_dep.
transitivity (sumn [seq (if odd (size cl) then
  size (undup (map (foata_nf crel) (all_words Tg (L - size cl))))
  else 0) | cl <- flatten [seq cliques_of_size Tg k crel | k <- iota 0 L.+1]]).
  congr sumn; apply: eq_map => cl /=.
  rewrite count_map /preim /=.
  rewrite (eq_count (a2 := fun _ => odd (size cl))); last first.
    by move=> y; rewrite /predC /sri_pair_sign /sp_clique /= negbK.
  by case: (odd (size cl)); [rewrite count_predT | rewrite count_pred0].
have map_const_nseq : forall (T : Type) (c : nat) (s : seq T),
  [seq c | _ <- s] = nseq (size s) c.
  by move=> T' c; elim=> //= a s'' ->.
have sumn_map_const : forall (T : Type) (c : nat) (s : seq T),
  sumn [seq c | _ <- s] = size s * c.
  by move=> T' c s'; rewrite map_const_nseq sumn_nseq mulnC.
set g := fun cl : seq nat => if odd (size cl) then
  size (undup (map (foata_nf crel) (all_words Tg (L - size cl)))) else 0.
transitivity (sumn [seq (if odd k then
  clique_count Tg k crel * n_traces_natB Tg (L - k) crel
  else 0) | k <- iota 0 L.+1]).
  elim: (iota 0 L.+1) => [|k ks IH] //=.
  rewrite map_cat sumn_cat IH; congr (_ + _).
  case Hodd : (odd k).
  - rewrite /clique_count.
    transitivity (sumn [seq n_traces_natB Tg (L - k) crel
      | _ <- cliques_of_size Tg k crel]).
      congr sumn; apply/eq_in_map => cl Hcl /=.
      rewrite /g (cliques_of_size_size Hcl) Hodd /n_traces_natB //.
    by rewrite sumn_map_const /clique_count mulnC.
  - transitivity (sumn [seq 0 | _ <- cliques_of_size Tg k crel]).
      congr sumn; apply/eq_in_map => cl Hcl /=.
      by rewrite /g (cliques_of_size_size Hcl) Hodd.
    by rewrite sumn_map_const muln0.
have sumn_if_filter : forall (p : pred nat) (f : nat -> nat) (s : seq nat),
  sumn [seq (if p x then f x else 0) | x <- s] = sumn [seq f x | x <- s & p x].
  move=> p' f'; elim=> [|x' s'' IHs''] //.
  rewrite /sumn /= -/(sumn _) -/(sumn _) IHs''.
  by case: (p' x').
exact: sumn_if_filter.
Qed.

Lemma clique_count_0 : clique_count Tg 0 crel = 1.
Proof. exact: clique_count0. Qed.

Lemma sri_alternating_identity (L : nat) :
  0 < L ->
  n_traces_natB Tg L crel +
  sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel
       | k <- iota 1 L & ~~ odd k] =
  sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel
       | k <- iota 1 L & odd k].
Proof.
move=> HL.
have Hcount := sri_alternating_count HL.
rewrite /= in Hcount.
have Hpos := count_sign_decomp HL.
have Hneg := count_nsign_decomp HL.
rewrite Hpos in Hcount.
rewrite Hneg in Hcount.
(* Hcount: sumn [... iota 0 L.+1 & ~~ odd k] = sumn [... iota 0 L.+1 & odd k] *)
(* iota 0 L.+1 = 0 :: iota 1 L *)
(* filter (~~ odd) (0 :: iota 1 L): odd 0 = false, so ~~ false = true, includes 0 *)
(* filter (odd) (0 :: iota 1 L): odd 0 = false, excludes 0 *)
rewrite /= subn0 in Hcount.
(* LHS of Hcount: clique_count Tg 0 crel * n_traces_natB Tg L crel + even_sum *)
rewrite clique_count_0 mul1n in Hcount.
exact: Hcount.
Qed.

End sri_alternating.

(* --- clique_traces_aux properties --- *)

Lemma cta_size (Tg : nat) (crel : nat -> nat -> bool) fuel memo :
  size (clique_traces_aux Tg crel fuel memo) = size memo + fuel.
Proof.
elim: fuel memo => [|fuel IH] memo /=; first by rewrite addn0.
by rewrite IH size_rcons addSnnS.
Qed.

Lemma cta_nth_old (Tg : nat) (crel : nat -> nat -> bool) fuel memo i :
  i < size memo ->
  nth 0 (clique_traces_aux Tg crel fuel memo) i = nth 0 memo i.
Proof.
elim: fuel memo => [|fuel IH] memo //= Hi.
rewrite IH; first by rewrite nth_rcons Hi.
by rewrite size_rcons ltnS ltnW.
Qed.

Lemma cta_last_step (Tg : nat) (crel : nat -> nat -> bool) fuel memo :
  nth 0 (clique_traces_aux Tg crel fuel.+1 memo) (size memo + fuel) =
  clique_step Tg crel (clique_traces_aux Tg crel fuel memo).
Proof.
elim: fuel memo => [|fuel IH] memo /=.
  by rewrite addn0 nth_rcons ltnn eqxx.
have -> : size memo + fuel.+1 = size (rcons memo (clique_step Tg crel memo)) + fuel.
  by rewrite size_rcons addSnnS.
exact: IH.
Qed.

Lemma cta_stable (Tg : nat) (crel : nat -> nat -> bool) fuel1 fuel2 memo i :
  i < size memo + fuel1 -> fuel1 <= fuel2 ->
  nth 0 (clique_traces_aux Tg crel fuel2 memo) i =
  nth 0 (clique_traces_aux Tg crel fuel1 memo) i.
Proof.
move: fuel1 memo i; elim: fuel2 => [|fuel2 IH] [|fuel1] memo i Hi Hle //=.
- rewrite addn0 in Hi.
  rewrite (@cta_nth_old _ _ fuel2); last by rewrite size_rcons ltnS ltnW.
  by rewrite nth_rcons Hi.
- apply: (IH fuel1) => //.
  by rewrite size_rcons addSnnS.
Qed.

Lemma cta_nth_eq (Tg : nat) (crel : nat -> nat -> bool) L i :
  i <= L ->
  nth 0 (clique_traces_aux Tg crel L [:: 1]) i = clique_traces Tg i crel.
Proof.
move=> Hi; rewrite /clique_traces.
by rewrite (@cta_stable _ _ i L [:: 1] i) // /= add1n ltnS.
Qed.

(* --- clique_traces recurrence --- *)

Lemma clique_traces_0 (Tg : nat) (crel : nat -> nat -> bool) :
  clique_traces Tg 0 crel = 1.
Proof. by rewrite /clique_traces /=. Qed.

Lemma clique_traces_rec (Tg : nat) (crel : nat -> nat -> bool) L :
  clique_traces Tg L.+1 crel =
  clique_step Tg crel [seq clique_traces Tg i crel | i <- iota 0 L.+1].
Proof.
have Hlast : clique_traces Tg L.+1 crel =
  clique_step Tg crel (clique_traces_aux Tg crel L [:: 1]).
  rewrite /clique_traces.
  have -> : L.+1 = (1 + L)%N by rewrite add1n.
  exact: cta_last_step.
rewrite Hlast; congr (clique_step Tg crel _).
apply: (@eq_from_nth _ 0).
  by rewrite cta_size /= add1n size_map size_iota.
move=> i; rewrite cta_size /= add1n => Hi.
have -> : nth 0 [seq clique_traces Tg i0 crel | i0 <- iota 0 L.+1] i =
          clique_traces Tg i crel.
  by rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite cta_nth_eq //; exact: ltnW.
Qed.

(* --- Extensionality: clique_traces and n_traces_natB are same for comm and comm_b --- *)

Lemma sumn_map_ext2 {A : eqType} (f g : A -> nat) (s : seq A) :
  (forall x, x \in s -> f x = g x) -> sumn (map f s) = sumn (map g s).
Proof.
elim: s => [|x s IH] //= Hfg.
rewrite Hfg; last by rewrite mem_head.
congr (_ + _); apply: IH => y Hy; apply: Hfg; by rewrite inE Hy orbT.
Qed.

Lemma clique_step_comm_b (Tg : nat) (crel : nat -> nat -> bool) memo :
  (forall a b, a < Tg -> b < Tg -> crel a b -> crel b a) ->
  (forall a, ~~ crel a a) ->
  clique_step Tg crel memo = clique_step Tg (comm_b Tg crel) memo.
Proof.
move=> Hsym Hirr; rewrite /clique_step.
congr (_ - _); apply: sumn_map_ext2 => k _;
by rewrite (@clique_count_comm_b Tg k crel Hsym Hirr).
Qed.

Lemma clique_traces_comm_b (Tg L : nat) (crel : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> crel a b -> crel b a) ->
  (forall a, ~~ crel a a) ->
  clique_traces Tg L crel = clique_traces Tg L (comm_b Tg crel).
Proof.
move=> Hsym Hirr; rewrite /clique_traces; congr (nth 0 _ L).
suff Haux : forall fuel memo,
  clique_traces_aux Tg crel fuel memo =
  clique_traces_aux Tg (comm_b Tg crel) fuel memo.
  exact: Haux.
elim => [|fuel IH] memo //=.
by rewrite -(@clique_step_comm_b Tg crel _ Hsym Hirr) -IH.
Qed.

(* --- The SRI recurrence for n_traces_natB --- *)
(* This is the key lemma: n_traces_natB satisfies the same recurrence as clique_traces *)

Lemma nth_map_iota_sub (f : nat -> nat) L k :
  0 < k -> k <= L ->
  nth 0 [seq f i | i <- iota 0 L] (L - k) = f (L - k).
Proof.
move=> Hk HkL.
have HLk : L - k < L by rewrite ltn_subrL Hk /= (leq_trans Hk).
rewrite (nth_map 0); last by rewrite size_iota.
by rewrite nth_iota // add0n.
Qed.

Lemma n_traces_recurrence (Tg : nat) (crel : nat -> nat -> bool) L :
  (forall a b, crel a b -> crel b a) ->
  (forall a, ~~ crel a a) ->
  0 < L ->
  n_traces_natB Tg L crel = clique_step Tg crel
    [seq n_traces_natB Tg i crel | i <- iota 0 L].
Proof.
move=> Hcsym Hcirr HL.
set memo := [seq n_traces_natB Tg i crel | i <- iota 0 L].
(* The alternating identity from the SRI *)
have Halt := @sri_alternating_identity Tg crel Hcsym Hcirr L HL.
(* Halt: m_L + neg_sum = pos_sum *)
(* clique_step = pos_sum' - neg_sum' where sums are over memo *)
(* We need: the sums over memo match the sums in Halt *)
rewrite /clique_step size_map size_iota.
(* Need to show the sums match *)
suff Hpos : sumn [seq clique_count Tg k crel * nth 0 memo (L - k) | k <- iota 1 L & odd k] =
            sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel | k <- iota 1 L & odd k].
suff Hneg : sumn [seq clique_count Tg k crel * nth 0 memo (L - k) | k <- iota 1 L & ~~ odd k] =
            sumn [seq clique_count Tg k crel * n_traces_natB Tg (L - k) crel | k <- iota 1 L & ~~ odd k].
  rewrite Hpos Hneg.
  (* Now: m_L = pos - neg, where m_L + neg = pos (from Halt) *)
  by rewrite -Halt addnK.
- apply: sumn_map_ext2 => k Hk; congr (_ * _).
  have Hk1 : 0 < k.
    by move: Hk; rewrite mem_filter => /andP [_ Hk'];
       rewrite mem_iota in Hk'; case/andP: Hk'.
  have Hk2 : k <= L.
    by move: Hk; rewrite mem_filter => /andP [_ Hk'];
       rewrite mem_iota add1n in Hk'; case/andP: Hk' => _ ; rewrite ltnS.
  exact: nth_map_iota_sub Hk1 Hk2.
- apply: sumn_map_ext2 => k Hk; congr (_ * _).
  have Hk1 : 0 < k.
    by move: Hk; rewrite mem_filter => /andP [_ Hk'];
       rewrite mem_iota in Hk'; case/andP: Hk'.
  have Hk2 : k <= L.
    by move: Hk; rewrite mem_filter => /andP [_ Hk'];
       rewrite mem_iota add1n in Hk'; case/andP: Hk' => _ ; rewrite ltnS.
  exact: nth_map_iota_sub Hk1 Hk2.
Qed.

(* --- Main theorem --- *)

Lemma cartier_foata (Tg L : nat) (comm : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> comm a b -> comm b a) ->
  (forall a, ~~ comm a a) ->
  clique_traces Tg L comm = n_traces_natB Tg L comm.
Proof.
move=> Hsym Hirr.
set cb := comm_b Tg comm.
have Hcb_sym : forall a b, cb a b -> cb b a := @comm_b_sym Tg comm Hsym.
have Hcb_irr : forall a, ~~ cb a a := @comm_b_irrefl Tg comm Hirr.
rewrite (@n_traces_natB_comm_b Tg L comm Hsym Hirr) (@clique_traces_comm_b Tg L comm Hsym Hirr).
(* Strong induction on L *)
suff Hstrong : forall L', clique_traces Tg L' cb = n_traces_natB Tg L' cb
  by exact: Hstrong.
apply: (well_founded_induction_type (Wf_nat.well_founded_ltof _ id)).
move=> L' IH.
case: L' IH => [|L' IH].
  by move=> _; rewrite clique_traces_0 n_traces_natB_0.
rewrite clique_traces_rec.
rewrite (@n_traces_recurrence Tg cb L'.+1 Hcb_sym Hcb_irr (ltn0Sn L')).
congr (clique_step Tg cb _).
apply/eq_in_map => i.
rewrite mem_iota add0n => /andP [_ Hi].
apply: IH; rewrite /Wf_nat.ltof /=.
exact/ltP.
Qed.

Lemma clique_traces_eq_natB (Tg L : nat) (comm : nat -> nat -> bool) :
  (forall a b, a < Tg -> b < Tg -> comm a b -> comm b a) ->
  (forall a, ~~ comm a a) ->
  clique_traces Tg L comm = n_traces_natB Tg L comm.
Proof. exact: cartier_foata. Qed.
