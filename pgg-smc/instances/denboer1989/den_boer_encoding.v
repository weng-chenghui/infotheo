(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer input encoding: the AND function via fc_arrange                   *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism cyclic bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo.dumas2017dual.lib Require Import extra_entropy.
Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_group five_card_kim five_card_family.
From pgg_smc Require Import five_card_leakage.
From pgg_reconstruct Require Import input_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** den_boer_layout — the den Boer starting layout: the two committed bits
    encoded into the five-card arrangement as 'I_5 shares.
    @intent: map_tuple encode_bool over fc_arrange_tup of the input bits. *)
Definition den_boer_layout (ab : bool * bool) : 5.-tuple 'I_5 :=
  map_tuple encode_bool (fc_arrange_tup ab.1 ab.2).

(** den_boer_assemble_valid — the encoded den Boer arrangement is a valid
    sharing of a && b.
    @composes: den_boer_encoding. *)
Lemma den_boer_assemble_valid (ab : bool * bool) :
  fcI_valid (ab.1 && ab.2) (den_boer_layout ab).
Proof.
rewrite /fcI_valid /den_boer_layout /=.
rewrite -map_comp.
under eq_map => x do rewrite /comp decode_encode_bool.
rewrite map_id.
by have := fc_correct ab.1 ab.2 (k:=0) isT; rewrite /fc_shuffle rot0.
Qed.

(** den_boer_orbit — inputs with equal AND give layouts that differ by a cyclic
    rotation: the three a&&b=false inputs lie in one rotation orbit.
    @composes: den_boer_encoding. *)
Lemma den_boer_orbit (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists k : 'I_5, val (den_boer_layout ab') = rot k (val (den_boer_layout ab)).
Proof.
move=> H; move: H; case: ab => a b; case: ab' => a' b'.
case: a; case: b; case: a'; case: b' => //=; move=> _;
  first [ exists (inord 0); by rewrite inordK// rot0
        | exists (inord 1); by rewrite inordK
        | exists (inord 2); by rewrite inordK
        | exists (inord 3); by rewrite inordK
        | exists (inord 4); by rewrite inordK ].
Qed.

(** den_boer_orbit_perm — den_boer_orbit in the rp_monodromy reindex form the
    InputEncoding.ie_orbit field expects.
    @composes: den_boer_encoding. *)
Lemma den_boer_orbit_perm (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists g : pgg_gT FiveCardKim_M, g \in pgg_G FiveCardKim_M /\
    den_boer_layout ab' =
      [tuple tnth (den_boer_layout ab) (rp_monodromy five_card_plug g i) | i < 5].
Proof.
move=> H; case: (den_boer_orbit H) => k Hk.
have Gcyc : pgg_G FiveCardKim_M = <[five_card_group.fc_sigma]>.
  rewrite /pgg_G /FiveCardKim_M /=.
  apply/val_inj => /=.
  apply/eqP; rewrite eqEsubset; apply/andP; split.
    rewrite gen_subG; apply/subsetP => x /imsetP[i _ ->].
    by rewrite fc_kim_sigmasE; exact: mem_cycle.
  rewrite cycle_subG; apply: mem_gen; apply/imsetP.
  by exists (@Ordinal 5 1 isT) => //; rewrite fc_kim_sigmasE expg1.
exists (five_card_group.fc_sigma ^+ k)%g; split.
  by rewrite Gcyc; exact: mem_cycle.
have Hmono : forall i,
    rp_monodromy five_card_plug (fc_sigma ^+ k)%g i = (fc_sigma ^+ k)%g i by [].
apply: eq_from_tnth => i.
rewrite tnth_mktuple Hmono.
rewrite (tnth_nth i) (tnth_nth i) Hk.
set s := \val (den_boer_layout ab).
have Hs : size s = 5 by rewrite /s size_tuple.
have nth_rot_mod : forall (n p : nat) (xs : seq 'I_5),
    n < 5 -> p < 5 -> size xs = 5 ->
    nth i (rot n xs) p = nth i xs ((p + n) %% 5).
  move=> n p xs Hn Hp Hxs.
  rewrite /rot nth_cat size_drop Hxs.
  case: (ltnP p (5 - n)) => Hpn.
    by rewrite nth_drop addnC modn_small // addnC -ltn_subRL.
  have Hqn : p - (5 - n) < n by rewrite ltn_subLR // subnK ?(ltnW Hn).
  rewrite nth_take //.
  have Heq2 : p + n - 5 = p - (5 - n) by rewrite subnBA ?(ltnW Hn).
  have Hpn5 : (5 <= p + n)%N by rewrite -(subnK (ltnW Hn)) leq_add2r.
  by rewrite -Heq2 -(subnK Hpn5) modnDr modn_small ?addnK //
     Heq2 (leq_ltn_trans (leq_subr _ _) Hp).
rewrite nth_rot_mod //.
by rewrite -/s fc_sigma_pow_val.
Qed.

(** den_boer_encoding — the AND-function input encoding through five_card_plug.
    @main correctness: assembles input bits into a valid five-card layout whose
    equal-output orbit is the cyclic cut group. *)
Definition den_boer_encoding : InputEncoding five_card_plug (bool * bool) :=
  @MkInputEncoding FiveCardKim_M bool five_card_plug (bool * bool)
    den_boer_layout
    (fun ab => ab.1 && ab.2)
    den_boer_assemble_valid
    den_boer_orbit_perm.

(******************************************************************************)
(* Perfect input privacy                                                      *)
(*                                                                            *)
(* The two input bits carry no information about each other beyond the output *)
(* a && b: conditioned on the secret, the inputs are independent of any        *)
(* partial view of the dealt row. The only non-trivial content is that the    *)
(* three a && b = false inputs (0,0), (0,1), (1,0) deal identically            *)
(* distributed rows, since their layouts lie in one cyclic rotation orbit      *)
(* (den_boer_orbit).                                                          *)
(******************************************************************************)

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section den_boer_input_privacy.

Import GRing.Theory Num.Theory.

Variable R : realType.

(** Inputs — the two committed input bits of an outcome.
    @intent: the pair (a, b) of input bits, the random variable whose
    conditional independence from the partial view given the secret a && b is
    the perfect-input-privacy statement. *)
Definition Inputs : {RV (P R) -> bool * bool} :=
  fun w => let: (a, b, _) := w in (a, b).

(** den_boer_view_count_eq — inputs with equal output deal a partial view with
    the same fibre count: for any position list and view value, the number of
    cuts realising it is the same across the orbit.
    @composes: den_boer_input_private. *)
Lemma den_boer_view_count_eq (A : seq nat) (b : (size A).-tuple bool)
    (x x' : bool * bool) :
  x.1 && x.2 = x'.1 && x'.2 ->
  #|preim [% Inputs, ViewA R A] (pred1 (x, b))|
  = #|preim [% Inputs, ViewA R A] (pred1 (x', b))|.
Proof.
move=> Hxx.
rewrite -!sum1_card.
rewrite (eq_bigl (fun w : Omega =>
   (Inputs w == x) && (ViewA R A w == b))); last first.
  by move=> w /=; rewrite inE /= xpair_eqE.
rewrite [in RHS](eq_bigl (fun w : Omega =>
   (Inputs w == x') && (ViewA R A w == b))); last first.
  by move=> w /=; rewrite inE /= xpair_eqE.
rewrite big_mkcond /= [in RHS]big_mkcond /=.
rewrite (stepO (fun w => if (Inputs w == x) && (ViewA R A w == b)
                         then 1 else 0))%N.
rewrite [in RHS](stepO (fun w => if (Inputs w == x') && (ViewA R A w == b)
                                 then 1 else 0))%N.
have InE : forall (ab : bool * bool) (k : 'I_5), Inputs (ab, k) = ab.
  by move=> [a0 b0] k.
under eq_bigr=> ab _ do under eq_bigr=> k _ do rewrite InE.
rewrite [in RHS](eq_bigr (fun ab => \sum_(k<5)
    (if (ab == x') && (ViewA R A (ab, k) == b) then 1 else 0)%N)); last first.
  by move=> ab _; apply: eq_bigr=> k _; rewrite InE.
have factor : forall (y : bool * bool) (ab : bool * bool),
    (\sum_(k<5) (if (ab == y) && (ViewA R A (ab, k) == b) then 1 else 0))%N
    = (if ab == y then \sum_(k<5) (if ViewA R A (ab, k) == b then 1 else 0)
       else 0)%N.
  move=> y ab; case: ifP => aby.
    by under eq_bigr=> k _ do rewrite andTb.
  by rewrite big1 // => k _; rewrite andFb.
under eq_bigr=> ab _ do rewrite (factor x ab).
under [in RHS]eq_bigr=> ab _ do rewrite (factor x' ab).
rewrite -big_mkcond /= -[in RHS]big_mkcond /=.
rewrite big_pred1_eq big_pred1_eq.
have orbit : exists j : 'I_5, fc_arrange x'.1 x'.2 = rot j (fc_arrange x.1 x.2).
  move: Hxx; case: x => a b0; case: x' => a' b' /=.
  case: a; case: b0; case: a'; case: b' => //= _;
    first [ exists (inord 0); by rewrite inordK// rot0
          | exists (inord 1); by rewrite inordK
          | exists (inord 2); by rewrite inordK
          | exists (inord 3); by rewrite inordK
          | exists (inord 4); by rewrite inordK ].
case: orbit => j Hj.
have HVx : forall (y : bool * bool) (k : 'I_5),
    ViewA R A (y, k)
    = map_tuple (fun i => nth false (rot k (fc_arrange y.1 y.2)) i) (in_tuple A).
  by move=> [a0 b0] k; rewrite /ViewA /arr /fc_shuffle.
under eq_bigr=> k _ do rewrite (HVx x k).
under [in RHS]eq_bigr=> k _ do rewrite (HVx x' k).
set L := fc_arrange x.1 x.2.
have HLsz : size L = 5 by rewrite /L fc_arrange_size.
under [in RHS]eq_bigr=> k _ do rewrite Hj.
have rotjk : forall (m jj : 'I_5) (s : seq bool), size s = 5 ->
    rot m (rot jj s) = rot ((m + jj) %% 5) s.
  move=> m jj s Hs.
  have rot5 : rot 5 s = s by have := rot_size s; rewrite Hs.
  rewrite rot_add_mod ?Hs ?(ltnW (ltn_ord _)) //.
  case: ifP => Hle.
    move: Hle; rewrite leq_eqVlt => /orP[/eqP Heq|Hlt].
      by rewrite Heq -{1}Hs rot_size modnn rot0.
    by rewrite modn_small.
  have H5 : (5 <= m + jj)%N by rewrite ltnW // ltnNge Hle.
  rewrite -[in RHS](subnK H5) modnDr modn_small ?subnK //.
  rewrite ltn_subLR //.
  by have H1 := ltn_ord m; have H2 := ltn_ord jj;
     rewrite -addnS; apply: leq_add => //; exact: ltnW.
under [in RHS]eq_bigr=> k _ do rewrite -/L (rotjk k j L HLsz).
pose phi := fun k : 'I_5 => inord ((k + j) %% 5) : 'I_5.
have phiK : forall k : 'I_5, val (phi k) = (k + j) %% 5.
  by move=> k; rewrite /phi /= inordK ?ltn_pmod.
have phi_inj : injective phi.
  move=> a c /(congr1 val); rewrite !phiK => Hac.
  apply/val_inj => /=.
  by move: Hac => /eqP; rewrite eqn_modDr !modn_small ?ltn_ord // => /eqP.
rewrite [LHS](reindex_inj phi_inj) /=.
apply: eq_bigr => k _.
by rewrite phiK.
Qed.

(** den_boer_cinde — conditioned on the secret, the inputs are independent of
    any partial view of the dealt row.
    @composes: den_boer_input_private. *)
Lemma den_boer_cinde (A : seq nat) :
  cinde_RV Inputs (ViewA R A) (Secret R).
Proof.
rewrite /cinde_RV => a b c.
rewrite !cpr_eqE.
rewrite !count_pr.
have SecI : forall w : Omega, Secret R w = (Inputs w).1 && (Inputs w).2.
  by move=> [[a0 b0] k].
have IS_eq : #|preim [% Inputs, Secret R] (pred1 (a, c))|
  = (if c == a.1 && a.2 then #|preim Inputs (pred1 a)| else 0)%N.
  case: ifP => [/eqP Hc|/negbT Hc].
    apply: eq_card => w /=; rewrite !inE /= xpair_eqE SecI.
    case: (eqVneq (Inputs w) a) => [->|//] /=.
    by rewrite Hc eqxx.
  apply: eq_card0 => w /=; rewrite !inE /= xpair_eqE SecI.
  case: (eqVneq (Inputs w) a) => [->|//] /=.
  by rewrite eq_sym (negbTE Hc).
have IVS_eq : #|preim [% Inputs, ViewA R A, Secret R] (pred1 (a, b, c))|
  = (if c == a.1 && a.2 then #|preim [% Inputs, ViewA R A] (pred1 (a, b))| else 0)%N.
  case: ifP => [/eqP Hc|/negbT Hc].
    apply: eq_card => w /=; rewrite !inE /= !xpair_eqE SecI.
    case: (eqVneq (Inputs w) a) => [->|_]; last by [].
    by rewrite /= Hc eqxx andbT.
  apply: eq_card0 => w /=; rewrite !inE /= !xpair_eqE SecI.
  case: (eqVneq (Inputs w) a) => [->|_]; last by [].
  by rewrite /= [a.1 && a.2 == c]eq_sym (negbTE Hc) andbF.
rewrite IS_eq IVS_eq; case: ifP => [/eqP Hc|/negbT Hc]; last by rewrite !mul0r.
have nIa5 : #|preim Inputs (pred1 a)| = 5%N.
  rewrite -sum1_card big_mkcond /=.
  rewrite (eq_bigr (fun w => if Inputs w == a then 1 else 0))%N; last first.
    by move=> w _; rewrite inE.
  rewrite (stepO (fun w => if Inputs w == a then 1 else 0))%N.
  have InE : forall (ab : bool * bool) (k : 'I_5), Inputs (ab, k) = ab.
    by move=> [a0 b0] k.
  rewrite (eq_bigr (fun ab => \sum_(k<5) (if ab == a then 1 else 0))%N); last first.
    by move=> ab _; apply: eq_bigr => k _; rewrite InE.
  rewrite (eq_bigr (fun ab => if ab == a then 5 else 0)%N); last first.
    move=> ab _; case: ifP => _; by rewrite ?sum_nat_const ?card_ord ?big1.
  by rewrite -big_mkcond big_pred1_eq.
have InVab_count : forall a' : bool * bool,
  #|preim [% Inputs, ViewA R A] (pred1 (a', b))|
  = (\sum_(k < 5) (if ViewA R A (a', k) == b then 1 else 0))%N.
  move=> a'.
  rewrite -sum1_card.
  rewrite (eq_bigl (fun w : Omega => (Inputs w == a') && (ViewA R A w == b))); last first.
    by move=> w /=; rewrite inE /= xpair_eqE.
  rewrite big_mkcond /=.
  rewrite (stepO (fun w => if (Inputs w == a') && (ViewA R A w == b) then 1 else 0))%N.
  have InE : forall (ab : bool * bool) (k : 'I_5), Inputs (ab, k) = ab.
    by move=> [a0 b0] k.
  rewrite (eq_bigr (fun ab => \sum_(k<5)
      (if (ab == a') && (ViewA R A (ab, k) == b) then 1 else 0))%N); last first.
    by move=> ab _; apply: eq_bigr=> k _; rewrite InE.
  rewrite (eq_bigr (fun ab => if ab == a'
      then \sum_(k<5) (if ViewA R A (ab, k) == b then 1 else 0) else 0)%N); last first.
    move=> ab _; case: ifP => abx.
      by under eq_bigr=> k _ do rewrite andTb.
    by rewrite big1 // => k _; rewrite andFb.
  by rewrite -big_mkcond big_pred1_eq.
have nVS_sum : #|preim [% ViewA R A, Secret R] (pred1 (b, c))|
  = (\sum_(a' : bool * bool)
       (if a'.1 && a'.2 == c then #|preim [% Inputs, ViewA R A] (pred1 (a', b))| else 0))%N.
  rewrite -sum1_card big_mkcond /=.
  rewrite (eq_bigr (fun w => if (ViewA R A w == b) && (Secret R w == c) then 1 else 0))%N; last first.
    by move=> w _; rewrite inE /= xpair_eqE.
  rewrite (stepO (fun w => if (ViewA R A w == b) && (Secret R w == c) then 1 else 0))%N.
  apply: eq_bigr => a' _.
  under eq_bigr=> k _ do rewrite SecI.
  have InE : forall (ab : bool * bool) (k : 'I_5), Inputs (ab, k) = ab.
    by move=> [a0 b0] k.
  under eq_bigr=> k _ do rewrite (InE a' k).
  case: ifP => a'c.
    rewrite InVab_count.
    by apply: eq_bigr => k _; rewrite andbT.
  by rewrite big1 // => k _; rewrite andbF.
have nS_sum : #|preim (Secret R) (pred1 c)|
  = (\sum_(a' : bool * bool) (if a'.1 && a'.2 == c then 5 else 0))%N.
  rewrite -sum1_card big_mkcond /=.
  rewrite (eq_bigr (fun w => if Secret R w == c then 1 else 0))%N; last first.
    by move=> w _; rewrite inE.
  rewrite (stepO (fun w => if Secret R w == c then 1 else 0))%N.
  apply: eq_bigr => a' _.
  under eq_bigr=> k _ do rewrite SecI.
  have InE : forall (ab : bool * bool) (k : 'I_5), Inputs (ab, k) = ab.
    by move=> [a0 b0] k.
  under eq_bigr=> k _ do rewrite (InE a' k).
  case: ifP => a'c.
    by rewrite sum_nat_const card_ord.
  by rewrite big1.
set nVab := #|preim [% Inputs, ViewA R A] (pred1 (a, b))|.
have key : (5 * #|preim [% ViewA R A, Secret R] (pred1 (b, c))|
            = #|preim (Secret R) (pred1 c)| * nVab)%N.
  rewrite nVS_sum nS_sum big_distrr /= big_distrl /=.
  apply: eq_bigr => a' _.
  case: ifP => a'c; last by rewrite muln0 mul0n.
  rewrite (den_boer_view_count_eq b (x:=a') (x':=a)); first by rewrite -/nVab mulnC.
  by move: a'c Hc => /eqP -> ->.
have nS_pos : (0 < #|preim (Secret R) (pred1 c)|)%N.
  by rewrite nS_sum (bigD1 a) //= eq_sym -Hc eqxx.
rewrite nIa5.
set nS := #|preim (Secret R) (pred1 c)|.
set nVS := #|preim [% ViewA R A, Secret R] (pred1 (b, c))|.
rewrite -/nS -/nVS in key nS_pos.
have nSR : (nS%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have keyR : (5%:R : R) * nVS%:R = nS%:R * nVab%:R.
  by rewrite -[5%:R]/(5%N%:R) -!natrM key.
have simp20 : forall x : R, x / 20 / (nS%:R / 20) = x / nS%:R.
  by move=> x; rewrite invf_div mulrA divfK ?pnatr_eq0.
rewrite !simp20.
by rewrite mulf_div keyR -mulf_div divff // mul1r.
Qed.

(** den_boer_input_private — perfect input privacy: conditioned on the secret,
    the inputs are independent of any partial view, so the conditional mutual
    information of the inputs and the view given the secret is zero.
    @main security: cond_mutual_info (`p_ [% Inputs, ViewA A, Secret]) = 0. *)
Lemma den_boer_input_private (A : seq nat) :
  cond_mutual_info (`p_ [% Inputs, ViewA R A, Secret R]) = 0 :> R.
Proof.
by apply: cinde_cond_mutual_info0; exact: den_boer_cinde.
Qed.

End den_boer_input_privacy.
