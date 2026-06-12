(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer input encoding: the AND function via fc_arrange                   *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism cyclic bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_group five_card_kim five_card_family.
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
