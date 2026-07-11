(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_secrecy: coalition view independence of the eight-card orbit scheme  *)
(*                                                                            *)
(* The uniformly shuffled dealt arrangement of the PGL(2,7) orbit scheme has  *)
(* a coalition view independent of the orbit secret for every coalition of at *)
(* most three cards. The abstract section generalizes the transitivity bridge *)
(* singleton corollary to arbitrary coalitions by k-tuple fiber counting.     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   ttrans_view_indep_gen == over a t-transitive shuffle, any coalition of   *)
(*     at most t positions has view independent of the secret                 *)
(*   pgl27_view_indep       == the PGL(2,7) instance at three cards           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope fdist_scope.

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
  apply/idP/idP => /eqP H; apply/eqP.
    apply: eq_from_tnth => l.
    move: (congr1 (fun z : k.-tuple _ => tnth z l) H).
    rewrite !tnth_mktuple => Hl.
    by rewrite -(ebK (rho g (tnth p l))) Hl.
  apply: eq_from_tnth => l.
  move: (congr1 (fun z : k.-tuple _ => tnth z l) H).
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
  (#|C| <= t)%N -> (0 < t)%N -> (forall b, uniq (encode b)) ->
  secretP `x (`U HG) |= coalition_view rho secretP HG encode C _|_
    @dealt_secret gT G R secretP HG.
Proof.
move=> HC _ Huniq.
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

End transitivity_privacy_gen.

Section pgl27_secrecy.
Local Open Scope proba_scope.
Variable R : realType.

(** pgl27P == the joint law of a uniform orbit secret and a uniform PGL(2,7)
    shuffle.
    @intent: the joint sample space of the eight-card orbit scheme. *)
Definition pgl27P : R.-fdist (bool * pgg_gT pgl27_M)%type :=
  (fdist_uniform card_bool) `x (`U pgl27_G_pos).

(** pgl27_secret == the dealt orbit-class secret component of a sample.
    @intent: the orbit-secret random variable. *)
Definition pgl27_secret : {RV pgl27P -> bool} := fun u => u.1.

(** pgl27_view == the dealt card values a coalition C observes at a sample,
    and ord0 outside C.
    @intent: the coalition observable random variable. *)
Definition pgl27_view (C : {set 'I_8}) : {RV pgl27P -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then
              tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i) else ord0].

(** pgl27_view_indep == any coalition of at most three cards has a view of the
    shuffled dealt arrangement independent of the orbit secret.
    @main security: instance coalition view independence from the bridge. *)
Lemma pgl27_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P |= pgl27_view C _|_ pgl27_secret.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R (fdist_uniform card_bool) pgl27_G_pos
  orbit_encode C HC isT orbit_encode_deck).
Qed.

End pgl27_secrecy.
