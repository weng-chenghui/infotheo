(* Probe: decomposition. The master theorem derived to Qed from Admitted     *)
(* supports. The ONLY file where Admitted is legitimate, and only for the    *)
(* supports listed below.                                                    *)
(* Spec: docs/superpowers/specs/                                            *)
(*   2026-08-10-five-card-all-reveal-cases-design.md                        *)
(* Ledger rows: L12, L16.                                                   *)
(*                                                                          *)
(* Imports the REAL five_card_leakage, so the seven proven anchors are used  *)
(* as published (L16). Its section is discharged over R, so Omega and arr    *)
(* carry no argument while P, Secret and ViewA take R; the three R-carrying  *)
(* names are pinned by Local Notation below.                                 *)
(*                                                                          *)
(* Legitimate Admitted supports (and only these):                            *)
(*   leak_k3_gap, mutual_info_view_inj, leak_rot1, leak_view_nil,            *)
(*   anchorT_k1, anchorT_k2_adj, anchorT_k2_dist2, anchorT_k3,               *)
(*   anchorT_k3_gap, anchorT_k4, anchorT_k5, leak_view_rest.                 *)
(* Everything else here, including the headline leak_view_set, is Qed.       *)

(* IMPORT ADJUSTMENT (recorded): mathcomp's div is added, as in the other    *)
(* two probes, because succ5 needs the notation "_ %% _".                    *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program five_card_leakage.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section probe_decomposition.

Variable R : realType.

Local Open Scope ring_scope.

(* Use the imported carrier: Omega, P, arr, Secret, ViewA and the anchors    *)
(* H_secret, leak_k1, leak_k2_adj, leak_k2_dist2, leak_k3, leak_k4, leak_k5  *)
(* all come from five_card_leakage; none of them is redefined here.          *)

Local Notation P := (P R).
Local Notation Secret := (Secret R).
Local Notation ViewA := (ViewA R).

(* ---- resolved definitions, transcribed from probe_objects.v ---- *)

Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* set_tuple resolution (probe_objects.v, L3): mathcomp's enum_tuple. *)
Definition set_tuple (A : {set 'I_5}) : #|A|.-tuple 'I_5 := enum_tuple A.

Definition ViewS (A : {set 'I_5}) : {RV P -> #|A|.-tuple bool} :=
  ViewT (set_tuple A).

Definition fc_adjacent (A : {set 'I_5}) : bool :=
  [exists i : 'I_5, A == [set i; succ5 i]].

Definition fc_leak (A : {set 'I_5}) : R :=
  match #|A| with
  | 0 => 0
  | 1 => 0
  | 2 => if fc_adjacent A
         then 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R
         else 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R / 20%:R) * log 7%:R
  | 3 => 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R
  | _ => 2%:R - (3%:R / 4%:R) * log 3%:R
  end.

(* ---- the membership-bit presentation of a subset of 'I_5 ---- *)
(* STATEMENT ADJUSTMENT (recorded, proof device only): the 32-way case split *)
(* is taken over the five membership bits, presented as setb5, rather than   *)
(* over 32 set literals.  Nothing in the headline statement changes; setb5   *)
(* b0 b1 b2 b3 b4 is the set literal whose membership vector is those bits,  *)
(* and setb5_ex says every A is of that shape.  This is what makes #|A| and  *)
(* enum A reduce to closed nat computations (see probe_objects.v: inord and  *)
(* insub do not reduce, because idP is Qed-opaque).                          *)

Definition setb5 (b0 b1 b2 b3 b4 : bool) : {set 'I_5} :=
  [set i : 'I_5 | nth false [:: b0; b1; b2; b3; b4] (val i)].

Lemma setb5_ex (A : {set 'I_5}) :
  exists b0 b1 b2 b3 b4 : bool, A = setb5 b0 b1 b2 b3 b4.
Proof.
exists (inord 0 \in A), (inord 1 \in A), (inord 2 \in A), (inord 3 \in A),
       (inord 4 \in A).
apply/setP => x; rewrite inE.
have E : forall (j : nat) (H : (j < 5)%N), Ordinal H = inord j.
  by move=> j H; apply: val_inj; rewrite /= inordK.
by case: x => [[|[|[|[|[|m]]]]] Hm] //=; rewrite (E _ Hm).
Qed.

Lemma enum_val5 (A : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in A) = q (val x)) ->
  map val (enum A) = filter q (iota 0 5).
Proof.
move=> H; rewrite -val_enum_ord filter_map; congr (map _ _).
by rewrite {1}/enum_mem -enumT; apply: eq_filter => x /=; exact: H.
Qed.

Lemma card_val5 (A : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in A) = q (val x)) -> #|A| = size (filter q (iota 0 5)).
Proof. by move=> H; rewrite cardE -(size_map val) (enum_val5 H). Qed.

Lemma mem_setb5 (b0 b1 b2 b3 b4 : bool) (x : 'I_5) :
  (x \in setb5 b0 b1 b2 b3 b4) = nth false [:: b0; b1; b2; b3; b4] (val x).
Proof. by rewrite inE. Qed.

Lemma card_setb5 (b0 b1 b2 b3 b4 : bool) :
  #|setb5 b0 b1 b2 b3 b4|
  = size (filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5)).
Proof. by apply: card_val5 => x; exact: mem_setb5. Qed.

Lemma enum_setb5 (b0 b1 b2 b3 b4 : bool) :
  map val (enum (setb5 b0 b1 b2 b3 b4))
  = filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5).
Proof. by apply: enum_val5 => x; exact: mem_setb5. Qed.

(* leak_view_of_tuple — the set-indexed view is the tuple-indexed view of any
   position tuple with the same length and the same ascending values.  The
   length equality is taken as an argument, so no cast appears in the
   statement of the headline theorem. *)
Lemma leak_view_of_tuple (A : {set 'I_5}) k (t : k.-tuple 'I_5) (e : #|A| = k) :
  map val (val (set_tuple A)) = map val (val t) ->
  `I( Secret ; ViewS A ) = `I( Secret ; ViewT t ).
Proof.
move: t; case: k / e => t H.
by rewrite /ViewS (val_inj (inj_map val_inj H)).
Qed.

(* ---- concrete positions, as Ordinal literals ---- *)
(* STATEMENT ADJUSTMENT (recorded): the anchors are stated with Ordinal      *)
(* literals i0..i4 rather than inord 0..4, so that val i reduces.            *)

Definition i0 : 'I_5 := Ordinal (isT : (0 < 5)%N).
Definition i1 : 'I_5 := Ordinal (isT : (1 < 5)%N).
Definition i2 : 'I_5 := Ordinal (isT : (2 < 5)%N).
Definition i3 : 'I_5 := Ordinal (isT : (3 < 5)%N).
Definition i4 : 'I_5 := Ordinal (isT : (4 < 5)%N).

Lemma succ5_val (i : 'I_5) : val (succ5 i) = (i.+1 %% 5)%N.
Proof. by rewrite /succ5 /= inordK // ltn_pmod. Qed.

Lemma tuple5_eq k (t u : k.-tuple 'I_5) :
  map val (val t) = map val (val u) -> t = u.
Proof. by move=> H; apply: val_inj; apply: (inj_map val_inj). Qed.

(* ---- component relabeling as a cyclic shift of the view tuple ---- *)
(* The concrete relabeling g of the spec is instantiated by rot_tuple n,     *)
(* which is injective, so mutual_info_view_inj applies with no side          *)
(* condition beyond rot_inj.                                                 *)

Lemma ViewTE k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT t w = map_tuple (fun j : 'I_5 => nth false (arr w) (val j)) t.
Proof. by apply: eq_from_tnth => i; rewrite /ViewT tnth_mktuple tnth_map. Qed.

Lemma ViewT_rot k n (t : k.-tuple 'I_5) :
  ViewT (rot_tuple n t) = (fun x : k.-tuple bool => rot_tuple n x) `o ViewT t.
Proof.
apply: boolp.funext => w; rewrite /comp_RV !ViewTE; apply: val_inj => /=.
exact: map_rot.
Qed.

Lemma rotV_inj k n : injective (fun x : k.-tuple bool => rot_tuple n x).
Proof. by move=> x y /(congr1 val) /= /rot_inj /val_inj. Qed.

(* ---- fc_leak read off from the cardinality ---- *)

Lemma fc_leakE0 (A : {set 'I_5}) : #|A| = 0%N -> fc_leak A = 0.
Proof. by rewrite /fc_leak => ->. Qed.

Lemma fc_leakE1 (A : {set 'I_5}) : #|A| = 1%N -> fc_leak A = 0.
Proof. by rewrite /fc_leak => ->. Qed.

Lemma fc_leakE2adj (A : {set 'I_5}) : #|A| = 2%N -> fc_adjacent A ->
  fc_leak A = 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Proof. by rewrite /fc_leak => -> ->. Qed.

Lemma fc_leakE3 (A : {set 'I_5}) : #|A| = 3%N ->
  fc_leak A = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof. by rewrite /fc_leak => ->. Qed.

Lemma fc_leakE4 (A : {set 'I_5}) : #|A| = 4%N ->
  fc_leak A = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /fc_leak => ->. Qed.

Lemma fc_leakE5 (A : {set 'I_5}) : #|A| = 5%N ->
  fc_leak A = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /fc_leak => ->. Qed.

(* ---- Admitted supports (each becomes a real lemma in implementation) ---- *)

(* MI invariance under injective view relabeling; probe_shapes.v proves it. *)
Lemma mutual_info_view_inj (A B : finType) (Y : {RV P -> A}) (g : A -> B) :
  injective g -> `I( Secret ; g `o Y ) = `I( Secret ; Y ).
Admitted.

(* leak_rotT — the relabeling instance actually used by the branches; Qed on
   top of the Admitted mutual_info_view_inj. *)
Lemma leak_rotT k n (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (rot_tuple n t) ) = `I( Secret ; ViewT t ).
Proof.
by rewrite ViewT_rot (mutual_info_view_inj (ViewT t) (@rotV_inj k n)).
Qed.

(* new anchor: the gapped three-card pattern, ViewA form *)
Lemma leak_k3_gap :
  `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Admitted.

(* rotation equivariance; probe_shapes.v proves it. *)
Lemma leak_rot1 k (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (map_tuple succ5 t) ) = `I( Secret ; ViewT t ).
Admitted.

(* empty view; probe_shapes.v proves it. *)
Lemma leak_view_nil : `I( Secret ; ViewT ([tuple] : 0.-tuple 'I_5) ) = 0.
Admitted.

(* the seven anchor values in ViewT form (bridged from the ViewA anchors of
   five_card_leakage in implementation; the bridge shape is Qed'd in
   probe_shapes.v as ViewT_ViewA_singleton) *)
Lemma anchorT_k1 : `I( Secret ; ViewT [tuple i0] ) = 0.
Admitted.

Lemma anchorT_k2_adj : `I( Secret ; ViewT [tuple i0; i1] ) =
  27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Admitted.

Lemma anchorT_k2_dist2 : `I( Secret ; ViewT [tuple i0; i2] ) =
  5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
    - (7%:R / 20%:R) * log 7%:R.
Admitted.

Lemma anchorT_k3 : `I( Secret ; ViewT [tuple i0; i1; i2] ) =
  6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Admitted.

Lemma anchorT_k3_gap : `I( Secret ; ViewT [tuple i0; i1; i3] ) =
  6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Admitted.

Lemma anchorT_k4 : `I( Secret ; ViewT [tuple i0; i1; i2; i3] ) =
  2%:R - (3%:R / 4%:R) * log 3%:R.
Admitted.

Lemma anchorT_k5 : `I( Secret ; ViewT [tuple i0; i1; i2; i3; i4] ) =
  2%:R - (3%:R / 4%:R) * log 3%:R.
Admitted.

(* remaining-branch escape hatch: the 26 membership-bit patterns not carried
   by a real chain below, as an explicit literal list *)
Lemma leak_view_rest (b0 b1 b2 b3 b4 : bool) :
  (b0, b1, b2, b3, b4) \in
   [:: (true, true, true, true, false); (true, true, true, false, true);
       (true, true, true, false, false); (true, true, false, true, true);
       (true, true, false, true, false); (true, true, false, false, true);
       (true, true, false, false, false); (true, false, true, true, true);
       (true, false, true, true, false); (true, false, true, false, false);
       (true, false, false, true, true); (true, false, false, true, false);
       (true, false, false, false, false); (false, true, true, true, false);
       (false, true, true, false, true); (false, true, true, false, false);
       (false, true, false, true, true); (false, true, false, true, false);
       (false, true, false, false, true); (false, false, true, true, true);
       (false, false, true, true, false); (false, false, true, false, true);
       (false, false, true, false, false); (false, false, false, true, true);
       (false, false, false, true, false); (false, false, false, false, true)] ->
  `I( Secret ; ViewS (setb5 b0 b1 b2 b3 b4) ) = fc_leak (setb5 b0 b1 b2 b3 b4).
Admitted.

(* ---- headline: MUST be Qed ---- *)
(* Six branches go through the real reduction chain: the full set; the      *)
(* gapped triple {0,2,4}, whose chain needs a component relabeling; the     *)
(* wrap-adjacent pair {0,4}; the four-set {1,2,3,4}; the singleton {1};     *)
(* and set0.  The other 26 route through leak_view_rest.                    *)

Theorem leak_view_set (A : {set 'I_5}) :
  `I( Secret ; ViewS A ) = fc_leak A.
Proof.
case: (setb5_ex A) => b0 [b1 [b2 [b3 [b4 ->]]]].
case: b0; case: b1; case: b2; case: b3; case: b4;
  try by apply: leak_view_rest; rewrite !inE.
(* {0,1,2,3,4} : the full reveal *)
- rewrite (fc_leakE5 (card_setb5 true true true true true)).
  rewrite (leak_view_of_tuple (t := [tuple i0; i1; i2; i3; i4])
    (card_setb5 true true true true true)); last by rewrite enum_setb5.
  exact: anchorT_k5.
(* {0,2,4} : gapped triple, four rotation steps then a component relabeling *)
- rewrite (fc_leakE3 (card_setb5 true false true false true)).
  rewrite (leak_view_of_tuple (t := [tuple i0; i2; i4])
    (card_setb5 true false true false true)); last by rewrite enum_setb5.
  have e1 : [tuple i0; i2; i4] = map_tuple succ5 [tuple i4; i1; i3].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e2 : [tuple i4; i1; i3] = map_tuple succ5 [tuple i3; i0; i2].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e3 : [tuple i3; i0; i2] = map_tuple succ5 [tuple i2; i4; i1].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e4 : [tuple i2; i4; i1] = map_tuple succ5 [tuple i1; i3; i0].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e5 : [tuple i1; i3; i0] = rot_tuple 1 [tuple i0; i1; i3].
    by apply: tuple5_eq.
  rewrite e1 leak_rot1 e2 leak_rot1 e3 leak_rot1 e4 leak_rot1 e5 leak_rotT.
  exact: anchorT_k3_gap.
(* {0,4} : wrap-adjacent pair *)
- have Hadj : fc_adjacent (setb5 true false false false true).
    apply/existsP; exists i4; apply/eqP; apply/setP => x.
    rewrite mem_setb5 !inE -!val_eqE /= succ5_val.
    by case: x => [[|[|[|[|[|m]]]]] Hm].
  rewrite (fc_leakE2adj (card_setb5 true false false false true) Hadj).
  rewrite (leak_view_of_tuple (t := [tuple i0; i4])
    (card_setb5 true false false false true)); last by rewrite enum_setb5.
  have e1 : [tuple i0; i4] = map_tuple succ5 [tuple i4; i3].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e2 : [tuple i4; i3] = map_tuple succ5 [tuple i3; i2].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e3 : [tuple i3; i2] = map_tuple succ5 [tuple i2; i1].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e4 : [tuple i2; i1] = map_tuple succ5 [tuple i1; i0].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  have e5 : [tuple i1; i0] = rot_tuple 1 [tuple i0; i1].
    by apply: tuple5_eq.
  rewrite e1 leak_rot1 e2 leak_rot1 e3 leak_rot1 e4 leak_rot1 e5 leak_rotT.
  exact: anchorT_k2_adj.
(* {1,2,3,4} : one rotation step off the four-card anchor *)
- rewrite (fc_leakE4 (card_setb5 false true true true true)).
  rewrite (leak_view_of_tuple (t := [tuple i1; i2; i3; i4])
    (card_setb5 false true true true true)); last by rewrite enum_setb5.
  have e1 : [tuple i1; i2; i3; i4] = map_tuple succ5 [tuple i0; i1; i2; i3].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  rewrite e1 leak_rot1; exact: anchorT_k4.
(* {1} : a singleton other than {0} *)
- rewrite (fc_leakE1 (card_setb5 false true false false false)).
  rewrite (leak_view_of_tuple (t := [tuple i1])
    (card_setb5 false true false false false)); last by rewrite enum_setb5.
  have e1 : [tuple i1] = map_tuple succ5 [tuple i0].
    by apply: tuple5_eq; rewrite /= !succ5_val.
  rewrite e1 leak_rot1; exact: anchorT_k1.
(* set0 : the empty reveal *)
- rewrite (fc_leakE0 (card_setb5 false false false false false)).
  rewrite (leak_view_of_tuple (t := ([tuple] : 0.-tuple 'I_5))
    (card_setb5 false false false false false)); last by rewrite enum_setb5.
  exact: leak_view_nil.
Qed.

End probe_decomposition.
