(* AUDIT FILE: replay the probe_shapes Qed supports against the REAL          *)
(* imported carrier (five_card_leakage's own P/Secret/arr), not the replica.  *)
(* probe_shapes proves these over its own verbatim copies; this file checks   *)
(* the proof scripts transfer to the constants the implementation will use.   *)
(* Also: one anchor bridge (anchorT_k1) fully Qed from the published leak_k1. *)

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

Section audit_supports_real.

Variable R : realType.

Local Open Scope ring_scope.

Local Notation P := (P R).
Local Notation Secret := (Secret R).
Local Notation ViewA := (ViewA R).

Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

Definition i0 : 'I_5 := Ordinal (isT : (0 < 5)%N).

Lemma succ5_val (i : 'I_5) : val (succ5 i) = (i.+1 %% 5)%N.
Proof. by rewrite /succ5 /= inordK // ltn_pmod. Qed.

(* ---- mutual_info_view_inj at the real carrier ---- *)

Lemma mutual_info_view_inj (A B : finType) (Y : {RV P -> A}) (g : A -> B) :
  injective g -> `I( Secret ; g `o Y ) = `I( Secret ; Y ).
Proof.
move=> gi.
rewrite !mutual_info_RVE; congr (_ - _).
apply: cPr_centropy_RV_comp => x y Hy.
rewrite !cpr_eqE (pfwd1_comp Y y gi); congr (_ / _).
have hinj : injective (fun p : bool * A => (p.1, g p.2)).
  by move=> [a1 b1] [a2 b2] [] -> /gi ->.
by rewrite -(pfwd1_comp [% Secret, Y] (x, y) hinj).
Qed.

(* ---- leak_rot1 at the real carrier ---- *)

Definition cutS (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, succ5 k).

Definition pred5 (i : 'I_5) : 'I_5 := inord ((i + 4) %% 5).

Lemma pred5_val (i : 'I_5) : val (pred5 i) = ((i + 4) %% 5)%N.
Proof. by rewrite /pred5 /= inordK // ltn_pmod. Qed.

Definition cutSinv (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, pred5 k).

Lemma cutSK : cancel cutS cutSinv.
Proof.
move=> [[a b] k]; congr (_, _); apply: val_inj.
by rewrite pred5_val succ5_val; case: k => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma cutSKV : cancel cutSinv cutS.
Proof.
move=> [[a b] k]; congr (_, _); apply: val_inj.
by rewrite succ5_val pred5_val; case: k => [[|[|[|[|[|m]]]]] Hm].
Qed.

Lemma fdistmap_cutS : fdistmap cutS P = P.
Proof.
apply/fdist_ext => w.
rewrite fdistmapE.
rewrite (big_pred1 (cutSinv w)); last first.
  by move=> i; rewrite !inE /=; apply/idP/idP => [/eqP <-|/eqP ->];
     rewrite ?cutSK ?cutSKV.
by rewrite /P !fdist_uniformE.
Qed.

Lemma ViewT_succ5 k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT (map_tuple succ5 t) w = ViewT t (cutS w).
Proof.
apply: eq_from_tnth => i.
rewrite /ViewT !tnth_mktuple tnth_map succ5_val.
case: w => [[a b] kk] /=.
rewrite /arr /fc_shuffle.
have nr5 : forall (s : seq bool) (i k : nat), size s = 5%N -> (i < 5)%N ->
    (k < 5)%N -> nth false (rot k s) i = nth false s ((i + k) %% 5)%N.
  move=> s i0' k0 Hs Hi Hk.
  move: Hs; case: s => [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]] //= _.
  by case: i0' Hi => [|[|[|[|[|i0']]]]] //= _;
     case: k0 Hk => [|[|[|[|[|k0]]]]] //=.
rewrite (nr5 _ _ _ (fc_arrange_size a b) (@ltn_pmod (tnth t i).+1 5 isT)
  (ltn_ord kk)).
rewrite (nr5 _ _ _ (fc_arrange_size a b) (ltn_ord (tnth t i)));
  last by rewrite succ5_val ltn_pmod.
rewrite succ5_val modnDml modnDmr.
by rewrite addSnnS.
Qed.

Lemma leak_rot1 k (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (map_tuple succ5 t) ) = `I( Secret ; ViewT t ).
Proof.
rewrite /mutual_info_RV; congr (mutual_info _).
have -> : [% Secret, ViewT (map_tuple succ5 t)] = [% Secret, ViewT t] \o cutS.
  apply: boolp.funext => w; rewrite /RV2 /=.
  by rewrite ViewT_succ5; case: w => [[a b] kk].
by rewrite /dist_of_RV -fdistmap_comp fdistmap_cutS.
Qed.

(* ---- leak_view_nil at the real carrier ---- *)

Lemma leak_view_nil :
  `I( Secret ; ViewT ([tuple] : 0.-tuple 'I_5) ) = 0.
Proof.
have Hinde : P |= Secret _|_ (ViewT ([tuple] : 0.-tuple 'I_5)).
  rewrite /inde_RV => s c; rewrite (tuple0 c) !count_pr.
  have -> : #|preim (ViewT ([tuple] : 0.-tuple 'I_5)) (pred1 [tuple])| = 20%N.
    rewrite -card_Omega20; apply: eq_card => w.
    by rewrite !inE /=; apply/eqP; exact: tuple0.
  have -> : #|preim [% Secret, ViewT ([tuple] : 0.-tuple 'I_5)]
                    (pred1 (s, [tuple]))| = #|preim Secret (pred1 s)|.
    apply: eq_card => w; rewrite !inE /= xpair_eqE.
    have -> : (ViewT ([tuple] : 0.-tuple 'I_5) w == [tuple]) = true.
      by apply/eqP; exact: tuple0.
    by rewrite andbT.
  by rewrite divff ?mulr1 // pnatr_eq0.
rewrite mutual_info_RVE.
have HcondE : `H( Secret | ViewT ([tuple] : 0.-tuple 'I_5)) = `H `p_Secret.
  have := chain_rule_RV (ViewT ([tuple] : 0.-tuple 'I_5)) Secret.
  rewrite -joint_entropy_RVC (inde_RV_joint_entropyE Hinde) => H1.
  have : `H `p_(ViewT ([tuple] : 0.-tuple 'I_5))
         + `H( Secret | ViewT ([tuple] : 0.-tuple 'I_5))
       = `H `p_(ViewT ([tuple] : 0.-tuple 'I_5)) + `H `p_Secret.
    by rewrite -H1 addrC.
  by move/addrI.
by rewrite HcondE subrr.
Qed.

(* ---- one full anchor bridge from the published leak_k1 ---- *)

Lemma ViewT_ViewA_singleton : ViewT [tuple i0] = ViewA [:: 0%N].
Proof.
apply: boolp.funext => w; apply: val_inj.
by rewrite /ViewT /ViewA /= enum_ordSl enum_ord0 /=.
Qed.

Lemma anchorT_k1_real : `I( Secret ; ViewT [tuple i0] ) = 0.
Proof. by rewrite ViewT_ViewA_singleton leak_k1. Qed.

End audit_supports_real.
