(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Additive one-time-pad secrecy head (T-of-T over Z/N): a randomized        *)
(* additive sharing whose every sub-threshold coalition view is independent  *)
(* of the secret.                                                             *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals zmodp.
From infotheo Require Import realType_ext realType_ln fdist proba entropy graphoid.
Require Import spp_proba spp_entropy.
From pgg_smc Require Import pgg_leakage_witness.

Import GRing.Theory Num.Theory.
Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope. Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Section randomized_sharing.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.
Variable N' : nat.  Let N := N'.+2.
Variable T' : nat.  Let T := T'.+1.
Let card_ZN : #|'Z_N| = N'.+1.+1.
Proof. by rewrite card_ord. Qed.

Notation masksvec rsh_mask :=
  ((fun u => [ffun i : 'I_T' => rsh_mask i u]) : {RV P -> {ffun 'I_T' -> 'Z_N}}).
Notation othermasks rsh_mask k :=
  ((fun u => [ffun i : 'I_T' => if i == k then 0 else rsh_mask i u])
    : {RV P -> {ffun 'I_T' -> 'Z_N}}).

(** RandomizedSharing — a T-of-T additive sharing of a secret over Z/N: T-1
    independent uniform masks and one dependent share carrying the residue.
    @intent: the masks are jointly uniform and independent of the secret, and
    each mask is independent of the secret bundled with the other masks. *)
Record RandomizedSharing := MkRandomizedSharing {
  rsh_secret      : {RV P -> 'Z_N} ;
  rsh_mask        : 'I_T' -> {RV P -> 'Z_N} ;
  rsh_mask_unif   : forall k, `p_ (rsh_mask k) = fdist_uniform card_ZN ;
  rsh_masks_indep : P |= (masksvec rsh_mask) _|_ rsh_secret ;
  rsh_mask_indep  : forall k : 'I_T',
      P |= rsh_mask k _|_ [% rsh_secret, (othermasks rsh_mask k)] }.

(** rsh_share — the j-th additive share: a mask coordinate for j < T-1, and the
    residual share s - sum of masks for the last index.
    @intent: the T shares of the secret in the T-of-T additive scheme. *)
Definition rsh_share (rs : RandomizedSharing) (j : 'I_T) : {RV P -> 'Z_N} :=
  if @unlift _ ord_max j is Some j' then rsh_mask rs j'
  else (rsh_secret rs \- (\sum_(i < T') rsh_mask rs i)).

(** rsh_view — the joint view of a coalition C, exposing only the shares whose
    index lies in C.
    @intent: what an index set C of corrupted parties observes. *)
Definition rsh_view (rs : RandomizedSharing) (C : {set 'I_T}) :
    {RV P -> {ffun 'I_T -> 'Z_N}} :=
  fun u => [ffun j => if j \in C then rsh_share rs j u else 0].

(** additive_allbut_indep — dropping one share leaves a view independent of the
    secret.
    @composes: additive_view_indep *)
Lemma additive_allbut_indep (rs : RandomizedSharing) (k : 'I_T) :
  P |= rsh_view rs (~: [set k]) _|_ rsh_secret rs.
Proof.
case: (eqVneq k ord_max) => [Hk|Hk].
- subst k.
  pose f := fun (m : {ffun 'I_T' -> 'Z_N}) =>
    [ffun j : 'I_T => if j \in [set~ ord_max]
                      then (if @unlift _ ord_max j is Some j' then m j' else 0)
                      else 0] : {ffun 'I_T -> 'Z_N}.
  have Hview : rsh_view rs [set~ ord_max]
             = f `o (fun u => [ffun i : 'I_T' => rsh_mask rs i u]).
    rewrite /comp_RV /f /rsh_view; apply: boolp.funext => u; apply/ffunP => j.
    rewrite !ffunE; case: ifP => // Hj; rewrite /rsh_share.
    have Hne : ord_max != j by move: Hj; rewrite !inE eq_sym.
    have [j' Hlift Hunl] := unlift_some Hne.
    by rewrite Hunl ffunE.
  rewrite Hview; exact: (inde_RV_comp f idfun (rsh_masks_indep rs)).
- have Hne : ord_max != k by rewrite eq_sym.
  have [k' Hklift Hkunl] := unlift_some Hne.
  set sec := rsh_secret rs.
  set W := (fun u => [ffun i : 'I_T' => if i == k' then 0 else rsh_mask rs i u])
    : {RV P -> {ffun 'I_T' -> 'Z_N}}.
  set Z := neg_RV (rsh_mask rs k').
  pose Xc := (sec \- (\sum_(i < T' | i != k') rsh_mask rs i)) : {RV P -> 'Z_N}.
  have Hdep : (sec \- (\sum_(i < T') rsh_mask rs i)) = Xc \+ Z.
    rewrite /Xc /Z (bigD1 k') //=; apply: boolp.funext => u.
    rewrite /sub_RV /add_RV /neg_RV /= !sumrRVE /=.
    by rewrite opprD addrA addrAC sub0r.
  have HZunif : `p_ Z = fdist_uniform card_ZN.
    rewrite /Z -(neg_RV_dist_eq (X := rsh_mask rs k')) //.
    exact: (rsh_mask_unif rs k').
    exact: (rsh_mask_unif rs k').
  have HXc_fun : Xc
    = (fun p : ('Z_N * {ffun 'I_T' -> 'Z_N}) => p.1 - \sum_(i < T') p.2 i)
        `o [% sec, W].
    rewrite /Xc /comp_RV; apply: boolp.funext => u.
    rewrite /sub_RV /= sumrRVE /=; congr (_ - _).
    rewrite [RHS](bigD1 k') //= ffunE eqxx add0r.
    by apply: eq_bigr => i Hi; rewrite ffunE (negbTE Hi).
  have HmW : P |= Z _|_ [% sec, W].
    rewrite /Z; apply/inde_RV_sym; apply: neg_RV_inde_eq.
    by apply/inde_RV_sym; exact: (rsh_mask_indep rs k').
  have HZindep : P |= Z _|_ [% Xc, [% sec, W]].
    have Heq : [% Xc, [% sec, W]]
      = (fun p : ('Z_N * {ffun 'I_T' -> 'Z_N}) => ((p.1 - \sum_(i < T') p.2 i), p))
          `o [% sec, W].
      rewrite /comp_RV; apply: boolp.funext => u.
      rewrite -[in LHS]/(_ u); congr (_, _); by rewrite HXc_fun.
    rewrite Heq; exact: (inde_RV_comp idfun _ HmW).
  have Hdep_ind : P |= (Xc \+ Z) _|_ [% sec, W].
    apply: (lemma_3_5' HZindep (n:=N'.+1)); exact: HZunif.
  have HWsec : P |= W _|_ sec.
    have HWfun : W = (fun m : {ffun 'I_T' -> 'Z_N} =>
        [ffun i => if i == k' then 0 else m i] : {ffun 'I_T' -> 'Z_N})
        `o (fun u => [ffun i : 'I_T' => rsh_mask rs i u]).
      rewrite /comp_RV /W; apply: boolp.funext => u; apply/ffunP => i.
      by rewrite !ffunE; case: ifP.
    rewrite HWfun; exact: (inde_RV_comp _ idfun (rsh_masks_indep rs)).
  have Hprem2 : sec _|_ W | unit_RV P.
    by apply/cinde_RV_unit; apply/inde_RV_sym; exact: HWsec.
  have Hprem1 : sec _|_ (Xc \+ Z) | [% unit_RV P, W].
    by apply: symmetry; apply: weak_union; apply/cinde_RV_unit; exact: Hdep_ind.
  have Hpair : P |= [% W, (Xc \+ Z)] _|_ sec.
    by apply/inde_RV_sym; apply/cinde_RV_unit; apply: contraction Hprem1 Hprem2.
  pose g := fun (p : ({ffun 'I_T' -> 'Z_N} * 'Z_N)) =>
    [ffun j : 'I_T => if j \in [set~ k]
                      then (if @unlift _ ord_max j is Some j' then p.1 j' else p.2)
                      else 0] : {ffun 'I_T -> 'Z_N}.
  have Hview : rsh_view rs [set~ k] = g `o [% W, (Xc \+ Z)].
    rewrite /comp_RV /g /rsh_view; apply: boolp.funext => u; apply/ffunP => j.
    rewrite !ffunE; case: ifP => // Hj; rewrite /rsh_share.
    case: (unliftP ord_max j) => [j' Hjeq|Hjeq].
    + rewrite ffunE.
      have Hj'k : j' != k'.
        by apply/eqP => Hjk'; move: Hj; rewrite Hjeq Hjk' -Hklift !inE eqxx.
      by rewrite (negbTE Hj'k).
    + exact: (congr1 (fun ff => ff u) Hdep).
  rewrite Hview; exact: (inde_RV_comp g idfun Hpair).
Qed.

(** additive_view_indep — any coalition of fewer than T shares learns nothing
    about the secret.
    @main security: a sub-threshold coalition view is independent of the secret. *)
Lemma additive_view_indep (rs : RandomizedSharing) (C : {set 'I_T}) :
  (#|C| < T)%N -> P |= rsh_view rs C _|_ rsh_secret rs.
Proof.
move=> HC.
have [k Hk] : exists k, k \notin C.
  apply/existsP; rewrite -negb_forall; apply/negP => /forallP Hall.
  have Hsub : setT \subset C by apply/subsetP => x _; exact: Hall.
  move: (subset_leq_card Hsub); rewrite cardsT card_ord leqNgt.
  by rewrite HC.
have HCsub : C \subset [set~ k].
  apply/subsetP => x Hx; rewrite !inE; apply/negP => /eqP Hxk; subst x.
  by rewrite Hx in Hk.
pose restrict := fun (v : {ffun 'I_T -> 'Z_N}) =>
  [ffun j : 'I_T => if j \in C then v j else 0] : {ffun 'I_T -> 'Z_N}.
have Hview : rsh_view rs C = restrict `o rsh_view rs [set~ k].
  rewrite /comp_RV /restrict /rsh_view; apply: boolp.funext => u; apply/ffunP => j.
  rewrite !ffunE; case: ifP => // Hj.
  by move/subsetP/(_ j Hj): HCsub => ->.
rewrite Hview; exact: (inde_RV_comp restrict idfun (additive_allbut_indep rs k)).
Qed.

(** additive_leakage — the leakage witness packaging a sub-threshold view.
    @composes: mechanism_leakage *)
Definition additive_leakage (rs : RandomizedSharing) (C : {set 'I_T})
    (HC : (#|C| < T)%N) : LeakageWitness P :=
  @MkLeakageWitness _ _ P _ _ (rsh_secret rs) (rsh_view rs C)
    (additive_view_indep rs HC).

End randomized_sharing.
