(* Probe: Qed miniatures of the genuinely new proof shapes.                   *)
(* Spec: docs/superpowers/specs/                                              *)
(*   2026-08-10-five-card-all-reveal-cases-design.md                          *)
(* Ledger rows: L2, L7, L9, L10, L11.                                         *)
(* Rules: final state has ZERO Admitted/Abort/Axiom; statements may be        *)
(* adjusted syntactically but never semantically; if an infotheo lemma        *)
(* already provides a shape, use it and record its name in a comment.         *)

(* IMPORT ADJUSTMENT (recorded): mathcomp's div is added, as in               *)
(* probe_objects.v, because succ5 needs the notation "_ %% _".                *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section probe_shapes.

Variable R : realType.

Local Open Scope ring_scope.

(* ---- carrier, replicated verbatim from five_card_leakage.v ---- *)

Definition Omega : finType := [the finType of (bool * bool * 'I_5)%type].

Lemma card_Omega20 : #|Omega| = 19.+1.
Proof. by rewrite !card_prod card_bool card_ord. Qed.

Definition P : R.-fdist Omega := fdist_uniform card_Omega20.

Definition arr (w : Omega) : seq bool :=
  let: (a, b, k) := w in fc_shuffle k (fc_arrange a b).

Definition Secret : {RV P -> bool} := fun w => let: (a, b, _) := w in a && b.

Definition ViewA (A : seq nat) : {RV P -> (size A).-tuple bool} :=
  fun w => map_tuple (fun i => nth false (arr w) i) (in_tuple A).

Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* ---- L2: MI invariance under an injective relabeling of the view      ---- *)
(* alphabet.                                                                  *)
(*                                                                            *)
(* ANCESTORS FOUND IN INFOTHEO (searched with rocq_query "Search centropy     *)
(* comp", "Search pfwd1 comp"):                                               *)
(*   cPr_centropy_RV_comp (information_theory/entropy):                       *)
(*     (forall x y, `Pr[Y = y] != 0 ->                                        *)
(*        cPr_eq X x (f `o Y) (f y) = `Pr[X = x | Y = y]) ->                   *)
(*     `H( X | f `o Y) = `H( X | Y)                                           *)
(*   pfwd1_comp (probability/proba):                                          *)
(*     injective f -> pfwd1 (f `o X) (f a) = `Pr[X = a]                        *)
(*   cpr_eqE (probability/proba):                                             *)
(*     `Pr[X = a | Y = b] = pfwd1 [% X, Y] (a, b) / `Pr[Y = b]                 *)
(* No single infotheo lemma states the injective-relabeling invariance, so it  *)
(* is derived here from those three plus mutual_info_RVE.                      *)

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

(* ---- L7: rotation equivariance ---- *)

(* succ5_val — the value of the successor position. *)
Lemma succ5_val (i : 'I_5) : val (succ5 i) = (i.+1 %% 5)%N.
Proof. by rewrite /succ5 /= inordK // ltn_pmod. Qed.

(* the cut-shift bijection on the sample space *)
Definition cutS (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, succ5 k).

(* pred5, cutSinv — the inverse shift, supplied explicitly so that cutS_bij
   is a Bijective witness rather than a finType cardinality argument. *)
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

Lemma cutS_bij : bijective cutS.
Proof. exact: (Bijective cutSK cutSKV). Qed.

Lemma fdistmap_cutS : fdistmap cutS P = P.
Proof.
apply/fdist_ext => w.
rewrite fdistmapE.
rewrite (big_pred1 (cutSinv w)); last first.
  by move=> i; rewrite !inE /=; apply/idP/idP => [/eqP <-|/eqP ->];
     rewrite ?cutSK ?cutSKV.
by rewrite /P !fdist_uniformE.
Qed.

(* componentwise view transport: reading rotated positions equals reading    *)
(* the original positions after one more cut                                 *)
Lemma ViewT_succ5 k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT (map_tuple succ5 t) w = ViewT t (cutS w).
Proof.
apply: eq_from_tnth => i.
rewrite /ViewT !tnth_mktuple tnth_map succ5_val.
case: w => [[a b] kk] /=.
rewrite /arr /fc_shuffle.
have nr5 : forall (s : seq bool) (i k : nat), size s = 5%N -> (i < 5)%N ->
    (k < 5)%N -> nth false (rot k s) i = nth false s ((i + k) %% 5)%N.
  move=> s i0 k0 Hs Hi Hk.
  move: Hs; case: s => [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]] //= _.
  by case: i0 Hi => [|[|[|[|[|i0]]]]] //= _; case: k0 Hk => [|[|[|[|[|k0]]]]] //=.
rewrite (nr5 _ _ _ (fc_arrange_size a b) (@ltn_pmod (tnth t i).+1 5 isT)
  (ltn_ord kk)).
rewrite (nr5 _ _ _ (fc_arrange_size a b) (ltn_ord (tnth t i)));
  last by rewrite succ5_val ltn_pmod.
rewrite succ5_val modnDml modnDmr.
by rewrite addSnnS.
Qed.

(* the full rotation-equivariance shape *)
Lemma leak_rot1 k (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (map_tuple succ5 t) ) = `I( Secret ; ViewT t ).
Proof.
rewrite /mutual_info_RV; congr (mutual_info _).
have -> : [% Secret, ViewT (map_tuple succ5 t)] = [% Secret, ViewT t] \o cutS.
  apply: boolp.funext => w; rewrite /RV2 /=.
  by rewrite ViewT_succ5; case: w => [[a b] kk].
by rewrite /dist_of_RV -fdistmap_comp fdistmap_cutS.
Qed.

(* ---- L9: the empty view is constant and leaks nothing ---- *)

(* count_pr — replicated from five_card_leakage.v lines 132-139. *)
Lemma count_pr (A : finType) (X : {RV P -> A}) (x : A) :
  pfwd1 X x = #|preim X (pred1 x)|%:R / 20%:R :> R.
Proof.
rewrite -dist_of_RVE /dist_of_RV fdistmapE.
under eq_bigr do rewrite fdist_uniformE.
rewrite big_const GRing.iter_addr_0 card_Omega20.
by rewrite -[20^-1 *+ _]mulr_natl mulrC.
Qed.

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

(* ---- L10: membership-bit case split ---- *)

(* miniature at 'I_2: the same identification shape, 4 subsets *)
Lemma set2_cases (A : {set 'I_2}) :
  [\/ A = set0, A = [set ord0],
      A = [set (inord 1 : 'I_2)] | A = [set: 'I_2]].
Proof.
have e1 : nat_of_ord (inord 1 : 'I_2) = 1%N by rewrite inordK.
have dec : forall x : 'I_2, (x == ord0) || (x == (inord 1 : 'I_2)).
  by move=> x; rewrite -!val_eqE /= e1; case: x => [[|[|m]] Hm].
have key : forall B : {set 'I_2},
    (ord0 \in A) = (ord0 \in B) ->
    ((inord 1 : 'I_2) \in A) = ((inord 1 : 'I_2) \in B) -> A = B.
  move=> B h0 h1; apply/setP => x.
  by case/orP: (dec x) => /eqP ->.
case: (boolP (ord0 \in A)) => H0; case: (boolP ((inord 1 : 'I_2) \in A)) => H1.
- by apply: Or44; apply: key; rewrite ?H0 ?H1 in_setT.
- by apply: Or42; apply: key;
    [rewrite H0 !inE eqxx | rewrite (negbTE H1) !inE -val_eqE /= e1].
- by apply: Or43; apply: key;
    [rewrite (negbTE H0) !inE -val_eqE /= e1 | rewrite H1 !inE eqxx].
- by apply: Or41; apply: key; rewrite ?(negbTE H0) ?(negbTE H1) in_set0.
Qed.

(* one worked 'I_5 branch: the literal-identification step of the master    *)
(* proof, at the wrap-adjacent branch {0,4}                                 *)
Lemma set5_branch_04 (A : {set 'I_5}) :
  inord 0 \in A -> inord 4 \in A ->
  inord 1 \notin A -> inord 2 \notin A -> inord 3 \notin A ->
  A = [set inord 0; inord 4].
Proof.
move=> H0 H4 H1 H2 H3.
have dec : forall x : 'I_5, (x == (inord 0 : 'I_5)) || (x == (inord 1 : 'I_5))
    || (x == (inord 2 : 'I_5)) || (x == (inord 3 : 'I_5))
    || (x == (inord 4 : 'I_5)).
  by move=> x; rewrite -!val_eqE /= !inordK //; case: x => [[|[|[|[|[|m]]]]] Hm].
apply/setP => x; move: (dec x).
by case/orP => [/orP[/orP[/orP[]|]|]|] /eqP ->;
   rewrite ?H0 ?H4 ?(negbTE H1) ?(negbTE H2) ?(negbTE H3) !inE
     -!val_eqE /= !inordK.
Qed.

(* ---- L11: anchor bridge, singleton case ---- *)
(* ViewT of the concrete position tuple equals the proven ViewA view; at    *)
(* concrete sizes both live in 1.-tuple bool definitionally.                *)

Lemma ViewT_ViewA_singleton :
  ViewT [tuple (inord 0 : 'I_5)] = ViewA [:: 0%N].
Proof.
apply: boolp.funext => w; apply: val_inj.
by rewrite /ViewT /ViewA /= enum_ordSl enum_ord0 /= tnth0 inordK.
Qed.

End probe_shapes.
