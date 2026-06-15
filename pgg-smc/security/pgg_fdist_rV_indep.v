(* Coordinate-independence facts for the iid product distribution P `^ n,
   generalized from a fixed size to an arbitrary number of coordinates. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop matrix perm.
From mathcomp Require Import ssralg ssrnum reals zmodp.
From infotheo Require Import realType_ext realType_ln ssralg_ext fdist proba entropy graphoid.

Import GRing.Theory Num.Theory.
Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope.
Local Open Scope ring_scope. Local Open Scope vec_ext_scope.

Section iid_coordinate_independence.
Variable R : realType.
Variable A : finType.
Variable P0 : R.-fdist A.

(** fdist_perm_rV — @composes: inde_RV_nth_rV:
    the iid product distribution is invariant under any coordinate permutation. *)
Lemma fdist_perm_rV n (s : {perm 'I_n}) : fdist_perm (P0 `^ n) s = P0 `^ n.
Proof.
apply/fdist_ext => v. rewrite fdist_permE !fdist_rVE.
under eq_bigr do rewrite mxE. by rewrite [RHS](reindex_perm s).
Qed.

(** inde_RV_head_rV — @composes: inde_RV_nth_rV:
    the head coordinate is independent of the tail vector under any
    post-processing of either side. *)
Lemma inde_RV_head_rV n (TB1 TB2 : finType) (g1 : A -> TB1) (g2 : 'rV[A]_n -> TB2) :
  (P0 `^ n.+1) |= ((fun v : 'rV_n.+1 => g1 (v ord0 ord0)) : {RV (P0 `^ n.+1) -> TB1})
              _|_ ((fun v : 'rV_n.+1 => g2 (rbehead v)) : {RV (P0 `^ n.+1) -> TB2}).
Proof.
rewrite /inde_RV => x y. rewrite !pfwd1E.
have E1 : finset (preim (fun v : 'rV_n.+1 => g1 v``_ord0) (pred1 x))
        = [set v : 'rV_n.+1 | v``_ord0 \in finset (preim g1 (pred1 x))].
  by apply/setP => v; rewrite !inE.
have E2 : finset (preim (fun v : 'rV_n.+1 => g2 (rbehead v)) (pred1 y))
        = [set v : 'rV_n.+1 | rbehead v \in finset (preim g2 (pred1 y))].
  by apply/setP => v; rewrite !inE.
rewrite E1 E2.
rewrite -(Pr_fdist_prod_of_rV1 (P0`^n.+1)) -(Pr_fdist_prod_of_rV2 (P0`^n.+1)).
rewrite (_ : finset (preim [% fun v : 'rV_n.+1 => g1 v``_ord0, fun v : 'rV_n.+1 => g2 (rbehead v)] (pred1 (x, y)))
           = [set v : 'rV[A]_n.+1 | v``_ord0 \in finset (preim g1 (pred1 x)) & rbehead v \in finset (preim g2 (pred1 y))]); last first.
  by apply/setP => v; rewrite !inE /= xpair_eqE; congr (_ && _).
rewrite -Pr_fdist_prod_of_rV.
rewrite fdist_prod_of_fdist_rV.
rewrite (_ : setX (finset (preim g1 (pred1 x))) (finset (preim g2 (pred1 y)))
           = (finset (preim g1 (pred1 x))) `*T :&: T`* (finset (preim g2 (pred1 y)))); last first.
  by apply/setP => -[a b]; rewrite !inE.
by rewrite Pr_fdist_prod.
Qed.

(** inde_RV_col_perm — @composes: inde_RV_nth_rV:
    independence of two coordinate functionals is preserved by precomposing
    both with the same coordinate permutation. *)
Lemma inde_RV_col_perm n (TB1 TB2 : finType)
    (B1 : {RV (P0 `^ n) -> TB1}) (B2 : {RV (P0 `^ n) -> TB2}) (s : {perm 'I_n}) :
  (P0 `^ n) |= B1 _|_ B2 ->
  (P0 `^ n) |= ((fun v => B1 (col_perm s v)) : {RV (P0 `^ n) -> TB1})
            _|_ ((fun v => B2 (col_perm s v)) : {RV (P0 `^ n) -> TB2}).
Proof.
move=> AB.
have Pr_premap : forall (TC : finType) (C : {RV (P0 `^ n) -> TC}) (Q : pred TC),
    Pr (P0 `^ n) (finset (preim (fun v => C (col_perm s v)) Q)) = Pr (P0 `^ n) (finset (preim C Q)).
  move=> TC C Q. rewrite /Pr.
  rewrite [in RHS](reindex (col_perm s)) /=; last first.
    by exists (col_perm (fingroup.invg s)) => w _;
       rewrite -col_permM (fingroup.mulgV, fingroup.mulVg) col_perm1.
  apply: eq_big => [w | w _].
    by rewrite !inE.
  by rewrite -fdist_permE fdist_perm_rV.
rewrite /inde_RV => x y. move: (AB x y). rewrite !pfwd1E.
rewrite (_ : finset (preim [% (fun v => B1 (col_perm s v)), (fun v => B2 (col_perm s v))] (pred1 (x,y)))
           = finset (preim (fun v => [% B1, B2] (col_perm s v)) (pred1 (x,y)))); last by [].
by rewrite !Pr_premap.
Qed.

End iid_coordinate_independence.

Section iid_nth_independence.
Variable R : realType.
Variable A : finType.
Variable P0 : R.-fdist A.

(** inde_RV_nth_rV — @main architecture: coordinate independence of the iid product:
    any single coordinate of the iid product distribution is independent of any
    post-processing of the remaining coordinates. *)
Lemma inde_RV_nth_rV n (TB : finType) (i : 'I_n.+1) (g : 'rV[A]_n -> TB) :
  (P0 `^ n.+1) |= ((fun v : 'rV_n.+1 => v ord0 i) : {RV (P0 `^ n.+1) -> A})
              _|_ ((fun v : 'rV_n.+1 => g (rbehead (col_perm (tperm ord0 i) v)))
                     : {RV (P0 `^ n.+1) -> TB}).
Proof.
rewrite (_ : (fun v : 'rV_n.+1 => v ord0 i)
           = (fun v => (fun w : 'rV_n.+1 => idfun (w ord0 ord0)) (col_perm (tperm ord0 i) v))); last first.
  by apply: boolp.funext => v; rewrite /= mxE tpermL.
apply: (@inde_RV_col_perm R A P0 n.+1 A TB
          (fun w : 'rV_n.+1 => idfun (w ord0 ord0))
          (fun w : 'rV_n.+1 => g (rbehead w))
          (tperm ord0 i)).
exact: (@inde_RV_head_rV R A P0 n A TB idfun g).
Qed.

End iid_nth_independence.

(** fdist_nth_unif — @composes: inde_RV_nth_rV:
    every coordinate marginal of an iid product of a uniform distribution
    is itself that uniform distribution. *)
Lemma fdist_nth_unif (R : realType) (A0 : finType) n m (cardA : #|A0| = m.+1) (i : 'I_n) :
  fdist_nth ((@fdist_uniform R _ _ cardA) `^ n) i = fdist_uniform cardA.
Proof.
case: n i => [|n'] i; first by case: i.
apply/fdist_ext => a. rewrite fdist_nthE.
rewrite -[in RHS](head_of_fdist_rV_fdist_rV n' (fdist_uniform cardA)).
rewrite head_of_fdist_rV_fdist_nth fdist_nthE.
rewrite (reindex (col_perm (tperm ord0 i))) /=; last first.
  by exists (col_perm (tperm ord0 i)) => x _; rewrite -col_permM tperm2 col_perm1.
apply: eq_big => [j | j _].
  by rewrite mxE tpermR.
by rewrite -fdist_permE fdist_perm_rV.
Qed.
