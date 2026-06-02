(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5-on-GF(5)^6 No-Go: no secret-encoding invariant submodule of dim 3 or 4 *)
(*                                                                            *)
(* The wired S_5 instance assigns shares along the natural permutation action *)
(* of S_5 on six GF(5)-coordinates: coordinate 0 is a fixed secret slot, and  *)
(* coordinates 1..5 are permuted.  A covering scheme that recovers the secret *)
(* would need a G-invariant submodule that (a) carries the secret direction   *)
(* e0 and (b) has one of the dimensions in the gap window [:: 3; 4].          *)
(*                                                                            *)
(* This file proves there is none.  The entire no-go reduces to ONE kernel    *)
(* fact about the natural permutation module P = GF(5)^5 of S_5:              *)
(*                                                                            *)
(*   KERNEL FACT (perm_module_no_dim23): P has no G-submodule of dimension    *)
(*   2 or 3.  Equivalently, the submodule dimensions are exactly {0,1,4,5}.   *)
(*                                                                            *)
(* The proof of the kernel fact is elementary and char-5 specific.  For a     *)
(* submodule W:                                                               *)
(*   * if W contains a NON-constant vector v (some v_i <> v_j) then, applying  *)
(*     the transposition tperm i j and subtracting, W contains a multiple of  *)
(*     the difference vector e_i - e_j, hence (rescaling) e_i - e_j itself;    *)
(*     conjugating by the 2-transitive S_5 action, W contains every e_a - e_b, *)
(*     so W contains the sum-zero subspace P_0 of dimension 4, giving         *)
(*     rank W >= 4;                                                            *)
(*   * otherwise every vector of W is constant, so W is contained in the line  *)
(*     spanned by the all-ones vector, giving rank W <= 1.                     *)
(* Hence rank W in {0,1,4,5}, never 2 or 3.  (The hypothesis char F = 5 is     *)
(* what places the all-ones vector inside P_0 and makes the lattice uniserial; *)
(* in coprime characteristic Maschke would split P_0 = <1> (+) (dim-3 heart)   *)
(* and dimensions 2,3 WOULD appear.  See invariant_profiler.maschke_ss.)       *)
(*                                                                            *)
(* The six-coordinate reduction turns a secret-encoding invariant submodule of *)
(* dimension d on GF(5)^6 into a submodule of dimension d-1 on the five-       *)
(* coordinate natural module P, so the kernel fact refutes d in {3,4}.         *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import mxrepresentation.
From pgg_reconstruct Require Import gap_dimension invariant_profiler.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.

(* Coordinate action of a permutation matrix on a row vector.
   Kind: helper.
   What: post-multiplying a row vector by perm_mx s permutes its entries by
         the inverse of s: coordinate j of v *m perm_mx s reads v at s^-1 j.
   Why: the computational backbone of every action argument below (difference
        vectors, transposition closure, constancy).
   Used-by: dvec_act and the constancy argument of perm_module_no_dim23. *)
Lemma perm_mx_actE (n : nat) (v : 'rV['F_5]_n) (s : {perm 'I_n}) (j : 'I_n) :
  (v *m perm_mx s) 0 j = v 0 ((s^-1)%g j).
Proof.
rewrite mxE (bigD1 ((s^-1)%g j)) //= !mxE permKV eqxx /= mulr1.
rewrite big1 ?addr0 // => k /negbTE Hk.
rewrite !mxE.
have -> : (s k == j) = (k == s^-1 j)
  by apply/eqP/eqP => [<-|->]; rewrite ?permK ?permKV.
by rewrite Hk mulr0.
Qed.

(* The four-row witness matrix of rank 4 inside the sum-zero subspace.
   Kind: helper.
   What: Dmx is the 4 x 5 matrix [ I_4 | -1 ], whose row i is the difference
         vector e_i - e_4.
   Why: provides a concrete rank-4 lower bound for any submodule that contains
        every difference vector e_a - e_b.
   Used-by: Dmx_rank, Dmx_row, and the rank-4 branch of the kernel fact. *)
Definition Dmx : 'M['F_5]_(4, 4 + 1) := row_mx 1%:M (const_mx (-1)).

(* Rank of the witness matrix.
   Kind: helper.
   What: \rank Dmx = 4.
   Why: the left block of Dmx is the identity, so its rank is full (4).
   Used-by: rank-4 branch of perm_module_no_dim23. *)
Lemma Dmx_rank : \rank Dmx = 4.
Proof.
apply/eqP; rewrite eqn_leq rank_leq_row /=.
have HM : Dmx *m col_mx 1%:M 0 = 1%:M.
  by rewrite /Dmx mul_row_col mulmx1 mulmx0 addr0.
have := mxrankM_maxl Dmx (col_mx (1%:M : 'M['F_5]_4) (0 : 'M['F_5]_(1, 4))).
by rewrite HM mxrank1.
Qed.

(* Rows of the witness matrix are difference vectors.
   Kind: helper.
   What: row i of Dmx equals e_(lshift 1 i) - e_(rshift 4 ord0), the difference
         of the i-th and the last standard basis row vectors.
   Why: connects the abstract rank-4 bound to the concrete membership "every
        difference vector lies in W".
   Used-by: rank-4 branch of perm_module_no_dim23. *)
Lemma Dmx_row (i : 'I_4) :
  row i Dmx = delta_mx 0 (lshift 1 i) - delta_mx 0 (rshift 4 ord0).
Proof.
apply/rowP => k; rewrite !mxE.
case: (split_ordP k) => l ->; rewrite !mxE eqxx /=.
- by rewrite eq_lrshift subr0 (inj_eq (@lshift_inj _ _)) eq_sym.
- rewrite eq_rlshift (inj_eq (@rshift_inj _ _)) [in X in _ - X]ord1 eqxx.
  by rewrite sub0r.
Qed.

Section Kernel.

Local Notation F := 'F_5.
Local Notation gT := {perm 'I_5}.
Local Notation G := [set: gT].

(* The natural permutation representation of S_5 on GF(5)^5.
   Kind: canonical.
   What: prep packages perm_mx as an mx_repr of the full symmetric group on
         five points; rG is the corresponding mx_representation.
   Why: the carrier of the kernel fact. *)
Definition prep : mx_repr G (fun s => perm_mx s : 'M[F]_5).
Proof. split=> [|x y _ _]; [exact: perm_mx1 | exact: perm_mxM]. Defined.

Definition rG : mx_representation F G 5 := MxRepresentation prep.

(* rG unfolds to perm_mx.
   Kind: helper. What: rG s = perm_mx s. Why: rewriting bridge.
   Used-by: every action lemma below. *)
Lemma rGE s : rG s = perm_mx s. Proof. by []. Qed.

(* Difference closure of a submodule.
   Kind: helper.
   What: a submodule W is closed under v |-> v - v *m perm_mx s, since both v
         and its image under the group action lie in W and W is a subspace.
   Why: turns the group action into the difference vectors that drive the
        rank-4 branch.
   Used-by: nonconst_dvec_in. *)
Lemma diff_in (m : nat) (W : 'M[F]_(m, 5)) (modW : mxmodule rG W)
    (v : 'rV[F]_5) (s : gT) :
  (v <= W)%MS -> (v - v *m perm_mx s <= W)%MS.
Proof.
move=> vW.
have HvsW : (v *m perm_mx s <= W)%MS.
  by rewrite -rGE; apply: mxmodule_trans => //; rewrite inE.
apply: addmx_sub => //.
by rewrite -scaleN1r scalemx_sub.
Qed.

(* The transposition-difference identity.
   Kind: helper.
   What: v - v *m perm_mx (tperm i j) equals (v_i - v_j) scaled by the
         difference vector e_i - e_j.
   Why: shows the difference closure produces a scalar multiple of a single
        difference vector e_i - e_j whenever v_i <> v_j.
   Used-by: nonconst_dvec_in. *)
Lemma tperm_diff (v : 'rV[F]_5) (i j : 'I_5) :
  (v - v *m perm_mx (tperm i j) =
   (v 0 i - v 0 j) *: (delta_mx 0 i - delta_mx 0 j))%R.
Proof.
apply/rowP => k.
rewrite mxE [in X in _ + X]mxE perm_mx_actE tpermV !mxE.
case: (eqVneq k i) => [->|Hki].
- rewrite tpermL eqxx.
  case: (eqVneq i j) => [->|Hij].
  + by rewrite subrr subrr mulr0.
  + by rewrite /= subr0 mulr1.
- case: (eqVneq k j) => [->|Hkj].
  + by rewrite tpermR /= sub0r mulrN1 opprB.
  + by rewrite tpermD 1?eq_sym //= subrr subrr mulr0.
Qed.

(* The group permutes difference vectors.
   Kind: helper.
   What: (e_i - e_j) *m perm_mx s = e_(s i) - e_(s j); the natural action sends
         the difference vector indexed by (i,j) to the one indexed by (s i,s j).
   Why: lets a single difference vector in W generate every difference vector by
        2-transitivity of S_5.
   Used-by: all_dvec_in. *)
Lemma dvec_act (i j : 'I_5) (s : gT) :
  ((delta_mx 0 i - delta_mx 0 j : 'rV[F]_5) *m perm_mx s
   = delta_mx 0 (s i) - delta_mx 0 (s j))%R.
Proof.
apply/rowP => k; rewrite perm_mx_actE !mxE.
by rewrite !(can2_eq (permKV s) (permK s)).
Qed.

(* A non-constant vector forces a difference vector into the submodule.
   Kind: helper.
   What: if v lies in W and its i-th and j-th coordinates differ, then the
         difference vector e_i - e_j lies in W.
   Why: this is the trigger of the rank-4 branch: any submodule that is not
        contained in the constant line contains a difference vector.
   Used-by: perm_module_no_dim23 (rank-4 branch). *)
Lemma nonconst_dvec_in (m : nat) (W : 'M[F]_(m, 5)) (modW : mxmodule rG W)
    (v : 'rV[F]_5) (i j : 'I_5) :
  (v <= W)%MS -> v 0 i != v 0 j ->
  ((delta_mx 0 i - delta_mx 0 j : 'rV[F]_5) <= W)%MS.
Proof.
move=> vW Hij.
have Hd : (v - v *m perm_mx (tperm i j) <= W)%MS by apply: diff_in.
rewrite tperm_diff in Hd.
have Hu : (v 0 i - v 0 j) != 0 by rewrite subr_eq0.
have := scalemx_sub ((v 0 i - v 0 j)^-1) Hd.
by rewrite scalerA mulVf // scale1r.
Qed.

(* Two-transitivity of the full symmetric group on an arbitrary index set.
   Kind: helper.
   What: for any two ordered pairs of distinct points (a,b) and (c,d), there is
         a permutation sending a to c and b to d.
   Why: realises the orbit of a difference vector under S_5 as all difference
        vectors, which all_dvec_in feeds into the rank-4 bound.
   Used-by: all_dvec_in. *)
Lemma pair_perm (k : nat) (a b c d : 'I_k) :
  a != b -> c != d ->
  exists s : {perm 'I_k}, s a = c /\ s b = d.
Proof.
move=> Hab Hcd.
pose s1 := tperm a c.
exists (s1 * tperm (s1 b) d)%g; rewrite !permM.
have Hs1a : s1 a = c by rewrite /s1 tpermL.
split.
- rewrite Hs1a tpermD //; last by rewrite eq_sym.
  rewrite /s1; apply: contraNneq Hab => Hsb.
  by rewrite -(tpermK a c b) /s1 Hsb tpermR.
- by rewrite tpermL.
Qed.

(* One difference vector in W forces them all.
   Kind: helper.
   What: if e_a - e_b lies in W (with a <> b) then e_c - e_d lies in W for every
         c <> d.
   Why: combines dvec_act and pair_perm; the difference vectors span the sum-
        zero subspace, so this is the substance of the rank-4 bound.
   Used-by: perm_module_no_dim23 (rank-4 branch). *)
Lemma all_dvec_in (m : nat) (W : 'M[F]_(m, 5)) (modW : mxmodule rG W)
    (a b c d : 'I_5) :
  a != b -> c != d ->
  ((delta_mx 0 a - delta_mx 0 b : 'rV[F]_5) <= W)%MS ->
  ((delta_mx 0 c - delta_mx 0 d : 'rV[F]_5) <= W)%MS.
Proof.
move=> Hab Hcd Hin.
have [s [Hsa Hsb]] := @pair_perm 5 a b c d Hab Hcd.
have := mxmodule_trans modW (x := s) (in_setT s) Hin.
by rewrite rGE dvec_act Hsa Hsb.
Qed.

(* The rank-4 lower bound: a single difference vector forces rank >= 4.
   Kind: helper.
   What: if some difference vector e_a - e_b (a <> b) lies in W, then rank W is
         at least 4, because then every difference vector lies in W and the
         witness matrix Dmx (rank 4) is contained in W.
   Why: the substance of the rank-4 branch of the kernel fact.
   Used-by: perm_module_no_dim23. *)
Lemma rank4_of_dvec (m : nat) (W : 'M[F]_(m, 5)) (modW : mxmodule rG W)
    (a b : 'I_5) :
  a != b ->
  ((delta_mx 0 a - delta_mx 0 b : 'rV[F]_5) <= W)%MS ->
  (4 <= \rank W)%N.
Proof.
move=> Hab Hin.
have HDW : (Dmx <= W)%MS.
  apply/row_subP => i; rewrite Dmx_row.
  have Hcd : (lshift 1 i != rshift 4 ord0 :> 'I_5).
    by rewrite -val_eqE /= addn0 neq_ltn ltn_ord.
  exact: (@all_dvec_in m W modW a b _ _ Hab Hcd Hin).
by have := mxrankS HDW; rewrite Dmx_rank.
Qed.

(* The kernel fact: the S_5 permutation module over GF(5) has no submodule of
   dimension 2 or 3.
   Kind: main.
   What: every G-submodule W of the natural permutation module GF(5)^5 has rank
         either at most 1 or at least 4; equivalently, no submodule has rank 2
         or 3.
   Why: this is the single representation-theoretic obstruction that the whole
        no-go reduces to.  Either W is contained in the all-ones line (rank <= 1)
        or W carries a non-constant vector, which forces a difference vector into
        W (nonconst_dvec_in) and hence rank >= 4 (rank4_of_dvec).  The all-ones
        vector sits inside the sum-zero subspace precisely because char F = 5
        divides the dimension 5, so the lattice is uniserial and the middle
        dimensions never occur.
   Used-by: s5_no_secret_dim3 and s5_no_secret_dim4 via the six-coordinate
        reduction. *)
Lemma perm_module_no_dim23 (m : nat) (W : 'M['F_5]_(m,5)) :
  mxmodule rG W -> (\rank W <= 1)%N || (4 <= \rank W)%N.
Proof.
move=> modW.
case: (boolP (W <= <<(const_mx (1%R) : 'rV['F_5]_5)>>)%MS) => [Hsub|Hnsub].
  apply/orP; left.
  apply: leq_trans (mxrankS Hsub) _.
  by rewrite genmxE; apply: rank_leq_row.
have [i Hi] := row_subPn Hnsub.
have Hconst : forall (v : 'rV['F_5]_5),
    (forall a b, v 0 a = v 0 b) -> (v <= <<(const_mx (1%R) : 'rV['F_5]_5)>>)%MS.
  move=> v Hv.
  have Hve : v = ((v 0 0) *: const_mx (1%R))%R.
    apply/rowP => k; rewrite !mxE mulr1.
    by rewrite (Hv k 0).
  rewrite Hve; apply: scalemx_sub.
  by rewrite (genmxE (const_mx (1%R) : 'rV['F_5]_5)); apply: submx_refl.
have Hex : ~~ [forall a, [forall b, (row i W) 0 a == (row i W) 0 b]].
  apply: contra Hi => /forallP Hall.
  apply: Hconst => a b.
  by have /forallP/(_ b)/eqP := Hall a.
move: Hex; rewrite negb_forall => /existsP [a].
rewrite negb_forall => /existsP [b Hab].
apply/orP; right.
have Hab' : a != b by apply: contraNneq Hab => ->.
have Hdin := nonconst_dvec_in modW (row_sub i W) Hab.
exact: (rank4_of_dvec modW Hab' Hdin).
Qed.

End Kernel.

Section SecretSixDim.

Local Notation F := 'F_5.
Local Notation gT := {perm 'I_5}.
Local Notation G := [set: gT].

(* The six-coordinate secret representation of S_5 over GF(5).
   Kind: canonical.
   What: rGVfun s is the block-diagonal matrix that fixes coordinate 0 (the
         secret slot) and permutes coordinates 1..5 by perm_mx s; under the 1+5
         block layout this is block_mx 1 0 0 (perm_mx s).
   Why: this is the representation actually wired into the S_5 covering scheme:
        the secret lives in the fixed coordinate 0 and the shares are the five
        permuted coordinates. *)
Definition rGVfun (s : gT) : 'M[F]_(1 + 5) :=
  block_mx 1%:M 0 0 (perm_mx s).

(* rGVfun is a matrix representation.
   Kind: instance.
   What: rGVfun is multiplicative and unital, hence an mx_repr of G.
   Why: packages the block-diagonal action as an mx_representation so the
        invariant-submodule machinery applies. *)
Lemma rGVfun_repr : mx_repr G rGVfun.
Proof.
split=> [|x y _ _].
  by rewrite /rGVfun perm_mx1 -scalar_mx_block.
rewrite /rGVfun perm_mxM mulmx_block.
by rewrite mul1mx !mulmx0 !mul0mx !addr0 !add0r.
Qed.

Definition rGV : mx_representation F G (1 + 5) := MxRepresentation rGVfun_repr.

(* The secret direction.
   Kind: canonical.
   What: e0 is the standard basis row vector at coordinate 0 (the secret slot)
         in the 1+5 layout.
   Why: a covering scheme recovers the secret exactly when its invariant
        submodule contains e0. *)
Definition e0 : 'rV[F]_(1 + 5) := delta_mx 0 (lshift 5 0).

(* The projection that discards the secret coordinate.
   Kind: helper.
   What: Pr is the (1+5) x 5 matrix col_mx 0 1, so v *m Pr keeps the last five
         (share) coordinates of v and drops coordinate 0.
   Why: the reduction sends a six-coordinate invariant submodule to its image
        under Pr, a submodule of the five-coordinate kernel module rG.
   Used-by: secret_reduction and the no-go theorems. *)
Definition Pr : 'M[F]_(1 + 5, 5) := col_mx 0 1%:M.

(* The projection intertwines the two actions.
   Kind: helper.
   What: rGV s *m Pr = Pr *m perm_mx s; projecting after the six-coordinate
         action equals acting on the five share coordinates after projecting.
   Why: this intertwining is what makes the projected submodule rG-invariant.
   Used-by: W_module. *)
Lemma rGV_Pr_comm (s : {perm 'I_5}) : rGV s *m Pr = Pr *m perm_mx s.
Proof.
rewrite /rGV /= /rGVfun /Pr mul_block_col mul_col_mx.
by rewrite !mul0mx !mulmx0 !mulmx1 !mul1mx !addr0 !add0r.
Qed.

(* The secret direction lies in the kernel of the projection.
   Kind: helper.
   What: e0 *m Pr = 0; projecting away coordinate 0 annihilates the secret
         direction.
   Why: this is why the rank drops by exactly one under projection: the
        coordinate-0 line that e0 contributes to U is killed by Pr.
   Used-by: W_rank_pred. *)
Lemma e0_Pr : e0 *m Pr = 0.
Proof.
apply/rowP => k; rewrite !mxE big_split_ord /= big1 ?big1 ?addr0 //.
- by move=> i _; rewrite !mxE eq_rlshift andbF mul0r.
- by move=> i _; rewrite !mxE (unsplitK (inl i)) mxE mulr0.
Qed.

(* The projection has full column rank.
   Kind: helper.
   What: \rank Pr = 5.
   Why: a full-rank projection has a one-dimensional kernel (mxrank_ker gives
        6 - 5 = 1), which pins the rank drop to exactly one.
   Used-by: W_rank_pred. *)
Lemma Pr_rank : \rank Pr = 5.
Proof.
apply/eqP; rewrite eqn_leq rank_leq_col /=.
apply: leq_trans (mxrankS (_ : ((1%:M : 'M['F_5]_5) <= Pr)%MS)).
  by rewrite mxrank1.
apply/submxP; exists (row_mx 0 1%:M : 'M['F_5]_(5, 1+5)).
by rewrite /Pr mul_row_col mul0mx mul1mx add0r.
Qed.

(* The projection of an invariant six-coordinate submodule is rG-invariant.
   Kind: helper.
   What: if U is an rGV-submodule then U *m Pr is an rG-submodule of the five-
         coordinate kernel module.
   Why: the projected submodule is the object to which the kernel fact
        perm_module_no_dim23 applies.
   Used-by: s5_no_secret_dim3 and s5_no_secret_dim4. *)
Lemma W_module (m : nat) (U : 'M['F_5]_(m, 1+5)) :
  mxmodule rGV U -> mxmodule rG (U *m Pr).
Proof.
move=> /mxmoduleP modU; apply/mxmoduleP => s _.
rewrite rGE -mulmxA -rGV_Pr_comm mulmxA.
apply: submxMr.
by have := modU s (in_setT s).
Qed.

(* Projection drops the rank by exactly one when the secret is present.
   Kind: helper.
   What: if e0 <= U then \rank (U *m Pr) = (\rank U).-1.
   Why: the secret direction e0 is the unique direction U has inside the one-
        dimensional kernel of Pr, so exactly one dimension is lost.  This is the
        rank bookkeeping that turns a dimension-d secret submodule into a
        dimension-(d-1) submodule of the kernel module.
   Used-by: s5_no_secret_dim3 and s5_no_secret_dim4. *)
Lemma W_rank_pred (m : nat) (U : 'M['F_5]_(m, 1+5)) :
  (e0 <= U)%MS -> \rank (U *m Pr) = (\rank U).-1.
Proof.
move=> He0.
have He0k : (e0 <= kermx Pr)%MS by apply/sub_kermxP; exact: e0_Pr.
have He0n : e0 != 0.
  apply/eqP => H; move/matrixP/(_ 0 (lshift 5 0)): H.
  by rewrite /e0 !mxE !eqxx /= => /eqP; rewrite oner_eq0.
have Hcape0 : (e0 <= U :&: kermx Pr)%MS by rewrite sub_capmx He0 He0k.
have Hcap1 : \rank (U :&: kermx Pr)%MS = 1%N.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - apply: leq_trans (mxrankS (capmxSr U (kermx Pr))) _.
    by rewrite mxrank_ker Pr_rank.
  - rewrite lt0n mxrank_eq0; apply/negP => /eqP H0.
    by move: Hcape0; rewrite H0 submx0 (negbTE He0n).
have := mxrank_mul_ker U Pr.
rewrite Hcap1 addn1 => <-.
by rewrite succnK.
Qed.

End SecretSixDim.

(* No secret-encoding invariant submodule of dimension 3.
   Kind: main.
   What: there is no rGV-submodule of dimension 3 that contains the secret
         direction e0.
   Why: such a submodule U would project (W_module, W_rank_pred) to an rG-
         submodule of dimension 3 - 1 = 2 of the kernel module, but
         perm_module_no_dim23 forbids dimension 2. *)
Theorem s5_no_secret_dim3 : ~ secret_inv_dim rGV e0 3.
Proof.
case=> m [U [modU rkU He0]].
have modW := W_module modU.
have rkW := W_rank_pred He0.
rewrite rkU /= in rkW.
have := perm_module_no_dim23 modW.
by rewrite rkW.
Qed.

(* No secret-encoding invariant submodule of dimension 4.
   Kind: main.
   What: there is no rGV-submodule of dimension 4 that contains the secret
         direction e0.
   Why: such a submodule U would project to an rG-submodule of dimension
         4 - 1 = 3 of the kernel module, but perm_module_no_dim23 forbids
         dimension 3. *)
Theorem s5_no_secret_dim4 : ~ secret_inv_dim rGV e0 4.
Proof.
case=> m [U [modU rkU He0]].
have modW := W_module modU.
have rkW := W_rank_pred He0.
rewrite rkU /= in rkW.
have := perm_module_no_dim23 modW.
by rewrite rkW.
Qed.

(* The S_5 gate rejects the gap window [:: 3; 4].
   Kind: main.
   What: the secret representation rGV is not feasible over the gap window
         [:: 3; 4]; no recoverable secret-encoding invariant submodule has a
         dimension in that window.
   Why: feasibility over [:: 3; 4] would require a secret submodule of dimension
        3 or 4, both refuted by s5_no_secret_dim3 and s5_no_secret_dim4.  This is
        the no-go that disqualifies the wired S_5 instance from the gap window. *)
Theorem s5_gate_rejects : ~ feasible rGV e0 [:: 3; 4].
Proof.
case=> d [Hd Hsec].
move: Hd; rewrite !inE => /orP[] /eqP Hd; rewrite Hd in Hsec.
- exact: s5_no_secret_dim3 Hsec.
- exact: s5_no_secret_dim4 Hsec.
Qed.

(* The S_5 wired gap is impossible: the gate fires on the whole gap regime.
   Kind: main.
   What: under the AG-Massey relations at length n = 6 (ts_T = n-1 = 5,
         ts_k = k-g, code dimension k), any parameters admitting a strict
         threshold gap force the required code dimension k into {3,4}
         (gap_dim_window), and no secret-encoding S_5-invariant submodule of
         either dimension exists (s5_no_secret_dim3/4). Hence no secret-encoding
         invariant code of dimension k exists for a gap instance.
   Why: this is the end-to-end prevention statement: it composes the gap-to-
        dimension window (gap_dimension.v, the required dimensions) with the
        representation-theoretic no-go (the available dimensions) to prove the
        wired S_5 gap mathematically impossible, which is exactly the dead end
        the cs_gap_feasible gate is meant to reject before any code is built. *)
Theorem s5_wired_gap_impossible (k g : nat) :
  (g < k)%N -> (k + g < 6)%N -> (6 <= k + g + 1)%N -> (k - g < 6 - 1)%N ->
  ~ secret_inv_dim rGV e0 k.
Proof.
move=> gk kg6 k6 gap.
have [g0 k1 k4] := gap_dim_window gk kg6 k6 gap.
clear gap.
move: gk kg6 k6 g0 k1 k4.
case: k => [|[|[|[|[|k']]]]] gk kg6 k6 g0 k1 k4 //.
- by move: gk g0 k6 kg6; case: g => [|[|g']].
- exact: s5_no_secret_dim3.
- exact: s5_no_secret_dim4.
Qed.
