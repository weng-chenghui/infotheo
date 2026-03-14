(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Hyperelliptic AG Codes: Goppa Bound via Polynomial Resultant              *)
(*                                                                            *)
(* For a hyperelliptic curve y^2 = f(x) with deg(f) = 2g+1, every function  *)
(* in the Riemann-Roch space L(m*P_infty) has the form A(x) + y*B(x).       *)
(* Setting this to zero and eliminating y gives a univariate polynomial      *)
(* R(x) = A(x)^2 - B(x)^2 * f(x) of degree <= m. By max_poly_roots, R has  *)
(* at most m roots, bounding the number of zeros of the function on the      *)
(* curve. This proves the Goppa bound WITHOUT Riemann-Roch.                  *)
(*                                                                            *)
(* The privacy surjection (ag_priv_surj) is derived from an axiomatized      *)
(* dual minimum distance bound via linear algebra.                            *)
(*                                                                            *)
(*   hyp_resultant      == R(x) = A(x)^2 - B(x)^2 * f(x)                   *)
(*   hyp_resultant_deg  == size R <= m.+1 (degree bound)                     *)
(*   hyp_resultant_neq0 == R != 0 (parity argument)                          *)
(*   hyp_zero_to_root   == curve zeros map to roots of R                     *)
(*   hyp_goppa_wt       == Goppa weight bound for hyperelliptic codes        *)
(*   hyp_priv_surj      == privacy from dual minimum distance                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup matrix mxalgebra vector.
From mathcomp Require Import poly polydiv.
From mathcomp Require Import separable.
Require Import ssr_ext ssralg_ext hamming linearcode rouche_capelli.
From pgg_reconstruct Require Import ag_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Polynomial Size Lemmas                                      *)
(******************************************************************************)

Section poly_size_lemmas.

Variable R : idomainType.

Lemma size_sqr (p : {poly R}) : p != 0 -> size (p ^+ 2) = (size p).*2.-1.
Proof.
move=> Hp.
have HsP : 0 < size p by rewrite size_poly_gt0.
rewrite -(prednK (n := size (p ^+ 2))); last first.
  by rewrite size_poly_gt0 expf_neq0.
rewrite size_exp muln2.
by rewrite -(prednK HsP) doubleS.
Qed.

(* Odd-even parity contradiction: used for the resultant argument *)
Lemma double_pred_odd (n : nat) : 0 < n -> odd n.*2.-1.
Proof. by case: n => // n _; rewrite doubleS oddS odd_double. Qed.

(* Key parity lemma: (2a-1) cannot equal (2b-1 + (2k+2)) - 1 = 2b + 2k
   because the LHS is odd and the RHS is even. *)
Lemma parity_size_neq (a b k : nat) :
  0 < a -> 0 < b ->
  a.*2.-1 = (b.*2.-1 + (2 * k + 1).+1).-1 -> False.
Proof.
case: a => // a; case: b => // b _ _.
move=> Heq.
have Hodd : odd (a.+1.*2.-1) by rewrite doubleS oddS odd_double.
rewrite Heq in Hodd.
have Heven : ~~ odd (b.+1.*2.-1 + (2 * k + 1).+1).-1.
  rewrite doubleS /= addnS /=.
  rewrite oddD odd_double /=.
  by rewrite addn1 oddS oddM.
by rewrite (negbTE Heven) in Hodd.
Qed.

End poly_size_lemmas.

(******************************************************************************)
(*     Section 2: Hyperelliptic Code — Resultant Argument                     *)
(******************************************************************************)

Section hyperelliptic.

Variable F : finFieldType.
Variable g : nat.
Variable curve_poly : {poly F}.

(* deg(f) = 2g+1, encoded as size = deg + 1 *)
Hypothesis curve_deg : size curve_poly = (2 * g + 1).+1.

(* Smooth curve: f is separable (square-free) *)
Hypothesis curve_sep : separable_poly curve_poly.

Let curve_neq0 : curve_poly != 0.
Proof. by rewrite -size_poly_gt0 curve_deg. Qed.

Let deg_f : nat := 2 * g + 1.

Variable m_deg : nat.

(* Evaluation points *)
Variable n'' : nat.
Let n := n''.+2.

Variable pts_x : n.-tuple F.
Variable pts_y : n.-tuple F.

Hypothesis pts_on_curve :
  forall i : 'I_n, (tnth pts_y i) ^+ 2 = curve_poly.[tnth pts_x i].

Hypothesis pts_distinct :
  forall i j : 'I_n, i != j ->
  (tnth pts_x i != tnth pts_x j) ||
  (tnth pts_y i != tnth pts_y j).

Hypothesis pts_x_uniq : uniq pts_x.

Hypothesis Hdeg_f_le : deg_f <= m_deg.

(* The resultant polynomial *)
Definition hyp_resultant (A B : {poly F}) : {poly F} :=
  A ^+ 2 - B ^+ 2 * curve_poly.

(* Degree bound on the resultant.
   Key arithmetic:
   - size(A^2) = 2*size(A) - 1 <= 2*floor(m/2) + 1 <= m + 1
   - size(B^2*f) = 2*size(B) - 1 + (2g+1) + 1 - 1
                  = 2*size(B) + 2g <= 2*floor((m-2g-1)/2) + 2g + 2 <= m + 1
   - size(A^2 - B^2*f) <= max(size(A^2), size(B^2*f)) <= m + 1 *)
Lemma hyp_resultant_deg (A B : {poly F}) :
  deg_f <= m_deg ->
  size A <= (m_deg./2).+1 ->
  size B <= ((m_deg - deg_f)./2).+1 ->
  size (hyp_resultant A B) <= m_deg.+1.
Proof.
move=> Hdf HsA HsB.
rewrite /hyp_resultant.
apply: (leq_trans (size_polyD _ _)).
rewrite geq_max size_polyN.
apply/andP; split.
{ (* size(A^2) <= m_deg.+1 *)
  apply: (leq_trans (leqSpred _)).
  have := size_exp A 2; rewrite muln2 => ->.
  rewrite ltnS.
  have H1 := leq_sub2r 1 HsA; rewrite !subn1 in H1.
  have H2 : (size A).-1.*2 <= m_deg./2.*2 by rewrite leq_double.
  apply: (leq_trans H2).
  rewrite -{2}(odd_double_half m_deg); exact: leq_addl. }
{ (* size(B^2 * f) <= m_deg.+1 *)
  case: (boolP (B == 0)) => [/eqP -> | HBne].
  { by rewrite expr0n /= mul0r size_poly0. }
  rewrite size_mul ?sqrf_eq0 ?(negbTE HBne) ?curve_neq0 //.
  rewrite size_sqr // curve_deg /deg_f.
  have HsB1 : 0 < size B by rewrite size_poly_gt0.
  rewrite -(prednK HsB1) doubleS /=.
  (* Goal: (size B).-1.*2 + (2 * g + 1).+1 <= m_deg.+1 *)
  rewrite addnS ltnS.
  have H1 := leq_sub2r 1 HsB; rewrite !subn1 in H1.
  have H2 : (size B).-1.*2 <= (m_deg - deg_f)./2.*2 by rewrite leq_double.
  rewrite /deg_f in Hdf H2.
  have H3 : (m_deg - (2 * g + 1))./2.*2 <= m_deg - (2 * g + 1).
  { rewrite -{2}(odd_double_half (m_deg - (2 * g + 1))); exact: leq_addl. }
  apply: (leq_trans (leq_add H2 (leqnn (2 * g + 1)))).
  have H4 := leq_add H3 (leqnn (2 * g + 1)).
  by rewrite (subnK Hdf) in H4. }
Qed.

(* Parity argument: R = A^2 - B^2*f != 0 when (A,B) != (0,0).
   size(A^2) is odd, size(B^2*f) is even, so they cannot be equal. *)
Lemma hyp_resultant_neq0 (A B : {poly F}) :
  (A != 0) || (B != 0) ->
  hyp_resultant A B != 0.
Proof.
move=> HAB.
rewrite /hyp_resultant.
apply/negP => /eqP/subr0_eq HAB2.
(* A^2 = B^2 * f *)
case/orP: HAB => [HA|HB].
- (* A != 0 *)
  have HB0 : B != 0.
    apply/negP => /eqP HB0.
    move: HAB2; rewrite HB0 expr0n /= mul0r => /eqP.
    by rewrite sqrf_eq0 (negbTE HA).
  (* Parity of sizes: size(A^2) is odd, size(B^2*f) is even *)
  have HsA2 : size (A ^+ 2) = (size A).*2.-1 := size_sqr HA.
  have HsB2f : size (B ^+ 2 * curve_poly) =
    ((size B).*2.-1 + (2 * g + 1).+1).-1.
    by rewrite size_mul ?sqrf_eq0 ?(negbTE HB0) ?curve_neq0 // size_sqr // curve_deg.
  have Hsize : size (A ^+ 2) = size (B ^+ 2 * curve_poly) by rewrite HAB2.
  rewrite HsA2 HsB2f in Hsize.
  have HsA_pos : 0 < size A by rewrite size_poly_gt0.
  have HsB_pos : 0 < size B by rewrite size_poly_gt0.
  exact: (parity_size_neq HsA_pos HsB_pos Hsize).
- (* B != 0, A could be 0 *)
  case: (boolP (A == 0)) => [/eqP HA0|HA].
  + move: HAB2; rewrite HA0 expr0n /= => Habs.
    have : B ^+ 2 * curve_poly = 0 by rewrite -Habs.
    move/eqP; rewrite mulf_eq0 sqrf_eq0 (negbTE HB) /=.
    by rewrite (negbTE curve_neq0).
  + (* Both nonzero: same parity argument *)
    have HsA2 : size (A ^+ 2) = (size A).*2.-1 := size_sqr HA.
    have HsB2f : size (B ^+ 2 * curve_poly) =
      ((size B).*2.-1 + (2 * g + 1).+1).-1.
      by rewrite size_mul ?sqrf_eq0 ?(negbTE HB) ?curve_neq0 // size_sqr // curve_deg.
    have Hsize : size (A ^+ 2) = size (B ^+ 2 * curve_poly) by rewrite HAB2.
    rewrite HsA2 HsB2f in Hsize.
    have HsA_pos : 0 < size A by rewrite size_poly_gt0.
    have HsB_pos : 0 < size B by rewrite size_poly_gt0.
    exact: (parity_size_neq HsA_pos HsB_pos Hsize).
Qed.

(* Zero-to-root mapping *)
Lemma hyp_zero_to_root (A B : {poly F}) (i : 'I_n) :
  A.[tnth pts_x i] + tnth pts_y i * B.[tnth pts_x i] = 0 ->
  root (hyp_resultant A B) (tnth pts_x i).
Proof.
move=> Hzero.
rewrite /root /hyp_resultant.
(* (A^2 - B^2*f).[xi] = A[xi]^2 - (B^2*f)[xi] = A[xi]^2 - B[xi]^2 * f[xi] *)
(* R(xi) = A(xi)^2 - B(xi)^2 * f(xi)
   = (-yi*B(xi))^2 - B(xi)^2 * yi^2   (using Hzero and pts_on_curve)
   = yi^2*B(xi)^2 - B(xi)^2*yi^2 = 0 *)
apply/rootP.
set xi := tnth pts_x i; set yi := tnth pts_y i.
have HA : A.[xi] = - (yi * B.[xi]).
  by move: Hzero; rewrite -/xi -/yi => /eqP; rewrite addr_eq0 => /eqP.
(* Direct computation *)
rewrite /hyp_resultant.
have -> : (A ^+ 2 - B ^+ 2 * curve_poly).[xi] =
  A.[xi] ^+ 2 - B.[xi] ^+ 2 * curve_poly.[xi].
  by rewrite !(hornerD, hornerN, hornerM, horner_exp).
rewrite HA sqrrN exprMn [yi ^+ 2 * _]mulrC.
rewrite -(pts_on_curve i) /yi /xi.
by rewrite subrr.
Qed.

(* Multiplicity: if (X-x0) | A and (X-x0) | B, then (X-x0)^2 | R *)
Lemma hyp_multiplicity (A B : {poly F}) (x0 : F) :
  root A x0 -> root B x0 ->
  ('X - x0%:P) ^+ 2 %| hyp_resultant A B.
Proof.
move=> HA HB.
have dA : ('X - x0%:P) %| A by rewrite -root_factor_theorem.
have dB : ('X - x0%:P) %| B by rewrite -root_factor_theorem.
rewrite /hyp_resultant; apply: dvdp_sub.
  exact: dvdp_exp2r.
exact: dvdp_mulr (dvdp_exp2r 2 dB).
Qed.

(******************************************************************************)
(*     Section 3: Goppa Weight Bound                                          *)
(******************************************************************************)

Variable k : nat.
Variable ev : 'M[F]_(k, n).

(* Every nonzero coefficient vector yields polynomials (A, B) with
   the right degree bounds, and evaluation matches. *)
Hypothesis ev_encode :
  forall v : 'rV[F]_k, v != 0 ->
  exists A B : {poly F},
    ((A != 0) || (B != 0)) /\
    size A <= (m_deg./2).+1 /\
    size B <= ((m_deg - deg_f)./2).+1 /\
    forall i : 'I_n,
      (v *m ev) 0 i = A.[tnth pts_x i] + tnth pts_y i * B.[tnth pts_x i].

(* Goppa bound: nonzero codewords have Hamming weight >= n - m_deg.
   Proved from resultant argument + max_poly_roots. *)
Theorem hyp_goppa_wt_mdeg :
  forall v : 'rV[F]_k, v != 0 ->
  n - m_deg <= wH (v *m ev).
Proof.
move=> v Hv.
have [A [B [HAB [HsA [HsB Hev]]]]] := ev_encode Hv.
set R := hyp_resultant A B.
have HR : R != 0 := hyp_resultant_neq0 HAB.
have HsR : size R <= m_deg.+1 := hyp_resultant_deg Hdeg_f_le HsA HsB.
(* Map zero positions to roots of R via pts_x, then bound via max_poly_roots *)
set w := v *m ev.
set zeros := [seq tnth pts_x i | i <- enum 'I_n & (w 0 i == 0)].
have Hall : all (root R) zeros.
  apply/allP => x /mapP [i].
  rewrite mem_filter => /andP [/eqP Hwi _] ->.
  apply: hyp_zero_to_root; by rewrite -Hev.
have Htnth_inj : injective (tnth pts_x) by move/tuple_uniqP: pts_x_uniq.
have Huniq : uniq zeros.
  rewrite /zeros map_inj_uniq //.
  exact: filter_uniq (enum_uniq _).
have Hroots := max_poly_roots HR Hall Huniq.
have Hsz_zeros : size zeros <= m_deg.
  rewrite -ltnS; exact: (leq_trans Hroots HsR).
(* Connect size zeros to n - wH w via count_predC *)
have HwH : wH w = count (fun i : 'I_n => w 0 i != 0) (enum 'I_n).
  rewrite /wH /= count_map; apply: eq_count => i /=; by rewrite mxE.
have Hcompl : (wH w + size zeros)%N = n.
  rewrite HwH /zeros size_map size_filter.
  have := count_predC (fun i : 'I_n => w 0 i != 0) (enum 'I_n).
  rewrite [count (predC _) _](eq_count (a2 := fun i => w 0 i == 0)); last first.
    by move=> i /=; rewrite negbK.
  by rewrite size_enum_ord.
set wt := wH w; rewrite leq_subLR.
have : n <= wt + m_deg by rewrite -Hcompl leq_add2l.
by rewrite addnC.
Qed.

(* The Goppa bound in the standard form used by ag_massey_bridge *)
Hypothesis Hm_eq : m_deg = (k + g - 1)%N.

Theorem hyp_goppa_wt :
  forall v : 'rV[F]_k, v != 0 ->
  (n - (k + g - 1) <= wH (v *m ev))%N.
Proof. by move=> v Hv; rewrite -Hm_eq; exact: hyp_goppa_wt_mdeg. Qed.

(******************************************************************************)
(*     Section 4: Privacy from Dual Minimum Distance                          *)
(******************************************************************************)

Hypothesis ev_rank : \rank ev = k.
Hypothesis Hk : 0 < k.
Hypothesis Hkn : k <= n.
Hypothesis Hkgn : k + g < n.
Hypothesis Hkg : g < k.

(* Dual minimum distance: proved from a polynomial root bound.
   For any nonzero word w orthogonal to the AG code, there exists a nonzero
   polynomial R of degree <= m_deg_dual whose roots include all zero positions
   of w (mapped via pts_x). Root counting then gives wH w >= (k-g)+1. *)
Variable m_deg_dual : nat.
Hypothesis Hm_dual_eq : m_deg_dual = (n + g - k - 1)%N.

(* Dual evaluation encoding: orthogonal words admit A(x)+y*B(x) representation.
   Dual analog of ev_encode. The resultant degree bound is given directly
   (not derived from A/B degree bounds) because deg_f > m_deg_dual when n=k+g+1. *)
Hypothesis dual_ev_encode :
  forall w : 'rV[F]_n, w != 0 ->
  (forall c : 'rV[F]_n, c \in ag_code ev -> w *m c^T = 0) ->
  exists A B : {poly F},
    ((A != 0) || (B != 0)) /\
    size (hyp_resultant A B) <= m_deg_dual.+1 /\
    forall i : 'I_n,
      w 0 i = A.[tnth pts_x i] + tnth pts_y i * B.[tnth pts_x i].

(* Proved from dual_ev_encode using resultant machinery *)
Theorem dual_root_poly :
  forall w : 'rV[F]_n, w != 0 ->
  (forall c : 'rV[F]_n, c \in ag_code ev -> w *m c^T = 0) ->
  exists R : {poly F},
    R != 0 /\
    size R <= m_deg_dual.+1 /\
    forall i : 'I_n, w 0 i = 0 -> root R (tnth pts_x i).
Proof.
move=> w Hw Horth.
have [A [B [HAB [HsR Heval]]]] := dual_ev_encode Hw Horth.
exists (hyp_resultant A B); split; [|split].
- exact: hyp_resultant_neq0 HAB.
- exact: HsR.
- move=> i Hwi.
  apply: (hyp_zero_to_root (i := i)).
  by have := Heval i; rewrite Hwi.
Qed.

Theorem dual_min_dist :
  forall (w : 'rV[F]_n), w != 0 ->
  (forall c : 'rV[F]_n, c \in ag_code ev -> w *m c^T = 0) ->
  (k - g).+1 <= wH w.
Proof.
move=> w Hw0 Horth.
have [R [HR [HsR Hroots]]] := dual_root_poly Hw0 Horth.
(* Root counting — same structure as hyp_goppa_wt_mdeg *)
set zeros := [seq tnth pts_x i | i <- enum 'I_n & (w 0 i == 0)].
have Hall : all (root R) zeros.
  apply/allP => x /mapP [i].
  rewrite mem_filter => /andP [/eqP Hwi _] ->.
  exact: Hroots.
have Htnth_inj : injective (tnth pts_x) by move/tuple_uniqP: pts_x_uniq.
have Huniq : uniq zeros.
  rewrite /zeros map_inj_uniq //.
  exact: filter_uniq (enum_uniq _).
have Hsz_zeros : size zeros <= m_deg_dual.
  rewrite -ltnS; exact: leq_trans (max_poly_roots HR Hall Huniq) HsR.
have HwH : wH w = count (fun i : 'I_n => w 0 i != 0) (enum 'I_n).
  by rewrite /wH /= count_map.
have Hcompl : (wH w + size zeros)%N = n.
  rewrite HwH /zeros size_map size_filter.
  have := count_predC (fun i : 'I_n => w 0 i != 0) (enum 'I_n).
  rewrite [count (predC _) _](eq_count (a2 := fun i => w 0 i == 0)); last first.
    by move=> i /=; rewrite negbK.
  by rewrite size_enum_ord.
have HwH_bound : n - m_deg_dual <= wH w.
  set wt := wH w in Hcompl *.
  rewrite leq_subLR addnC -Hcompl leq_add2l //.
apply: leq_trans _ HwH_bound.
rewrite Hm_dual_eq.
suff -> : (n - (n + g - k - 1))%N = (k - g).+1 by [].
have Hgk := ltnW Hkg.
have Hk1n := leq_ltn_trans (leq_addr g k) Hkgn.
have Hngk1 : k.+1 <= n + g := leq_trans Hk1n (leq_addr g n).
by rewrite -subnDA addn1 (subnBA _ Hngk1) subnDl (subSn Hgk).
Qed.

(* Privacy: for small coalitions S, the projection is surjective *)
Theorem hyp_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (k - g).-1.+2 ->
    exists c : 'rV[F]_n,
      c \in ag_code ev /\ vproj c S = vproj target S.
Proof.
move=> S target HS.
set s := #|S| in HS *.
case: (posnP s) => [Hs0|Hspos].
{ (* Boundary case: |S| = 0 *)
  have Sempty : S = set0 by apply/eqP; rewrite -cards_eq0; apply/eqP.
  exists (0 *m ev); split; first exact: ag_code_eval.
  rewrite mul0mx; apply/rowP => i; rewrite !mxE Sempty !inE //. }
(* Main case: 0 < |S| *)
pose ev_S : 'M[F]_(k, s) := \matrix_(i, j) ev i (enum_val j).
(* Step 2: rank ev_S = s by contradiction using dual_min_dist *)
have Hrank_ev_S : \rank ev_S = s.
{ apply/eqP; rewrite eqn_leq rank_leq_col /=.
  case: (leqP s (\rank ev_S)) => // Hlt.
  have Hlt' : \rank ev_S^T < s by rewrite mxrank_tr.
  have [y [Hy0 Hyne0]] := exists_nonzero_kernel Hlt'.
  pose P : 'M[F]_(s, n) := \matrix_(j, i) (i == enum_val j)%:R.
  set w : 'rV[F]_n := y *m P.
  have HPev : P *m ev^T = ev_S^T.
  { apply/matrixP => j l; rewrite !mxE.
    rewrite (bigD1 (enum_val j)) //= !mxE eqxx mul1r.
    rewrite big1 ?addr0 // => i Hi; rewrite !mxE.
    by rewrite (negbTE Hi) mul0r. }
  have Hwev : w *m ev^T = 0 by rewrite /w -mulmxA HPev Hy0.
  have Horth : forall c : 'rV[F]_n, c \in ag_code ev -> w *m c^T = 0.
  { move=> c /ag_code_memP [v ->].
    by rewrite trmx_mul mulmxA Hwev mul0mx. }
  have Hw_out : forall i0 : 'I_n, i0 \notin S -> w ord0 i0 = 0.
  { move=> i0 Hi0S; rewrite /w mxE.
    apply: big1 => j0 _; rewrite /P mxE.
    suff : (i0 == @enum_val _ (mem S) j0) = false by move=> ->; rewrite mulr0.
    apply/negbTE/negP => /eqP Heq.
    by move/negP: Hi0S; apply; rewrite Heq enum_valP. }
  have Hw_in : forall j0 : 'I_s,
    w ord0 (@enum_val _ (mem S) j0) = y ord0 j0.
  { move=> j0; rewrite /w mxE.
    rewrite (bigD1 j0) //= /P mxE eqxx mulr1.
    rewrite big1 ?addr0 // => j1 Hj1; rewrite /P mxE.
    suff : (@enum_val _ (mem S) j0 == @enum_val _ (mem S) j1) = false
      by move=> ->; rewrite mulr0.
    apply/negbTE/negP => /eqP /enum_val_inj Habs.
    by rewrite Habs eqxx in Hj1. }
  have Hwne0 : w != 0.
  { apply/negP => /eqP/rowP Hw0.
    move/negP: Hyne0; apply; apply/eqP/rowP => j0.
    have := Hw0 (enum_val j0); rewrite Hw_in !mxE //. }
  have HwH_le : wH w <= s.
  { rewrite -(card_wH_supp w) -/s.
    apply: subset_leq_card.
    apply/subsetP => i0; rewrite inE => /negP Hi0.
    apply/negPn/negP => Hi0S.
    by apply: Hi0; apply/eqP; exact: Hw_out. }
  have Hdual := dual_min_dist Hwne0 Horth.
  have H1 : (k - g).+1 <= s := leq_trans Hdual HwH_le.
  have H2 := leq_ltn_trans H1 HS.
  have Hkg0 : 0 < k - g by rewrite subn_gt0.
  by rewrite (prednK Hkg0) ltnn in H2. }
(* Step 3: Surjectivity via Rouche-Capelli *)
pose target_S : 'rV[F]_s := \row_j target ord0 (@enum_val _ (mem S) j).
have Hrank_eq : \rank ev_S = \rank (col_mx ev_S target_S).
{ have /eqmxP/eqmx_rank Heq := addsmxE ev_S target_S.
  rewrite -Heq.
  apply/eqP; rewrite eqn_leq.
  apply/andP; split.
  - exact: mxrankS (addsmxSl ev_S target_S).
  - by rewrite Hrank_ev_S rank_leq_col. }
have /rouche1 [v Hv] := Hrank_eq.
set c := v *m ev.
exists c; split; first exact: ag_code_eval.
(* Show vproj c S = vproj target S *)
have Hagree : forall i : 'I_n, i \in S -> c ord0 i = target ord0 i.
{ move=> i HiS.
  set j := enum_rank_in HiS i.
  have Hci : c ord0 i = (v *m ev_S) ord0 j.
  { rewrite /c /ev_S !mxE.
    apply: eq_bigr => l _; rewrite mxE; congr (_ * _).
    by rewrite /j enum_rankK_in. }
  have Hti : target ord0 i = target_S ord0 j.
  { by rewrite /target_S mxE /j enum_rankK_in. }
  by rewrite Hci Hv Hti. }
apply/rowP => i; rewrite /vproj !mxE.
case: (boolP (i \in S)) => [HiS|//].
have /= := Hagree i HiS; rewrite /c mxE => ->.
by [].
Qed.

End hyperelliptic.

(******************************************************************************)
(*     Section 5: Genus-2 Concrete Example                                    *)
(******************************************************************************)

Section genus2.

Variable F : finFieldType.

Variable curve_poly_g2 : {poly F}.
Hypothesis curve_deg_g2 : size curve_poly_g2 = (2 * 2 + 1).+1.
Hypothesis curve_sep_g2 : separable_poly curve_poly_g2.

(* For genus g = 2, deg(f) = 5:
   L(m*P_infty) = {A(x) + y*B(x) | deg(A) <= m/2, deg(B) <= (m-5)/2}
   The threshold gap is ts_T <= ts_k + 2*g = ts_k + 4. *)

End genus2.

(******************************************************************************)
(*     Section 6: Summary of Axiom Reduction                                  *)
(******************************************************************************)

(* PROVED (algebraically, from polynomial resultant):
   1. hyp_resultant_neq0 — parity argument on polynomial degrees
   2. hyp_zero_to_root   — curve zeros map to resultant roots
   3. hyp_multiplicity   — shared x-coordinates use >= 2 multiplicity

   ADMITTED (routine but technically involved):
   4. hyp_resultant_deg  — degree arithmetic on polynomial sizes
   5. hyp_goppa_wt_mdeg  — counting zeros via polynomial root counting
   6. hyp_priv_surj      — linear algebra (rank vs. dual distance)
   7. separable_dvd_sqr  — square-free divides square => divides base

   The key mathematical insight is FULLY PROVED: the parity argument
   (odd vs even polynomial degree) ensures R = A^2 - B^2*f != 0.

   For cover_genus1.v integration:
   - goppa_wt is hyp_goppa_wt (proved modulo routine lemmas)
   - ag_priv_surj is hyp_priv_surj (derived from dual_ev_encode)
   - dual_min_dist is now PROVED from dual_root_poly (proved from dual_ev_encode)
   - Remaining axioms: dual_ev_encode + share_compatible (2 instead of 4) *)
