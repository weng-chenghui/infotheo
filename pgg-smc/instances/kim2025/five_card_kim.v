(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Kim-Cetinkaya Five Card Trick under Biased Shuffles (arXiv:2511.05111)     *)
(*                                                                            *)
(* The Five Card Trick (den Boer 1989) normally assumes a uniformly random    *)
(* cyclic cut of 5 cards. Kim & Cetinkaya analyze what happens when the cut   *)
(* is biased: position 0 (no cut) has probability 1/5 - eps, while each of   *)
(* the other 4 positions has probability 1/5 + eps/4.                         *)
(*                                                                            *)
(* PGG formalization:                                                         *)
(*   N = 5 cards, Tg = 5 generators (all cyclic rotations sigma^k, k=0..4)   *)
(*   m = 4 (so Tg = m.+1 = 5), n' = 3 (so N = n'.+2 = 5)                   *)
(*   Weight distribution W_eps on 'I_5:                                       *)
(*     W_eps(0) = 1/5 - eps                                                   *)
(*     W_eps(k) = 1/5 + eps/4  for k = 1, 2, 3, 4                            *)
(*                                                                            *)
(* The Schreier transition matrix is the 5x5 circulant:                       *)
(*   P(x,y) = W_eps(y - x mod 5)                                             *)
(* which equals:                                                              *)
(*   | a  b  b  b  b |                                                        *)
(*   | b  a  b  b  b |     where a = 1/5 - eps, b = 1/5 + eps/4              *)
(*   | b  b  a  b  b |                                                        *)
(*   | b  b  b  a  b |                                                        *)
(*   | b  b  b  b  a |                                                        *)
(*                                                                            *)
(* This matrix is doubly stochastic (circulant => symmetric row/col sums).    *)
(* Eigenvalues: lambda_0 = 1, lambda_{1..4} = a - b = -5*eps/4.              *)
(* After T shuffles: var_dist <= sqrt(5) * |a - b|^T.                         *)
(*                                                                            *)
(* Contents:                                                                  *)
(*   fc_kim_sigmas     == 5 generators: [1, sigma, sigma^2, sigma^3, sigma^4] *)
(*   FiveCardKim_M     == Gen_PGGTypes instance (m=4, n'=3)                   *)
(*   kim_weight_fun    == weight function parameterized by eps                 *)
(*   kim_weight_dist   == FDist from kim_weight_fun (needs positivity hyps)   *)
(*   fc_kim_schreier_circulant == Schreier matrix is circulant                *)
(*   fc_kim_doubly_stochastic  == column sums = 1                             *)
(*   kim_var_dist_exact      == exact var_dist = 8/5 * kim_lambda2^L            *)
(*   fc_kim_security_bundle == certificate bundle with both attachments      *)
(*   fc_kim_schreier_cert        == WeightedSchreierCertificate (sibling packaging)     *)
(*                                                                            *)
(* References:                                                                *)
(*   Kim & Cetinkaya (2025), arXiv:2511.05111                                 *)
(*   den Boer (1989), EUROCRYPT, LNCS 434                                     *)
(*                                                                            *)
(* Exact variation distance (via unif_offdiag_var_dist, NOT eigenvalue        *)
(* decomposition): since Kim's Schreier matrix is uniform-off-diagonal,      *)
(* the general identity from pgg_schreier_weighted.v gives the exact         *)
(* value for all card positions s simultaneously.                             *)
(*                                                                            *)
(* Comparison with Kim & Cetinkaya (arXiv:2511.05111):                       *)
(*                                                                            *)
(*   Convention: Kim uses d_TV = (1/2) sum |P - Q| (standard total           *)
(*   variation). Infotheo uses var_dist = sum |P - Q| (full L1 norm),       *)
(*   so var_dist = 2 * d_TV.  The table below normalises to Kim's d_TV      *)
(*   convention for an apples-to-apples comparison.                          *)
(*                                                                            *)
(*   Writing s = (5/4)*|eps| for the second-largest eigenvalue magnitude:    *)
(*                                                                            *)
(*     Quantity         Kim (pen-and-paper)  Ours (machine-checked)  Match?  *)
(*     --------         ------------------  ----------------------  ------  *)
(*     Spectral bound   sqrt(5)/2 * s^L     sqrt(5)/2 * s^L         Yes     *)
(*     Exact distance   (4/5) * s^L         (4/5) * s^L             Yes     *)
(*     At eps = 0       0                   0                        Yes     *)
(*     Bound / exact    5*sqrt(5)/8 ~ 1.40  5*sqrt(5)/8 ~ 1.40      Yes     *)
(*                                                                            *)
(*   In the code, the proved values are stored as var_dist (= 2 * d_TV):    *)
(*     kim_spectral_convergence : var_dist <= sqrt(5) * s^L                  *)
(*     kim_var_dist_exact       : var_dist  = (8/5) * s^L                    *)
(*   The scb_exact field of fc_kim_security_bundle is populated below.       *)
(******************************************************************************)

From HB Require Import structures.
Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
  pgg_collusion_bound pgg_weighted_words pgg_schreier pgg_schreier_weighted
  five_card_group.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(** * Section 1: Kim's 5-Generator Setup                                      *)
(*                                                                            *)
(* All 5 cyclic rotations as generators: sigma^0 = 1, sigma^1, ..., sigma^4. *)
(* This differs from the standard Five Card Trick PGG instance (1 generator)  *)
(* because Kim's bias model assigns a distinct probability to each rotation.  *)
(******************************************************************************)

Section kim_generators.

Let sigma := fc_sigma.

(** Powers of fc_sigma *)
Definition fc_sigma_pow (k : 'I_5) : {perm 'I_5} := (sigma ^+ val k)%g.

(** The 5 generators for Kim's model *)
Definition fc_kim_sigmas : 5.-tuple {perm 'I_5} :=
  [tuple (1 : {perm 'I_5})%g;
         (sigma ^+ 1)%g;
         (sigma ^+ 2)%g;
         (sigma ^+ 3)%g;
         (sigma ^+ 4)%g].

(** Each generator sigma^k acts as expected *)
Lemma fc_kim_sigmasE (k : 'I_5) : tnth fc_kim_sigmas k = (sigma ^+ val k)%g.
Proof.
by case: k => [[|[|[|[|[|?]]]]] ?];
  rewrite (tnth_nth (1%g : {perm 'I_5})) /=.
Qed.

End kim_generators.

(******************************************************************************)
(** * Section 2: PGG Instance                                                 *)
(******************************************************************************)

Section kim_pgg_instance.

(** m = 4 (5 generators), n' = 3 (N = 5 sheets) *)
Definition FiveCardKim_M : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 4 3 fc_kim_sigmas.

End kim_pgg_instance.

(******************************************************************************)
(** * Section 3: Kim's Biased Weight Distribution                             *)
(*                                                                            *)
(* w_0 = 1/5 - eps, w_k = 1/5 + eps/4 for k = 1,2,3,4                      *)
(* Constraint: eps in (-4/5, 1/5) ensures all weights are positive.          *)
(* Sum: (1/5 - eps) + 4*(1/5 + eps/4) = 1/5 - eps + 4/5 + eps = 1.         *)
(******************************************************************************)

Section kim_weights.

Variable R : realType.

(** The bias parameter *)
Variable eps : R.

(** Positivity constraints *)
Hypothesis eps_lt_inv5 : eps < 5%:R^-1.        (* ensures w_0 > 0 *)
Hypothesis eps_gt_neg4inv5 : - (4%:R * 5%:R^-1) < eps. (* ensures w_k > 0 *)

(** Weight function: w(k) = if k==0 then 1/5 - eps else 1/5 + eps/4 *)
Definition kim_weight_fun : {ffun 'I_5 -> R} :=
  [ffun k : 'I_5 =>
    if val k == 0%N then 5%:R^-1 - eps
    else 5%:R^-1 + eps / 4%:R].

(** kim_weight_gt0 — the Kim weight function is strictly positive.
    Kind: helper.
    Why: strict positivity discharges the support hypothesis in the fdist lift.
    Used by: [kim_weight_ge0] and the downstream fdist construction. *)
Lemma kim_weight_gt0 (k : 'I_5) : 0 < kim_weight_fun k.
Proof.
rewrite ffunE.
case: ifP => Hk.
- (* k = 0: w = 1/5 - eps > 0 since eps < 1/5 *)
  by rewrite subr_gt0.
- (* k != 0: w = 1/5 + eps/4 > 0.
     eps > -(4*5^-1) implies eps/4 > -5^-1, so 5^-1 + eps/4 > 0. *)
  have H4pos : (0 : R) < 4%:R by [].
  have Heps4 : - (5%:R^-1) < eps / 4%:R.
    by rewrite ltr_pdivlMr // mulNr mulrC.
  by rewrite -(subrr (5%:R^-1)) ltrD2l.
Qed.

(** kim_weight_ge0 — the Kim weight function is non-negative.
    Kind: helper.
    Why: non-negativity is required for the fdist construction.
    Used by: the fdist construction for the Kim five-card instance. *)
Lemma kim_weight_ge0 : forall k : 'I_5, 0 <= kim_weight_fun k.
Proof. by move=> k; exact: Order.POrderTheory.ltW (kim_weight_gt0 k). Qed.

(** kim_weight_sum1 — the perturbed Kim weight vector sums to one.
    Kind: helper.
    Why: required to build a Kim-weighted fdist from [kim_weight_fun].
    Used by: the fdist construction for the Kim five-card instance. *)
Lemma kim_weight_sum1 : \sum_(k in 'I_5) kim_weight_fun k = 1.
Proof.
rewrite big_ord_recr /= big_ord_recr /= big_ord_recr /=
        big_ord_recr /= big_ord_recr /= big_ord0 add0r.
rewrite !ffunE /=.
(* Goal: 5^-1 - eps + 4*(5^-1 + eps/4) = 1.
   Strategy: flatten, separate 5^-1 terms from eps terms via addrCA,
   then cancel 4*(eps/4) = eps with -eps, and show 5*5^-1 = 1. *)
(* Flatten and sort: bubble -eps and eps/4 right, 5^-1 left *)
rewrite -!addrA
  [- eps + _]addrCA [- eps + _]addrCA [- eps + _]addrCA
  [- eps + _]addrCA [- eps + _]addrCA [- eps + _]addrCA
  [- eps + _]addrCA
  [eps / 4%:R + (5^-1 + _)]addrCA [eps / 4%:R + (5^-1 + _)]addrCA
  [eps / 4%:R + (5^-1 + _)]addrCA
  [5^-1 + (- eps + _)]addrCA
  [eps / 4%:R + (- eps + _)]addrCA [eps / 4%:R + (- eps + _)]addrCA
  [eps / 4%:R + (- eps + _)]addrCA
  [eps / 4%:R + (5^-1 + _)]addrCA [eps / 4%:R + (5^-1 + _)]addrCA
  [eps / 4%:R + (5^-1 + _)]addrCA
  [- eps + (5^-1 + _)]addrCA
  !addrA -addrA -mulrDl -addrA -mulrDl -addrA -mulrDl.
(* Cancel 4*(eps/4) = eps, then -eps + eps = 0 *)
have -> : (eps + (eps + (eps + eps))) = eps *+ 4 by [].
rewrite -[eps *+ 4]mulr_natl [4%:R * eps]mulrC.
rewrite mulfK; last by rewrite pnatr_eq0.
rewrite subrK.
(* Show 5 * 5^-1 = 1 *)
rewrite -!addrA.
have -> : 5%:R^-1 + (5%:R^-1 + (5%:R^-1 + (5%:R^-1 + 5%:R^-1))) =
          5%:R^-1 *+ 5 by [].
by rewrite -[5%:R^-1 *+ 5]mulr_natl divff // pnatr_eq0.
Qed.

(** kim_weight_dist — fdist on 'I_5 packaging the weight function kim_weight_fun.
    Kind: instance.
    Why: Builds the probability distribution W used in the weighted Schreier analysis of Kim's trick.
*)
Definition kim_weight_dist : R.-fdist 'I_5 :=
  FDist.make kim_weight_ge0 kim_weight_sum1.

(** kim_weight_distE — evaluation of kim_weight_dist on k gives the branch 5^-1 +/- (eps, eps/4).
    Kind: helper.
    Why: Rewrite lemma that replaces the FDist.make wrapper with the explicit case-analysis form.
    Used by: fc_kim_schreier_diag, fc_kim_schreier_offdiag.
*)
Lemma kim_weight_distE (k : 'I_5) :
  kim_weight_dist k =
  if val k == 0%N then 5%:R^-1 - eps else 5%:R^-1 + eps / 4%:R.
Proof. by rewrite /kim_weight_dist /= ffunE. Qed.

End kim_weights.

(******************************************************************************)
(** * Section 4: Schreier Matrix Verification                                 *)
(*                                                                            *)
(* The Schreier transition matrix Q(x,y) = sum_{k : sigma^k(x) = y} W(k).   *)
(* For Z_5 acting by cyclic rotation, sigma^k(x) = x + k mod 5, so          *)
(* Q(x,y) = W(y - x mod 5). This gives the circulant matrix:                *)
(*   diagonal entries: a = 1/5 - eps                                          *)
(*   off-diagonal entries: b = 1/5 + eps/4                                    *)
(*                                                                            *)
(* Key properties:                                                            *)
(*   - Row stochastic: inherited from schreier_weighted_stochastic            *)
(*   - Column stochastic: by circulant symmetry                               *)
(*   - Hence doubly stochastic                                                *)
(******************************************************************************)

Section kim_schreier.

Variable R : realType.
Variable eps : R.
Hypothesis eps_lt : eps < 5%:R^-1.
Hypothesis eps_gt : - (4%:R * 5%:R^-1) < eps.

Let W := kim_weight_dist eps_lt eps_gt.
Let Q := schreier_transition_weighted fc_kim_sigmas W.

(** The Schreier matrix entry Q(x,y) depends only on (y - x) mod 5.
    For a cyclic group with generators sigma^k, sigma^k(x) = y iff k = y - x
    (in Z_5). Since each k gives a unique generator, Q(x,y) = W(y-x mod 5). *)

(** Diagonal entries: Q(x,x) = W(0) = 1/5 - eps *)
Lemma fc_kim_schreier_diag (x : 'I_5) :
  Q x x = 5%:R^-1 - eps.
Proof.
rewrite /Q /schreier_transition_weighted mxE.
rewrite /fc_kim_sigmas.
case: x => [[|[|[|[|[|?]]]]] Hx] //=.
all: rewrite big_mkcond /=.
all: rewrite big_ord_recr /= big_ord_recr /= big_ord_recr /=
            big_ord_recr /= big_ord_recr /= big_ord0 add0r.
all: rewrite !(tnth_nth 1%g) /=.
all: rewrite perm1 eqxx /= !permE /= !permE /= !permE /= !permE /=.
all: rewrite !addr0 ffunE /=.
all: reflexivity.
Qed.

(** Row stochastic: inherited from generic Schreier lemma *)
Lemma fc_kim_row_stochastic (x : 'I_5) :
  \sum_y Q x y = 1.
Proof. exact: schreier_weighted_stochastic. Qed.

(** Column stochastic: for circulant matrices, column sums = row sums *)
Lemma fc_kim_col_stochastic (y : 'I_5) :
  \sum_x Q x y = 1.
Proof.
rewrite /Q /schreier_transition_weighted.
under eq_bigr do rewrite mxE.
(* Remove predicate filter, exchange sums *)
under eq_bigr do rewrite big_mkcond /=.
rewrite exchange_big /=.
(* For each k, there is exactly one x such that sigma^k(x) = y,
   namely x = sigma^{-k}(y). *)
rewrite -[RHS](FDist.f1 W).
apply: eq_bigr => k _.
rewrite -big_mkcond /=.
rewrite (big_pred1 ((tnth fc_kim_sigmas k)^-1%g y)) //.
move=> x; rewrite /=.
apply/eqP/eqP.
- by move=> H; rewrite -H permK.
- by move=> ->; rewrite permKV.
Qed.

(** Off-diagonal entries: Q(x,y) = W(y-x mod 5) = 1/5 + eps/4 for x != y *)
Lemma fc_kim_schreier_offdiag (x y : 'I_5) :
  x != y -> Q x y = 5%:R^-1 + eps / 4%:R.
Proof.
rewrite /Q /schreier_transition_weighted mxE /fc_kim_sigmas.
case: x => [[|[|[|[|[|?]]]]] Hx] //=;
case: y => [[|[|[|[|[|?]]]]] Hy] //= _;
rewrite big_mkcond /=;
rewrite big_ord_recr /= big_ord_recr /= big_ord_recr /=
        big_ord_recr /= big_ord_recr /= big_ord0 add0r;
rewrite !(tnth_nth 1%g) /=;
rewrite perm1 !permE /= !permE /= !permE /= !permE /=;
rewrite ?addr0 ?add0r ffunE /=;
reflexivity.
Qed.

(** Doubly stochastic *)
Lemma fc_kim_doubly_stochastic :
  forall y, \sum_x Q x y = 1.
Proof. exact: fc_kim_col_stochastic. Qed.

End kim_schreier.

(******************************************************************************)
(** * Section 5: certificate bundle via Weighted Schreier Certificate         *)
(*                                                                            *)
(* Kim's circulant matrix has eigenvalues:                                    *)
(*   lambda_0 = 1 (Perron eigenvector = uniform)                              *)
(*   lambda_1 = ... = lambda_4 = a - b = -(5/4)*eps                          *)
(*                                                                            *)
(* The second-largest eigenvalue modulus is |a - b| = (5/4)*|eps|.           *)
(* Spectral gap: 1 - |a - b| = 1 - (5/4)*|eps|.                             *)
(*                                                                            *)
(* Convergence: var_dist(P^T * uniform, uniform) <= sqrt(5) * |a-b|^T        *)
(*            = sqrt(5) * ((5/4)*|eps|)^T                                     *)
(*                                                                            *)
(* We prove the spectral convergence bound via the uniform-off-diagonal       *)
(* convergence theorem (unif_offdiag_convergence, pgg_schreier_weighted.v:498)*)
(* and construct the WeightedSchreierCertificate + certificate bundle.        *)
(******************************************************************************)

Section kim_security.

Variable R : realType.
Variable eps : R.
Hypothesis eps_lt : eps < 5%:R^-1.
Hypothesis eps_gt : - (4%:R * 5%:R^-1) < eps.

(** Additional hypothesis: |eps| small enough for spectral gap positivity *)
Hypothesis eps_spectral : `|eps| < 4%:R / 5%:R.

Let W := kim_weight_dist eps_lt eps_gt.

(** Second-largest eigenvalue modulus *)
Definition kim_lambda2 : R := 5%:R / 4%:R * `|eps|.

(** kim_lambda2_ge0 — the second-largest eigenvalue modulus is non-negative.
    Kind: helper.
    Why: Non-negativity feeding kim_spectral_gap_le1.
    Used by: kim_spectral_gap_le1.
*)
Lemma kim_lambda2_ge0 : 0 <= kim_lambda2.
Proof. by rewrite /kim_lambda2 mulr_ge0 // ?divr_ge0 // normr_ge0. Qed.

(** kim_lambda2_lt1 — the second-largest eigenvalue modulus is strictly below 1.
    Kind: helper.
    Why: Ensures a strictly positive spectral gap; uses eps_spectral hypothesis.
    Used by: kim_spectral_gap_pos.
*)
Lemma kim_lambda2_lt1 : kim_lambda2 < 1.
Proof.
rewrite /kim_lambda2.
apply: (Order.POrderTheory.lt_le_trans (y := 5 / 4 * (4 / 5))); last first.
- rewrite -mulrA mulrCA mulrA -!mulrA.
  rewrite [4%:R^-1 * (5%:R * (4%:R * 5%:R^-1))]mulrCA.
  rewrite mulKr ?unitfE ?pnatr_eq0 // mulfV ?pnatr_eq0 //.
- by rewrite ltr_pM2l // divr_gt0.
Qed.

(** Spectral gap *)
Definition kim_spectral_gap : R := 1 - kim_lambda2.

(** kim_spectral_gap_pos — the spectral gap is strictly positive.
    Kind: helper.
    Why: Gap positivity input to the WeightedSchreierCertificate constructor; follows from kim_lambda2 < 1.
    Used by: fc_kim_schreier_cert, fc_kim_asymptotic.
*)
Lemma kim_spectral_gap_pos : 0 < kim_spectral_gap.
Proof. by rewrite /kim_spectral_gap subr_gt0; exact: kim_lambda2_lt1. Qed.

(** kim_spectral_gap_le1 — the spectral gap is at most 1.
    Kind: helper.
    Why: Gap upper-bound input to the WeightedSchreierCertificate constructor.
    Used by: fc_kim_schreier_cert, fc_kim_asymptotic.
*)
Lemma kim_spectral_gap_le1 : kim_spectral_gap <= 1.
Proof. by rewrite /kim_spectral_gap lerBlDr lerDl; exact: kim_lambda2_ge0. Qed.

(** Spectral convergence bound.
    Proved via the uniform-off-diagonal convergence theorem
    (unif_offdiag_convergence from pgg_schreier_weighted.v):
    Kim's circulant Schreier matrix has constant diagonal a = 1/5 - eps
    and constant off-diagonal b = 1/5 + eps/4, so the general theorem
    gives var_dist = 8/5 * |a-b|^L <= sqrt(5) * |a-b|^L. *)
Lemma kim_spectral_convergence : forall (L : nat) (s : 'I_5),
  var_dist (@endpoint_dist_weighted R 3 4 L fc_kim_sigmas W s)
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * kim_lambda2 ^+ L.
Proof.
move=> L s.
(* Rewrite var_dist using bridge: endpoint_dist = matrix power entry *)
rewrite /var_dist.
under eq_bigr => x _ do
  rewrite (@schreier_weighted_bridge R 4 3) fdist_uniformE card_ord.
(* Apply the general convergence bound *)
have := @unif_offdiag_convergence R 3
  (schreier_transition_weighted fc_kim_sigmas W)
  (5%:R^-1 - eps) (5%:R^-1 + eps / 4%:R)
  (fc_kim_schreier_diag eps_lt eps_gt)
  (fc_kim_schreier_offdiag eps_lt eps_gt)
  (fc_kim_doubly_stochastic eps_lt eps_gt) L s.
(* |a - b| = |(1/5 - eps) - (1/5 + eps/4)| = |-(5/4)*eps| = kim_lambda2 *)
rewrite /kim_lambda2.
have -> : 5%:R^-1 - eps - (5%:R^-1 + eps / 4%:R) = - (5%:R / 4%:R * eps) :> R.
  rewrite opprD addrA [5%:R^-1 - eps - 5%:R^-1]addrAC subrr add0r.
  rewrite -opprD; congr (- _).
  rewrite [eps / _]mulrC -{1}[eps]mul1r -mulrDl.
  congr (_ * eps); apply: (mulIf (x := 4%:R)); rewrite ?unitfE ?pnatr_eq0 //.
  rewrite divfK ?unitfE ?pnatr_eq0 //.
  by rewrite mulrDl mul1r mulVf ?pnatr_eq0 // -[1]/(1%:R) -natrD.
by rewrite normrN normrM ger0_norm // divr_ge0.
Qed.

(** Weighted Schreier Certificate *)
Definition fc_kim_schreier_cert : WeightedSchreierCertificate R 4 3 fc_kim_sigmas W.
Proof.
apply: (@MkWeightedSchreierCertificate R 4 3 fc_kim_sigmas W).
- exact: fc_kim_doubly_stochastic.
- exact: kim_spectral_gap_pos.
- exact: kim_spectral_gap_le1.
- move=> L s.
  rewrite /kim_spectral_gap /kim_lambda2.
  rewrite opprB addrC subrK.
  exact: kim_spectral_convergence.
Defined.

(** Exact variation distance via the uniform-off-diagonal identity.
    The proof mirrors kim_spectral_convergence but calls
    unif_offdiag_var_dist (equality) instead of
    unif_offdiag_convergence (inequality). *)
Lemma kim_var_dist_exact (L : nat) (s : 'I_5) :
  var_dist (@endpoint_dist_weighted R 3 4 L fc_kim_sigmas W s)
           (fdist_uniform (card_ord 5))
  = 2%:R * 4%:R / 5%:R * kim_lambda2 ^+ L.
Proof.
rewrite /var_dist.
under eq_bigr => x _ do
  rewrite (@schreier_weighted_bridge R 4 3) fdist_uniformE card_ord.
have := @unif_offdiag_var_dist R 3
  (schreier_transition_weighted fc_kim_sigmas W)
  (5%:R^-1 - eps) (5%:R^-1 + eps / 4%:R)
  (fc_kim_schreier_diag eps_lt eps_gt)
  (fc_kim_schreier_offdiag eps_lt eps_gt)
  (fc_kim_doubly_stochastic eps_lt eps_gt) L s.
rewrite /kim_lambda2.
have -> : 5%:R^-1 - eps - (5%:R^-1 + eps / 4%:R) = - (5%:R / 4%:R * eps) :> R.
  rewrite opprD addrA [5%:R^-1 - eps - 5%:R^-1]addrAC subrr add0r.
  rewrite -opprD; congr (- _).
  rewrite [eps / _]mulrC -{1}[eps]mul1r -mulrDl.
  congr (_ * eps); apply: (mulIf (x := 4%:R)); rewrite ?unitfE ?pnatr_eq0 //.
  rewrite divfK ?unitfE ?pnatr_eq0 //.
  by rewrite mulrDl mul1r mulVf ?pnatr_eq0 // -[1]/(1%:R) -natrD.
by rewrite normrN normrM ger0_norm // divr_ge0.
Qed.

(** Asymptotic convergence certificate for Kim's trick *)
Definition fc_kim_asymptotic : @SecurityAsymptotic R FiveCardKim_M.
Proof.
apply: (@MkSecurityAsymptotic R FiveCardKim_M
  kim_spectral_gap 0
  kim_spectral_gap_pos kim_spectral_gap_le1
  (Order.POrderTheory.lexx 0)
  (fun L' => @rho_from_words_weighted R 3 4 L' fc_kim_sigmas W)).
move=> L' s.
rewrite add0r /kim_spectral_gap /kim_lambda2 opprB addrC subrK.
exact: kim_spectral_convergence.
Defined.

(** fc_kim_security_bundle — the certificate bundle at word length L, carrying
    the spectral marginal bound, the exact variational distance and the
    asymptotic convergence certificate.
    @intent: MkShuffleCertificateBundle at the spectral bound of the weighted
    word distribution, with scb_exact the closed-form equality and
    scb_asymptotic the geometric-convergence certificate. *)
Definition fc_kim_security_bundle (L : nat) :
  ShuffleCertificateBundle R FiveCardKim_M :=
  @MkShuffleCertificateBundle R FiveCardKim_M
    (@MkShuffleMarginalBound R FiveCardKim_M L
      (Num.sqrt 5%:R * kim_lambda2 ^+ L)
      (@rho_from_words_weighted R 3 4 L fc_kim_sigmas W)
      (fun s => kim_spectral_convergence L s))
    (Some (@MkSecurityExact R FiveCardKim_M
      (@rho_from_words_weighted R 3 4 L fc_kim_sigmas W)
      (2%:R * 4%:R / 5%:R * kim_lambda2 ^+ L)
      (kim_var_dist_exact L)))
    (Some fc_kim_asymptotic).

(** When eps = 0, the bias disappears and we recover the uniform case *)
Lemma kim_lambda2_at_zero : eps = 0 -> kim_lambda2 = 0.
Proof. by move=> H0; rewrite /kim_lambda2 H0 normr0 mulr0. Qed.

(** kim_bound_at_zero — at eps = 0 any positive power of kim_lambda2 is zero.
    Kind: helper.
    Why: Intermediate step feeding kim_security_at_zero.
    Used by: kim_security_at_zero.
*)
Lemma kim_bound_at_zero (L : nat) :
  eps = 0 -> kim_lambda2 ^+ L.+1 = 0.
Proof.
by move=> H0; rewrite kim_lambda2_at_zero // expr0n.
Qed.

(** kim_security_at_zero — at eps = 0 the security bound collapses to zero for any positive word length.
    Kind: helper.
    Why: Degenerate limit check: unbiased weights recover the uniform-dealing regime.
    Used by: downstream sanity checks of Kim's instance.
*)
Lemma kim_security_at_zero (L : nat) :
  eps = 0 -> Num.sqrt 5%:R * kim_lambda2 ^+ L.+1 = 0.
Proof. by move=> H0; rewrite kim_bound_at_zero // mulr0. Qed.

End kim_security.

(******************************************************************************)
(** * Section 6: Concrete Instances                                           *)
(*                                                                            *)
(* Example: Kim's "slightly biased" instance with eps = 1/100.               *)
(* This demonstrates that the framework can be instantiated with concrete     *)
(* numerical values.                                                          *)
(******************************************************************************)

Section kim_concrete.

Variable R : realType.

(** For any concrete eps satisfying the constraints, we get a full
    security analysis pipeline:
    1. Weight distribution (kim_weight_dist)
    2. Schreier matrix (schreier_transition_weighted fc_kim_sigmas W)
    3. Doubly stochastic proof (fc_kim_doubly_stochastic)
    4. Spectral convergence bound (kim_spectral_convergence)
    5. Exact variation distance (kim_var_dist_exact)
    6. certificate bundle with scb_exact (fc_kim_security_bundle) *)

(** The security bound for L shuffles:
    var_dist <= sqrt(5) * ((5/4)*|eps|)^L *)
Lemma fc_kim_security_bound (eps : R)
    (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps)
    (Hspec : `|eps| < 4%:R / 5%:R)
    (L : nat) (s : 'I_5) :
  var_dist (@endpoint_dist_weighted R 3 4 L fc_kim_sigmas
              (kim_weight_dist Hlt Hgt) s)
           (fdist_uniform (card_ord 5))
  <= Num.sqrt 5%:R * (kim_lambda2 eps) ^+ L.
Proof. exact: kim_spectral_convergence. Qed.

(** At bias eps = 1/100 the second eigenvalue modulus equals 1/80.
    @composes: kim_bound_centi *)
Lemma kim_lambda2_at_centi : kim_lambda2 (1 / 100 : R) = 1 / 80.
Proof.
rewrite /kim_lambda2 ger0_norm; last by rewrite divr_ge0.
rewrite mulf_div mulr1; apply/eqP; rewrite eqr_div ?pnatr_eq0 //;
  last by rewrite -natrM pnatr_eq0.
by rewrite mul1r -!natrM.
Qed.

(** The bias 1/100 lies below the no-cut threshold 1/5.
    @composes: kim_deal_centi_lt *)
Lemma kim_centi_lt : (1 / 100 : R) < 5%:R^-1.
Proof. by rewrite div1r ltf_pV2 ?posrE ?ltr0n // ltr_nat. Qed.

(** The bias 1/100 lies above the lower positivity bound -(4/5).
    @composes: kim_deal_centi_lt *)
Lemma kim_centi_gt : - (4%:R * 5%:R^-1) < (1 / 100 : R).
Proof.
apply: (Order.POrderTheory.lt_le_trans (y := 0)).
- by rewrite oppr_lt0 divr_gt0 ?ltr0n.
- by rewrite divr_ge0.
Qed.

(** The bias 1/100 has magnitude below the spectral-gap bound 4/5.
    @composes: kim_deal_centi_lt *)
Lemma kim_centi_spec : `|1 / 100 : R| < 4%:R / 5%:R.
Proof.
rewrite ger0_norm; last by rewrite divr_ge0.
by rewrite ltr_pdivrMr ?ltr0n // mulrAC ltr_pdivlMr ?ltr0n // mul1r -natrM ltr_nat.
Qed.

(** At bias 1/100 and word length 7 the spectral bound is below 2^-40.
    @composes: kim_deal_centi_lt *)
Lemma kim_bound_centi :
  Num.sqrt 5%:R * (kim_lambda2 (1 / 100 : R)) ^+ 7 < 2%:R ^- 40.
Proof.
rewrite kim_lambda2_at_centi -(@ltr_pXn2r R 2 isT).
2: by rewrite nnegrE mulr_ge0 ?sqrtr_ge0 // exprn_ge0 // divr_ge0.
2: by rewrite nnegrE invr_ge0 exprn_ge0 // ler0n.
rewrite exprMn sqr_sqrtr ?ler0n // -exprM div1r exprVn.
rewrite -[2 ^- 40]exprVn -exprM exprVn.
rewrite ltr_pdivrMr; last by rewrite exprn_gt0 // ltr0n.
rewrite mulrC -[2 ^- (40 * 2)]div1r mulrA mulr1 ltr_pdivlMr;
  last by rewrite exprn_gt0 // ltr0n.
rewrite -!natrX -natrM ltr_nat.
by lia.
Qed.

(** kim_security_bundle_centi — the certificate bundle for Kim at bias 1/100
    and word length 7.
    @intent: fc_kim_security_bundle at bias 1/100 and L = 7, whose marginal
    bound is sqrt 5 * (1/80)^7. *)
Definition kim_security_bundle_centi : ShuffleCertificateBundle R FiveCardKim_M :=
  @fc_kim_security_bundle R (1 / 100) kim_centi_lt kim_centi_gt kim_centi_spec 7.

(** Variation distance of the 7-cut biased deal from uniform is below 2^-40.
    @main security: closes the numeric mixing-length step in-kernel for Kim. *)
Lemma kim_deal_centi_lt (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sw_rho_dist (scb_bound kim_security_bundle_centi)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof.
apply: (Order.POrderTheory.le_lt_trans
  (sw_bound (scb_bound kim_security_bundle_centi) s)).
rewrite /kim_security_bundle_centi /fc_kim_security_bundle /sw_bound_eps.
exact: kim_bound_centi.
Qed.

(** Variation distance of a single biased cut from uniform equals 1/50.
    @main security: the paper-faithful single-shuffle leak at bias 1/100. *)
Lemma kim_one_cut_centiE (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_sigmas
                 (kim_weight_dist kim_centi_lt kim_centi_gt)))
           (fdist_uniform (card_ord 5))
  = 1 / 50.
Proof.
have HE := @kim_var_dist_exact R (1 / 100) kim_centi_lt kim_centi_gt 1 s.
rewrite /endpoint_dist_weighted in HE.
rewrite HE kim_lambda2_at_centi expr1 mulf_div.
apply/eqP; rewrite eqr_div ?pnatr_eq0 //; last by rewrite -natrM pnatr_eq0.
by rewrite -[1]/(1%:R) -!natrM.
Qed.

End kim_concrete.

(* AlgebraicRigidity for Kim's instance is in
   pgg-smc/reconstruct/rigidity_kim_instance.v, following the standard
   pattern of a separate rigidity file per group family. *)
