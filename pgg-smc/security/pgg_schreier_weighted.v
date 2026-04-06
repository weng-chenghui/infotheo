(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Weighted Schreier Graph Infrastructure for PGG Security                     *)
(*                                                                            *)
(* Generalization of the Schreier transition matrix (pgg_schreier.v) from     *)
(* uniform generator weights (each sigma_i chosen with probability 1/Tg) to  *)
(* arbitrary generator weights W : fdist 'I_Tg.                               *)
(*                                                                            *)
(* == Contents ==                                                             *)
(*                                                                            *)
(* Weighted Schreier transition matrix:                                       *)
(*   schreier_transition_weighted W ==                                        *)
(*     N x N matrix with Q_w(x,y) = sum_{i : sigma_i(x)=y} W(i)             *)
(*   schreier_weighted_stochastic == each row sums to 1 (proved)             *)
(*   schreier_weighted_entry_ge0 == all entries are >= 0 (proved)            *)
(*   schreier_weighted_uniform == when W = uniform, recovers                 *)
(*     schreier_transition from pgg_schreier.v                                *)
(*                                                                            *)
(* Weighted Schreier certificate:                                             *)
(*   WeightedSchreierCertificate R m n' sigmas W == record packaging:         *)
(*     wsc_doubly_stochastic : columns also sum to 1                          *)
(*     wsc_lambda_gap   : spectral gap value (0 < gap <= 1)                   *)
(*     wsc_convergence  : var_dist <= sqrt(N) * (1 - gap)^L for all L, s     *)
(*       Uses endpoint_dist_weighted from pgg_weighted_words.v                *)
(*                                                                            *)
(* == Relationship to pgg_schreier.v ==                                       *)
(*                                                                            *)
(* The uniform case schreier_transition Q(x,y) = #{sigma_i(x)=y} / Tg       *)
(* is recovered when W = fdist_uniform: each generator contributes 1/Tg,     *)
(* so Q_w(x,y) = #{sigma_i(x)=y} * (1/Tg) = #{sigma_i(x)=y} / Tg.         *)
(*                                                                            *)
(* References:                                                                *)
(*   Same as pgg_schreier.v (Diaconis 1988, Saloff-Coste 1997, etc.)        *)
(*   Extended to non-uniform step distributions.                              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound
  pgg_schreier pgg_weighted_words.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Section 1: Weighted Schreier Transition Matrix                         *)
(******************************************************************************)

Section schreier_transition_weighted.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.

(* Generator weight distribution *)
Variable W : R.-fdist 'I_Tg.

(* Weighted transition matrix: Q_w(x,y) = sum_{i : sigma_i(x)=y} W(i) *)
Definition schreier_transition_weighted : 'M[R]_(N, N) :=
  \matrix_(x, y) \sum_(i : 'I_Tg | tnth sigmas i x == y) W i.

(* All entries are non-negative *)
Lemma schreier_weighted_entry_ge0 (x y : 'I_N) :
  0 <= schreier_transition_weighted x y.
Proof.
rewrite mxE; apply: sumr_ge0 => i _.
exact: FDist.ge0.
Qed.

(* Each row sums to 1 (row-stochastic).
   Proof: partition generators by target sheet, then use FDist.f1.
   For each generator i, there is exactly one y = sigma_i(x),
   so sum_y sum_{i:sigma_i(x)=y} W(i) = sum_i W(i) = 1. *)
Lemma schreier_weighted_stochastic (x : 'I_N) :
  \sum_y schreier_transition_weighted x y = 1.
Proof.
rewrite /schreier_transition_weighted.
under eq_bigr do rewrite mxE.
rewrite (exchange_big_dep predT) //=.
rewrite -[RHS](FDist.f1 W).
apply: eq_bigr => i _.
rewrite (big_pred1 (tnth sigmas i x)) //.
Qed.

(* When W is uniform (W(i) = 1/Tg for all i), the weighted transition
   matrix recovers the original schreier_transition. *)
Lemma schreier_weighted_uniform :
  W = fdist_uniform (card_ord Tg) ->
  schreier_transition_weighted = schreier_transition R sigmas.
Proof.
move=> HW; apply/matrixP => x y.
rewrite !mxE /schreier_gen_count -sum1dep_card natr_sum.
rewrite mulr_suml; apply: eq_bigr => i Hi.
by rewrite HW fdist_uniformE card_ord mul1r.
Qed.

End schreier_transition_weighted.

Arguments schreier_transition_weighted {R m n'} sigmas W.

(******************************************************************************)
(*     Section 2: Weighted Schreier Certificate                               *)
(*                                                                            *)
(* A WeightedSchreierCertificate extends SchreierCertificate to               *)
(* non-uniform generator weights. The convergence bound uses                  *)
(* endpoint_dist_weighted from pgg_weighted_words.v.                          *)
(*                                                                            *)
(* The doubly-stochastic hypothesis (columns also sum to 1) ensures the       *)
(* stationary distribution is uniform, which is needed for the Diaconis       *)
(* upper bound lemma. For symmetric generator sets (S = S^{-1}) with         *)
(* symmetric weights (W(sigma) = W(sigma^{-1})), this holds automatically.   *)
(******************************************************************************)

Section weighted_schreier_certificate.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.
Variable W : R.-fdist 'I_Tg.

Record WeightedSchreierCertificate := MkWeightedSchreierCertificate {
  (* Doubly stochastic: each column also sums to 1.
     Ensures the stationary distribution is uniform on 'I_N. *)
  wsc_doubly_stochastic :
    forall y, \sum_x schreier_transition_weighted sigmas W x y = 1 ;

  (* The spectral gap value lambda_gap in (0, 1] *)
  wsc_lambda_gap : R ;
  wsc_lambda_pos : 0 < wsc_lambda_gap ;
  wsc_lambda_le1 : wsc_lambda_gap <= 1 ;

  (* The convergence bound: var_dist at each sheet bounded by
     sqrt(N) * (1 - lambda_gap)^L.
     Uses endpoint_dist_weighted from pgg_weighted_words.v. *)
  wsc_convergence : forall (L : nat) (s : 'I_N),
    var_dist (@endpoint_dist_weighted R n' m L sigmas W s)
             (fdist_uniform (card_ord N))
    <= Num.sqrt (N%:R) * (1 - wsc_lambda_gap) ^+ L
}.

(* The convergence rate: 1 - lambda_gap, in [0, 1) *)
Definition weighted_convergence_rate (wsc : WeightedSchreierCertificate) : R :=
  1 - wsc_lambda_gap wsc.

Lemma weighted_convergence_rate_ge0 (wsc : WeightedSchreierCertificate) :
  0 <= weighted_convergence_rate wsc.
Proof.
rewrite /weighted_convergence_rate subr_ge0.
exact: (wsc_lambda_le1 wsc).
Qed.

Lemma weighted_convergence_rate_lt1 (wsc : WeightedSchreierCertificate) :
  weighted_convergence_rate wsc < 1.
Proof.
rewrite /weighted_convergence_rate ltrBlDr addrC -ltrBlDr subrr.
exact: (wsc_lambda_pos wsc).
Qed.

(* Epsilon from weighted Schreier certificate *)
Definition weighted_schreier_epsilon
    (wsc : WeightedSchreierCertificate) (L : nat) : R :=
  Num.sqrt (N%:R) * (1 - wsc_lambda_gap wsc) ^+ L.

(* Epsilon is non-negative *)
Lemma weighted_schreier_epsilon_ge0
    (wsc : WeightedSchreierCertificate) (L : nat) :
  0 <= weighted_schreier_epsilon wsc L.
Proof.
apply: mulr_ge0; first exact: sqrtr_ge0.
apply: exprn_ge0.
exact: weighted_convergence_rate_ge0.
Qed.

(* Epsilon is monotonically decreasing in L *)
Lemma weighted_schreier_epsilon_decreasing
    (wsc : WeightedSchreierCertificate) (L1 L2 : nat) :
  (L1 <= L2)%N ->
  weighted_schreier_epsilon wsc L2 <= weighted_schreier_epsilon wsc L1.
Proof.
move=> HL; rewrite /weighted_schreier_epsilon.
apply: ler_wpM2l; first exact: sqrtr_ge0.
rewrite -(subnK HL) exprD.
apply: ler_piMl.
- by apply: exprn_ge0; exact: weighted_convergence_rate_ge0.
- apply: exprn_ile1; first exact: weighted_convergence_rate_ge0.
  rewrite /weighted_convergence_rate lerBlDr lerDl.
  exact: Order.POrderTheory.ltW (wsc_lambda_pos wsc).
Qed.

(* Monotone security: if secure at L1, at least as secure at L2 >= L1 *)
Lemma weighted_security_monotone
    (wsc : WeightedSchreierCertificate)
    (L1 L2 : nat) (HL : (L1 <= L2)%N) :
  forall (s : 'I_N),
  var_dist (@endpoint_dist_weighted R n' m L2 sigmas W s)
           (fdist_uniform (card_ord N))
  <= weighted_schreier_epsilon wsc L1.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans (wsc_convergence wsc L2 s)).
exact: weighted_schreier_epsilon_decreasing.
Qed.

End weighted_schreier_certificate.

Arguments WeightedSchreierCertificate R m n' sigmas W : clear implicits.
Arguments MkWeightedSchreierCertificate {R m n' sigmas W}.

(******************************************************************************)
(*     Section 3: Weighted Schreier Bridge Lemma                              *)
(*                                                                            *)
(* Connects the L-step weighted Schreier walk (matrix power) to the actual    *)
(* endpoint distribution from weighted word sampling.                         *)
(*                                                                            *)
(*   schreier_weighted_bridge :                                               *)
(*     endpoint_dist_weighted sigmas L W s x                                  *)
(*     = (schreier_transition_weighted sigmas W ^+ L) s x                     *)
(*                                                                            *)
(* Proof by induction on L, analogous to schreier_walk_eq_endpoint from       *)
(* pgg_schreier.v but with arbitrary weights instead of uniform 1/Tg.        *)
(******************************************************************************)

Section schreier_weighted_bridge.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.

Local Notation M := (Gen_PGGTypes sigmas).

Variable W : R.-fdist 'I_Tg.

Lemma schreier_weighted_bridge : forall (L : nat) (s x : 'I_N),
  @endpoint_dist_weighted R n' m L sigmas W s x =
  (schreier_transition_weighted sigmas W ^+ L) s x.
Proof.
elim => [|L IH] s x.
(* Base case: L = 0 — both sides are (s == x)%:R *)
  rewrite expr0 mxE.
  rewrite /endpoint_dist_weighted /rho_from_words_weighted fdistmap_comp
    fdistmapE.
  rewrite big_mkcond /=.
  rewrite (big_pred1 [tuple]); first last.
    by move=> t; apply/esym/eqP; exact: tuple0.
  rewrite inE /= /word_eval big_ord0 perm1.
  rewrite word_weightedE big_ord0.
  by case: eqP.
(* Inductive step: L.+1 *)
(* RHS: Q^{L+1} s x = \sum_y Q s y * (Q^L) y x *)
rewrite exprS mxE.
under eq_bigr do rewrite -IH.
(* LHS: unfold endpoint_dist_weighted, reindex as (head, tail) pairs *)
rewrite /endpoint_dist_weighted /rho_from_words_weighted fdistmap_comp
  fdistmapE big_mkcond /=.
under [LHS]eq_bigr do rewrite inE /=.
rewrite (reindex (fun p : 'I_Tg * L.-tuple 'I_Tg => [tuple of p.1 :: p.2]));
  last first.
  exists (fun t => (thead t, [tuple of behead t])) => [[i w] | t] _ /=.
    by rewrite theadE; congr pair; exact: val_inj.
  exact/esym/tuple_eta.
(* Decompose word_eval and word_weighted for cons tuples *)
under eq_bigr do rewrite word_eval_cons_endpoint.
under eq_bigr do rewrite word_weightedE big_ord_recl.
under eq_bigr do rewrite tnth0 /=.
have Htail : forall (h : 'I_Tg) (t : L.-tuple 'I_Tg),
  \prod_(i0 < L) W (tnth [tuple of h :: t] (lift ord0 i0)) =
  \prod_(i0 < L) W (tnth t i0).
  move=> h t; apply: eq_bigr => i0 _; by rewrite tnthS.
under eq_bigr do rewrite Htail -word_weightedE.
(* Split into double sum and partition by y = sigma_i(s) *)
rewrite -(pair_big xpredT xpredT
  (fun i (w : L.-tuple 'I_Tg) =>
    if word_eval w (tnth sigmas i s) == x
    then W i * word_weighted L W w
    else 0)).
rewrite (partition_big (fun i : 'I_Tg => tnth sigmas i s) xpredT) //=.
apply: eq_bigr => y _.
(* Replace sigma_i(s) with y in the inner sum *)
under eq_bigr => i /eqP Hi do under eq_bigr do rewrite Hi.
(* Factor W(i) out of the if-then-else *)
under eq_bigr => i Hi do
  (rewrite (eq_bigr (fun w : L.-tuple 'I_Tg =>
    W i * if @word_eval (Gen_PGGTypes sigmas) L w y == x
    then word_weighted L W w else 0)); first last;
   first by move=> w _; case: ifP => //; rewrite mulr0).
(* Factor W(i) out of the inner sum *)
under eq_bigr => i Hi do rewrite -mulr_sumr.
(* The inner sum is endpoint_dist_weighted L ... y x *)
have Hinner :
  \sum_w (if @word_eval (Gen_PGGTypes sigmas) L w y == x
    then word_weighted L W w else 0) =
  fdistmap ((fun_of_perm (T:='I_N))^~ y)
    (fdistmap (@word_eval (Gen_PGGTypes sigmas) L) (word_weighted L W)) x.
  rewrite fdistmap_comp fdistmapE big_mkcond /=.
  rewrite -big_mkcond /=; apply: eq_bigl => w; by rewrite inE.
(* Factor out the common inner sum *)
rewrite -mulr_suml.
congr (_ * _).
  by rewrite /schreier_transition_weighted mxE.
exact: Hinner.
Qed.

End schreier_weighted_bridge.

(******************************************************************************)
(*     Section 4: Convergence for Uniform-Off-Diagonal Matrices               *)
(*                                                                            *)
(* An N x N matrix Q is "uniform-off-diagonal" if Q(x,x) = a for all x and  *)
(* Q(x,y) = b for all x != y, for some constants a, b.  When Q is also      *)
(* doubly stochastic (column sums = 1), we have a + (N-1)*b = 1.            *)
(*                                                                            *)
(* Main results:                                                              *)
(*   unif_offdiag_power_entry == Q^L(s,x) = (a-b)^L * (d(s,x) - 1/N) + 1/N *)
(*   unif_offdiag_var_dist    == exact variation distance formula:            *)
(*     sum_x |Q^L(s,x) - 1/N| = 2*(N-1)/N * |a-b|^L                        *)
(*   unif_offdiag_convergence == convergence bound:                           *)
(*     sum_x |Q^L(s,x) - 1/N| <= sqrt(N) * |a-b|^L                          *)
(*                                                                            *)
(* Comparison with the standard Diaconis spectral framework:                  *)
(*                                                                            *)
(*              Diaconis spectral         Uniform-off-diagonal                *)
(*   Scope      Any doubly stochastic     Constant diagonal a,                *)
(*              matrix                    constant off-diagonal b             *)
(*   Requires   Eigendecomposition        Column-stochasticity + induction    *)
(*   Result     Upper bound               Exact closed-form formula           *)
(*              (tight in worst case)     var_dist = 2(N-1)/N * |a-b|^L       *)
(*   Bound      sqrt(N) * rho^L           2(N-1)/N * |a-b|^L <= sqrt(N)*..   *)
(*                                                                            *)
(* The uniform-off-diagonal class arises naturally when the Schreier action   *)
(* is transitive and the weight distribution is symmetric across generators.  *)
(* Kim's Z_5 cyclic shuffle protocol (arXiv:2511.05111) falls in this class: *)
(*   - Z_5 acts transitively on 5 card positions by cyclic rotation           *)
(*   - The biased weight W(0) = 1/5 - eps, W(k) = 1/5 + eps/4 for k>0       *)
(*     produces a circulant Schreier matrix with a = 1/5 - eps, b = 1/5+e/4  *)
(*   - Exact result: var_dist = 8/5 * ((5/4)*|eps|)^L                        *)
(*   - This is tighter than the Diaconis bound sqrt(5) * ((5/4)*|eps|)^L     *)
(*     by a factor of sqrt(5)/(8/5) = 1.398                                  *)
(*                                                                            *)
(* The Diaconis bound remains necessary for protocols whose Schreier matrix   *)
(* does not have the uniform-off-diagonal structure (e.g., non-transitive     *)
(* actions or asymmetric weight distributions).                               *)
(******************************************************************************)

Section unif_offdiag_convergence.

Variable R : realType.
Variable n' : nat.
Let N := n'.+2.

Variable Q : 'M[R]_(N, N).
Variables a b : R.

Hypothesis Hdiag : forall x : 'I_N, Q x x = a.
Hypothesis Hoffdiag : forall x y : 'I_N, x != y -> Q x y = b.
Hypothesis Hcol : forall y : 'I_N, \sum_x Q x y = 1.

(** Row stochastic follows from column stochastic + uniform-off-diagonal:
    a + (N-1)*b = 1. We derive this rather than assuming it. *)
Lemma unif_offdiag_row_sum : a + (N.-1)%:R * b = 1.
Proof.
rewrite mulr_natl.
have := Hcol ord0.
rewrite (bigD1 ord0) //= Hdiag.
rewrite (eq_bigr (fun=> b)); last by move=> i Hi; rewrite Hoffdiag // eq_sym.
by rewrite sumr_const cardC1 card_ord.
Qed.

(** a - b = 1 - N * b *)
Lemma unif_offdiag_ab : a - b = 1 - N%:R * b.
Proof.
have Hab := unif_offdiag_row_sum.
apply/eqP. rewrite subr_eq. apply/eqP.
have HN1: N%:R = N.-1%:R + 1 :> R by rewrite -[1]/(1%:R) -natrD addn1 prednK.
rewrite HN1 mulrDl mul1r -addrA opprD addrA -addrA subrK.
by rewrite -[LHS]addr0 -{1}(subrr (N.-1%:R * b)) addrA Hab.
Qed.

(** Key identity: (a - b) / N + b = 1/N *)
Lemma unif_offdiag_key_identity : (a - b) / N%:R + b = N%:R^-1.
Proof.
have HN : N%:R != 0 :> R by rewrite pnatr_eq0.
rewrite unif_offdiag_ab mulrDl mul1r mulNr -mulrA.
by rewrite mulrCA mulfV // mulr1 subrK.
Qed.

(** Column sums of Q^L are 1 (doubly stochastic is preserved under powers) *)
Lemma doubly_stochastic_power (L : nat) (x : 'I_N) :
  \sum_y (Q ^+ L) y x = 1.
Proof.
elim: L x => [|L IH] x.
  rewrite expr0.
  rewrite (bigD1 x) //= mxE eqxx.
  rewrite (eq_bigr (fun=> 0)); last by move=> i Hi; rewrite mxE (negbTE Hi).
  by rewrite sumr_const mul0rn addr0.
rewrite exprSr.
under eq_bigr do rewrite mxE.
rewrite exchange_big /=.
under eq_bigr => j _ do rewrite -mulr_suml IH mul1r.
exact: Hcol.
Qed.

(** Q^L entries for uniform-off-diagonal matrices *)
Lemma unif_offdiag_power_entry (L : nat) (s x : 'I_N) :
  (Q ^+ L) s x = (a - b) ^+ L * ((s == x)%:R - N%:R^-1) + N%:R^-1.
Proof.
elim: L => [|L IH].
  by rewrite !expr0 mxE mul1r subrK.
rewrite exprS mxE.
rewrite (bigD1 s) //= Hdiag.
have -> : \sum_(i < N | i != s) Q s i * (Q ^+ L) i x =
          b * \sum_(i < N | i != s) (Q ^+ L) i x.
  rewrite mulr_sumr; apply: eq_bigr => i Hi.
  by rewrite Hoffdiag // eq_sym.
have -> : \sum_(i < N | i != s) (Q ^+ L) i x = 1 - (Q ^+ L) s x.
  have := doubly_stochastic_power L x.
  rewrite (bigD1 s) //=.
  by move=> /(f_equal (fun z => z - (Q ^+ L) s x)); rewrite addrC addrK.
rewrite IH.
set c := a - b; set d := (s == x)%:R - N%:R^-1.
set E := c ^+ L * d + N%:R^-1.
rewrite mulrBr mulr1.
rewrite addrCA -mulrBl -/c addrC.
rewrite /E mulrDr mulrA -exprS -addrA.
congr (_ + _).
rewrite /c.
exact: unif_offdiag_key_identity.
Qed.

(** Exact variation distance formula *)
Lemma unif_offdiag_var_dist (L : nat) (s : 'I_N) :
  \sum_(x : 'I_N) `| (Q ^+ L) s x - N%:R^-1 | =
  2%:R * (N.-1)%:R / N%:R * `|a - b| ^+ L.
Proof.
under eq_bigr do rewrite unif_offdiag_power_entry addrK normrM normrX.
rewrite -mulr_sumr mulrC.
congr (_ * _).
rewrite (bigD1 s) //= eqxx /= ger0_norm; last first.
  rewrite subr_ge0. rewrite invf_le1 //. by rewrite ler1n.
under [in LHS]eq_bigr => i Hi do
  rewrite eq_sym (negbTE Hi) /= add0r normrN ger0_norm ?invr_ge0 ?ler0n //.
rewrite sumr_const cardC1 card_ord.
rewrite -[_ *+ N.-1]mulr_natr [N%:R^-1 * _]mulrC.
have HN: N%:R != 0 :> R by rewrite pnatr_eq0.
apply: (mulIf HN).
rewrite divfK //.
rewrite mulrDl mulrBl mul1r.
rewrite mulVf // divfK //.
rewrite /N -addn1 natrD.
by rewrite [_ + 1 - 1]addrK addn1 /= mulrDl mul1r.
Qed.

(** The prefactor 2*(N-1)/N is at most sqrt(N) for N >= 2 *)
Lemma two_Nm1_div_N_le_sqrtN : 2%:R * (N.-1)%:R / N%:R <= Num.sqrt N%:R :> R.
Proof.
have HN0 : (0 : R) < N%:R by rewrite ltr0n.
have HNne : N%:R != 0 :> R by rewrite pnatr_eq0.
have Hge0 : 0 <= 2 * N.-1%:R / N%:R :> R.
  by rewrite mulr_ge0 ?divr_ge0 ?ler0n // mulr_ge0 // ler0n.
rewrite -[X in X <= _]ger0_norm //.
rewrite -sqrtr_sqr.
apply: ler_wsqrtr.
(* (2*(N-1)/N)^2 <= N *)
rewrite exprMn exprVn.
rewrite ler_pdivrMr; last by rewrite exprn_gt0.
rewrite -exprS exprMn -!natrX -natrM ler_nat.
(* Pure nat: 4*(N-1)^2 <= N^3. Case split: n'=0,1 by compute, n'>=2 by monotonicity *)
rewrite /N /=.
case: n' => [//|[//|n]].
(* n >= 2, N = n+4: 4*(n+3)^2 <= (n+4)^3 *)
(* Split: 4*(n+3)^2 <= 4*(n+4)^2 <= (n+4)^3 *)
apply: (leq_trans (n := 2 ^ 2 * n.+4 ^ 2)).
  by rewrite leq_mul2l /= leq_sqr.
by rewrite expnS leq_pmul2r.
Qed.

(** Convergence bound *)
Lemma unif_offdiag_convergence (L : nat) (s : 'I_N) :
  \sum_(x : 'I_N) `| (Q ^+ L) s x - N%:R^-1 |
  <= Num.sqrt N%:R * `|a - b| ^+ L.
Proof.
rewrite unif_offdiag_var_dist.
by rewrite ler_wpM2r // ?exprn_ge0 // ?normr_ge0 // two_Nm1_div_N_le_sqrtN.
Qed.

End unif_offdiag_convergence.
