(******************************************************************************)
(* Den Boer / Kim Five-Card Trick: input privacy under a biased cut           *)
(*                                                                            *)
(* Bounds, as conditional mutual information in bits, the information a        *)
(* partial reveal of the dealt five-card row carries about the individual     *)
(* inputs (a, b) GIVEN the computed output a && b, when the cyclic cut is      *)
(* Kim's biased W_eps (w_0 = 1/5 - eps; w_k = 1/5 + eps/4, k = 1..4) rather    *)
(* than uniform.                                                              *)
(*                                                                            *)
(* Mechanism. Two inputs with the same output (e.g. (0,1) and (1,0)) differ   *)
(* only by a cyclic rotation of the arrangement. A uniform cut averages over  *)
(* all rotations equally, so the rotation is invisible and equal-output       *)
(* inputs deal the SAME view distribution: input privacy is exact,            *)
(* I(Inputs ; View | Secret) = 0 (den Boer). The biased weight favours some    *)
(* cut positions, reweighting the rotation, so equal-output inputs deal        *)
(* slightly different view distributions, and that gap is the leakage.         *)
(*                                                                            *)
(* Order of magnitude. The per-view probability gap is first order in the     *)
(* bias, O(eps), tracking || W_eps - uniform ||. The leaked information is a   *)
(* KL / chi-square quantity, second order in that gap, so                      *)
(* I(Inputs ; View | Secret) <= kim_leak_bound eps = O(eps^2), with           *)
(* kim_leak_bound 0 = 0, recovering den Boer's exact zero.                     *)
(*                                                                            *)
(* The leakage is carried entirely by the output-0 fibre {(0,0),(0,1),(1,0)}; *)
(* output 1 forces (a, b) = (1,1), leaving nothing to leak.                    *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop ssralg ssrnum reals.
From mathcomp Require Import lra.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_leakage den_boer_encoding five_card_kim.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Section kim_input_privacy.
Variable R : realType.
Variable eps : R.
Hypothesis eps_lt_inv5 : eps < 5%:R^-1.
Hypothesis eps_gt_neg4inv5 : - (4%:R * 5%:R^-1) < eps.

(** card_bool2 — the input alphabet [bool * bool] has four elements.
    @composes: kim_input_private *)
Lemma card_bool2 : #|{: bool * bool}| = 3.+1.
Proof. by rewrite card_prod !card_bool. Qed.

(** kim_input_dist — the biased joint law on [Omega = bool * bool * 'I_5]: fair
    inputs [(a, b)] times Kim's weighted cyclic cut [W_eps].
    @intent: the probability space for Kim's input-privacy analysis. *)
Definition kim_input_dist : R.-fdist Omega :=
  (fdist_uniform card_bool2 : R.-fdist (bool * bool))
    `x (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).

(** kim_inputs — the input pair [(a, b)] over [kim_input_dist], reusing the den
    Boer function so [den_boer_view_count_eq] applies.
    @intent: the secret-determining inputs of Kim's trick. *)
Definition kim_inputs : {RV kim_input_dist -> bool * bool} := Inputs R.

(** kim_secret — the output [a && b] over [kim_input_dist].
    @intent: the den Boer / Kim computed value. *)
Definition kim_secret : {RV kim_input_dist -> bool} := Secret R.

(** kim_view — the partial card view at positions [A] over [kim_input_dist].
    @intent: the adversary's revealed colours. *)
Definition kim_view (A : seq nat) : {RV kim_input_dist -> (size A).-tuple bool} :=
  ViewA R A.

(** kim_leak_bound — the [O(eps^2)] leakage ceiling.
    @intent: Kim's input-privacy bound as a function of the bias. *)
Definition kim_leak_bound (e : R) : R :=
  12%:R * log (sequences.expR 1) * e ^+ 2 / (5%:R^-1 - `|e|).

Let PQR (A : seq nat) := `p_ [% kim_inputs, kim_view A, kim_secret].

(** cdiv1_secret_true0 — conditioned on the output a && b being true, the inputs
    are the point mass (1, 1), so the secret-true fibre's conditional KL term is
    zero.
    @composes: kim_input_private *)
Fact cdiv1_secret_true0 (A : seq nat) : cdiv1 (PQR A) true = 0.
Proof.
rewrite /PQR /cdiv1; apply: big1 => x _.
have [px0|pxN0] := eqVneq
  (jfdist_cond.jcPr `p_ [% kim_inputs, kim_view A, kim_secret] [set x] [set true])
  0.
  by rewrite px0 mul0r.
rewrite fdist_proj13_RV3 extra_proba.fdist_proj23_RV3.
rewrite !jfdist_cond.jPr_Pr !cpr_in1 (surjective_pairing x) /=.
have HSI : kim_secret = (fun ab : bool * bool => ab.1 && ab.2) `o kim_inputs
  by apply: boolp.funext => -[[a b] i].
move: pxN0; rewrite jfdist_cond.jPr_Pr cpr_in1 (surjective_pairing x) => HN.
rewrite /=.
have Hcoll : forall (W : finType) (Wrv : {RV kim_input_dist -> W}) (w : W),
    `Pr[ Wrv = w ] != 0 ->
    (forall a : bool * bool, a != (true, true) ->
      cPr_eq kim_inputs a Wrv w = 0) ->
    cPr_eq kim_inputs (true, true) Wrv w = 1.
  move=> W Wrv w Hw Hoff.
  have Hsum := extra_proba.sum_cPr_eq kim_inputs Hw.
  rewrite (bigD1 (true, true)) //= in Hsum.
  by rewrite big1 ?addr0 // in Hsum => a aN; exact: Hoff.
have HsecN0 : `Pr[ kim_secret = true ] != 0
  by apply: contra HN => /eqP H0; rewrite cpr_eqE H0 invr0 mulr0.
have HVS : `Pr[ [% kim_view A, kim_secret] = (x.2, true) ] != 0.
  apply: contra HN => /eqP H0.
  rewrite (cpr_eq_product_rule kim_inputs (kim_view A) kim_secret).
  by rewrite cpr_eqE H0 invr0 mulr0 mul0r.
have Hcimp : forall t, kim_secret t ==> (kim_inputs t == (true, true))
  by move=> t; apply/implyP => Hs; move: Hs; rewrite HSI /comp_RV;
     case: (kim_inputs t) => -[] [].
have HoffVS : forall a : bool * bool, a != (true, true) ->
    cPr_eq kim_inputs a [% kim_view A, kim_secret] (x.2, true) = 0.
  move=> a aN.
  apply: (extra_proba.cond_prob_zero_outside_constraint
    (constraint := fun (vs : _ * bool) i => vs.2 ==> (i == (true, true)))).
  - by move=> t; exact: Hcimp.
  - exact: HVS.
  - by rewrite implyTb.
have HoffS : forall a : bool * bool, a != (true, true) ->
    cPr_eq kim_inputs a kim_secret true = 0.
  move=> a aN.
  apply: (extra_proba.cond_prob_zero_outside_constraint
    (constraint := fun (s : bool) i => s ==> (i == (true, true)))).
  - by move=> t; exact: Hcimp.
  - exact: HsecN0.
  - by rewrite implyTb.
have Hx1 : x.1 = (true, true).
  apply: contraNeq HN => Hne.
  rewrite (cpr_eq_product_rule kim_inputs (kim_view A) kim_secret).
  by rewrite HoffVS // mul0r.
rewrite Hx1.
have Hq1 : cPr_eq kim_inputs (true, true) kim_secret true = 1
  by apply: Hcoll; [exact: HsecN0 | exact: HoffS].
have HqVS :
    cPr_eq kim_inputs (true, true) [% kim_view A, kim_secret] (x.2, true) = 1
  by apply: Hcoll; [exact: HVS | exact: HoffVS].
rewrite (cpr_eq_product_rule kim_inputs (kim_view A) kim_secret).
rewrite HqVS mul1r Hq1 mul1r.
have [->|q2N] := eqVneq (cPr_eq (kim_view A) x.2 kim_secret true) 0;
  first by rewrite mul0r.
by rewrite divff // log1 mulr0.
Qed.

(** kim_cond_mutual_infoE — the conditional mutual information is carried entirely
    by the output-false fibre, which has probability 3 / 4.
    @composes: kim_input_private *)
Fact kim_cond_mutual_infoE (A : seq nat) :
  cond_mutual_info (PQR A) = 3%:R / 4%:R * cdiv1 (PQR A) false.
Proof.
rewrite /PQR cond_mutual_infoE2 big_bool cdiv1_secret_true0 mulr0.
rewrite [LHS]add0r; congr (_ * _).
rewrite snd_RV3 snd_RV2 fdistmapE.
under eq_bigr => a Ha do rewrite fdist_prodE.
rewrite (eq_bigl (fun a : Omega => ((a.1.1 && a.1.2) == false) && true));
  last by move=> -[[a b] i]; rewrite !inE /= andbT.
rewrite -(pair_big (fun ab : bool * bool => (ab.1 && ab.2) == false) predT
  (fun ab i => fdist_uniform card_bool2 ab *
    kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5 i)) /=.
under eq_bigr => i Hi do rewrite -big_distrr /=.
rewrite kim_weight_sum1.
under eq_bigr => i Hi do rewrite mulr1.
under eq_bigr => i Hi do rewrite fdist_uniformE card_bool2.
rewrite big_const iter_addr addr0.
have -> : #|(fun i : bool * bool => ~~ (i.1 && i.2) (+) false)| = 3.
  rewrite -sum1_card big_mkcond /=.
  rewrite -(pair_bigA _ (fun a b => if ~~ (a && b) (+) false then 1 else 0))%N /=.
  by rewrite !big_bool.
by rewrite mulrnAl mul1r.
Qed.

(** chi2_div — the Pearson chi-square divergence sum_a (P a - Q a)^2 / Q a.
    @intent: the second-order surrogate that upper-bounds the KL divergence. *)
Definition chi2_div (T : finType) (P Q : R.-fdist T) : R :=
  \sum_(a in T) (P a - Q a) ^+ 2 / Q a.

(** le_div_chi2 — KL is bounded by chi-square times log e (a one-step
    consequence of log x <= (x - 1) log e).
    @composes: kim_input_private *)
Fact le_div_chi2 (T : finType) (P Q : R.-fdist T) :
  (forall a, 0 < Q a) ->
  divergence.div P Q <= chi2_div P Q * log (sequences.expR 1).
Proof.
move=> Qpos; rewrite /divergence.div /chi2_div.
have Hbound : divergence.div P Q <=
    (\sum_(a in T) (P a ^+ 2 / Q a - P a)) * log (sequences.expR 1).
  rewrite big_distrl /= /divergence.div.
  apply: ler_sum => a _.
  have QaN0 : Q a != 0 by apply: lt0r_neq0; exact: Qpos.
  have [Pa0|PaN0] := eqVneq (P a) 0.
    by rewrite Pa0 expr0n /= mul0r !mul0r subr0 mul0r.
  have HPQ : 0 < P a / Q a by rewrite divr_gt0 // lt0r PaN0 FDist.ge0.
  have Hlog := log_id_cmp HPQ.
  rewrite -mulrA -[X in _ - X]mulr1 -mulrBr -mulrA.
  by apply: ler_wpM2l; [exact: FDist.ge0 | exact: Hlog].
have HR : \sum_(a in T) (P a ^+ 2 / Q a - P a) =
    (\sum_(a in T) P a ^+ 2 / Q a) - 1 by rewrite sumrB FDist.f1.
have Hterm : forall a : T, (P a - Q a) ^+ 2 / Q a =
    P a ^+ 2 / Q a - P a *+ 2 + Q a.
  move=> a.
  have QaN0 : Q a != 0 by apply: lt0r_neq0; exact: Qpos.
  apply: (mulIf QaN0).
  rewrite divfK // sqrrB mulrDl mulrBl divfK //.
  by rewrite mulrnAl -expr2.
have HL : \sum_(a in T) (P a - Q a) ^+ 2 / Q a =
    (\sum_(a in T) P a ^+ 2 / Q a) - 1.
  under eq_bigr => a _ do rewrite Hterm.
  rewrite big_split /= sumrB FDist.f1 sumrMnl FDist.f1 mulr2n.
  by rewrite opprD addrA addrNK.
by rewrite HL -HR; exact: Hbound.
Qed.

Local Notation W := (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).

(** kim_mass — the Kim joint law factors as a uniform input times the biased cut.
    @composes: kim_input_private *)
Fact kim_mass (w : Omega) : kim_input_dist w = 4%:R^-1 * W w.2.
Proof. by case: w => [ab k]; rewrite /kim_input_dist fdist_prodE /= fdist_uniformE card_bool2. Qed.

(** kim_w_dev — each Kim weight deviates from uniform by at most the bias.
    @composes: kim_input_private *)
Fact kim_w_dev (k : 'I_5) : `|W k - 5%:R^-1| <= `|eps|.
Proof.
rewrite /W kim_weight_distE; case: ifP => _.
  by rewrite addrAC subrr add0r normrN.
have -> : 5%:R^-1 + eps / 4%:R - 5%:R^-1 = eps / 4%:R by lra.
rewrite normrM (@ger0_norm _ (4%:R^-1)) ?invr_ge0 //.
by rewrite ler_pdivrMr ?ltr0n // ler_peMr ?normr_ge0 // ler1n.
Qed.

(** kim_w_ge — each Kim weight is at least the uniform value minus the bias.
    @composes: kim_input_private *)
Fact kim_w_ge (k : 'I_5) : 5%:R^-1 - `|eps| <= W k.
Proof.
have := kim_w_dev k; rewrite ler_norml => /andP[H1 _]; lra.
Qed.

(** kim_w_tv — the Kim weight vector deviates from uniform by total variation
    at most twice the bias.
    @composes: kim_input_private *)
Fact kim_w_tv : \sum_(k in 'I_5) `|W k - 5%:R^-1| <= 2%:R * `|eps|.
Proof.
rewrite /W /kim_weight_dist /=.
rewrite big_ord_recl big_ord_recr /= !ffunE /=.
under eq_bigr => i _ do rewrite ffunE /=.
have inner_eq : `|5%:R^-1 + eps / 4%:R - 5%:R^-1| = `|eps / 4%:R|
  by congr (`| _ |); lra.
have step : \sum_(i < 3) `|(5%:R^-1 + eps / 4%:R) - 5%:R^-1| = `|eps / 4%:R| *+ 3
  by rewrite sumr_const card_ord inner_eq.
rewrite step inner_eq.
have -> : 5%:R^-1 - eps - 5%:R^-1 = - eps by lra.
rewrite normrN normrM (@ger0_norm _ (4%:R^-1)) ?invr_ge0 //.
by rewrite -mulr_natr; lra.
Qed.

(** kim_q — the weight a given input deals to a given view: the cut mass that
    realises that partial reveal.
    @intent: per-input view law, summed weight of cuts matching the view. *)
Definition kim_q (A : seq nat) (x : bool * bool) (v : (size A).-tuple bool) : R :=
  \sum_(k in 'I_5 | ViewA R A (x, k) == v) W k.
Arguments kim_q A x v : clear implicits.

(** kim_qctr — the uniform-cut reference value for kim_q: the same sum with each
    weight replaced by 1 / 5.
    @intent: the den Boer (unbiased) view law against which kim_q is compared. *)
Definition kim_qctr (A : seq nat) (x : bool * bool)
    (v : (size A).-tuple bool) : R :=
  \sum_(k in 'I_5 | ViewA R A (x, k) == v) 5%:R^-1.
Arguments kim_qctr A x v : clear implicits.

(** kim_qbar — the view law conditioned on the output being false: the average
    of kim_q over the three false-fibre inputs.
    @intent: the product-reference view marginal in the chi-square comparison. *)
Definition kim_qbar (A : seq nat) (v : (size A).-tuple bool) : R :=
  3%:R^-1 * \sum_(x in {: bool * bool} | ~~ (x.1 && x.2)) kim_q A x v.
Arguments kim_qbar A v : clear implicits.

(** kim_q_ge0 — kim_q is non-negative.
    @composes: kim_input_private *)
Fact kim_q_ge0 (A : seq nat) (x : bool * bool) (v : (size A).-tuple bool) :
  0 <= kim_q A x v.
Proof. by apply: sumr_ge0 => k _; exact: FDist.ge0. Qed.

(** kim_qbar_ge0 — kim_qbar is non-negative.
    @composes: kim_input_private *)
Fact kim_qbar_ge0 (A : seq nat) (v : (size A).-tuple bool) : 0 <= kim_qbar A v.
Proof.
rewrite /kim_qbar mulr_ge0 ?invr_ge0 ?ler0n //.
by apply: sumr_ge0 => x _; exact: kim_q_ge0.
Qed.

(** kim_qsum1 — kim_q is a probability law over views.
    @composes: kim_input_private *)
Fact kim_qsum1 (A : seq nat) (x : bool * bool) : \sum_v kim_q A x v = 1.
Proof.
rewrite /kim_q (exchange_big_dep predT) //=.
under eq_bigr => k _ do rewrite (big_pred1 (ViewA R A (x, k))) //=.
exact: (FDist.f1 W).
Qed.

(** kim_qctr_card — the uniform reference value counts the cuts matching the
    view, as a preimage cardinality of the joint input-view map.
    @composes: kim_input_private *)
Fact kim_qctr_card (A : seq nat) (x : bool * bool) (v : (size A).-tuple bool) :
  kim_qctr A x v =
  #|preim [% Inputs R, ViewA R A] (pred1 (x, v))|%:R * 5%:R^-1.
Proof.
rewrite /kim_qctr -sum1_card natr_sum big_distrl /=.
rewrite [RHS](reindex (fun k : 'I_5 => ((x, k) : Omega))) /=; last first.
  exists (fun w : Omega => w.2) => [k _|]; first by [].
  by move=> [[a b] k]; rewrite !inE /= xpair_eqE => /andP[/eqP /= -> _].
apply: eq_big => [k|k _]; last by rewrite mul1r.
rewrite inE /=.
have -> : [% Inputs R, ViewA R A] (x, k) = (x, ViewA R A (x, k)) by case: x.
by rewrite xpair_eqE eqxx.
Qed.

(** kim_qctr_eq — equal-output inputs share the uniform reference view value:
    the cut count realising a view is the same across the false fibre.
    @composes: kim_input_private *)
Fact kim_qctr_eq (A : seq nat) (x x' : bool * bool) (v : (size A).-tuple bool) :
  x.1 && x.2 = x'.1 && x'.2 -> kim_qctr A x v = kim_qctr A x' v.
Proof.
move=> Hxx; rewrite !kim_qctr_card.
by rewrite (den_boer_view_count_eq R v Hxx).
Qed.

(** kim_q_dev — the per-input view law deviates from the uniform reference in
    total variation by at most twice the bias.
    @composes: kim_input_private *)
Fact kim_q_dev (A : seq nat) (x : bool * bool) :
  \sum_v `|kim_q A x v - kim_qctr A x v| <= 2%:R * `|eps|.
Proof.
apply: (order.Order.POrderTheory.le_trans
  (y := \sum_(k in 'I_5) `|W k - 5%:R^-1|)); last exact: kim_w_tv.
rewrite [X in _ <= X](eq_bigr (fun k =>
  \sum_(v | ViewA R A (x, k) == v) `|W k - 5%:R^-1|)); last first.
  move=> i _.
  rewrite (eq_bigl (fun v => v == ViewA R A (x, i)));
    last by move=> v; rewrite eq_sym.
  by rewrite big_pred1_eq.
rewrite (exchange_big_dep predT) //=.
apply: ler_sum => v _.
rewrite /kim_q /kim_qctr -sumrB.
apply: (order.Order.POrderTheory.le_trans (ler_norm_sum _ _ _)).
by apply: ler_sum => k _.
Qed.

(** kim_qbar_diff — a false-fibre input's view law differs from the mixed
    reference in total variation by at most four times the bias.
    @composes: kim_input_private *)
Fact kim_qbar_diff (A : seq nat) (x : bool * bool) :
  ~~ (x.1 && x.2) ->
  \sum_v `|kim_q A x v - kim_qbar A v| <= 4%:R * `|eps|.
Proof. Admitted.

(** kim_input_private — under Kim's biased cut, a partial view carries at most
    kim_leak_bound eps conditional mutual information about the inputs given the
    output a && b.
    @main security: cond_mutual_info bound on inputs vs view given the secret. *)
Lemma kim_input_private (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps.
Proof.
Admitted.

End kim_input_privacy.
